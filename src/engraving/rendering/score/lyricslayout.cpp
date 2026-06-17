/*
 * SPDX-License-Identifier: GPL-3.0-only
 * MuseScore-Studio-CLA-applies
 *
 * MuseScore Studio
 * Music Composition & Notation
 *
 * Copyright (C) 2023 MuseScore Limited and others
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License version 3 as
 * published by the Free Software Foundation.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <https://www.gnu.org/licenses/>.
 */
#include "lyricslayout.h"

#include "dom/factory.h"
#include "dom/repeatlist.h"
#include "style/styledef.h"

#include "dom/chordrest.h"
#include "dom/lyrics.h"
#include "dom/measure.h"
#include "dom/score.h"
#include "dom/segment.h"
#include "dom/staff.h"
#include "dom/stafftype.h"
#include "dom/system.h"

#include "editing/undo.h"

#include "tlayout.h"
#include "textlayout.h"

#include <cmath>
#include <limits>
#include <set>

using namespace mu;
using namespace mu::engraving;
using namespace mu::engraving::rendering::score;
#include "lyrics_utils.h"

namespace {
constexpr bool kVerboseLyricsVerseScanLog = false;

int textColumns(const String& s)
{
    int col = 0;
    for (size_t i = 0; i < s.size(); ++i) {
        if (!s.at(i).isHighSurrogate()) {
            ++col;
        }
    }
    return col;
}

// Use shared helper from lyrics_utils.h

void cleanupLeadingVerseNumberFormattingIfDefault(Score* score, staff_idx_t staffIdx)
{
    if (!score) {
        return;
    }

    std::map<int, bool> firstSyllableChecked;
    const track_idx_t startTrack = staffIdx * VOICES;
    const track_idx_t endTrack = startTrack + VOICES;

    for (Measure* measure = score->firstMeasure(); measure; measure = measure->nextMeasure()) {
        for (Segment& seg : measure->segments()) {
            if (!seg.isChordRestType()) {
                continue;
            }
            for (track_idx_t track = startTrack; track < endTrack; ++track) {
                EngravingItem* el = seg.element(track);
                if (!el || !el->isChordRest()) {
                    continue;
                }

                for (Lyrics* lyr : toChordRest(el)->lyrics()) {
                    const int verse = lyr->verse();
                    if (firstSyllableChecked.count(verse)) {
                        continue;
                    }
                    firstSyllableChecked[verse] = true;

                    const String plain = lyr->plainText();
                    const String leading = extractLeadingVerseNumber(plain, true);
                    if (leading.isEmpty()) {
                        continue;
                    }

                    const int leadingCols = textColumns(leading);
                    if (leadingCols <= 0) {
                        continue;
                    }

                    const FontStyle defaultStyle = FontStyle(lyr->propertyDefault(Pid::FONT_STYLE).value<int>());
                    const Color defaultColor = lyr->propertyDefault(Pid::COLOR).value<Color>();
                    const String defaultFamily = lyr->propertyDefault(Pid::FONT_FACE).value<String>();
                    const double defaultSize = lyr->propertyDefault(Pid::FONT_SIZE).toDouble();
                    const VerticalAlignment defaultValign = VerticalAlignment(lyr->propertyDefault(Pid::TEXT_SCRIPT_ALIGN).toInt());

                    const String plainXml = TextBase::plainToXmlText(plain);
                    if (lyr->xmlText() == plainXml) {
                        continue;
                    }

                    lyr->createBlocks();
                    const std::list<TextFragment> fragments = lyr->fragmentList();

                    bool leadingHasDefaultStyleAndColor = true;
                    bool allFormattingDefault = true;
                    int col = 0;

                    for (const TextFragment& fragment : fragments) {
                        const FontStyle fragmentStyle = fragment.format.style();
                        const Color fragmentColor = fragment.format.color();
                        const String fragmentFamily = fragment.format.fontFamily();
                        const double fragmentSize = fragment.format.fontSize();
                        const VerticalAlignment fragmentValign = fragment.format.valign();

                        if (fragmentStyle != defaultStyle
                            || fragmentColor != defaultColor
                            || fragmentFamily != defaultFamily
                            || std::fabs(fragmentSize - defaultSize) > 0.01
                            || fragmentValign != defaultValign) {
                            allFormattingDefault = false;
                        }

                        for (size_t i = 0; i < fragment.text.size(); ++i) {
                            if (fragment.text.at(i).isHighSurrogate()) {
                                continue;
                            }
                            if (col < leadingCols && (fragmentStyle != defaultStyle || fragmentColor != defaultColor)) {
                                leadingHasDefaultStyleAndColor = false;
                            }
                            ++col;
                        }
                    }

                    if (leadingHasDefaultStyleAndColor && allFormattingDefault) {
                        lyr->setPlainText(plain);
                    }
                }
            }
        }
    }
}

void clearGeneratedLyricsLabels(staff_idx_t staffIdx, System* system)
{
    if (!system) {
        return;
    }

    const track_idx_t startTrack = staffIdx * VOICES;
    const track_idx_t endTrack = startTrack + VOICES;
    size_t removedCount = 0;
    size_t removeFailedCount = 0;

    for (MeasureBase* mb : system->measures()) {
        if (!mb || !mb->isMeasure()) {
            continue;
        }

        Measure* measure = toMeasure(mb);
        for (Segment& segment : measure->segments()) {
            if (!segment.isChordRestType()) {
                continue;
            }

            for (track_idx_t track = startTrack; track < endTrack; ++track) {
                EngravingItem* element = segment.element(track);
                if (!element || !element->isChordRest()) {
                    continue;
                }

                ChordRest* cr = toChordRest(element);
                if (!cr) {
                    continue;
                }

                std::vector<EngravingItem*> toDelete;
                toDelete.reserve(cr->el().size());
                for (EngravingItem* child : cr->el()) {
                    if (child && child->type() == ElementType::LYRICS_LABEL && child->generated()) {
                        toDelete.push_back(child);
                    }
                }

                for (EngravingItem* child : toDelete) {
                    if (!child) {
                        continue;
                    }
                    // Remove from owner list first; only delete on success to avoid dangling pointers in m_el.
                    cr->remove(child);
                    if (std::find(cr->el().begin(), cr->el().end(), child) == cr->el().end()) {
                        delete child;
                        ++removedCount;
                    } else {
                        LLOG("clearGeneratedLyricsLabels: remove failed for %p on cr %p", child, cr);
                        ++removeFailedCount;
                    }
                }
            }
        }
    }

    if (removedCount || removeFailedCount) {
        LLOG("clearGeneratedLyricsLabels: staff=%ld system=%p removed=%zu failed=%zu",
             staffIdx, system, removedCount, removeFailedCount);
    }
}

}

// extractLeadingVerseNumber implemented as local helper above

// ---------------------------------------------------------------------------
// buildVerseNumberMap
//   Scan all measures to find the first Lyrics per verse for the given staff
//   that has a digit-leading fragment. Returns verseIdx -> display string.
// ---------------------------------------------------------------------------
std::map<int, String> LyricsLayout::buildVerseNumberMap(Score* score, staff_idx_t staffIdx)
{
    std::map<int, String> result;
    std::map<int, bool> firstSyllableChecked;
    if (!score) {
        LOGD("VRNUM buildVerseNumberMap: staff=%ld no score", staffIdx);
        return result;
    }

    const track_idx_t startTrack = staffIdx * VOICES;
    const track_idx_t endTrack = startTrack + VOICES;

    for (Measure* measure = score->firstMeasure(); measure; measure = measure->nextMeasure()) {
        for (Segment& seg : measure->segments()) {
            if (!seg.isChordRestType()) {
                continue;
            }
            for (track_idx_t track = startTrack; track < endTrack; ++track) {
                EngravingItem* el = seg.element(track);
                if (!el || !el->isChordRest()) {
                    continue;
                }
                for (Lyrics* lyr : toChordRest(el)->lyrics()) {
                    const int verse = lyr->verse();
                    if (firstSyllableChecked.count(verse)) {
                        continue; // only inspect first syllable for each verse
                    }

                    firstSyllableChecked[verse] = true;

                    const String leading = extractLeadingVerseNumber(lyr->plainText(), false);
                    if (!leading.isEmpty()) {
                        // Do not alter the original Lyrics formatting here — leave any
                        // in-place formatting untouched. We only record the leading
                        // verse-number string for label generation.
                        result[verse] = leading;
                        // Low-risk: mark leading range invisible in-memory so layout
                        // accounts for width, but rendering will skip painting it.
                        lyr->createBlocks();
                        // mark fragments covering the leading columns as invisible
                        const int leadingCols = textColumns(leading);
                        if ((leadingCols > 0) && !false) {
                            int col = 0;
                            for (TextBlock& tb : lyr->mutldata()->blocks) {
                                int blockCols = tb.columns();
                                if (col >= leadingCols) {
                                    break;
                                }
                                if (col + blockCols <= leadingCols) {
                                    // whole block is in leading part, mark it invisible
                                    tb.changeFormat(FormatId::Invisible, FormatValue(true), 0, blockCols);
                                    col += blockCols;
                                    continue;
                                }
                                // only part of the block is in leading part, split it and mark the leading part
                                tb.changeFormat(FormatId::Invisible, FormatValue(true), 0, leadingCols);
                                break;
                            }
                            lyr->setTextInvalid();
                        }                        
                    }
                }
            }
        }
    }

    return result;
}

void LyricsLayout::precomputeAndCacheVerseNumberMaps(Score* score)
{
    if (!score) return;
    for (staff_idx_t staffIdx = 0; staffIdx < score->nstaves(); ++staffIdx) {
        auto map = buildVerseNumberMap(score, staffIdx);
        score->setCachedVerseNumberMap(staffIdx, map);

        LOGD() << "---------------------------------";
        for (const auto& p : map) {
            LOGD() << "  staff=" << staffIdx << " verse=" << p.first << " -> '" << muPrintable(p.second) << "'";
        }
        LOGD() << "---------------------------------";
    }
}

void LyricsLayout::layout(Lyrics* item, LayoutContext& ctx)
{
    if (!item->explicitParent()) {   // palette & clone trick
        item->setPos(PointF());
        TextLayout::layoutBaseTextBase1(item, ctx);
        return;
    }

    Lyrics::LayoutData* ldata = item->mutldata();

    //
    // parse leading verse number and/or punctuation, so we can factor it into layout separately
    //
    bool hasNumber = false;   // _verseNumber;

    // find:
    // 1) string of numbers and non-word characters at start of syllable
    // 2) at least one other character (indicating start of actual lyric)
    // 3) string of non-word characters at end of syllable
    //QRegularExpression leadingPattern("(^[\\d\\W]+)([^\\d\\W]+)");

    const String text = item->plainText();
    String leading;
    String trailing;

    if (ctx.conf().styleB(Sid::lyricsAlignVerseNumber)) {
        // Use shared helper to extract a normalized leading verse fragment
        leading = extractLeadingVerseNumber(text, true);

        // trailing: keep existing logic to capture non-letter suffix
        size_t trailingIdx = text.size() - 1;
        for (int i = static_cast<int>(text.size() - 1); i >= 0; --i) {
            Char ch = text.at(i);
            if (ch.isLetter()) {
                trailingIdx = i;
                break;
            }
        }

        if (trailingIdx != text.size() - 1) {
            trailing = text.mid(trailingIdx + 1);
        }

        if (!leading.isEmpty()) {
            hasNumber = true;
        }
    }

    createOrRemoveLyricsLine(item, ctx);

    if (item->isMelisma() || hasNumber) {
        // use the melisma style alignment setting
        if (item->isStyled(Pid::POSITION)) {
            if (ctx.conf().styleB(Sid::lyricsCenterDashedSyllables) && !(item->separator() && item->separator()->isEndMelisma())) {
                item->setPosition(AlignH::HCENTER);
            } else {
                item->setPosition(ctx.conf().styleV(Sid::lyricsMelismaAlign).value<Align>().horizontal);
            }
        }
    } else {
        // use the text style alignment setting
        if (item->isStyled(Pid::POSITION)) {
            item->setPosition(item->propertyDefault(Pid::POSITION).value<AlignH>());
        }
    }

    // Negate ChordRest offset
    ChordRest* cr = item->chordRest();
    double x = -cr->x();

    TextLayout::layoutBaseTextBase1(item, ctx);
    TextLayout::computeTextHighResShape(item, ldata);

    double centerAdjust = 0.0;
    double leftAdjust   = 0.0;

    if (ctx.conf().styleB(Sid::lyricsAlignVerseNumber)) {
        // Calculate leading and trailing parts widths. Lyrics
        // should have text layout to be able to do it correctly.
        DO_ASSERT(ldata->blocks.size() != 0);
        if (!leading.isEmpty() || !trailing.isEmpty()) {
            const TextBlock& tb = ldata->blocks.at(0);

            const double leadingXpos = tb.xpos(leading.size(), item);
            const double leadingWidth = leadingXpos - tb.boundingRect().x();
                //  LOGD() << "measurement: leading='" << leading << "' leading.size=" << leading.size()
                //      << " tb.columns=" << tb.columns() << " leadingXpos=" << leadingXpos << " tb.bbox.x=" << tb.boundingRect().x()
                //      << " leadingWidth=" << leadingWidth;
            const size_t trailingPos = text.size() - trailing.size();
            const double trailingWidth = tb.boundingRect().right() - tb.xpos(trailingPos, item);

            leftAdjust = leadingWidth;
            centerAdjust = leadingWidth - trailingWidth;
        }
    }

    if (item->position() == AlignH::HCENTER) {
        //
        // center under notehead, not origin
        // however, lyrics that are melismas or have verse numbers will be forced to left alignment
        //
        // center under note head
        x += -centerAdjust * 0.5;
    } else if (item->position() == AlignH::LEFT) {
        // even for left aligned syllables, ignore leading verse numbers and/or punctuation
        x -= leftAdjust;
    }

    ldata->setPosX(x);

    if (item->ticks().isNotZero()) {
        // set melisma end
        ChordRest* ecr = ctx.mutDom().findCR(item->endTick(), item->track());
        if (ecr) {
            ecr->setMelismaEnd(true);
        }
    }
}

void LyricsLayout::layout(LyricsLine* item)
{
    if (item->isDash()) {    // dash(es)
        item->setNextLyrics(searchNextLyrics(item->lyrics()->segment(),
                                             item->staffIdx(),
                                             item->lyrics()->verse(),
                                             item->lyrics()->placement()
                                             ));
        item->setTrack2(item->nextLyrics() ? item->nextLyrics()->track() : item->track());

        Fraction endTick = item->tick();
        const Measure* lyricsMeasure = item->lyrics()->segment()->measure();
        const Segment* endCRSeg = lyricsMeasure ? lyricsMeasure->last(SegmentType::ChordRest) : nullptr;

        const ChordRest* endCR = nullptr;
        if (endCRSeg && !endCRSeg->empty()) {
            for (EngravingItem* cr : endCRSeg->elist()) {
                if (cr && cr->isChordRest()) {
                    endCR = toChordRest(cr);
                    break;
                }
            }
        }

        if (item->nextLyrics()) {
            endTick = item->nextLyrics()->tick();
        } else if (endCR && endCR->hasFollowingJumpItem()) {
            endTick = endCR->tick();
        }

        item->setTick2(endTick);
    }
}

void LyricsLayout::layout(LyricsLineSegment* item, LayoutContext& ctx)
{
    UNUSED(ctx);

    assert(item->isPartialLyricsLineSegment() || item->lyrics());

    LyricsLineSegment::LayoutData* ldata = item->mutldata();
    ldata->clearDashes();

    if (item->lyricsLine()->isEndMelisma()) {
        layoutMelismaLine(item);
    } else {
        layoutDashes(item);
    }

    double halfLineWidth = item->absoluteFromSpatium(item->lineWidth());
    RectF rect(PointF(), item->pos2());
    rect.adjust(0.0, -halfLineWidth, 0.0, halfLineWidth);

    ldata->setShape(Shape(rect, item));
}

void LyricsLayout::layoutMelismaLine(LyricsLineSegment* item)
{
    const bool isPartialLyricsLine = item->isPartialLyricsLineSegment();
    LyricsLine* lyricsLine = item->lyricsLine();
    Lyrics* startLyrics = lyricsLine->lyrics();

    System* system = item->system();
    if (!system) {
        return;
    }
    const MStyle& style = item->style();

    double startX = lyricsLineStartX(item);
    double endX = lyricsLineEndX(item);

    double tolerance = 0.05 * item->spatium();
    if (endX - startX < style.styleAbsolute(Sid::lyricsMelismaMinLength) - tolerance) {
        const Fraction ticks = isPartialLyricsLine ? lyricsLine->ticks() : startLyrics->ticks();
        if (style.styleB(Sid::lyricsMelismaForce) || ticks == Lyrics::TEMP_MELISMA_TICKS) {
            endX = startX + style.styleAbsolute(Sid::lyricsMelismaMinLength);
        } else {
            endX = startX;
        }
    }

    adjustLyricsLineYOffset(item);

    item->mutldata()->setPosX(startX);
    item->setPos2(PointF(endX - startX, 0.0));

    item->mutldata()->addDash(LineF(PointF(), item->pos2()));
}

void LyricsLayout::layoutDashes(LyricsLineSegment* item)
{
    const bool isPartialLyricsLine = item->isPartialLyricsLineSegment();
    LyricsLine* lyricsLine = item->lyricsLine();

    ChordRest* endCR = lyricsLine->endElement()
                       && lyricsLine->endElement()->isChordRest() ? toChordRest(lyricsLine->endElement()) : nullptr;
    Lyrics* endLyrics = nullptr;
    if (endCR) {
        for (Lyrics* lyr : endCR->lyrics()) {
            if (lyr->verse() == item->verse()) {
                endLyrics = lyr;
                break;
            }
        }
    }

    // When the end element is a timetick segment rather than a chordrest, the start element should be a chord with a following repeat
    ChordRest* startCR = lyricsLine->startElement()
                         && lyricsLine->startElement()->isChordRest() ? toChordRest(lyricsLine->startElement()) : nullptr;
    bool hasFollowingJump = endCR ? endCR->hasFollowingJumpItem() : (startCR ? startCR->hasFollowingJumpItem() : false);

    if (!endLyrics && !isPartialLyricsLine && !hasFollowingJump) {
        return;
    }

    System* system = item->system();
    if (!system) {
        return;
    }
    const MStyle& style = item->style();

    double startX = lyricsLineStartX(item);
    double endX = 0.0;
    if (endCR) {
        endX = lyricsLineEndX(item, endLyrics);
    } else {
        endX = startCR ? startCR->measure()->endingXForOpenEndedLines() : endX;
    }

    adjustLyricsLineYOffset(item, endLyrics);

    item->mutldata()->setPosX(startX);
    item->setPos2(PointF(endX - startX, 0.0));

    bool isDashOnFirstSyllable = lyricsLine->tick2() == system->firstMeasure()->tick();
    const double userStart = startX + item->offset().x();
    const double userEnd = endX + item->userOff2().x();
    double curLength = userEnd - userStart;
    double dashMinLength = style.styleAbsolute(Sid::lyricsDashMinLength);
    bool firstAndLastGapAreHalf = style.styleB(Sid::lyricsDashFirstAndLastGapAreHalf);
    bool forceDash = style.styleB(Sid::lyricsDashForce)
                     || (style.styleB(Sid::lyricsShowDashIfSyllableOnFirstNote) && isDashOnFirstSyllable);
    double maxDashDistance = style.styleAbsolute(Sid::lyricsDashMaxDistance);
    int dashCount = firstAndLastGapAreHalf && curLength > maxDashDistance ? std::ceil(curLength / maxDashDistance)
                    : std::floor(curLength / maxDashDistance);

    if (curLength > dashMinLength || forceDash) {
        dashCount = std::max(dashCount, 1);
    }

    if (style.styleB(Sid::lyricsLimitDashCount)) {
        dashCount = std::min(dashCount, style.styleI(Sid::lyricsMaxDashCount));
    }

    if (curLength < dashMinLength && dashCount > 0) {
        double diff = dashMinLength - curLength;
        if (isDashOnFirstSyllable) {
            startX -= diff;
        } else {
            startX -= 0.5 * diff;
            endX += 0.5 * diff;
        }
        item->mutldata()->setPosX(startX);
        item->setPos2(PointF(endX - startX, 0.0));
        curLength = endX - startX;
    }

    double dashWidth = std::min(curLength, style.styleAbsolute(Sid::lyricsDashMaxLength));

    LyricsDashSystemStart lyricsDashSystemStart = style.styleV(Sid::lyricsDashPosAtStartOfSystem).value<LyricsDashSystemStart>();
    bool dashesLeftAligned = lyricsDashSystemStart != LyricsDashSystemStart::STANDARD && !item->isSingleBeginType();
    double dashDist = curLength / (dashesLeftAligned || firstAndLastGapAreHalf ? dashCount : dashCount + 1);
    double xDash = 0.0;
    if (dashesLeftAligned) {
        for (int i = 0; i < dashCount; ++i) {
            item->mutldata()->addDash(LineF(PointF(xDash, 0.0), PointF(xDash + dashWidth, 0.0)));
            xDash += dashDist;
        }
    } else {
        for (int i = 0; i < dashCount; ++i) {
            if (firstAndLastGapAreHalf && i == 0) {
                xDash += 0.5 * dashDist;
            } else {
                xDash += dashDist;
            }
            item->mutldata()->addDash(LineF(PointF(xDash - 0.5 * dashWidth, 0.0), PointF(xDash + 0.5 * dashWidth, 0.0)));
        }
    }
}

Lyrics* LyricsLayout::findNextLyrics(const ChordRest* endChordRest, int verseNumber)
{
    if (!endChordRest) {
        return nullptr;
    }
    for (Segment* segment = endChordRest->segment()->next1(SegmentType::ChordRest); segment;
         segment = segment->next1(SegmentType::ChordRest)) {
        if (!segment->element(endChordRest->track())) {
            continue;
        }
        ChordRest* nextCR = toChordRest(segment->element(endChordRest->track()));
        for (Lyrics* lyr : nextCR->lyrics()) {
            if (lyr->verse() == verseNumber) {
                return lyr;
            }
        }
    }

    return nullptr;
}

void LyricsLayout::createOrRemoveLyricsLine(Lyrics* item, LayoutContext& ctx)
{
    if (item->needRemoveInvalidSegments()) {
        item->removeInvalidSegments();
    }

    auto isEndMelisma = [item]() {
        return item->ticks().isNotZero();
    };

    Fraction lyricsLineTicks = Lyrics::TEMP_MELISMA_TICKS;

    // Update the end tick
    if (isEndMelisma()) {
        const track_idx_t track = item->track();

        const Segment* const startSegment = item->segment();
        const Fraction startTick = startSegment->tick();

        // if lyrics has a temporary one-chord melisma, interpret as 0 ticks (just its own chord)
        Fraction itemEndTick = item->ticks() == Lyrics::TEMP_MELISMA_TICKS ? startTick : item->endTick();
        Fraction endTick = itemEndTick;

        const Segment* endSegment = startSegment;
        while (endSegment && endSegment->tick() < endTick) {
            endSegment = endSegment->nextCR(track, true);
        }
        if (!endSegment) {
            // user probably deleted measures at end of score, leaving this melisma too long
            // set endSegment to last segment and reset lyricsEndTick to trigger FIXUP code below
            endSegment = ctx.dom().lastSegment();
            endTick = Fraction(-1, 1);
        }

        EngravingItem* endSegmentElement = endSegment->element(track);
        if (endSegment->tick() == endTick && endSegmentElement && endSegmentElement->isChord()) {
            // everything is OK if we have reached a chord at right tick on right track
            // advance to next CR after duration of note, or last segment if no next CR
            const Segment* endChordSeg = endSegment;
            const Chord* endChord = toChord(endSegmentElement);

            endSegment = endChordSeg->nextCR(track, false);

            if (!endSegment || endSegment->tick() > endChord->endTick()) {
                endSegment = endChordSeg;
                while (endSegment && endSegment->tick() < endChord->endTick()) {
                    endSegment = endSegment->nextCR(muse::nidx, true);
                }
            }
        } else {
            // FIXUP - lyrics tick count not valid
            // this happens if edits to score have removed the original end segment
            // so let's fix it here
            // endSegment is already pointing to segment past endTick (or to last segment)
            // we should shorten the lyrics tick count to make this work
            const Segment* ns = endSegment;
            const Segment* ps = endSegment->prev1(SegmentType::ChordRest);
            while (ps && ps != startSegment) {
                EngravingItem* pe = ps->element(track);
                // we're looking for an actual chord on this track
                if (pe && pe->isChord()) {
                    break;
                }
                endSegment = ps;
                ps = ps->prev1(SegmentType::ChordRest);
            }

            if (!ps || ps == startSegment) {
                // either there is no valid previous CR, or the previous CR is the one the lyric starts on
                // we don't want to make the melisma longer arbitrarily, but there is a possibility that the next
                // CR won't extend the melisma, so let's check it
                ps = ns;
                endSegment = ps->nextCR(track, false);
                EngravingItem* e = endSegment ? endSegment->element(track) : nullptr;

                // check to make sure we have a chord
                if (!e || !e->isChord() || ps->tick() > itemEndTick) {
                    // nope, nothing to do but set ticks to 0
                    // this will result in no melisma
                    item->undoChangeProperty(Pid::LYRIC_TICKS, Fraction::fromTicks(0));
                } else {
                    item->undoChangeProperty(Pid::LYRIC_TICKS, ps->tick() - startTick);
                }
            } else {
                item->undoChangeProperty(Pid::LYRIC_TICKS, ps->tick() - startTick);
            }
        }

        if (endSegment) {
            // Lyrics::_ticks points to the beginning of the last spanned segment,
            // but the line shall include it:
            // include the duration of this last segment in the melisma duration
            lyricsLineTicks = endSegment->tick() - startTick;
        } else {
            lyricsLineTicks = item->score()->endTick() - startTick;
        }
    }

    ChordRest* cr = item->chordRest();

    if (isEndMelisma() || item->syllabic() == LyricsSyllabic::BEGIN || item->syllabic() == LyricsSyllabic::MIDDLE) {
        if (!item->separator()) {
            LyricsLine* separator = Factory::createLyricsLine(ctx.mutDom().dummyParent());
            separator->setTick(cr->tick());
            item->setSeparator(separator);
            ctx.mutDom().addUnmanagedSpanner(item->separator());
        }
        item->separator()->setParent(item);
        item->separator()->setTick(cr->tick());
        item->separator()->setTicks(lyricsLineTicks);
        item->separator()->setTrack(item->track());
        item->separator()->setTrack2(item->track());
        item->separator()->styleChanged();
    } else {
        if (item->separator()) {
            item->separator()->removeUnmanaged();
            delete item->separator();
            item->setSeparator(nullptr);
        }
    }
}

void LyricsLayout::computeVerticalPositions(System* system, LayoutContext& ctx)
{
    staff_idx_t nStaves = system->score()->nstaves();
    const bool generateLyricsLabels = ctx.conf().styleB(Sid::lyricsRepeatVerseNumber);

    ChordRest* widthProbeCR = nullptr;
    const track_idx_t maxTrack = nStaves * VOICES;
    for (MeasureBase* mb : system->measures()) {
        if (!mb || !mb->isMeasure()) {
            continue;
        }
        for (Segment& segment : toMeasure(mb)->segments()) {
            if (!segment.isChordRestType()) {
                continue;
            }
            for (track_idx_t track = 0; track < maxTrack; ++track) {
                EngravingItem* e = segment.element(track);
                if (e && e->isChordRest()) {
                    widthProbeCR = toChordRest(e);
                    break;
                }
            }
            if (widthProbeCR) {
                break;
            }
        }
        if (widthProbeCR) {
            break;
        }
    }

    double globalMaxLabelWidth = 0.0;
    if (generateLyricsLabels && widthProbeCR) {
        std::set<String> uniqueLabels;

        for (staff_idx_t staffIdx = 0; staffIdx < nStaves; ++staffIdx) {
            // Do NOT build or mutate the verse-number map during layout.
            // Always read the precomputed cache; if it's dirty, log and use cached map (may be empty).
            std::map<int, String> verseNumberMap = system->score()->cachedVerseNumberMap(staffIdx);
            if (system->score()->verseNumberCache().dirty) {
                LOGD("VRNUM computeVerticalPositions: verseNumberCache dirty during precompute for staff=%ld - using cached map", staffIdx);
            }
            for (const auto& versePair : verseNumberMap) {
                uniqueLabels.insert(versePair.second );
            }
        }
        // Clear dirty flag after precomputation
        system->score()->verseNumberCache().dirty = false;

        LyricsLabel widthProbe(widthProbeCR);
        for (const String& labelText : uniqueLabels) {
            widthProbe.setPlainText(labelText);
            TextLayout::layoutBaseTextBase1(&widthProbe, ctx);
            TextLayout::computeTextHighResShape(&widthProbe, widthProbe.mutldata());
            globalMaxLabelWidth = std::max(globalMaxLabelWidth, widthProbe.ldata()->bbox().width());
        }
    }

    for (staff_idx_t staffIdx = 0; staffIdx < nStaves; ++staffIdx) {
        if (system->staff(staffIdx)->show()) {
            computeVerticalPositions(staffIdx, system, ctx, globalMaxLabelWidth, generateLyricsLabels);
        }
    }
}

void LyricsLayout::computeVerticalPositions(staff_idx_t staffIdx, System* system, LayoutContext& ctx,
                                            double globalMaxLabelWidth, bool generateLyricsLabels)
{
    LyricsVersesMap lyricsVersesAbove;
    LyricsVersesMap lyricsVersesBelow;

    // ALWAYS clear old generated labels - they may be stale after measure moves.
    clearGeneratedLyricsLabels(staffIdx, system);

    // When the feature is disabled, also drop redundant custom prefix formatting
    // if it effectively resolves to default text formatting.
    if (!generateLyricsLabels) {
        cleanupLeadingVerseNumberFormattingIfDefault(system ? system->score() : nullptr, staffIdx);
    }

    collectLyricsVerses(staffIdx, system, lyricsVersesAbove, lyricsVersesBelow);

    setDefaultPositions(staffIdx, lyricsVersesAbove, lyricsVersesBelow, ctx);

    std::map<int, String> verseNumberMap;
    if (generateLyricsLabels) {
        // Layout-time MUST NOT build or mutate the verse-number map.
        // Always read the precomputed cache; if it's dirty, that's an invariant
        // violation indicating we failed to precompute earlier.
        Score* score = system->score();
        if (!score) {
            LLOG("VRNUM computeVerticalPositions: no score for staff=%ld", staffIdx);
        } else if (score->verseNumberCache().dirty) {
            LLOG("VRNUM ERROR: verseNumberCache dirty during layout for staff=%ld - invariant violated", staffIdx);
            // Do NOT call buildVerseNumberMap here. Use cached map (may be empty)
            verseNumberMap = score->cachedVerseNumberMap(staffIdx);
        } else {
            verseNumberMap = score->cachedVerseNumberMap(staffIdx);
        }
    }

    const bool isFirstSystem = (system->firstMeasure() == system->score()->firstMeasure());

    checkCollisionsWithStaffElements(system, staffIdx, ctx, lyricsVersesAbove, lyricsVersesBelow);

    addToSkyline(system, staffIdx, ctx, lyricsVersesAbove, lyricsVersesBelow);

    if (generateLyricsLabels) {
        // Delegate generated label creation & placement to helper
        layoutLyricLabels(system, staffIdx, verseNumberMap, ctx, globalMaxLabelWidth, isFirstSystem);
    }
}

void LyricsLayout::collectLyricsVerses(staff_idx_t staffIdx, System* system, LyricsVersesMap& lyricsVersesAbove,
                                       LyricsVersesMap& lyricsVersesBelow)
{
    track_idx_t startTrack = staffIdx * VOICES;
    track_idx_t endTrack = startTrack + VOICES;

    for (MeasureBase* mb : system->measures()) {
        if (!mb->isMeasure()) {
            continue;
        }
        for (Segment& segment : toMeasure(mb)->segments()) {
            if (!segment.isChordRestType()) {
                continue;
            }
            for (track_idx_t track = startTrack; track < endTrack; ++track) {
                EngravingItem* element = segment.element(track);
                if (!element) {
                    continue;
                }
                for (Lyrics* lyrics : toChordRest(element)->lyrics()) {
                    int verse = lyrics->verse();
                    if (lyrics->placeAbove()) {
                        lyricsVersesAbove[verse].addLyrics(lyrics);
                    } else {
                        lyricsVersesBelow[verse].addLyrics(lyrics);
                    }
                }
            }
        }
    }

    for (SpannerSegment* spannerSegment : system->spannerSegments()) {
        if (spannerSegment->staffIdx() == staffIdx && spannerSegment->isLyricsLineSegment()) {
            if (muse::RealIsNull(spannerSegment->pos2().x())) {
                continue;
            }
            LyricsLineSegment* lyricsLineSegment = toLyricsLineSegment(spannerSegment);
            int verse = lyricsLineSegment->verse();
            if (lyricsLineSegment->lyricsPlaceAbove()) {
                lyricsVersesAbove[verse].addLine(lyricsLineSegment);
            } else {
                lyricsVersesBelow[verse].addLine(lyricsLineSegment);
            }
        }
    }

}

void LyricsLayout::layoutLyricLabels(System* system, staff_idx_t staffIdx, const std::map<int, String>& verseNumberMap,
                                     LayoutContext& ctx, double globalMaxLabelWidth, bool isFirstSystem)
{
    struct LabelPlacement {
        LyricsLabel* label = nullptr;
        ChordRest* anchorCR = nullptr;
        double candidateRightEdge = 0.0;  // used for first-system close placement
        double labelRight = 0.0;
        double labelWidth = 0.0;
        double labelY = 0.0;
    };

    std::vector<LabelPlacement> placements;
    // collect labels from verses already collected by caller
    // We need to find anchor lyrics per verse in this system

    auto collectForVerses = [&](const LyricsVersesMap& lyricsVerses) {
        std::set<int> createdVerses;
        for (const auto& pair : lyricsVerses) {
            int verseNumber = pair.first;

            const LyricsVerse& lyricsVerse = pair.second;
            if (lyricsVerse.lyrics().empty()) {
                continue;
            }

            Lyrics* anchorLyrics = lyricsVerse.lyrics().front();
            ChordRest* anchorCR = anchorLyrics ? anchorLyrics->chordRest() : nullptr;
            if (!anchorCR) {
                continue;
            }

            Measure* crMeasure = anchorCR->measure();
            if (!crMeasure) continue;

            bool measureInSystem = false;
            for (const MeasureBase* mb : system->measures()) {
                if (mb == crMeasure) { measureInSystem = true; break; }
            }
            if (!measureInSystem) continue;

            if (createdVerses.count(verseNumber)) continue;

            const auto verseLabelIt = verseNumberMap.find(verseNumber);
            const String verseLabel = (verseLabelIt != verseNumberMap.end()) ? verseLabelIt->second : String();
            if (verseLabel.isEmpty()) continue;

            LyricsLabel* label = new LyricsLabel(anchorCR);
            LOGD() << "create: staff=" << staffIdx << " cr=" << anchorCR
                   << " verse=" << verseNumber << " label='" << muPrintable(verseLabel) << "'"
                   << " isFirstSystem=" << isFirstSystem
                   << " globalMaxLabelWidth=" << globalMaxLabelWidth;
            label->setPlainText(verseLabel);
            createdVerses.insert(verseNumber);

            if (isFirstSystem) {
                label->setFontStyle(FontStyle(ctx.conf().styleI(Sid::lyricsLabelFirstSystemFontStyle)));
                label->setColor(ctx.conf().styleV(Sid::lyricsLabelFirstSystemColor).value<Color>());
            } else {
                label->setFontStyle(FontStyle(ctx.conf().styleI(Sid::lyricsLabelFollowingSystemFontStyle)));
                label->setColor(ctx.conf().styleV(Sid::lyricsLabelFollowingSystemColor).value<Color>());
            }

            anchorCR->add(label);

              TextLayout::layoutBaseTextBase1(label, ctx);
              TextLayout::computeTextHighResShape(label, label->mutldata());

            const double offset = label->absoluteFromSpatium(ctx.conf().styleS(Sid::lyricsRepeatedVerseNumberOffset));
            const RectF anchorBbox = anchorLyrics->ldata()->bbox();
            const RectF labelBbox = label->ldata()->bbox();

            const double anchorBaseline = anchorLyrics->y() + anchorLyrics->baseLine();
            const double labelY = anchorBaseline - label->baseLine();

              const double anchorLeftSystem = anchorCR->x() + anchorLyrics->x() + anchorBbox.left();
              const double candidateRightEdge = anchorLeftSystem - offset;

              // Debug after computing anchorLeftSystem / candidateRightEdge
              const RectF dbgLabelBbox2 = label->ldata()->bbox();
              LOGD("LyricsLayout DEBUG labelBBox: staff=%ld system=%p verse=%d label=%p left=%f right=%f width=%f",
                  staffIdx, system, anchorLyrics->verse(), label, dbgLabelBbox2.left(), dbgLabelBbox2.right(), dbgLabelBbox2.width());
              LOGD("LyricsLayout DEBUG anchor: cr=%p pageX=%f x=%f anchorLeftSystem=%f candidateRightEdge=%f",
                  anchorCR, anchorCR->pageX(), anchorCR->x(), anchorLeftSystem, candidateRightEdge);
              LOGD("LyricsLayout DEBUG effectiveMaxLabelWidth=%f globalMaxLabelWidth=%f",
                  globalMaxLabelWidth, globalMaxLabelWidth);

              placements.push_back({ label, anchorCR, candidateRightEdge, labelBbox.right(), labelBbox.width(), labelY });
              LOGD("LyricsLabel PoC label: staff=%ld system=%p label=%p cr=%p measure=%d verse=%d",
                  staffIdx, system, label, anchorCR,
                  crMeasure->measureNumber() + 1, anchorLyrics->verse());
        }
    };

    // Reconstruct lyrics verses maps for this system to collect anchors
    LyricsVersesMap lyricsVersesAbove, lyricsVersesBelow;
    collectLyricsVerses(staffIdx, system, lyricsVersesAbove, lyricsVersesBelow);
    collectForVerses(lyricsVersesAbove);
    collectForVerses(lyricsVersesBelow);

    LLOG("LyricsLabel PoC: staff=%ld system=%p placements=%zu live=%zu",
         staffIdx, system, placements.size(), LyricsLabel::debugLiveCount());

    if (placements.empty()) return;

    if (isFirstSystem) {
        double sharedRightEdge = std::numeric_limits<double>::infinity();
        for (const LabelPlacement& placement : placements) {
            sharedRightEdge = std::min(sharedRightEdge, placement.candidateRightEdge);
        }
        for (const LabelPlacement& placement : placements) {
            if (!placement.anchorCR) continue;
            const double labelX = sharedRightEdge - placement.anchorCR->x() - placement.labelRight;
            placement.label->mutldata()->setPosX(labelX);
            placement.label->mutldata()->setPosY(placement.labelY);
        }
    } else {
        double effectiveMaxLabelWidth = globalMaxLabelWidth;
        if (effectiveMaxLabelWidth <= 0.0) {
            for (const LabelPlacement& placement : placements) {
                effectiveMaxLabelWidth = std::max(effectiveMaxLabelWidth, placement.labelWidth);
            }
        }

        const Measure* firstMeasure = system->firstMeasure();
        if (!firstMeasure) {
            for (const LabelPlacement& placement : placements) {
                if (!placement.anchorCR) continue;
                placement.label->mutldata()->setPosX(0.0);
                placement.label->mutldata()->setPosY(placement.labelY);
            }
        } else {
            const double systemLeftPage = firstMeasure->pageBoundingRect().left();
            const double sharedRightPage = systemLeftPage + effectiveMaxLabelWidth;

            for (const LabelPlacement& placement : placements) {
                if (!placement.anchorCR) continue;
                const double labelX = sharedRightPage - placement.anchorCR->pageX() - placement.labelRight;
                placement.label->mutldata()->setPosX(labelX);
                placement.label->mutldata()->setPosY(placement.labelY);
            }
        }
    }
}

void LyricsLayout::setDefaultPositions(staff_idx_t staffIdx, const LyricsVersesMap& lyricsVersesAbove,
                                       const LyricsVersesMap& lyricsVersesBelow,
                                       LayoutContext& ctx)
{
    double staffHeight = ctx.dom().staff(staffIdx)->staffHeight();
    double lyricsLineHeightFactor = ctx.conf().styleD(Sid::lyricsLineHeight);

    int maxVerseAbove = !lyricsVersesAbove.empty() ? lyricsVersesAbove.crbegin()->first : 0;
    for (auto& pair : lyricsVersesAbove) {
        int verse = pair.first;
        const LyricsVerse& lyricsVerse = pair.second;
        for (Lyrics* lyrics : lyricsVerse.lyrics()) {
            double y = -(maxVerseAbove - verse) * lyrics->lineSpacing() * lyricsLineHeightFactor;
            PointF defaultPos = lyrics->defaultPos();
            y += defaultPos.y();
            lyrics->setYRelativeToStaff(y);
        }
        for (LyricsLineSegment* lyricsLineSegment : lyricsVerse.lines()) {
            double y = -(maxVerseAbove - verse) * lyricsLineSegment->lineSpacing() * lyricsLineHeightFactor;
            lyricsLineSegment->move(PointF(0.0, y + lyricsLineSegment->baseLineShift()));
        }
    }

    for (auto& pair : lyricsVersesBelow) {
        int verse = pair.first;
        const LyricsVerse& lyricsVerse = pair.second;
        for (Lyrics* lyrics : lyricsVerse.lyrics()) {
            double y = staffHeight + verse * lyrics->lineSpacing() * lyricsLineHeightFactor;
            PointF defaultPos = lyrics->defaultPos();
            y += defaultPos.y();
            lyrics->setYRelativeToStaff(y);
        }
        for (LyricsLineSegment* lyricsLineSegment : lyricsVerse.lines()) {
            double y = staffHeight + verse * lyricsLineSegment->lineSpacing() * lyricsLineHeightFactor;
            lyricsLineSegment->move(PointF(0.0, y + lyricsLineSegment->baseLineShift()));
        }
    }
}

void LyricsLayout::checkCollisionsWithStaffElements(System* system, staff_idx_t staffIdx,  LayoutContext& ctx,
                                                    const LyricsVersesMap& lyricsVersesAbove,
                                                    const LyricsVersesMap& lyricsVersesBelow)
{
    SysStaff* systemStaff = system->staff(staffIdx);

    double lyricsMinDist = ctx.conf().styleAbsolute(Sid::lyricsMinTopDistance);

    SkylineLine& staffSkylineNorth = systemStaff->skyline().north();
    SkylineLine& staffSkylineSouth = systemStaff->skyline().south();

    int maxVerseAbove = !lyricsVersesAbove.empty() ? lyricsVersesAbove.crbegin()->first : 0;
    int maxVerseBelow = !lyricsVersesBelow.empty() ? lyricsVersesBelow.crbegin()->first : 0;

    for (int verse = maxVerseAbove; verse >= 0; --verse) {
        if (lyricsVersesAbove.count(verse) == 0) {
            continue;
        }
        SkylineLine verseSkyline = createSkylineForVerse(verse, false, lyricsVersesAbove, system);
        double minDistance = -verseSkyline.minDistance(staffSkylineNorth);
        if (minDistance < lyricsMinDist) {
            double diff = lyricsMinDist - minDistance;
            moveThisVerseAndOuterOnes(verse, 0, true, -diff, lyricsVersesAbove);
        }
    }

    for (int verse = 0; verse <= maxVerseBelow; ++verse) {
        if (lyricsVersesBelow.count(verse) == 0) {
            continue;
        }
        SkylineLine verseSkyline = createSkylineForVerse(verse, true, lyricsVersesBelow, system);
        double minDistance = -staffSkylineSouth.minDistance(verseSkyline);
        if (minDistance < lyricsMinDist) {
            double diff = lyricsMinDist - minDistance;
            moveThisVerseAndOuterOnes(verse, maxVerseBelow, false, diff, lyricsVersesBelow);
        }
    }
}

SkylineLine LyricsLayout::createSkylineForVerse(int verse, bool north, const LyricsVersesMap& lyricsVerses, System* system)
{
    double systemX = system->pageX();

    SkylineLine lyricsSkyline(north);

    if (lyricsVerses.count(verse) > 0) {
        const LyricsVerse& lyricsVerse = lyricsVerses.at(verse);
        for (Lyrics* lyrics : lyricsVerse.lyrics()) {
            if (lyrics->addToSkyline()) {
                Shape lyricsShape = lyrics->highResShape().translated(PointF(lyrics->pageX() - systemX, lyrics->yRelativeToStaff()));
                lyricsSkyline.add(lyricsShape);
            }
        }
        for (LyricsLineSegment* lyricsLineSeg : lyricsVerse.lines()) {
            if (lyricsLineSeg->lyricsAddToSkyline()) {
                lyricsSkyline.add(lyricsLineSeg->shape().translate(lyricsLineSeg->pos()));
            }
        }
    }

    return lyricsSkyline;
}

void LyricsLayout::moveThisVerseAndOuterOnes(int verse, int lastVerse, bool above, double diff, const LyricsVersesMap& lyricsVerses)
{
    auto moveVerse = [&](int verse) {
        if (lyricsVerses.count(verse) > 0) {
            const LyricsVerse& lyricsVerse = lyricsVerses.at(verse);
            for (Lyrics* lyrics : lyricsVerse.lyrics()) {
                lyrics->move(PointF(0.0, diff));
            }
            for (LyricsLineSegment* lyricsLineSeg : lyricsVerse.lines()) {
                lyricsLineSeg->move(PointF(0.0, diff));
            }
        }
    };

    if (above) {
        for (int otherVerse = verse; otherVerse >= lastVerse; --otherVerse) {
            moveVerse(otherVerse);
        }
    } else {
        for (int otherVerse = verse; otherVerse <= lastVerse; ++otherVerse) {
            moveVerse(otherVerse);
        }
    }
}

void LyricsLayout::addToSkyline(System* system, staff_idx_t staffIdx, LayoutContext& ctx, const LyricsVersesMap& lyricsVersesAbove,
                                const LyricsVersesMap& lyricsVersesBelow)
{
    double systemX = system->pageX();
    // HACK: subtract minVerticalDistance here because it's added later during staff distance calculations. Needs a better solution.
    double lyricsVerticalPadding = ctx.conf().styleAbsolute(Sid::lyricsMinBottomDistance) - ctx.conf().styleAbsolute(
        Sid::minVerticalDistance);
    Skyline& skyline = system->staff(staffIdx)->skyline();
    for (auto& pair : lyricsVersesAbove) {
        const LyricsVerse& lyricsVerse = pair.second;
        for (Lyrics* lyrics : lyricsVerse.lyrics()) {
            if (lyrics->addToSkyline()) {
                Shape lyricsShape
                    = lyrics->highResShape().translated(PointF(lyrics->pageX() - systemX, lyrics->yRelativeToStaff()));
                skyline.north().add(lyricsShape.adjust(0.0, -lyricsVerticalPadding, 0.0, 0.0));
            }
        }
        for (LyricsLineSegment* lyricsLineSeg : lyricsVerse.lines()) {
            if (lyricsLineSeg->lyricsAddToSkyline()) {
                Shape lineShape = lyricsLineSeg->shape().translate(lyricsLineSeg->pos());
                skyline.north().add(lineShape.adjust(0.0, -lyricsVerticalPadding, 0.0, 0.0));
            }
        }
    }
    for (auto& pair : lyricsVersesBelow) {
        const LyricsVerse& lyricsVerse = pair.second;
        for (Lyrics* lyrics : lyricsVerse.lyrics()) {
            if (lyrics->addToSkyline()) {
                Shape lyricsShape
                    = lyrics->highResShape().translated(PointF(lyrics->pageX() - systemX, lyrics->yRelativeToStaff()));
                skyline.south().add(lyricsShape.adjust(0.0, 0.0, 0.0, lyricsVerticalPadding));
            }
        }
        for (LyricsLineSegment* lyricsLineSeg : lyricsVerse.lines()) {
            if (lyricsLineSeg->lyricsAddToSkyline()) {
                Shape lineShape = lyricsLineSeg->shape().translate(lyricsLineSeg->pos());
                skyline.south().add(lineShape.adjust(0.0, 0.0, 0.0, lyricsVerticalPadding));
            }
        }
    }
}

double LyricsLayout::lyricsLineStartX(const LyricsLineSegment* item)
{
    const System* system = item->system();
    const LyricsLine* lyricsLine = item->lyricsLine();
    const Lyrics* startLyrics = lyricsLine->lyrics();
    const MStyle& style = item->style();
    const bool melisma = lyricsLine->isEndMelisma();

    const LyricsDashSystemStart lyricsDashSystemStart = style.styleV(Sid::lyricsDashPosAtStartOfSystem).value<LyricsDashSystemStart>();
    const bool leading = melisma || (lyricsDashSystemStart != LyricsDashSystemStart::UNDER_FIRST_NOTE);

    // Full melisma or dashes at beginning of system
    if (!item->isSingleBeginType()) {
        return system->firstNoteRestSegmentX(leading);
    }

    // Partial melisma or dashes
    if (lyricsLine->isPartialLyricsLine()) {
        const Measure* measure = lyricsLine->findStartMeasure();
        return measure->firstNoteRestSegmentX(leading);
    }

    // Full melisma or dashes in middle of system
    const double pad = melisma ? style.styleAbsolute(Sid::lyricsMelismaPad) : style.styleAbsolute(Sid::lyricsDashPad);
    const double lyricsRightEdge = startLyrics->pageX() - system->pageX() + startLyrics->shape().right();
    return lyricsRightEdge + pad;
}

double LyricsLayout::lyricsLineEndX(const LyricsLineSegment* item, const Lyrics* endLyrics)
{
    const System* system = item->system();
    const LyricsLine* lyricsLine = item->lyricsLine();
    const ChordRest* endChordRest = toChordRest(lyricsLine->endElement());
    const double systemPageX = system->pageX();
    const MStyle& style = item->style();
    const bool melisma = lyricsLine->isEndMelisma();
    const bool hasFollowingJump = endChordRest->hasFollowingJumpItem();
    const bool hasPrecedingJump = endChordRest->hasPrecedingJumpItem();

    if (!melisma && !item->isPartialLyricsLineSegment() && !endLyrics && !hasFollowingJump) {
        return 0.0;
    }

    const bool dashesEndOfSystem = !melisma && lyricsLine->tick2() == system->endTick();

    // Full melisma or dashes at end of system
    if (!item->isSingleEndType() || dashesEndOfSystem || !lyricsLine->endElement()) {
        return system->endingXForOpenEndedLines();
    }

    // Partial dashes after a repeat
    if (!melisma && hasPrecedingJump && item->isPartialLyricsLineSegment()) {
        if (endLyrics) {
            const double lyricsLeftEdge = endLyrics->pageX() - systemPageX + endLyrics->ldata()->bbox().left();
            return lyricsLeftEdge - style.styleAbsolute(Sid::lyricsDashPad);
        } else if (endChordRest->isChord()) {
            const Chord* endChord = toChord(endChordRest);
            const Note* note = endChord->up() ? endChord->downNote() : endChord->upNote();
            return note->pageX() - systemPageX + note->headWidth();
        }
    }

    // Full dashes or melisma before a repeat - possibly with a partial dash/repeat on the other side of the repeat
    if (endChordRest && hasFollowingJump && !lyricsLine->nextLyrics()) {
        Measure* endMeasure = lyricsLine->findEndMeasure();
        // check if there is a partial lyrics line in a following measure
        if (repeatHasPartialLyricLine(endMeasure) || endChordRest == lyricsLine->startElement()) {
            return endMeasure->endingXForOpenEndedLines();
        }
    }

    // Full or partial dashes in middle of system
    if (!melisma && endLyrics) {
        const double lyricsLeftEdge = endLyrics->pageX() - systemPageX + endLyrics->ldata()->bbox().left();
        return lyricsLeftEdge - style.styleAbsolute(Sid::lyricsDashPad);
    }

    // Full or partial melisma in middle of system
    if (endChordRest->isChord()) {
        const Chord* endChord = toChord(endChordRest);
        const Note* note = endChord->up() ? endChord->downNote() : endChord->upNote();
        return note->pageX() - systemPageX + note->headWidth();
    }

    return endChordRest->pageX() - systemPageX + endChordRest->rightEdge();
}

void LyricsLayout::adjustLyricsLineYOffset(LyricsLineSegment* item, const Lyrics* endLyrics)
{
    const LyricsLine* lyricsLine = item->lyricsLine();
    ChordRest* endChordRest = lyricsLine->endElement()
                              && lyricsLine->endElement()->isChordRest() ? toChordRest(lyricsLine->endElement()) : nullptr;
    const Lyrics* startLyrics = lyricsLine->lyrics();
    const bool melisma = lyricsLine->isEndMelisma();

    LyricsLineSegment::LayoutData* ldata = item->mutldata();

    // Partial melisma or dashes
    if (lyricsLine->isPartialLyricsLine()) {
        Lyrics* nextLyrics = findNextLyrics(endChordRest, item->verse());
        if (nextLyrics) {
            PointF nextLyricsDefaultPos = nextLyrics->defaultPos();
            ldata->setPosY(nextLyrics->offset().y() + nextLyricsDefaultPos.y());
        } else {
            PointF lyricsOffset = item->styleValue(Pid::OFFSET,
                                                   item->placeBelow() ? Sid::lyricsPosBelow : Sid::lyricsPosAbove).value<PointF>();
            ldata->setPosY(lyricsOffset.y());
        }
        return;
    }

    if (item->isSingleBeginType()) {
        PointF startLyricsDefaultPos = startLyrics->defaultPos();
        ldata->setPosY(startLyrics->offset().y() + startLyricsDefaultPos.y());
        return;
    }

    if (melisma || !endLyrics) {
        const Lyrics* nextLyrics = findNextLyrics(endChordRest, item->verse());

        const Lyrics* refLyrics = nextLyrics ? nextLyrics : startLyrics;
        PointF refLyricsDefaultPos = refLyrics->defaultPos();

        ldata->setPosY(refLyrics->offset().y() + refLyricsDefaultPos.y());
        return;
    }

    PointF endLyricsDefaultPos = endLyrics->defaultPos();

    ldata->setPosY(endLyrics->offset().y() + endLyricsDefaultPos.y());
}
