/* Internal helper shared between lyrics layout and lyrics edit code */
#pragma once

#include "types/string.h"

namespace mu {

inline String extractLeadingVerseNumber(const String& text, const bool withSpaces = false)
{
    if (text.isEmpty() || !text.at(0).isDigit()) {
        return String();
    }

    size_t i = 0;
    while (i < text.size() && text.at(i).isDigit()) {
        ++i;
    }

    if (i < text.size() && text.at(i) == u'.') {
        ++i;
    }

    size_t endDotOrDigit = i;
    while (i < text.size() && text.at(i).isSpace()) {
        ++i;
    }

    if (withSpaces) {
        endDotOrDigit = i;
    }

    if (i >= text.size() || !text.at(i).isLetter()) {
        return String();
    }

    return text.mid(0, endDotOrDigit);
}

} // namespace mu::engraving
