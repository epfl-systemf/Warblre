//Provides: check_string
function check_string (s) {
    if (typeof s !== 'string') {
        throw new TypeError('"' + s.toString() + '" does not have type string.');
    }
    return s;
}

//Provides: check_utf16_char
//Requires: check_string
function check_utf16_char (c) {
    check_string(c);
    if (c.length !== 1) {
        throw new TypeError('"' + c.toString() + '" is not a single Utf16 code unit.');
    }
    return c;
}

//Provides: char_utf16_equal
//Requires: check_utf16_char
function char_utf16_equal (l, r) {
    check_utf16_char(l);
    check_utf16_char(r);
    return l === r;
}

//Provides: char_utf16_compare
//Requires: check_utf16_char
function char_utf16_compare (l, r) {
    check_utf16_char(l);
    check_utf16_char(r);
    return r.charCodeAt(0) - l.charCodeAt(0);
}

//Provides: char_utf16_numeric_value
//Requires: check_utf16_char
function char_utf16_numeric_value (c) {
    check_utf16_char(c);
    return c.charCodeAt(0);
}


//Provides: char_utf16_from_numeric_value
//Requires: check_utf16_char
function char_utf16_from_numeric_value (i) {
    if (typeof i !== 'number' || Math.floor(i) !== i) {
        throw new TypeError('"' + i.toString() + '" is not an integer.');
    }
    if (i < 0 || 0xFFFF < i) {
        throw new Error(i.toString() + " is not a valid Utf16 numeric value.")
    }
    return check_utf16_char(String.fromCharCode(i));
}

//Provides: char_utf16_to_uppercase
//Requires: check_utf16_char,char_utf16_numeric_value,char_utf16_from_numeric_value
function char_utf16_to_uppercase (ch) {
    check_utf16_char(ch);
    const u = ch.toUpperCase();
    if (u.length > 1) {
        return ch;
    }
    else {
        const cu = u.charCodeAt(0);
        if (char_utf16_numeric_value(ch) >= 128 && cu < 128) {
            return ch;
        }
        else {
            return char_utf16_from_numeric_value(cu);
        }
    }
}

//Provides: string_equal
//Requires: check_string
function string_equal (l, r) {
    check_string(l);
    check_string(r);
    return l === r;
}