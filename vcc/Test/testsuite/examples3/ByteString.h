#ifndef _BYTESTRING_H
#define _BYTESTRING_H

#include <vcc.h>

typedef unsigned char            UINT8;
typedef unsigned char            BYTE;
typedef UINT8                    BOOL;
typedef unsigned short           UINT16;
typedef short                    INT16;
typedef unsigned long            UINT32;
typedef long                     INT32;
typedef unsigned long long       UINT64;
typedef long long                INT64;

_(ghost
typedef BYTE ByteSequence[\integer];

typedef _(record) struct ByteString {
    ByteSequence bytes;
    \integer length;

} ByteString;
)

_(def \bool valid(ByteString s)
{
    return s.length >= 0 && (\forall \integer i; (i < 0 || s.length <= i) ==> (s.bytes[i] == (BYTE) 0));
}
)

_(logic \bool nonempty(ByteString s) = valid(s) && s.length > 0)

_(def ByteString empty()
{
    return (ByteString) {
        .length = 0,
        .bytes = \lambda \integer i; (BYTE) 0
        };
}
)

_(def ByteString cons(ByteString s, BYTE b)
    _(requires valid(s))
    _(ensures \result.bytes[0] == b)
{
    return (ByteString) {
        .length = s.length + 1,
        .bytes = \lambda \integer i;
            i == 0                        ?    b :
            1 <= i && i < s.length + 1    ?    s.bytes[i - 1] :
                                            (BYTE) 0
        };
}
)

_(def ByteString substring(ByteString s, \integer first, \integer len)
    _(requires valid(s))
    _(requires len > 0 ==> 0 <= first && first < s.length)
    _(requires 0 <= len && len < s.length - first + 1)
{
    return (ByteString) {
        .length = len,
        .bytes = \lambda \integer i;
            0 <= i && i < len    ?    s.bytes[first + i] :
                                    (BYTE) 0
        };
}
)

_(def ByteString concat(ByteString s1, ByteString s2)
    _(requires valid(s1) && valid(s2))
{
    return (ByteString) {
        .length = s1.length + s2.length,
        .bytes = \lambda \integer i;
            0 <= i && i < s1.length                        ?    s1.bytes[i] :
            s1.length <= i && i < s1.length + s2.length    ?    s2.bytes [i - s1.length] :
            (BYTE) 0
        };
}
)

_(def ByteString reversed(ByteString s)
    _(requires valid(s))
{
    return (ByteString) {
        .length = s.length,
        .bytes = \lambda \integer i;
            0 <= i && i < s.length    ?    s.bytes [s.length - i - 1]:
                                        (BYTE) 0
        };
}
)

_(def ByteString from_array(BYTE a[], \integer size)
    _(reads \universe())
    _(requires size >= 0)
    _(ensures \forall \integer i; {a[i]} 0 <= i && i < size ==> a[i] == \result.bytes[i])
{
    return (ByteString) {
        .length = size,
        .bytes = \lambda \integer i;
            0 <= i && i < size    ?    a [i] :
                                    (BYTE) 0
        };
}
)

_(def \bool contains_byte_string(BYTE a[], ByteString s)
    _(reads \universe())
    _(requires valid(s))
{
    return s == from_array(a, s.length);
}
)

_(abstract ByteString int_bytes(\integer x, size_t size)
    _(requires x >= 0)
    _(ensures valid(\result))
    _(ensures \result.length == size)
    _(decreases size)
{
    return size == 0 ? empty() : cons(int_bytes(x / 8, size - 1), (BYTE)(x % 256));
})

_(axiom \forall UINT16 x, y; int_bytes((\integer)x, 2) == int_bytes((\integer)y, 2) ==> x == y)
_(axiom \forall UINT32 x, y; int_bytes((\integer)x, 4) == int_bytes((\integer)y, 4) ==> x == y)
_(axiom \forall UINT64 x, y; int_bytes((\integer)x, 8) == int_bytes((\integer)y, 8) ==> x == y)

_(ghost

/* Lemmas */

_(pure) void lemma_cons_injective(ByteString s1, BYTE b1, ByteString s2, BYTE b2)
    _(requires valid(s1) && valid(s2))
    _(ensures cons(s1, b1) == cons(s2, b2) <==> s1 == s2 && b1 == b2)
{
    _(assert b1 == cons(s1, b1).bytes[0])
    _(assert \forall \integer i; 0 <= i && i < s1.length ==> s1.bytes[i] == cons(s1, b1).bytes[i + 1])
}

_(pure) void lemma_concat_associative(ByteString s1, ByteString s2, ByteString s3)
    _(requires valid(s1) && valid(s2) && valid(s3))
    _(ensures concat(s1, concat(s2, s3)) == concat(concat(s1, s2), s3))
{}

_(pure) void lemma_concat_substring(ByteString s, \integer i)
    _(requires valid(s))
    _(requires 0 <= i && i < s.length)
    _(ensures concat(substring(s, 0, i), substring(s, i, s.length - i)) == s)
{}

_(pure) void lemma_substring_concat(ByteString s1, ByteString s2)
    _(requires valid(s1) && valid(s2))
    _(ensures s1 == substring(concat(s1, s2), 0, s1.length))
    _(ensures s2 == substring(concat(s1, s2), s1.length, s2.length))
{}

_(pure) void lemma_substring_concat_generic()
    _(ensures \forall ByteString s1, s2; valid(s1) && valid(s2) ==> s1 == substring(concat(s1, s2), 0, s1.length) && s2 == substring(concat(s1, s2), s1.length, s2.length))
{}

_(pure) void lemma_concat_injective(ByteString s1, ByteString s2, ByteString t1, ByteString t2)
    _(requires valid(s1) && valid(s2) && valid(t1) && valid(t2))
    _(requires s1.length == t1.length)
    _(ensures concat(s1, s2) == concat(t1, t2) <==> s1 == t1 && s2 == t2)
{
    _(assert s1 == substring(concat(s1, s2), 0, s1.length))
    _(assert s2 == substring(concat(s1, s2), s1.length, s2.length))
}

_(pure) void lemma_reverse_twice(ByteString s)
    _(requires valid(s))
    _(ensures reversed(reversed(s)) == s)
{}

_(pure) void lemma_reverse_injective(ByteString s1, ByteString s2)
    _(requires valid(s1) && valid(s2))
    _(ensures reversed(s1) == reversed(s2) <==> s1 == s2)
{
    lemma_reverse_twice(s1);
    lemma_reverse_twice(s2);
}

_(pure) void lemma_from_array_concat(BYTE a[], \integer m, \integer n)
    _(reads \universe())
    _(requires m >= 0 && n >= 0)
    _(ensures from_array(a, n + m) == concat(from_array(a, m), from_array(a + m, n)))
{}

_(pure) void lemma_contains_concat(BYTE a[], ByteString s1, ByteString s2)
    _(reads \universe())
    _(requires valid(s1) && valid(s2))
    _(ensures contains_byte_string(a, concat(s1, s2)) <==> contains_byte_string(a, s1) && contains_byte_string(a + s1.length, s2))
{
    lemma_substring_concat(s1, s2);
}
)

#endif
