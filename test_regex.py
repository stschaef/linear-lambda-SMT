# Functions as defined in your request
def tensor(a, b):
    return f"({a} ⊗ {b})"

def oplus(a, b):
    return f"({a} ⊕ {b})"

def star(a):
    return f"({a}*)"

def one():
    return "1"  # Empty string in linear logic

# Updated tests with the linear logic representations
tests = {
    "oplus(oplus(oplus(a, b), c), d)": {  # "a|b|c|d"
        "a": True,
        "b": True,
        "c": True,
        "d": True,
        "ab": False,
        "cd": False,
        "abcd": False,
        "a" * 100: True,  # 100 'a's
        "bbbbbbbbb": False  # 9 'b's
    },
    "star(a)": {  # "a*"
        "aaa": True,
        "a": True,
        "b": False,
        "c": False,
        "d": False,
        "a" * 100: True,  # 100 'a's
        "a" * 99 + "b": False  # 99 'a's followed by 'b'
    },
    "star(b)": {  # "b*"
        "bbb": True,
        "b": True,
        "a": False,
        "cd": False,
        "b" * 100: True,  # 100 'b's
        "abcd": False  # Mixed 'a', 'b', 'c', 'd'
    },
    "tensor(star(a), tensor(star(b), tensor(star(c), star(d))))": {  # "a*b*c*d*"
        "aaaabbbbccccdddd": True,
        "ab": True,
        "abcd": True,
        "a": True,
        "b": True,
        "c": True,
        "d": True,
        "a" * 50 + "b" * 20 + "c" * 15 + "d" * 10: True,  # 50 'a's, 20 'b's, 15 'c's, 10 'd's
        "abcdabcd": True,  # Repeated pattern
        "acbd": False  # 'c' and 'b' are out of order
    },
    "star(oplus(oplus(oplus(a, b), c), d))": {  # "(a|b|c|d)*"
        "abab": True,
        "ab": True,
        "ba": True,
        "aaaa": True,
        "abcd": True,
        "a" * 100 + "b" * 100: True,  # 100 'a's followed by 100 'b's
        "acbd": True,  # Mixed order of 'a', 'b', 'c', 'd'
        "xyz": False  # Contains 'x', 'y', and 'z', which are not in the alphabet
    },
    "oplus(tensor(tensor(star(a), star(b)), tensor(star(c), star(d))), tensor(tensor(star(b), star(a)), tensor(star(d), star(c))))": {  # "a*b*c*d*|b*a*d*c*"
        "ab": True,
        "ba": True,
        "abcd": True,
        "acbd": True,
        "aaaaabbbbbcccd": True,  # Several 'a's, 'b's, 'c's, and 'd's in order
        "bcad": True,  # Mixed order of 'b', 'c', 'a', 'd'
        "ababcd": False  # Wrong ordering of characters
    },
    "oplus(oplus(oplus(star( tensor(a, a)), star(b)), star(c)), star(d))": {  # "(aa)*|bb*|cc*|dd*"
        "aa": True,
        "aaaa": True,
        "bb": True,
        "cc": True,
        "dd": True,
        "bbbbb": True,  # One or more 'b's
        "abcd": False,  # Mixed characters
        "abab": False  # Incorrect pattern
    },
    "oplus(a, tensor(star(oplus(b, star(oplus(c, d)))), star(oplus(d, b))))": {  # "a|(b|(c|d))*(d|b)*"
        "a": True,
        "b": True,
        "c": True,
        "d": True,
        "ab": True,
        "ac": True,
        "ad": True,
        "ba": True,
        "bb": True,
        "bc": True,
        "bd": True,
        "bcd": True,
        "bbdd": True,
        "dcb": True,
        "cdb": True,
        "aabbcd": True,
        "abbbccdd": True,
        "abcda": True,
        "abccba": True,
        "abbbcdcd": True,
        "abcdabcd": True,
        "abcdabcdabcd": True,
        "abccbaabcd": True,
        "abdc": True,
        "acbd": True,
        "adbbcc": True,
        "abbccdde": False,  # Contains invalid ending 'e'
        "abcae": False,  # Contains 'e'
        "abcde": False,  # Contains 'e' which is outside the alphabet
        "bbcc": False,  # Invalid combination with no proper nesting
        "acdd": False  # Incorrect order of 'c' and 'd'
    }
}
