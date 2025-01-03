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
    "a|b|c|d": {  # "a|b|c|d"
        "a": True,
        "b": True,
        "c": True,
        "d": True,
        "ab": False,
        "cd": False,
        "abcd": False,
        "a" * 100: False,  # 100 'a's
        "bbbbbbbbb": False  # 9 'b's
    },
    "a*": {  # "a*"
        "aaa": True,
        "a": True,
        "b": False,
        "c": False,
        "d": False,
        "a" * 100: True,  # 100 'a's
        "a" * 99 + "b": False  # 99 'a's followed by 'b'
    },
    "b*": {  # "b*"
        "bbb": True,
        "b": True,
        "a": False,
        "cd": False,
        "b" * 100: True,  # 100 'b's
        "abcd": False  # Mixed 'a', 'b', 'c', 'd'
    },
    "a*b*c*d*": {  # "a*b*c*d*"
        "aaaabbbbccccdddd": True,
        "ab": True,
        "abcd": True,
        "a": True,
        "b": True,
        "c": True,
        "d": True,
        "a" * 50 + "b" * 20 + "c" * 15 + "d" * 10: True,  # 50 'a's, 20 'b's, 15 'c's, 10 'd's
        "abcdabcd": False,  # Repeated pattern
        "acbd": False  # 'c' and 'b' are out of order
    },
    "(a|b|c|d)*": {  # "(a|b|c|d)*"
        "abab": True,
        "ab": True,
        "ba": True,
        "aaaa": True,
        "abcd": True,
        "a" * 100 + "b" * 100: True,  # 100 'a's followed by 100 'b's
        "acbd": True,  # Mixed order of 'a', 'b', 'c', 'd'
        "xyz": False  # Contains 'x', 'y', and 'z', which are not in the alphabet
    },
    "a*b*c*d*|b*a*d*c*": {  # "a*b*c*d*|b*a*d*c*"
        "ab": True,
        "ba": True,
        "abcd": True,
        "acbd": False,
        "aaaaabbbbbcccd": True,  # Several 'a's, 'b's, 'c's, and 'd's in order
        "bcad": False,  # Mixed order of 'b', 'c', 'a', 'd'
        "ababcd": False  # Wrong ordering of characters
    },
    "(aa)*|bb*|cc*|dd*": {  # "(aa)*|bb*|cc*|dd*"
        "aa": True,
        "aaaa": True,
        "bb": True,
        "cc": True,
        "dd": True,
        "bbbbb": True,  # One or more 'b's
        "abcd": False,  # Mixed characters
        "abab": False  # Incorrect pattern
    },
    "a|(b|(c|d))*(d|b)*": {  # "a|(b|(c|d))*(d|b)*"
        "a": True,
        "b": True,
        "c": True,
        "d": True,
        "ab": False,
        "ac": False,
        "ad": False,
        "ba": False,
        "bb": True,
        "bc": True,
        "bd": True,
        "bcd": True,
        "bbdd": True,
        "dcb": True,
        "cdb": True,
        "aabbcd": False,
        "abbbccdd": False,
        "abcda": False,
        "abccba": False,
        "abbbcdcd": False,
        "abcdabcd": False,
        "abcdabcdabcd": False,
        "abccbaabcd": False,
        "abdc": False,
        "acbd": False,
        "adbbcc": False,
        "abbccdde": False,  # Contains invalid ending 'e'
        "abcae": False,  # Contains 'e'
        "abcde": False,  # Contains 'e' which is outside the alphabet
        "bbcc": True,  # Invalid combination with no proper nesting
        "acdd": False  # Incorrect order of 'c' and 'd'
    }
}
