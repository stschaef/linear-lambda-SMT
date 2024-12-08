from z3 import *
import re
import time


def mkStr(n):
    string = ""
    for i in range(n):
        string+="xyz"
    string+="a"
    return string

string = mkStr(100)
# print(string)
is_match =  re.compile('a|b|c|d').fullmatch("a")
if is_match:
    print(is_match.groups())
else:
    print("no")


tests = [
    # (regex, string, expected_boolean)
    (r"hello*", "hello", True),
    (r"hello", "hello world", False),
    (r"Hello*", "hello", False),
    # (r"\d+", "123456", True),
    # (r"\d{5}", "12345", True),
    # (r"\d{5}", "1234", False),
    # (r"[A-Za-z0-9]+", "abc123XYZ", True),
    # (r"[A-Za-z0-9]+", "abc-123", False),
    # (r"^abc$", "abc", True),
    # (r"^abc$", "ab", False),
    # (r"\w+", "hello_world123", True),
    # (r"\w+", "hello world", False),
    # (r"\s+", "   ", True),
    # (r"\S+", "   ", False),
    # (r"(cat|dog)", "cat", True),
    # (r"(cat|dog)", "cow", False),
    # (r"(ab)(cd)?(ef)", "abef", True),
    # (r"(ab)(cd)?(ef)", "abcdef", True),
    (r"(a(bc)d)", "abcd", True),
    # (r"ab(?=c)", "abc", True),
    # (r"ab(?=c)", "abx", False),
    # (r"abc(?!d)", "abcx", True),
    # (r"abc(?!d)", "abcd", False),
    # (r"^\w+$", "café", True),
    # (r"[A-Z][a-z]{2,5}\d{2,4}", "Abc123", True),
    # (r"[A-Z][a-z]{2,5}\d{2,4}", "Ab12", False),
]

for pattern, string, expected in tests:
    regex = re.compile(pattern)
    result = bool(regex.fullmatch(string))
    print(f"Pattern: {pattern}, String: '{string}' => ")
    if(result == expected):
        print("yes")
    else:
        print("no")
    # print(f"Pattern: {pattern}, String: '{string}' => "
    #       f"{'Matched' if result else 'Did not match'}; "
    #       f"Expected: {'Matched' if expected else 'Did not match'}")


from test_regex_lib import tests

def str_to_ll(s):
    if len(s) < 2:
        return eval(s)
    return eval(s[0])+str_to_ll(s[1:])

for regex, cases in tests.items():
    start = time.time()
    print("testing", regex)
    for case, match in cases.items():
        # if not match:       # uncomment this to run tests with non-matching strings
        #     continue
        print("\ttesting", case)
        tmp = re.compile(regex)
        result = bool(tmp.fullmatch(case))
        print("\t", result)
        if(result == match):
            print("yes")
        else:
            print("no")
    end = time.time()
    print("time taken:", end-start)