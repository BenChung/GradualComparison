class Test:
    def id(self, x : Dyn) -> Dyn:
        return x
class TestTyped:
    def id(self, x : Int) -> Int:
        return x
class TestTypedPrime:
    def id(self, x : String) -> String:
        return x

def cast(x : Dyn) -> TestTyped:
    return x

def evil(x):
    return x("hello")

print(evil(cast(Test()).id))