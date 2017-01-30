class C:
    def n(self, x:C) -> C:
        return self
class D:
    def o(self, x:D) -> D:
        return self

class A:
    def m(self, x:Dyn) -> Dyn:
        return self
class I:
    def m(self, x:C) -> C:
        return x

class J:
    def m(self, x:D) -> D:
        return x

@fields({'f':I,'g':J})
class E:
    def __init__(self, f, g):
        self.f = f
        self.g = g


class T:
    def t(self, x:Dyn) -> Dyn:
        E(x,x).f

T().t(A())
