class C:
    def n(self, x:C) -> C:
        return self
class D:
    def o(self, x:D) -> D:
        return self

@fields({'f':Dyn})
class A:
    def __init__(self, f):
        self.f = f
    def m(self, x:A) -> A:
        res = A(C())
        self.f = res
        return res

@fields({'f':D})
class I:
    def __init__(self, f):
        self.f = f
    def m(self, x:I) -> I:
        return self

class T:
    def s(self, x:I) -> I:
        return x.m(x)
    def t(self, x:Dyn) -> Dyn:
        return self.s(x)


T().t(A(D()))
