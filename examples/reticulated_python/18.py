class A:
	def foo(self:A) -> Int:
		return 1

class B(A):
	def foo(self) -> Int:
		return 1

class C(A):
	def foo(self) -> Int:
		return 1

def f(x:{'a' : B}):
    x.a
    
class M(metaclass=Monotonic):
    a = B()

p = M()
f(p)
p.a = C()
