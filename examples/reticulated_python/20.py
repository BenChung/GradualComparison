
@fields({'a' : Dyn})
class E:
	a = 1

@fields({'a' : Int})
class Ep:
	a = 1

@fields({'a' : Dyn})
class A:
	a = 1

@fields({'a' : Int, 'b' : Ap})
class Ap:
	a = 1

def cast(a : Ap) -> Int:
	return a.a

a = A()
a.b = A()
a.b.b = A()
a.b.b.b  = a
print(cast(a))