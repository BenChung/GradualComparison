
@fields({'a' : Dyn})
class A:
	a = 1

@fields({'a' : Int})
class Ap:
	a = 1

@fields({'b': Dyn})
class B:
	b = 1

@fields({'b' : A})
class Bp:
	b = A()

@fields({'b' : Ap})
class Bpp:
	b = Ap()

def cast(b : Bp) -> Bp:
	return b

def cast2(b : Bpp) -> Bpp:
	return b

x = B()
x.b = A()

xp = cast(x)
xpp = cast2(x)
x.b.a = "hi"

print(x.b.a)
print(xpp.b.a + 2)
