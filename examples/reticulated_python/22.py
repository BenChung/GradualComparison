@fields({'a' : Dyn})
class A:
	a = 0

@fields({'a' : Int})
class B:
	a = 0

def cast(b:B) -> B:
	return b

def err(a:A) -> Int:
	c = cast(a)
	return 2

a = A()
a.a = 2
err(a)
a.a = "bar"
print(a.a)