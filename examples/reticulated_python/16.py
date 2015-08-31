class B:
	def foo() -> Int:
		return 2

class C:
	def foo() -> Dyn:
		return "hello"

@fields({'b' : B, 'c' : C})
class C:
	b = B()
	c = C()
	def main(self:C) -> Int:
		self.c = C()
		self.b = self.c
		return self.b.foo()


print(C().main())
