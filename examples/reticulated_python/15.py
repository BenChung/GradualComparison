@fields({'a':Dyn})
class A:
	a = 1

@fields({'a':Int})
class B(A):
	a = 1

@fields({'a' : A, 'b' : B, 'i' : Int})
class C:
	a = A()
	b = B()
	i = 2
	def main(self:C) -> Int:
		self.a = B()
		self.b = self.a
		self.a.a = "foo"
		return self.b.a


