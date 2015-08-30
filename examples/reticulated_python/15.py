@fields({'a':Dyn})
class A:
	a = 1
	def setA(self:A, v:Dyn):
		self.a = v

@fields({'a':Int})
class B(A):
	a = 1
	def setA(self:B, v:Dyn):
		# empty
		return

@fields({'a' : A, 'b' : B})
class C:
	a = A()
	b = B()
	def main(self:C) -> Dyn:
		self.a = A()
		self.b = self.a # a is now required to be an int
		self.a.setA("hello") # should get a type violation
		return self.a.a


print(C().main())
