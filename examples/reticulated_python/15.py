@fields({'a':Dyn})
class A:
	a = 1
	def setA(self:A, v:dyn):
		self.a = v

@fields({'a':Int})
class B(A):
	a = 1
	setA(self:B, v:dyn):
		# empty

@fields({'a' : A, 'b' : B})
class C:
	a = A()
	b = B()
	def main(self:C) -> Int:
		self.a = A()
		self.b = a # a is now required to be an int
		self.a.setA("hello") # should get a type violation
		return self.b.a


