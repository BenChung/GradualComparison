@fields({'a' : Dyn})
class A:
	def __init__(self, a:Int):
		self.a = a
	def getA(self:A)->Dyn:
		return self.a

@fields({'a' : Int})
class B(A):
	a = 1
	def __init__(self:B, a:Int):
		self.a = a
	def getA(self:B)->Int:
		return self.a

@fields({'ref' : A})
class C:
	ref = A(1)
	def main(self):
		self.ref = A(2)
		self.ref = B(2)
		self.ref.getA()


C().main()
