class A:
	def getN()->Int:
		return 2

class C(A):
	def getN()->Int:
		return 4

@fields({'ref' : A, 'anyref' : Dyn})
class D:
	ref = A()
	anyref = A()
	def main(self:D) -> C:
		self.ref = C()
		self.anyref = self.ref
		return self.anyref


D().main()
