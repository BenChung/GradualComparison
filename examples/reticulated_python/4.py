class A:
	def getN()->Int:
		return 2

class B:
	def foo()->String:
		return "meh"

@fields({'ref' : A, 'anyref' : Dyn})
class D:
	ref = A()
	anyref = A()
	def main(self:D) -> B:
		self.ref = A()
		self.anyref = self.ref
		return self.anyref

d = D()
d.main()
