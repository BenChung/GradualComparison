class A:
	def f() -> Int:
		return 1
class B:
	def g() -> String:
		return "meh"

class DAB(A,B):
	def f() -> Int:
		return 1
	def g() -> String:
		return "meh"

class D:
	def main(self:D, x:DAB, i : Int):
		if i == 0:
			return x.f() 
		else:
			return x.g()

D().main(A(), 0)
