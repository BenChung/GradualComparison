class A:
	def x(self,i:Dyn) -> Dyn:
		return 2

class B:
	def x(self,i:Int) -> Int:
		return i

def cast(i:B) -> B:
	return i
def castA(i:A) -> A:
	return i

print(castA(cast(A())).x("foo"))