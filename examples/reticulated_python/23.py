class A:
	def x(self,i:Dyn) -> Dyn:
		return 2

class B:
	def x(self,i:Int) -> Int:
		return i

class C:
	def x(self,i:str) -> str:
		return i

def castA(i:A) -> A:
	return i
def castB(i:B) -> B:
	return i
def castC(i:C) -> C:
	return i

ca = castA(B())
ca.x("boo")
r = castC(ca)
r.x("foo")