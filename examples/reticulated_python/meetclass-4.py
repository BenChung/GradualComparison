def dcast(x:Dyn)->Dyn:
	return x

class C:
	def m1(self,x:C)->Dyn:
		return 2

class E:
	def m1(self,x:E)->Int:
		return 2

def castE(e:E) -> E:
	return e

c = C()
#e = castE(c)
c.m1(C())
