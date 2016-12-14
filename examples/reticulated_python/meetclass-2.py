class C:
	def m1(self,x:C,v:Int,g:Dyn)->Dyn:
		return 2

class D:
	def m1(self,x:D,v:Dyn,g:Int)->Dyn:
		return 2

class E:
	def m1(self,x:E,v:Int,g:Int)->Dyn:
		return 2

def castD(e:D) -> D:
	return e

c = C()
e = castD(c)
c.m1(c,2,2)
