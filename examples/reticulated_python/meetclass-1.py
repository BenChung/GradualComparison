class C:
	def m1(self,v:Int,g:Dyn)->Dyn:
		return 2

class D:
	def m1(self,v:Dyn,g:Int)->Dyn:
		return 2

class E:
	def m1(self,v:Int,g:Int)->Dyn:
		return 2

def castC(e:C) -> C:
	return e

e = E()
c = castC(e)
c.m1(2,2)
