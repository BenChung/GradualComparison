class C:
	def m1(self,x:C)->Dyn:
		return 2

class E:
	def m1(self,x:E)->Int:
		return 2

c = C()
e = castE(c)
c.m1(c)
