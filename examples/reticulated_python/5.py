@fields({'a':Dyn, 'b':Dyn})
class A:
	def __init__(self, a:Dyn, b:Dyn):
		self.a = a
		self.b = b
	def main(self:A) -> Dyn:
		return self.foo(self.a, self.b)
	def foo(self:A, a:Int, b:Int) -> Int:
		return a + b

A(2,2).main()
