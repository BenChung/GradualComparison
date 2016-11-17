class A:
	def main(self:A):
		return self.tbs(2, 3)
	def tbs(self:A, a:Dyn, b:Dyn) -> Dyn:
		return a + b

A().main()
