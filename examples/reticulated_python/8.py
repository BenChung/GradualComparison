class A:
	def main(self:A) -> Dyn:
		return self.f(2)
	def f(self:A, i:Dyn) -> Dyn:
		return i

print(A().main())
