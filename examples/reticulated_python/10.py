class Fact:
	def mult(self:Fact, x:int, y:int) -> int:
		if x == 0:
			return 0
		else:
			return y+self.mult(x-1, y)
	def fact(self:Fact, x:Dyn) -> Dyn:
		if x == 0:
			return 1
		else:
			return self.mult(x, self.fact(x-1))
	def main(self:Fact) -> Dyn:
		return self.fact(6)

print(Fact().main())
