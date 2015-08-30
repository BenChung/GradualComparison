class Fact:
	def mult(self:Mult, x:int, y:int) -> int:
		if x == 0:
			return 0
		else:
			return y+self.mult(x-1, y)
	def fact(self:Mult, x:int) -> any:
		if x == 0:
			return 1
		else:
			return self.mul(x, self.fact(x-1))
	def main(self:Mult) -> dyn:
		return self.mult(6,6)