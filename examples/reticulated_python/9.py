class Mult:
	def mult(self:Mult, x:int, y:int) -> int:
		if x == 0:
			return 0
		else:
			return y+self.mult(x-1, y)
	def main(self:Mult) -> dyn:
		return self.mult(6,6)