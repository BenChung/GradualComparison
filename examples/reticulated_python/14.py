
@fields({'i':Dyn})
class Inner:
	i = 1
	def set(self:Inner, x:Dyn) -> Dyn:
		self.i = x
		return self.i
	def get(self:Inner):
		return self.i


@fields({'i':Inner})
class Main:
	i = Inner()
	def main(self:Main) -> Dyn:
		self.i = Inner()
		self.i.set(1)
		self.i.set("test")
		return self.i.get()


Main().main()
