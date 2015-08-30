
@fields({'i':Dyn})
class Inner:
	i = 1
	def set(self:Inner, x:Dyn):
		self.i = x
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
