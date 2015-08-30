
@fields({'i':dyn})
class Inner:
	def set(self:Inner, x:dyn):
		self.i = x
	def get(self:Inner):
		return self.i


@fields({'i':Inner})
class Main:
	i = Inner()
	def main(self:Main) -> dyn:
		self.i = Inner()
		self.i.set(1)
		self.i.set("test")
		return self.i.get()
