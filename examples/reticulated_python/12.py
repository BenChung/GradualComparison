class Fruit:
	def say()->string:
		return "Fruit"
class Apple(Fruit):
	def say()->string:
		return "apple"
class Banana(Fruit):
	def say()->string:
		return "banana"

@fields({'f':Fruit})
class Main:
	f=Fruit()
	def main(self:Main) -> string:
		self.f = Apple()
		self.f = Banana()
		return self.say()