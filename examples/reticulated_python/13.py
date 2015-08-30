class Fruit:
	def say()->string:
		return "Fruit"
class Animal:
	def say()->string:
		return "animal"
class Apple(Fruit):
	def say()->string:
		return "apple"
class Cat(Animal):
	def say()->string:
		return "animal"

@fields({'f':Fruit})
class Main:
	f=Fruit()
	def main(self:Main) -> string:
		self.f = Apple()
		self.f = Cat()
		return self.say()