class Fruit:
	def say(self:Fruit)->str:
		return "Fruit"
class Animal:
	def say(self:Animal)->str:
		return "animal"
class Apple(Fruit):
	def say(self:Apple)->str:
		return "apple"
class Cat(Animal):
	def say(self:Cat)->str:
		return "animal"

@fields({'f':Fruit})
class Main:
	f=Fruit()
	def main(self:Main) -> str:
		self.f = Apple()
		self.f = Cat()
		return self.f.say()

Main().main()
