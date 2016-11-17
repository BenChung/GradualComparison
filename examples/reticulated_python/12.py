class Fruit:
	def say(self:Fruit)->str:
		return "Fruit"
class Apple:
	def say(self:Apple)->str:
		return "apple"
class Banana:
	def say(self:Banana)->str:
		return "banana"

@fields({'f':Fruit})
class Main:
	f=Fruit()
	def main(self:Main) -> str:
		self.f = Apple()
		self.f = Banana()
		return self.f.say()

print(Main().main())
