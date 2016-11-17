class Gun:
	def shoot(self) -> Void:
		print("bang")
		pass

@fields({'gun':Dyn})
class Cowboy:
	def __init__(self, gun):
		self.gun = gun
	def draw(self) -> Void:
		self.gun.shoot()

@fields({'gun':Gun})
class Sheriff:
	def draw(self) -> Void:
		pass

def magic(inp : Sheriff) -> Sheriff:
	return inp

cowboy = Cowboy(Gun())
cowboy.draw()
sheriff = magic(cowboy)
sheriff.draw()
cowboy.gun = 42
print(cowboy.gun)
print(sheriff.gun)
