class Gun:
	def shoot(self) -> Void:
		pass


@fields({'gun':Dyn})
class Cowboy:
	def __init__(self, gun):
		self.gun = gun
	def draw(self) -> Void:
		self.gun.shoot()

@fields({'gun':Gun})
class Cowboy2:
	def draw(self) -> Void:
		pass

def magic(inp : Cowboy2) -> Cowboy2:
	return inp

cowboy = Cowboy(Gun())
cowboy.draw()
cowboy2 = magic(cowboy)
cowboy2.draw()
cowboy.gun = 42
cowboy2.draw()
