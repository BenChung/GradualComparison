class Pistol:
	pass

class Shotgun:
	def cock(self):
		pass

@fields({'gun' : Dyn})
class Cowboy:
	def __init__(self, gun):
		self.gun = gun

def prepare(cowboy : {'gun':Shotgun}) -> Void:
	pass

cowboy = Cowboy(Shotgun())
prepare(cowboy)
cowboy.gun = Pistol()
