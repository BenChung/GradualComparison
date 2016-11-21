# demonstrate that RPy updates the RTTI of objects at cast sites, and then checks assignments against that type

class Gun:
	pass

class Shotgun:
	def cock(self) -> Int:
		return 1

class Cowboy:
	def __init__(self, gun:Dyn):
		self.gun = gun
	gun = None

def prepare(cowboy : {'gun':Shotgun}) -> Void:
	pass


Shotgun().cock()
