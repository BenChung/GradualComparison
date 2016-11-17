class Pistol:
	def __init__(self):
		pass
	def reload(self) -> Int:  
		return 6

class Shotgun:
	def cock(self) -> Int:
		return 1

@fields({'gun':Dyn})
class Cowboy:
	def __init__(self, gun:Dyn):
		self.gun = gun
	gun = None

class Western:
	def __init__(self):
		pass
	def scene(self) -> Void:
		cowboy1 = Cowboy(Pistol())
		self.prepare(cowboy1)
		cowboy1.gun = Shotgun()


	def prepare(self, cowboy : {'gun':Pistol}) -> Void:
		cowboy.gun.reload()	


movie = Western()
movie.scene()
