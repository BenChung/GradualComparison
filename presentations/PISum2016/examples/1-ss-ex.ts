class Gun {
	shoot() {
		console.log("bang")
	}
}

class Pencil {}

class Cowboy {
	draw(gun : !Gun) {
		gun.shoot()
	}
}

new Cowboy().draw(<any> new Pencil())
