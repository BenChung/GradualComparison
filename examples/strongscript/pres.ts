class Gun {
	shoot() {}
}

class Pencil {}

class Cowboy {
	draw(gun) { // no type -> 1 Gun -> 2 !Gun
		gun.shoot()
	}
}

new Cowboy().draw(new Gun())
//new Cowboy().draw(new Pencil())
//new Cowboy().draw(new Pencil()) -> 1
//new Cowboy().draw(<any>new Pencil()) -> 2
//new Cowboy().draw(<any>new Pencil())

