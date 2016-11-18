class Gun {
	shoot() {
		console.log("bang")
	}
}

class Pencil {
	write() {}
}

class Cowboy {
	draw(gun) {
		gun.shoot()
	}
	draw2(gun : Gun) {
		gun.shoot()
	}
	draw3(gun : !Gun) {
		gun.shoot()
	}
}



new Cowboy().draw(new Gun())     // Success
 
//new Cowboy().draw(new Pencil())  // Failure

//new Cowboy().draw(<any> new Pencil())

//new Cowboy().draw2(new Pencil())

//new Cowboy().draw2(<any>new Pencil())

//new Cowboy().draw3( new Pencil())

//new Cowboy().draw2(<any> new Pencil())

//(<any> new Cowboy()) .draw4( new Pencil() )

// (<any> new Cowboy()) .draw3( new Pencil() ) 

