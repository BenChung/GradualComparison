	
class Gun { shoot() { } }

class Pencil { write() {} }

class Cowboy {
  draw (gun)        { gun.shoot() }

  draw2(gun :  Gun) { gun.shoot() }

  draw3(gun : !Gun) { gun.shoot() }
}

