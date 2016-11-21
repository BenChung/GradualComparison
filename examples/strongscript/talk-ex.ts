class Point3d {
	constructor(
		public x,
		public y,
		public z) {}
	sqnorm() {
		return this.x*this.x + this.y*this.y + this.z*this.z
	}
}

class LinkedList {
	constructor(
		public point : Point3d, 
		public next : !LinkedList) {}
	append(p:Point3d):!LinkedList {
		return new LinkedList(p,this)
	}
}

new LinkedList(new Point3d("foo","bar","bas"), new LinkedList(new Point3d(1,2,3), null)) // okay

new LinkedList(new Point3d("foo","bar","bas"), new LinkedList(<any>2, null)) // also okay

//change to point : !Point3d
new LinkedList(new Point3d("foo","bar","bas"), new LinkedList(<any>2, null)) // not okay anymore

new LinkedList(new Point3d("foo","bar","bas"), new LinkedList(new Point3d(1,2,3), null)) // still okay

