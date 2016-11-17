class A {
	constructor() {}
	getN():!number { return 2; }
}

class C extends A {
	constructor() {super()}
	getN():!number { return 4; }
}

class D {
	constructor(public ref : !A, public anyref) {}
	main():!number { 
		this.ref = new C();
		this.anyref = this.ref;
		return this.anyref; }
}
