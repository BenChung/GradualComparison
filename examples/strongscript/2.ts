class A {
	constructor(public a) {}
	getA() { return this.a }
}

class B extends A {
	constructor(public a : !number) {super(a); }
	getA():!number { return this.a }
}

class C {
	constructor(public ref) {}
	main() {
		var ref:!A = new A(2)
		ref = new B(2)
		return ref.getA()
	}
}
