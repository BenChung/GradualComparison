class A {
	foo() : !number { return 1 }
}

class B {
	foo() : !string {return "meh"}
}

class D {
	ref : !A
	anyref : any
	main() : !B {
		this.ref = new A()
		this.anyref = this.ref
		return this.anyref
	}
}
