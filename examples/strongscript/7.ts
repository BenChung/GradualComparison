class A {
	f() : !number { return 1 }
}

class B {
	g() : !string { return "meh" }
}

class DAB {
	f() : !number { return 2 }	
	g() : !string { return "meh" }
}

class D {
	main(x:DAB, i:!number) {
		if (i == 0) { return x.f() } else { return x.g() }
	}
}

// use case:
new D().main( new A(), 0 )
new D().main( new B(), 1 )
