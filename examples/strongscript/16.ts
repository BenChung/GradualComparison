class B {
	foo():!number { return 2 }
}
class C {
	foo():any { return "hello" }
}

class D {
	b:!B
	c:!C
	main():!number {
		this.c = new C()
		this.b = <!B>this.c
		return this.b.foo()
	}
}