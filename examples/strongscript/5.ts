class A {
	a : any
	b : any
	main():any {
		this.foo(this.a, this.b)
	}
	foo(a:!number, b:!number) {
		return a + b
	}
}
