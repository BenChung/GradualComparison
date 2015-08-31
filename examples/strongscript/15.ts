class A {
}

class B extends A {
	foo():!number { return 2 }

}
class C extends A {
	bar():!number { return 3 }
}

class D {
	a:!A;
	b:!B;
	c:!C;
	main():!number {
		this.b = <!B>new B()
		this.a = this.b
		this.c = <!C>this.a
		return this.b.foo()
	}
}

new D().main()