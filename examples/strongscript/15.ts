class A {
	var a:Dyn
}

class B extends A {
	var a:Int
}

class C {
	var a:A
	var b:B
	var i:Int
	main():Int {
		this.a = new B(1)
		this.b = <B>this.a //a.a must be an Int now
		this.a.a = "foo" // Shouldn't work - type violation
		return this.b.a 
	}
}
