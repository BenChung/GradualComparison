class Empty {
	baz() {}
}
class Test {
	foo(b : Empty) {
		console.log("foo")
	}
}

new Test().foo(<any>2)