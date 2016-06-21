class Empty:
	def baz() -> Void:
		pass
class Test:
	def foo(b:Empty) -> Void:
		print("foo")

def magic(a:Int) -> Dyn:
	return a

Test.foo(magic(2))