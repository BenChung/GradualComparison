class C:
    def n(self, x:C) -> C:
        return self

@fields({'x':C})
class X:
  def __init__(self):
      self.x = "hello"

o = X()
print(o.x)
