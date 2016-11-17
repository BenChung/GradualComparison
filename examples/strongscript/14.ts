class Inner {
  var i : any
  set(x:any) { i = x }
  get():any { return x }
}

class Main {
  main():any {
    i = new Inner()
    i.set(1)
    i.set("test")
    return i.get()
  }
}
