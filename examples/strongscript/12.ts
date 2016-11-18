class Fruit { say():!string {} }
class Apple extends Fruit { say():!string { return "apple" } }
class Banana extends Fruit { say():!string { return "banana" } }

class Main {
  main():!string {
    var f:!Fruit = new Apple()
    f = new Banana()
    f.say()
  }
}

