class Fruit { say():!string {} }
class Animal { say():!string {} }
class Apple extends Fruit { say():!string { "apple" } }
class Cat extends Animal { say():!string { "cat" } }

class Main {
  main():!string {
    var f:!Fruit = new Apple()
    f = new Cat()
    f.say()
  }
}
