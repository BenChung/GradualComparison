class Fact {
  mul(x:!number,y:!number):!number { 
     if(x==0){ return 0 } 
     else { y+mul(x+(-1), y) } 
  }
  fact(x:!number):any { 
     if(x==0){ return 1 } 
     else { return mul(x, fact(x+(-1))) } 
  }
  main():any { return this.fact(5) }
}
