class Mult {
  mul(x:!number,y:!number):!number { 
     if(x==0){ return 0 } 
     else { return y+mul(x+(-1), y) } 
  }
  main():any { return mul(6,6) }
}
