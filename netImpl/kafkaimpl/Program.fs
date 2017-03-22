// Learn more about F# at http://fsharp.org
// See the 'F# Tutorial' project for more help.
open System
open Parser

[<EntryPoint>]
let main argv = 
    let res = Parser.parse @"
class B {
    f:D
    fd:Z
    fsa:D
    m(x:any):any { <D>new B(x, y, z) }
    m(x:any):any { (<D>new B(x, y, z)).bee(baz) }
    m(x:any):any { too.bar(); 
                   too.bee(); 
                   too.bam() }
    m(x:any):any { too.bar(baz) }
    m(x:any):any { too.bar: C -> D (baz) }
    m(x:any):any { too@bar(baz) }
    m(x:any):any { too@bar(baz).bar(baz).bar : C -> D(bee).bar() }
}
class D {}
hello"
    printfn "%A" argv
    0 // return an integer exit code
