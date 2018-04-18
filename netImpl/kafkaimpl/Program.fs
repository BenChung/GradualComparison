﻿// Learn more about F# at http://fsharp.org
// See the 'F# Tutorial' project for more help.
open System
open Parser
open AST
open CGAST
open CodeGen

(**
Optional Semantics:

*****************Litmus test one*****************

@"
class A {
    m(x:Any):Any { this } }
class I {
    n(x:Any):Any { this } }
class T {
    s(x:Any):Any { this } 
    t(x:Any):Any {this@s : Any -> Any (x) }}

(new T())@t(new A())"


*****************Litmus test two*****************

@"
class A {
    m(x:Any):Any { this } }
class Q {
    n(x:Any):Any { this } }
class I {
    m(x:Any):Any { this } }
class T {
    s(x:Any):Any { this } 
    t(x:Any):Any { this@s : Any -> Any (x) }}

(new T())@t(new A())"


*****************Litmus test three*****************

@"
class C {
    a(x:Any):Any { this } }
class D {
    b(x:Any):Any { this } }
class E {
    a(x:Any):Any { this } }
class F {
    m(x:Any):Any { x } 
    n(x:Any):Any { this@m : Any -> Any (x) }}

(new F())@n(new C())@a(new C())"


***************************************************
Transient Semantics:

*****************Litmus test one*****************

@"
class A {
    m(x:Any):Any { <Any> this } }
class I {
    n(x:Any):Any { <Any> this } }
class T {
    s(x:Any):Any { this } 
    t(x:Any):Any { <|Any|>(this.s : I -> T ( <Any> x)) }}

(<Any>new T())@t(<|Any|>new A())"


*****************Litmus test two*****************

*****************Litmus test three*****************




***************************************************
Behavioral Semantics: Is the call for each of the litmus test, <any> or <|any|>?

*****************Litmus test one*****************
@"
class A {
    m(x:A):A { this } }
class I {
    n(x:I):I { this } }
class T {
    s(x:I):T { this } 
    t(x:Any):Any { <|Any|>(this.s : I -> T ( <|I|> x)) }}

(<Any>new T())@t(<|Any|>new A())"


*****************Litmus test two*****************
@"
class A {
    m(x:A):A { this } }
class Q {
    n(x:Q):Q { this } }
class I {
    m(x:Q):I { this } }
class T {
    s(x:I):T { this } 
    t(x:Any):Any { <|Any|>(this.s : I -> T ( <|I|> x)) }}

(<Any>new T())@t(<|Any|>new A())"


*****************Litmus test three*****************
@"
class C {
    a(x:C):C { this } }
class D {
    b(x:D):D { this } }
class E {
    a(x:D):D { this } }
class F {
    m(x:E):E { x } 
    n(x:Any):Any { <|Any|>(this.m : E -> E ( <|E|> x)) }}

(<Any>new F())@n(<|Any|>new C())@a(<|Any|>new C())"



***************************************************
Concrete Semantics:

*****************Litmus test one*****************
@"
class A {
    m(x:A):A { this } }
class I {
    n(x:I):I { this } }
class T {
    s(x:I):T { this } 
    t(x:Any):Any { <Any>(this.s : I -> T ( <I> x)) }}

(<Any>new T())@t(<Any>new A())"


*****************Litmus test two*****************
@"
class A {
    m(x:A):A { this } }
class Q {
    n(x:Q):Q { this } }
class I {
    m(x:Q):I { this } }
class T {
    s(x:I):T { this } 
    t(x:Any):Any { <Any>(this.s : I -> T ( <I> x)) }}

(<Any>new T())@t(<Any>new A())"


*****************Litmus test three*****************
@"
class C {
    a(x:C):C { this } }
class D {
    b(x:D):D { this } }
class E {
    a(x:D):D { this } }
class F {
    m(x:E):E { x } 
    n(x:Any):any { <Any>(this.m : E -> E ( <E> x)) }}

(<Any>new F())@n(<Any>new C())@a(<Any>new C())"

*)


[<EntryPoint>]
let main argv = 
    
    printfn "Hello Worldddddddddddddddd" 

    let res = Parser.parse @"
    class A {
        m(x:A) : A { this } }
    class I {
        n(x:I) : I { this } }
    class T {
        s(x : I) : T { this } 
        t(x : Any) : Any { <Any>(this.s : I -> T ( <I> x)) } }

    (<Any>new T())@t(<|Any|>new A())"

    let limtusTwo = Parser.parse @"
    class A {
        m(x:A):A { this } }
    class Q {
        n(x:Q):Q { this } }
    class I {
        m(x:Q):I { this } }
    class T {
        s(x:I):T { this } 
        t(x:Any):Any { <Any>(this.s : I -> T ( <I> x)) }}

    (<Any>new T())@t(<|Any|>new A())"

    let limtusThree = Parser.parse @"
    class C {
        a(x:C):C { this } }
    class D {
        b(x:D):D { this } }
    class E {
        a(x:D):D { this } }
    class F {
        m(x:E):E { x } 
        n(x:Any):Any { <Any>(this.m : E -> E ( <E> x)) }}

    (<Any>new F())@n(<|Any|>new C())@a(<|Any|>new C())"
 
    let tsv = Translations.ts_progtrans res.Value
    let _ = Typechecker.wfprog tsv
    let trans = CGAST.transp(tsv)
    let subtypeRels = SubIL.addSubtypeImpls(tsv)(trans)
    let outp = CodeGen.genProg(subtypeRels, true, true)
    let evaluated = Executor.execute(outp)
    
    printfn "Hello World" 
    printfn "%A" evaluated
    printfn "%A" evaluated
    printfn "%A" evaluated
    printfn "%A" evaluated
    printfn "%A" evaluated
    printfn "%A" evaluated
    printfn "%A" evaluated
    printfn "Hello World" 

    0 // return an integer exit code
