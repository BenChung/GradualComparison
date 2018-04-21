// Learn more about F# at http://fsharp.org
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
    m(x:any):any { this } }
class I {
    n(x:any):any { this } }
class T {
    s(x:any):any { this } 
    t(x:any):any {this@s : any -> any (x) }}

(new T())@t(new A())"


*****************Litmus test two*****************

@"
class A {
    m(x:any):any { this } }
class Q {
    n(x:any):any { this } }
class I {
    m(x:any):any { this } }
class T {
    s(x:any):any { this } 
    t(x:any):any { this@s : any -> any (x) }}

(new T())@t(new A())"


*****************Litmus test three*****************

@"
class C {
    a(x:any):any { this } }
class D {
    b(x:any):any { this } }
class E {
    a(x:any):any { this } }
class F {
    m(x:any):any { x } 
    n(x:any):any { this@m : any -> any (x) }}

(new F())@n(new C())@a(new C())"


***************************************************
***************************************************
Transient Semantics:

*****************Litmus test one*****************

@"
class A {
    m(x:any):any { <A> x; <any> this } }
class I {
    n(x:any):any { <I> x; <any> this } }
class T {
    s(x:any):any { <I> x; <any> this } 
    t(x:any):any { <any> x; <any><T>(this.s : any -> any ( <any><any> x)) }}

(<any>new T())@t(<any>new A())"


*****************Litmus test two*****************

@"
class A {
    m(x:any):any { <A> x; <any> this } }
class Q {
    n(x:any):any { <Q> x; <any> this } }
class I {
    m(x:any):any { <Q> x; <any> this } }
class T {
    s(x:any):any { <I> x; <any> this } 
    t(x:any):any { <any> x; <any><T>(this.s : any -> any ( <any><any> x)) }}

(<any>new T())@t(<any>new A())"

*****************Litmus test three*****************

@"
class C {
    a(x:any):any { <C> x; <any> this } }
class D {
    b(x:any):any { <D> x; <any> this } }
class E {
    a(x:any):any { <D> x; <any> this } }
class F {
    m(x:any):any { <E> x; <any> x } 
    n(x:any):any { <any> x; <any>(<E>(this.m : any -> any ( <any>(<any> x)))) }}

(<any>new F())@n(<any>new C())@a(<any>new C())"


***************************************************
***************************************************
Behavioral Semantics:

*****************Litmus test one*****************
@"
class A {
    m(x:A):A { this } }
class I {
    n(x:I):I { this } }
class T {
    s(x:I):T { this } 
    t(x:any):any { <|any|>(this.s : I -> T ( <|I|> x)) }}

(<any>new T())@t(<|any|>new A())"


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
    t(x:any):any { <|any|>(this.s : I -> T ( <|I|> x)) }}

(<any>new T())@t(<|any|>new A())"


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
    n(x:any):any { <|any|>(this.m : E -> E ( <|E|> x)) }}

(<any>new F())@n(<|any|>new C())@a(<|any|>new C())"


***************************************************
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
    t(x:any):any { <any>(this.s : I -> T ( <I> x)) }}

(<any>new T())@t(<any>new A())"


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
    t(x:any):any { <any>(this.s : I -> T ( <I> x)) }}

(<any>new T())@t(<any>new A())"


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
    n(x:any):any { <any>(this.m : E -> E ( <E> x)) }}

(<any>new F())@n(<any>new C())@a(<any>new C())"

*)

[<EntryPoint>]
let main argv = 
    
    (*write an example that access fields*)
    let test = Parser.parse @"
    class A {
        m(x:A) : A { this } }"

    let res = Parser.parse @"
    class A {
        m(x:A) : A { this } }
    class I {
        n(x:I) : I { this } }
    class T {
        s(x : I) : T { this } 
        t(x : any) : any { <any>(this.s : I -> T ( <I> x)) } }

    (<any>new T())@t(<|any|>new A())"

    let limtusTwo = Parser.parse @"
    class A {
        m(x:A):A { this } }
    class Q {
        n(x:Q):Q { this } }
    class I {
        m(x:Q):I { this } }
    class T {
        s(x:I):T { this } 
        t(x:any):any { <any>(this.s : I -> T ( <I> x)) }}

    (<any>new T())@t(<|any|>new A())"

    let limtusThree = Parser.parse @"
    class C {
        a(x:C):C { this } }
    class D {
        b(x:D):D { this } }
    class E {
        a(x:D):D { this } }
    class F {
        m(x:E):E { x } 
        n(x:any):any { <any>(this.m : E -> E ( <E> x)) }}

    (<any>new F())@n(<|any|>new C())@a(<|any|>new C())"
    
    let res1 = Parser.parse @"
    class A {
        m(x:A) : A { this } }
    class I {
        n(x:I) : I { this } }
    class T {
        s(x : I) : T { this } 
        t(x : any) : any { this.s : I -> T ( <I> x) } }

    (new T().t(new A()))"

    let tsv = Translations.trs_progtrans res1.Value
    let _ = Typechecker.wfprog tsv
    let trans = CGAST.transp(tsv)
    let subtypeRels = SubIL.addSubtypeImpls(tsv)(trans)
    let outp = CodeGen.genProg(subtypeRels, true, true)
    let evaluated = Executor.execute(outp)
    
    printfn "%A" evaluated

    0 // return an integer exit code
