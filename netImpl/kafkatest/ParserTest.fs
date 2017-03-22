module ParserTest
open NUnit.Framework
open FsUnit
open AST
(**
Parser.parse @"
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
*)

[<TestFixture>]
type ParserTest1() =
    [<Test>]
    member x.TestVars() =
        Parser.parse @"hello" |> should equal (Some(Program([], Var("hello"))))
    [<Test>]
    member x.TestNew1() =
        (Parser.parse @"new B()") |> should equal (Some(Program([], NewExn("B", []) )))
    [<Test>]
    member x.TestNew2() =
        (Parser.parse @"new B(bee)") |> should equal (Some(Program([], NewExn("B", [Var("bee")]) )))
    [<Test>]
    member x.TestNew3() =
        (Parser.parse @"new B(") |> should equal None
    [<Test>]
    member x.TestGet() =
        (Parser.parse @"x.f()") |> should equal (Some(Program([], GetF(Var "x", "f") )))
    [<Test>]
    member x.TestSet() =
        (Parser.parse @"x.f(y)") |> should equal (Some(Program([], SetF(Var "x", "f", Var "y") )))
    [<Test>]
    member x.TestMCall() =
        (Parser.parse @"x.m : t -> t (y)") |> should equal (Some(Program([], Call(Var "x", Class "t", Class "t", "m", Var "y"))))
    [<Test>]
    member x.TestMDUCall() =
        (Parser.parse @"x@m(y)") |> should equal (Some(Program([], DynCall(Var "x", "m", Var "y"))))
    [<Test>]
    member x.TestCast() =
        (Parser.parse @"<t2>x") |> should equal (Some(Program([], Cast(Class "t2", Var "x"))))
    [<Test>]
    member x.TestParen() =
        (Parser.parse @"<t2>(<t1>x)") |> should equal (Some(Program([], Cast(Class "t2", Cast(Class "t1", Var "x")))))
    [<Test>]
    member x.TestSeq1() =
        (Parser.parse @"a.b();b.c()") |> should equal (Some(Program([], Seq[ GetF(Var "a", "b") ; GetF(Var "b", "c")])))
    [<Test>]
    member x.TestSeq2() =
        (Parser.parse @"(a.b();b).c()") |> should equal (Some(Program([], GetF(Seq[ GetF(Var "a", "b") ; Var "b"], "c"))))
    [<Test>]
    member x.TestClass() =
        (Parser.parse @"class B {}
        hello") |> should equal (Some(Program([ClassDef("B",[],[])], Var("hello"))))
    [<Test>]
    member x.TestField1() =
        (Parser.parse @"class B { 
            f:t 
        }
        hello") |> should equal (Some(Program([ClassDef("B",[FDef("f",Class "t")],[])], Var("hello"))))
    [<Test>]
    member x.TestField2() =
        (Parser.parse @"class B { f:t }
        hello") |> should equal (Some(Program([ClassDef("B",[FDef("f",Class "t")],[])], Var("hello"))))
    [<Test>]
    member x.TestGetter() =
        (Parser.parse @"class B { f():t { baz } }
        hello") |> should equal (Some(Program([ClassDef("B",[],[GDef("f", Class "t", Var("baz"))])], Var("hello"))))
    [<Test>]
    member x.TestSetter() =
        (Parser.parse @"class B { f(x):t { baz } }
        hello") |> should equal (Some(Program([ClassDef("B",[],[SDef("f", "x", Class "t", Var("baz"))])], Var("hello"))))
    [<Test>]
    member x.TestUTMethod() =
        (Parser.parse @"class B { m(x:any):any { baz } }
        hello") |> should equal (Some(Program([ClassDef("B",[],[MDef("m", "x", Any, Any, Var("baz"))])], Var("hello"))))
    [<Test>]
    member x.TestTMethod() =
        (Parser.parse @"class B { m(x:B):B { baz } }
        hello") |> should equal (Some(Program([ClassDef("B",[],[MDef("m", "x", Class "B", Class "B", Var("baz"))])], Var("hello"))))