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
        (Parser.parse @"this.f") |> should equal (Some(Program([], GetF("f") )))
    [<Test>]
    member x.TestSet() =
        (Parser.parse @"this.f = y") |> should equal (Some(Program([], SetF("f", Var "y") )))
    [<Test>]
    member x.TestMCall() =
        (Parser.parse @"x.m : t -> t (y)") |> should equal (Some(Program([], Call(Var "x", Class "t", Class "t", "m", Var "y"))))
    [<Test>]
    member x.TestMDUCall() =
        (Parser.parse @"x@m(y)") |> should equal (Some(Program([], DynCall(Var "x", "m", Var "y"))))
    [<Test>]
    member x.TestCast() =
        (Parser.parse @"<t2>x") |> should equal (Some(Program([], SubCast(Class "t2", Var "x"))))
    [<Test>]
    member x.TestCast2() =
        (Parser.parse @"<|t2|>x") |> should equal (Some(Program([], BehCast(Class "t2", Var "x"))))
    [<Test>]
    member x.TestParen() =
        (Parser.parse @"<t2>(<t1>x)") |> should equal (Some(Program([], SubCast(Class "t2", SubCast(Class "t1", Var "x")))))
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
    member x.TestUTMethod() =
        (Parser.parse @"class B { m(x:any):any { baz } }
        hello") |> should equal (Some(Program([ClassDef("B",[],[MDef("m", "x", Any, Any, [Var("baz")])])], Var("hello"))))
    [<Test>]
    member x.TestTMethod() =
        (Parser.parse @"class B { m(x:B):B { baz } }
        hello") |> should equal (Some(Program([ClassDef("B",[],[MDef("m", "x", Class "B", Class "B", [Var("baz")])])], Var("hello"))))
    [<Test>]
    member x.TestTMethod2() =
        (Parser.parse @"class B { m(x:B):B { baz ; x} }
        hello") |> should equal (Some(Program([ClassDef("B",[],[MDef("m", "x", Class "B", Class "B", [Var("baz") ; Var("x")])])], Var("hello"))))