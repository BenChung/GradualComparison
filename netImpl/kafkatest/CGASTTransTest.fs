module CGASTTransTest
open NUnit.Framework
open FsUnit
open AST
open CGAST

[<TestFixture>]
type CGASTTests() =
    [<Test>]
    member x.TestEmpty() =
        (match CGAST.findps([])([]) with (a,b) -> a = [] && b = []) |> should equal true
    [<Test>]
    member x.TestMd() =
        (match CGAST.findps([])([MDef("m","x",Any,Any, [Var "x"])]) with (a,b) -> a = [] && b = [CMDef("m","x",Any,Any, [Var "x"])]) |> should equal true
    [<Test>]
    member x.TestFd() =
        (match CGAST.findps([FDef("f",Any)])([]) with (a,b) -> a = [CFDef("f",Any)] && b = []) |> should equal true
    [<Test>]
    member x.TestPd() =
        (match CGAST.findps([])([(GDef("f",Any,[Var "x"]))]) with (a,b) -> a = [CPDef("f",Any, Some(CGDef([ Var "x" ])),None)] && b = []) |> should equal true
    [<Test>]
    member x.TestPd2() =
        (match CGAST.findps([])([(GDef("f",Any,[Var "x"])) ; (SDef("f","x",Any,[Var "x"]))]) with 
            (a,b) -> a = [CPDef("f",Any, Some(CGDef([ Var "x" ])),Some(CSDef("x", [Var "x"])))] && b = []) |> should equal true
    [<Test>] 
    member x.TestPd3() =
        (TestDelegate (fun () -> (CGAST.findps([])([(GDef("f",Any,[Var "x"])) ; (GDef("f",Any,[Var "y"]))])) |> ignore)) |> should throw typeof<FieldExistsError> 
    [<Test>]
    member x.TestPd4() =
        (TestDelegate (fun () -> CGAST.findps([])([(SDef("f","x",Any,[Var "x"])) ; (SDef("f","x",Any,[Var "y"]))]) |> ignore)) |> should throw typeof<FieldExistsError>
    