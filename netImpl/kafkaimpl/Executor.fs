module Executor
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open System.IO
open System.Collections.Generic
open System
open System.Reflection

exception CSharpCompilerError of string

let execute(s:string) =
    let an = Path.GetRandomFileName()
        MetadataReference.CreateFromFile(typeof<obj>.Assembly.Location) ;
        MetadataReference.CreateFromFile(typeof<IEnumerable<int>>.Assembly.Location) ]
    let compilation = CSharpCompilation.Create(
        an,
        [ CSharpSyntaxTree.ParseText(s) ],
        refs,
        CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary))
    use ms = MemoryStream()
    let result = compilation.Emit(ms)
    match result.Success with
    | false -> result.Diagnostics |> Seq.filter (fun res -> res.IsWarningAsError || res.Severity = DiagnosticSeverity.Error) |> Seq.map Console.Error.WriteLine |> (fun x -> raise (CSharpCompilerError "Exception:"))
    | true -> do ms.Seek(int64(0), SeekOrigin.Begin)
              let assembly = Assembly.Load(ms.ToArray())
              let mainClass = assembly.GetType("Kafka.Program")
              mainClass.GetMethod("Main").Invoke(null, Array.empty<obj>)
