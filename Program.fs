namespace LambdaProject
open LambdaCalculus

module main = 

    let a = "a"
    let c = "c"
    let s = "s"
    let f = "f"
    let x = "x"
    let y = "y"
    let z = "z"
    let e1 = "e1"
    let e2 = "e2"

    let lambda_definitions =
        [
            "identity",
            Func(x, Name(x));  
            "true",
            Func(x, Func(y, Name(x)));
            "false",
            Func(x, Func(y, Name(y)));
            "pair",
            Func(x,
                 Func(y,
                      Func(f,
                           Application(
                            Name(f),
                            Application(
                             Name(x),
                             Name(y))))));
            "self_application",
            Func(x,
                 Application(Name(x), Name(x)));
            "condition",
            Func(e1, 
                 Func(e2, 
                      Func(c,
                           Application(
                            Application(
                             Name c,
                             Name e1),
                            Name(e2)))));
        ] |> Map.ofList
    let lambdadef name = Map.find name lambda_definitions

    let NOT =
        Func(x,
             Application(
              Application(
               Application(Map.find "condition" lambda_definitions,
                           Map.find "false" lambda_definitions),
               Map.find "true" lambda_definitions),
              Name x))

    [<EntryPoint>]
    let main argv = 
        let lambda = Application(NOT, lambdadef "false")
        NormalOrderReduction lambda
        |> List.ofSeq
        |> List.map (PrettyPrint true lambda_definitions)
        |> List.iter (printfn "%A")

        0 // return an integer exit code
