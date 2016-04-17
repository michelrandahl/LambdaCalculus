namespace LambdaProject.Tests

module ``Lambda calculus tests`` =
    open LambdaProject.LambdaCalculus
    open NUnit.Framework
    open FsUnit

    let a = "a"
    let c = "c"
    let s = "s"
    let f = "f"
    let x = "x"
    let y = "y"
    let z = "z"
    let e1 = "e1"
    let e2 = "e2"

    //map of base functions
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

    //utility functions
    let lambdadef name = Map.find name lambda_definitions

    let PrettyPrint1 expr = PrettyPrint false lambda_definitions expr
    let PrettyPrint2 expr = PrettyPrint true lambda_definitions expr

    //val TestPrinter : print_method:('a -> 'b) -> test_name:string -> input_expr:'a ->
    //results_printer:(('a -> 'b) -> 'c -> 'd) -> results:'c -> 'd
    let TestPrinter print_method test_name input_expr results_printer results =
        sprintf " -- %s --" test_name |> printfn "%A"
        print_method input_expr
        |> sprintf "INPUT: %A"
        |> printfn "%A"
        printfn "RESULTS:"
        results_printer print_method results

    (* - complex functions - *)
    let NOT =
        Func(x,
             Application(
              Application(
               Application(Map.find "condition" lambda_definitions,
                           Map.find "false" lambda_definitions),
               Map.find "true" lambda_definitions),
              Name x))

    (* - tests - *)
    [<TestFixture>]
    type ``Alpha equivalence tests``() =
        [<Test>]
        member test.``are alpha equivalent 1``() =
            let lambda1 = Func(x,Name(x))
            let lambda2 = Func(x,Name(x))
            AlphaEquivalent lambda1 lambda2
            |> should equal true

        [<Test>]
        member test.``are alpha equivalent 2``() =
            let lambda1 = Func(x,Name(x))
            let lambda2 = Func(z,Name(z))
            AlphaEquivalent lambda1 lambda2
            |> should equal true

        [<Test>]
        member test.``are alpha equivalent 3``() =
            let lambda1 = Func(x,Name(x))
            let lambda2 = Func(z,Name(x))
            AlphaEquivalent lambda1 lambda2
            |> should equal false

        [<Test>]
        member test.``are alpha equivalent 4``() =
            let lambda1 = Func(x, Func(y, Func(f, Application(Name(f), Application(Name(x),Name(y))))))
            let lambda2 = Func(x, Application(Name(x), Name(x)))
            AlphaEquivalent lambda1 lambda2
            |> should equal false

        [<Test>]
        member test.``are alpha equivalent 5``() =
            let lambda1 = Func(x, Name(x))
            let lambda2 = Func(x, Application(Name(x), Name(x)))
            AlphaEquivalent lambda1 lambda2
            |> should equal false

        [<Test>]
        member test.``are alpha equivalent 6``() =
            let lambda1 = Func(x, Func(y, Func(f, Application(Name(f), Application(Name(x),Name(y))))))
            let lambda2 = Func(z, Func(f, Func(x, Application(Name(x), Application(Name(z),Name(f))))))
            AlphaEquivalent lambda1 lambda2
            |> should equal true

        [<Test>]
        member test.``are alpha equivalent 7``() =
            let lambda1 = Func(x, Func(x, Name x))
            let lambda2 = Func(x, Func(y, Name x))
            AlphaEquivalent lambda1 lambda2
            |> should equal false

    [<TestFixture>]
    type ``pretty print tests``() =
        [<Test>]
        member test.``pretty print 1``() =
            let lambda = Func(x,Name(x))
            let expected = "identity"
            PrettyPrint2 lambda
            |> should equal expected

        [<Test>]
        member test.``pretty print 2``() =
            let lambda = Func(z,Name(z))
            let expected = "identity"
            PrettyPrint2 lambda
            |> should equal expected

        [<Test>]
        member test.``pretty print 3``() =
            let lambda = Func(x,Name(x))
            let expected = @"\x.x"
            PrettyPrint1 lambda
            |> should equal expected

        [<Test>]
        member test.``pretty print 4``() =
            let lambda = Func(x, Func(y, Func(f, Application(Name(f), Application(Name(x),Name(y))))))
            let expected = "pair"
            PrettyPrint2 lambda
            |> should equal expected

        [<Test>]
        member test.``pretty print 5``() =
            let lambda = Func(x, Func(y, Func(f, Application(Name(f), Application(Name(x),Name(y))))))
            let expected = @"\x.\y.\f.f x y"
            PrettyPrint1 lambda
            |> should equal expected

    [<TestFixture>]
    type ``Beta reduction tests``() =
        let TestPrinter' test_name input_expr result =
            let results_printer print_method result =
                print_method result
                |> printfn "%A"
            result
            |> TestPrinter PrettyPrint1 test_name input_expr results_printer

        [<Test>]
        member test.``beta reduce 1``() =
            let lambda = Application(
                          Func(x,Name x),
                          Func(y,Name y))
            let expected = Func(y,Name y)

            let result = BetaReduce lambda
            TestPrinter' "beta reduce 1" lambda result
            result |> should equal expected

        [<Test>]
        member test.``beta reduce 2``() =
            let lambda = Application(
                          Func(x,Func(x, Name x)),
                          Func(y, Name y))
            let expected = Func(x, Name x)

            let result = BetaReduce lambda
            TestPrinter' "beta reduce 2" lambda result
            result |> should equal expected

        [<Test>]
        member test.``beta reduce 3``() =
            let lambda = Application(
                          Func(x,Func(z, Name x)),
                          Func(y, Name y))
            let expected = Func(z, Func(y, Name y))

            let result = BetaReduce lambda
            TestPrinter' "beta reduce 3" lambda result
            result |> should equal expected

    [<TestFixture>]
    type ``Eta reduction tests``() =
        let TestPrinter' test_name input_expr result =
            let results_printer print_method result =
                print_method result
                |> printfn "%A"
            result
            |> TestPrinter PrettyPrint2 test_name input_expr results_printer

        [<Test>]
        member test.``eta reduce 1``() =
            let lambda = Func(x, Application(Func(y, Name y), Name x))
            let expected = Func(y, Name y)

            let result = EtaReduce lambda
            TestPrinter' "eta reduce 1" lambda result
            result |> should equal expected

        [<Test>]
        member test.``eta reduce 2``() =
            let lambda = Func(x, Func(y, Application(Name y, Name x)))
            let expected = Func(y, Name y)

            let result = EtaReduce lambda
            TestPrinter' "eta reduce 2" lambda result
            result |> should equal expected

        [<Test>]
        member test.``eta reduce 3``() =
            let lambda = lambdadef "self_application"
            let expected = lambdadef "self_application"

            let result = EtaReduce lambda
            TestPrinter' "eta reduce 3" lambda result
            result |> should equal expected

        [<Test>]
        member test.``eta reduce 4``() =
            let lambda = Func(a,
                              Func(x,
                                   Application(
                                    Application(
                                     Name x,
                                     Name x),
                                    Name a)))
            let expected = lambdadef "self_application"

            let result = EtaReduce lambda
            TestPrinter' "eta reduce 4" lambda result
            result |> should equal expected

        [<Test>]
        member test.``eta reduce 5``() =
            let lambda = Func(a,
                              Func(x,
                                   Application(
                                    Name x,
                                    Application(
                                     Name x,
                                     Name a))))
            let expected = lambdadef "self_application"

            let result = EtaReduce lambda
            TestPrinter' "eta reduce 5" lambda result
            result |> should equal expected

    [<TestFixture>]
    type ``normal order reductions``() =
        let TestPrinter' test_name input_expr results =
            let results_printer print_method results =
                results
                |> Seq.map print_method
                |> Seq.iter (printfn "%A")
            results
            |> TestPrinter PrettyPrint2 test_name input_expr results_printer

        [<Test>]
        member test.``normal reduce 1``() =
            let lambda = Func(x, Application(Func(y, Name y), Name x))
            let expected = Func(y, Name y)

            let result =
                NormalOrderReduction lambda
                |> List.ofSeq
            TestPrinter' "normal reduce 1" lambda result
            result |> Seq.last
            |> AlphaEquivalent expected
            |> should equal true

        [<Test>]
        member test.``normal reduce 2``() =
            let lambda = Application(lambdadef "identity",
                                     lambdadef "self_application")
            let expected = lambdadef "self_application"

            let result =
                NormalOrderReduction lambda
                |> List.ofSeq
            TestPrinter' "normal reduce 2" lambda result
            result |> Seq.last
            |> should equal expected

        [<Test>]
        member test.``normal reduce 3``() =
            let lambda = Func(a,
                              Func(x,
                                   Application(
                                    Application(
                                     Name x,
                                     Name x),
                                    Name a)))
            let expected = lambdadef "self_application"

            let result =
                NormalOrderReduction lambda
                |> List.ofSeq
            TestPrinter' "normal reduce 3" lambda result
            result |> Seq.last
            |> should equal expected

        [<Test>]
        member test.``normal reduce 4``() =
            let lambda = Func(a,
                              Func(x,
                                   Application(
                                    Name x,
                                    Application(
                                     Name x,
                                     Name a))))
            let expected = lambdadef "self_application"

            let result = 
                NormalOrderReduction lambda
                |> List.ofSeq
            TestPrinter' "normal reduce 4" lambda result
            result |> Seq.last
            |> should equal expected

        [<Test>]
        member test.``normal reduce 5``() =
            let lambda = Application(Func(f, Func(a, Application(Name f, Name a))),
                                     lambdadef "self_application")
            let expected = lambdadef "self_application"

            let result = 
                NormalOrderReduction lambda
                |> List.ofSeq
            TestPrinter' "normal reduce 5" lambda result
            result |> Seq.last
            |> AlphaEquivalent expected
            |> should equal true

        [<Test>]
        member test.``normal reduce on NOT``() =
            let lambda = NOT
            let expected = 
                Func(c,
                     Application(
                      Application(
                       Name c,
                       lambdadef "false"),
                      lambdadef "true"))

            let result =
                NormalOrderReduction lambda
                |> List.ofSeq
            TestPrinter' "normal reduce on NOT" lambda result
            result |> Seq.last
            |> AlphaEquivalent expected
            |> should equal true

        [<Test>]
        member test.``normal reduce NOT TRUE``() =
            let lambda = Application(NOT, lambdadef "true")
            let expected = lambdadef "false"

            let result =
                NormalOrderReduction lambda
                |> List.ofSeq
            TestPrinter' "normal reduce NOT TRUE" lambda result
            result |> Seq.last
            |> AlphaEquivalent expected
            |> should equal true