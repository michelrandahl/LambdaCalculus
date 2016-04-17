namespace LambdaProject

module LambdaCalculus =
    type LambdaExpr = 
        | Name of string
        | Func of string * LambdaExpr
        | Application of LambdaExpr * LambdaExpr

    //test if two given lambda expressions are equivalent
    let AlphaEquivalent expr1 expr2 =
        let rec loop vars1 vars2 = function
        | Name(n1), Name(n2) ->
            let idx1 = vars1 |> List.tryFindIndex ((=)n1)
            let idx2 = vars2 |> List.tryFindIndex ((=)n2)
            match idx1,idx2 with
            | Some(idx1),Some(idx2) -> idx1 = idx2
            | _ -> false
        | Func(v1,b1), Func(v2,b2) ->
            loop (v1::vars1) (v2::vars2) (b1,b2)
        | Application(expr1,expr2), Application(expr3,expr4) ->
            loop vars1 vars2 (expr1,expr3) &&
            loop vars1 vars2 (expr2,expr4)
        | _ -> false
        loop [] [] (expr1,expr2)

    //partial active pattern
    //helps to extract definition name of a given lambda expression
    let (|NamedLambda|_|) (definitions: Map<string, LambdaExpr>) expr = 
        definitions |> Map.tryFindKey (fun name expr' -> AlphaEquivalent expr expr')

    //generates a more readable output for lambda expressions
    let PrettyPrint simplify definitions expr =
        let rec loop definitions = function
        | NamedLambda definitions n when simplify -> n
        | Name(n) -> n
        | Func(f,b) -> sprintf "\%s.%s" f (loop definitions b)
        | Application(f1,f2) ->
            sprintf "%s %s" (loop definitions f1) (loop definitions f2)
        loop definitions expr

    //collect the set of free variables in an expression
    let FreeVars expr =
        let rec loop bound = function
        | Name v when not(Seq.exists ((=)v) bound) -> [v]
        | Name v -> []
        | Func(x, M) -> loop (x::bound) M
        | Application(M,N) -> (loop bound M) @ (loop bound N)
        loop [] expr
        |> Set.ofSeq

    //renaming a variable without name clashes
    let rec RenameVar v taken =
        if taken |> Seq.exists ((=)v) then
            RenameVar (v+"'") taken
        else v

    //capture avoiding substitution
    let rec Substitute N x M =
        match M with
        | Name(y) when x = y -> N
        | Name(y) -> Name(y)
        | Func(y,M) when x = y -> Func(y,M)
        | Func(y,M) when x <> y && not(Seq.exists ((=)y) (FreeVars N)) ->
            Func(y, Substitute N x M)
        | Func(y,M) -> //x <> y && y is in FreeVars
            let z = RenameVar (y+"'") (FreeVars N)
            Func(z, Substitute (Name z) y M)
            |> Substitute N x
        | Application(M, M') ->
            Application(Substitute N x M, Substitute N x M')

    //attempt beta-reduction
    //returns beta-reduced expression
    //or original expression, if no beta-reduction can be performed
    let rec BetaReduce =  function
        | Application(Func(x,M),N) -> 
            Substitute N x M
        | Application(M,N) ->
            let M' = BetaReduce M
            if M' <> M then
                Application(M',N)
            else
                let N' = BetaReduce N
                Application(M, N')
        | Func(x,M) ->
            let M' = BetaReduce M
            Func(x,M')
        | other -> other

    //partial active pattern
    //determines if a given function expression
    //can be eta-reduced and returns it
    let (|EtaReduced|_|) expr =
        let rec loop x M =
            match M with
            | Application(M',Name x')
              when x'=x && not(Seq.exists ((=)x) (FreeVars M')) ->
                Some M' 
            | Application(M,N) ->
                let N' = loop x N
                match N' with
                | Some(N') -> Application(M,N') |> Some
                | None -> None
            | Func(x',M) when x' <> x ->
                let M' = loop x M
                match M' with
                | Some(M') -> Func(x',M') |> Some
                | None -> None
            | _ -> None
        match expr with
        | Func(x,M) -> loop x M
        | _ -> None

    //attempt eta-reduction on an expression
    //returns eta-reduced expression
    //or original expression, if no eta-reduction can be performed
    let rec EtaReduce = function
        | EtaReduced M' -> M'
        | Application(M,N) ->
            let M' = EtaReduce M
            if M' <> M then
                Application(M',N)
            else
                let N' = BetaReduce N
                Application(M,N')
        | Func(x,M) ->
            let M' = EtaReduce M
            Func(x,M')
        | other -> other

    //generating a sequence of reductions
    //by normal order reduction
    let NormalOrderReduction expr =
        let rec beta_reduction_seq expr = seq {
            yield expr
            let expr' = BetaReduce expr
            if expr' <> expr then
                yield! beta_reduction_seq expr'
            else
                yield! eta_reduction_seq expr
            }
        and eta_reduction_seq expr = seq {
            let expr' = EtaReduce expr
            if expr' <> expr then
                yield expr'
                yield! eta_reduction_seq expr'
            }
        beta_reduction_seq expr