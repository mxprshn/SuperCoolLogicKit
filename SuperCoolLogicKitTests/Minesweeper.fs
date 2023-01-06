module Minesweeper

open System

open Microsoft.Z3
open NUnit.Framework
open SuperCoolLogicKit.Formula
open SuperCoolLogicKit.DPLL

let rec private getCombinations n m p =
    if m = 0 then
        [[]]
    elif n = 0 then
        []
    else
        let a = getCombinations (n - 1) m (p + 1)
        let b = getCombinations (n - 1) (m - 1) (p + 1) |> List.map (fun l -> p :: l)
        a @ b

let private getCombinations8 n =
    getCombinations 8 n 0

let private populationCount combinations (variables : VariableId array) =
    assert(variables.Length = 8)
    let conjunctByCombination combination =
        variables
        |> Seq.mapi (fun i v -> if List.contains i combination then Literal <| Var v else Literal <| Neg v)
        |> Seq.fold (*) True
    combinations |> Seq.map conjunctByCombination |> Seq.fold (+) False

let fieldToFormula (field : string list) bombX bombY =
    let n = field.Length
    let vars = Array2D.init (n + 2) (n + 2) (fun i j -> VariableId $"p_{i}_{j}")
    let getNeighbours i j =
        [|
            (i - 1, j - 1);
            (i - 1, j);
            (i - 1, j + 1);
            (i, j - 1);
            (i, j + 1);
            (i + 1, j - 1);
            (i + 1, j);
            (i + 1, j + 1)
        |]

    // Require border elements to be without bombs
    let formula =
        Seq.allPairs (seq { 0..n + 1 }) (seq { 0..n + 1 })
        |> Seq.filter (fun (i, j) -> i = 0 || i = n + 1 || j = 0 || j = n + 1)
        |> Seq.map (fun (i, j) -> Neg vars[i, j] |> Literal)
        |> Seq.fold (*) True

    // Map numeric cells to corresponding population count functions
    let formula2 =
        field
        |> Seq.mapi (fun i r ->
            Seq.mapi (fun j c ->
                match c with
                | '?' ->
                   (Neg vars[i + 1, j + 1] |> Literal) + (Var vars[i + 1, j + 1] |> Literal)
                | '0' -> Neg vars[i + 1, j + 1] |> Literal
                | _ ->
                    let number = int c - int '0'
                    let pCount =
                        getNeighbours i j
                        |> Array.map (fun (i, j) -> vars[i + 1, j + 1])
                        |> populationCount (getCombinations8 number)
                    let pCount = pCount * (Neg vars[i + 1, j + 1] |> Literal)
                    let pCountStr = pCount.ToString()
                    pCount
                ) r
            )
        |> Seq.collect id
        |> Seq.fold (*) True

    // Assume that there is a bomb in target cell
    formula * (Literal <| Var vars[bombX + 1, bombY + 1]) * formula2

[<SetUp>]
let setup () = ()

let field1 = ["???"; "?30"; "?10"]
let field2 =
    [
        "01?10001?";
        "01?100011";
        "011100000";
        "000000000";
        "111110011";
        "????1001?";
        "????3101?";
        "?????211?";
        "?????????"
    ]

let cases() : obj[] seq = seq {
    yield [|field1; 0; 0; true|]
    yield [|field1; 0; 1; true|]
    yield [|field1; 0; 2; true|]
    yield [|field1; 1; 0; true|]
    yield [|field1; 1; 1; false|]
    yield [|field1; 1; 2; false|]
    yield [|field1; 2; 0; true|]
    yield [|field1; 2; 1; false|]
    yield [|field1; 2; 2; false|]

    yield [|field2; 0; 2; false|]
    yield [|field2; 1; 2; true|]
    yield [|field2; 0; 2; false|]
    yield [|field2; 5; 1; false|]
    yield [|field2; 5; 2; false|]
    yield [|field2; 5; 3; true|]
    yield [|field2; 6; 8; false|]
    yield [|field2; 7; 8; false|]
}

[<Test>]
[<TestCaseSource(nameof(cases))>]
let minesweeperTest(field : string list, bombX : int, bombY : int, expected : bool) =
    let formula = fieldToFormula field bombX bombY
    match dpll formula with
    | Unsat when expected -> Assert.Fail()
    | Sat _ when not expected -> Assert.Fail()
    | _ -> Assert.Pass()
