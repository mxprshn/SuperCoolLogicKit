module SuperCoolLogicKit.Formula

type VariableId = string

type Literal =
    | Var of VariableId
    | Neg of VariableId

    static member (~-) (l : Literal) =
        match l with
        | Var id -> Neg id
        | Neg id -> Var id

let variableIdOf literal =
    match literal with
    | Var i
    | Neg i -> i

let isNegation literal =
    match literal with
    | Var _ -> false
    | Neg _ -> true

let mutable counter = 0

let newVariableId() =
    counter <- counter + 1
    $"_p_{counter}" |> VariableId

let newVariable() =
    newVariableId() |> Var

type Formula =
    | Literal of Literal
    | Negation of Formula
    | Conjunction of Formula * Formula
    | Disjunction of Formula * Formula
    | True
    | False

    static member (~-) (f : Formula) =
        match f with
        | Literal l -> Literal -l
        | Negation f -> f
        | True -> False
        | False -> True
        | f -> Negation f

    static member (*) (f1, f2) =
        match f1, f2 with
        | False, _
        | _, False -> False
        | True, _ -> f2
        | _, True -> f1
        | _ -> Conjunction(f1, f2)

    static member (+) (f1, f2) =
        match f1, f2 with
        | True, _
        | _, True -> True
        | False, _ -> f2
        | _, False -> f1
        | _ -> Disjunction(f1, f2)
