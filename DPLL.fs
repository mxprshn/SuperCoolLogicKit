module SuperCoolLogicKit.DPLL

open System.Diagnostics
open System.Collections.Generic
open Formula
open Microsoft.FSharp.Collections
open SuperCoolLogicKit.Formula
open System.Linq

type CNF = Literal Set Set

let cnfOf (l : Literal list list) : CNF =
    List.map Set.ofList l |> Set.ofList

let rec private tseytinInternal formula (delta : CNF) (newVarId : unit -> VariableId)=
    match formula with
    | Literal l -> l, delta
    | Negation f ->
        let l, delta = tseytinInternal f delta newVarId
        -l, delta
    | Conjunction(f1, f2) ->
        let l1, delta1 = tseytinInternal f1 delta newVarId
        let l2, delta2 = tseytinInternal f2 delta1 newVarId
        let p = newVarId() |> Var
        p, Set.union delta2 (cnfOf [[-p; l1]; [-p; l2]; [-l1; -l2; p]])
    | Disjunction(f1, f2) ->
        let l1, delta1 = tseytinInternal f1 delta newVarId
        let l2, delta2 = tseytinInternal f2 delta1 newVarId
        let p = newVarId() |> Var
        p, Set.union delta2 (cnfOf [[-p; l1; l2]; [-l1; p]; [-l2; p]])
    | _ -> raise <| UnreachableException()

let tseytin (formula : Formula) : CNF * VariableId Set =
    match formula with
    | True -> Set.empty, Set.empty
    | False -> Set.empty |> Set.singleton, Set.empty
    | _ ->
        let mutable counter = 0
        let newVars = HashSet<VariableId>()
        let newVariableId() =
            counter <- counter + 1
            let i = $"_p_{counter}" |> VariableId
            newVars.Add i |> ignore
            i
        let l, delta = tseytinInternal formula Set.empty newVariableId
        Set.union delta (Set.singleton l |> Set.singleton), newVars |> Set

type DPLLResult =
    | Sat of Literal Set
    | Unsat

type private InternalCNF private (elements : HashSet<HashSet<Literal>>) =

    let getLiteralToClausesMap() =
        let literalToClauses = Dictionary<Literal, HashSet<HashSet<Literal>>>()
        for clause in elements do
            for literal in clause do
                if not <| literalToClauses.ContainsKey literal then
                    literalToClauses[literal] <- HashSet()
                literalToClauses[literal].Add clause |> ignore
        literalToClauses

    let rec propagateUnits (literalToClause : Dictionary<Literal, HashSet<HashSet<Literal>>>) (units : Set<Literal>) =
        let unit = elements.FirstOrDefault(fun d -> d.Count = 1)
        if unit <> null then
            let unit = unit.Single()
            for unitClause in literalToClause[unit] do
                elements.Remove unitClause |> ignore
            if literalToClause.ContainsKey -unit then
                for negUnitClause in literalToClause[-unit] do
                    negUnitClause.Remove -unit |> ignore
            propagateUnits literalToClause (Set.add unit units)
        else
            units

    new(cnf : CNF) =
        let elements = HashSet<HashSet<Literal>>()
        cnf
        |> Seq.iter (fun clause ->
            let mutableClause = HashSet<Literal>()
            clause |> Set.iter (mutableClause.Add >> ignore)
            elements.Add mutableClause |> ignore
        )
        InternalCNF elements

    member x.Copy (newUnit : Literal) =
        let copy = HashSet<HashSet<Literal>>()
        let unitClause = HashSet<Literal>()
        unitClause.Add newUnit |> ignore
        copy.Add unitClause |> ignore
        for clause in elements do
            let clauseCopy = HashSet<Literal>()
            clause |> Seq.iter (clauseCopy.Add >> ignore)
            copy.Add clauseCopy |> ignore
        InternalCNF copy

    member x.Add (literal : Literal) =
        let clause = HashSet<Literal>()
        clause.Add literal |> ignore
        elements.Add clause |> ignore

    member x.PropagateUnits() : Literal Set =
        let literalToClauses = getLiteralToClausesMap()
        let pures = literalToClauses.Where(fun kvp -> not <| literalToClauses.ContainsKey(-kvp.Key))
        for pureLiteral in pures do
            for clause in pureLiteral.Value do
                elements.Remove clause |> ignore
        let pures = pures |> Seq.map (fun kvp -> kvp.Key) |> Set.ofSeq
        let units = propagateUnits (getLiteralToClausesMap()) Set.empty
        Set.union pures units

    member x.SelectLiteral() =
        elements.First().First()

    member x.IsEmpty with get() = elements.Count = 0

    member x.ContainsEmptyClause with get() = elements.Any(fun d -> d.Count = 0)

let rec private dpllK (cnf : InternalCNF) (model : Literal Set) k =
    let units = cnf.PropagateUnits()
    let model = Set.union units model
    if cnf.IsEmpty then
        k <| Sat model
    elif cnf.ContainsEmptyClause then
        k <| Unsat
    else
        let literal = cnf.SelectLiteral()
        let newCnf = cnf.Copy literal
        let newModel = Set.add literal model
        let cont res =
            match res with
            | Sat _ as sat -> k sat
            | Unsat ->
                let literal = -literal
                cnf.Add literal
                let newModel = Set.add literal model
                dpllK cnf newModel k
        dpllK newCnf newModel cont

let dpll (formula : Formula) =
    let cnf, newVars = tseytin formula
    match dpllK (InternalCNF cnf) Set.empty id with
    | Unsat -> Unsat
    | Sat mdl ->
        mdl
        |> Set.filter (fun l -> not <| Set.contains (variableIdOf l) newVars)
        |> Sat
