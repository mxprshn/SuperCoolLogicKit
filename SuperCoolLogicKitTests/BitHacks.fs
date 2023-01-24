module SuperCoolLogicKitTests.BitHacks

open Microsoft.Z3
open NUnit.Framework

let bvLe (ctx : Context) x y = ctx.MkITE(ctx.MkBVSLT(x, y), ctx.MkBV(1, 32u), ctx.MkBV(0, 32u)) :?> BitVecExpr

[<Test>]
let hackedMinCorrectness() =
    let ctx = new Context()
    let x = ctx.MkBVConst("x", 32u)
    let y = ctx.MkBVConst("y", 32u)
    // r = y ^ ((x ^ y) & -(x < y))
    let hackedMin = ctx.MkBVXOR(y, ctx.MkBVAND(ctx.MkBVXOR(x, y), ctx.MkBVNeg(bvLe ctx x y)))
    // Minimum should be equal to one of the operands and should be leq than both of them
    let conditionCheck = ctx.MkAnd(
        ctx.MkBVSLE(hackedMin, x),
        ctx.MkBVSLE(hackedMin, y),
        ctx.MkOr(ctx.MkEq(hackedMin, x), ctx.MkEq(hackedMin, y))
    )
    let slv = ctx.MkSolver()
    match slv.Check(ctx.MkNot(conditionCheck)) with
    | Status.UNSATISFIABLE -> Assert.Pass()
    | _ -> Assert.Fail()

[<Test>]
let hackedMaxCorrectness() =
    let ctx = new Context()
    let x = ctx.MkBVConst("x", 32u)
    let y = ctx.MkBVConst("y", 32u)
    // r = x ^ ((x ^ y) & -(x < y))
    let hackedMax = ctx.MkBVXOR(x, ctx.MkBVAND(ctx.MkBVXOR(x, y), ctx.MkBVNeg(bvLe ctx x y)))
    // Maximum should be equal to one of the operands and should be geq than both of them
    let conditionCheck = ctx.MkAnd(
        ctx.MkBVSGE(hackedMax, x),
        ctx.MkBVSGE(hackedMax, y),
        ctx.MkOr(ctx.MkEq(hackedMax, x), ctx.MkEq(hackedMax, y))
    )
    let slv = ctx.MkSolver()
    match slv.Check(ctx.MkNot(conditionCheck)) with
    | Status.UNSATISFIABLE -> Assert.Pass()
    | _ -> Assert.Fail()
