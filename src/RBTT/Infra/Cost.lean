    import Lean
    open Lean Meta Elab Command

    namespace RBTT

    /-- Simple structural "cost" for proof terms.
        This is *kernel-agnostic* but deterministic:
        - size     : total Expr nodes
        - apps     : number of applications
        - lambdas  : number of lambda / forall binders
        - lets     : number of let expressions
        - maxDepth : maximum nesting depth
    -/
    structure ProofCost where
      size     : Nat := 0
      apps     : Nat := 0
      lambdas  : Nat := 0
      lets     : Nat := 0
      maxDepth : Nat := 0
    deriving Repr

    instance : ToMessageData ProofCost where
      toMessageData c := m!"ProofCost(size={c.size}, apps={c.apps}, lambdas={c.lambdas}, lets={c.lets}, maxDepth={c.maxDepth})"

    private def combine (a b : ProofCost) : ProofCost :=
      { size := a.size + b.size,
        apps := a.apps + b.apps,
        lambdas := a.lambdas + b.lambdas,
        lets := a.lets + b.lets,
        maxDepth := Nat.max a.maxDepth b.maxDepth }

    /-- Count structural metrics on an expression (unsafe implementation). -/
    unsafe def countExprUnsafe (e : Expr) : ProofCost :=
      go 0 e
    where
      go (d : Nat) (e : Expr) : ProofCost :=
        match e with
        | Expr.app f a =>
            let cf := go (d+1) f
            let ca := go (d+1) a
            { (combine cf ca) with
              size := cf.size + ca.size + 1,
              apps := cf.apps + ca.apps + 1,
              maxDepth := Nat.max (d+1) (Nat.max cf.maxDepth ca.maxDepth) }
        | Expr.lam _ _ b _ =>
            let cb := go (d+1) b
            { cb with size := cb.size + 1, lambdas := cb.lambdas + 1, maxDepth := Nat.max (d+1) cb.maxDepth }
        | Expr.forallE _ _ b _ =>
            let cb := go (d+1) b
            { cb with size := cb.size + 1, lambdas := cb.lambdas + 1, maxDepth := Nat.max (d+1) cb.maxDepth }
        | Expr.letE _ v t b _ =>
            let cv := go (d+1) v
            let ct := go (d+1) t
            let cb := go (d+1) b
            let c := combine (combine cv ct) cb
            { c with size := c.size + 1, lets := c.lets + 1, maxDepth := Nat.max (d+1) c.maxDepth }
        | Expr.mdata _ b =>
            let cb := go (d+1) b
            { cb with size := cb.size + 1, maxDepth := Nat.max (d+1) cb.maxDepth }
        | Expr.proj _ _ s =>
            let cs := go (d+1) s
            { cs with size := cs.size + 1, maxDepth := Nat.max (d+1) cs.maxDepth }
        | _ => { size := 1, maxDepth := d }

    /-- Safe wrapper for countExpr, implemented by unsafe version. -/
    @[implemented_by countExprUnsafe]
    def countExpr (e : Expr) : ProofCost :=
      { size := 0, apps := 0, lambdas := 0, lets := 0, maxDepth := 0 }

    /-- Render as JSON (string) for CI consumption. -/
    def ProofCost.toJson (c : ProofCost) : Json :=
      Json.mkObj
        [ ("size",     Json.num c.size)
        , ("apps",     Json.num c.apps)
        , ("lambdas",  Json.num c.lambdas)
        , ("lets",     Json.num c.lets)
        , ("maxDepth", Json.num c.maxDepth) ]

    /-- `#rb_cost Foo`: compute and print cost metrics for constant `Foo`. -/
    elab "#rb_cost" n:ident : command => do
      let name := n.getId
      try
        let ci ← getConstInfo name
        match ci.value? with
        | some val =>
            let c := countExpr val
            logInfo m!"RB cost for {name}: {c}
JSON: {(ProofCost.toJson c).compress}"
        | none =>
            logWarning m!"{name} has no value (axiom/opaque); cannot compute cost."
      catch e =>
        logError m!"#rb_cost error: {e.toMessageData}"

    end RBTT
