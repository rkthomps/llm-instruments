

import LlmInstruments.TheoremCharacterization

import Lean
open Lean


namespace LlmInstruments

def sorrySeqStx : MetaM Syntax := `(tacticSeq| sorry)

def sorryStx : MetaM Syntax := `(tactic| sorry)

#eval sorrySeqStx

-- partial def stripTacticsDepth (stx : Syntax) (depth : Nat) : MetaM Syntax :=
--   match depth, stx with
--   | 0, .node _ `Lean.Parser.Tactic.tacticSeq _ => sorryStx
--   | 0, .node i k a => do
--     return .node i k (← a.mapM (fun c => stripTacticsDepth c 0))
--   | d+1, .node i k a => do
--     if (isTactic stx).isSome then
--       return .node i k (← a.mapM (fun c => stripTacticsDepth c d))
--     else
--       return .node i k (← a.mapM (fun c => stripTacticsDepth c depth))
--   | _, s => return s



/--
A wrapper around the Lean `Syntax` type that we can use to represent syntax with hidden parts.
-/
inductive HiddenTacticSyntax where
  | raw (stx : Syntax)
  | node (i : Lean.SourceInfo) (k : SyntaxNodeKind) (args : Array HiddenTacticSyntax)
  /-- Hide children hideIdx onward. Note that this index also applies to "null" children
      invariant: there will always be at least one non-null child in hiddenChildren -/
  | hiddenChildren (i : Lean.SourceInfo) (args : Array HiddenTacticSyntax) (hideIdx : Nat)
deriving Inhabited

def HiddenTacticSyntax.getKind : HiddenTacticSyntax → SyntaxNodeKind
  | .raw stx => stx.getKind
  | .node _ k _ => k
  | .hiddenChildren _ _ _ => `null

def isRealChild (c : Syntax) : Bool :=
  c.getKind != `null

def countChildren (children : Array Syntax) : Nat :=
  children.foldl (fun acc c => acc + if isRealChild c then 1 else 0) 0

def countHiddenChildren (children : Array HiddenTacticSyntax) : Nat :=
  children.foldl (fun acc c => acc + if c.getKind != `null then 1 else 0) 0

partial def createInitialHiddenTacticSyntax (stx : Syntax) : HiddenTacticSyntax :=
  match stx with
  | .node i `Lean.Parser.Tactic.tacticSeq1Indented args =>
    let childSeq := args[0]!
    match childSeq with
    | .node ci `null ca =>
      if 0 < countChildren ca then
        HiddenTacticSyntax.node i `Lean.Parser.Tactic.tacticSeq1Indented (#[
          HiddenTacticSyntax.hiddenChildren ci (ca.map createInitialHiddenTacticSyntax) 0])
      else
        HiddenTacticSyntax.node i `Lean.Parser.Tactic.tacticSeq1Indented (args.map (fun c => createInitialHiddenTacticSyntax c))
    | _ => panic "Unexpected syntax structure"
  | .node i `Lean.Parser.Tactic.tacticSeqBracketed args =>
    let childSeq := args[1]!
    match childSeq with
    | .node ci `null ca =>
      if 0 < countChildren ca then
        HiddenTacticSyntax.node i `Lean.Parser.Tactic.tacticSeqBracketed (#[
          HiddenTacticSyntax.raw args[0]!,
          HiddenTacticSyntax.hiddenChildren ci (ca.map createInitialHiddenTacticSyntax) 0,
          HiddenTacticSyntax.raw args[2]!])
      else
        HiddenTacticSyntax.node i `Lean.Parser.Tactic.tacticSeqBracketed (args.map (fun c => createInitialHiddenTacticSyntax c))
    | _ => panic "Unexpected syntax structure"
  | .node i k args => HiddenTacticSyntax.node i k (args.map (fun c => createInitialHiddenTacticSyntax c))
  | s => HiddenTacticSyntax.raw s


partial def hiddenSyntaxToSyntaxWithSorry (hs : HiddenTacticSyntax) : MetaM Syntax :=
  match hs with
  | .raw stx => return stx
  | .node i k args => return (.node i k (← args.mapM hiddenSyntaxToSyntaxWithSorry))
  | .hiddenChildren i args hideIdx => do
    let sorryArgs ← args.mapM (fun c => hiddenSyntaxToSyntaxWithSorry c)
    let newArgs := sorryArgs[:hideIdx].toArray.append #[← sorryStx]
    return .node i `null newArgs


structure ExpandCandidate where
  inOrderIdx : Nat
  expandResult : HiddenTacticSyntax
  depth : Nat
deriving Inhabited


partial def getExpandCandidates
  (hs : HiddenTacticSyntax)
  (depth : Nat)
  (reconstructFn : HiddenTacticSyntax → HiddenTacticSyntax) : StateM Nat (Array ExpandCandidate) := do
  match hs with
  | .raw _ => return #[]
  | .node info k args =>
    let mut candidates := #[]
    for (a, i) in args.zipWithIndex do
      let newReconstructFn childHidden := reconstructFn (.node info k (args.set! i childHidden))
      candidates := candidates.append (← getExpandCandidates a (depth + 1) newReconstructFn)
    return candidates
  | .hiddenChildren info args hideIdx =>
    -- invariant: there will always be at least one non-null child in args
    -- if expanding the node reveals all children, then we replace this node with a hiddennode, and create hidden nodes for each child
    let remainingChildren := countHiddenChildren args[hideIdx:].toArray
    if remainingChildren == 0 then
      let mut candidates := #[]
      for (a, i) in args.zipWithIndex do
        let newReconstructFn childHidden := reconstructFn (.node info `null (args.set! i childHidden))
        candidates := candidates.append (← getExpandCandidates a (depth + 1) newReconstructFn)
      return candidates
    else
      let mut nextHideIdx := none
      let mut candidates := #[]
      for (a, i) in args.zipWithIndex do
        if i <= hideIdx then
          let newReconstructFn childHidden := reconstructFn (.hiddenChildren info (args.set! i childHidden) hideIdx)
          candidates := candidates.append (← getExpandCandidates a (depth + 1) newReconstructFn)
          continue
        else if a.getKind == `null then
          continue
        nextHideIdx := some i
        break
      match nextHideIdx with
      | some idx =>
        let visitIdx ← get
        set (visitIdx + 1)
        let expandResult := reconstructFn (HiddenTacticSyntax.hiddenChildren info args idx)
        return candidates.append #[{ inOrderIdx := visitIdx, expandResult := expandResult, depth := depth}]
      | none => panic "Invariant violation: there should be at least one non-null child"


def iterateExpand (numExpands : Nat) (hStx : HiddenTacticSyntax) (scoreFn : ExpandCandidate → Float) : HiddenTacticSyntax :=
  match numExpands with
  | 0 => hStx
  | n+1 =>
    let candidates := Id.run ((getExpandCandidates hStx 0 id).run' 0)
    if candidates.isEmpty then
      hStx
    else
      let bestCandidate := candidates.foldl (fun best c => if scoreFn c > scoreFn best then c else best) candidates[0]!
      iterateExpand n bestCandidate.expandResult scoreFn


def expand (stx : Syntax) (numExpands : Nat) (scoreFn : ExpandCandidate → Float) : MetaM Syntax := do
  let initialHidden := createInitialHiddenTacticSyntax stx
  let finalHidden := iterateExpand numExpands initialHidden scoreFn
  hiddenSyntaxToSyntaxWithSorry finalHidden


/--
Replaces tacics at depth >= depth with `sorry`
Depth is the depth of tactic nesting. Depth 0 means the top-level will be replaced with `sorry`.
-/
partial def stripTacticsBreadth (stx : Syntax) (depth width : Nat) : MetaM Syntax :=
  match depth, width, stx with
  | 0, 0, .node _ `Lean.Parser.Tactic.tacticSeq _ => sorrySeqStx

  | 0, w, .node i `Lean.Parser.Tactic.tacticSeq1Indented a => do
    let childSeq := a[0]!
    match childSeq with
    | .node ci `null ca => do
      let newChildren ← ca[:(2 * w)].toArray.mapM (fun c => stripTacticsBreadth c 1 0)
      return .node i `Lean.Parser.Tactic.tacticSeq1Indented #[
        .node ci `null (newChildren.append #[← sorryStx])
      ]
    | _ => panic "Unexpected syntax structure"

  | 0, w, .node i `Lean.Parser.Tactic.tacticSeqBracketed a => do
    let childSeq := a[1]!
    match childSeq with
    | .node ci `null ca => do
      let newChildren ← ca[:(2 * w)].toArray.mapM (fun c => stripTacticsBreadth c 1 0)
      return .node i `Lean.Parser.Tactic.tacticSeq1Indented #[
        .node ci `null (#[a[0]!].append ((newChildren.append #[(← sorryStx)]).push a[2]!))
      ]
    | _ => panic "Unexpected syntax structure"

  | 0, w, .node i k a => do
    return .node i k (← a.mapM (fun c => stripTacticsBreadth c 0 w))
  | d+1, w, .node i k a => do
    if (isTactic stx).isSome then
      return .node i k (← a.mapM (fun c => stripTacticsBreadth c d w))
    else
      return .node i k (← a.mapM (fun c => stripTacticsBreadth c depth w))
  | _, _, s => return s


partial def stripTacticsDepth (stx : Syntax) (depth width : Nat) : MetaM Syntax :=
  match depth, width, stx with
  | 0, _, .node _ `Lean.Parser.Tactic.tacticSeq _ => sorrySeqStx

  | d, w, .node i `Lean.Parser.Tactic.tacticSeq1Indented a => do
    let childSeq := a[0]!
    match childSeq with
    | .node ci `null ca => do
      let newChildren ← ca[:(2 * w)].toArray.mapM (fun c => stripTacticsDepth c d w)
      return .node i `Lean.Parser.Tactic.tacticSeq1Indented #[
        .node ci `null (newChildren.append #[← sorryStx])
      ]
    | _ => panic "Unexpected syntax structure"

  | d, w, .node i `Lean.Parser.Tactic.tacticSeqBracketed a => do
    let childSeq := a[1]!
    match childSeq with
    | .node ci `null ca => do
      let newChildren ← ca[:(2 * w)].toArray.mapM (fun c => stripTacticsDepth c d w)
      return .node i `Lean.Parser.Tactic.tacticSeq1Indented #[
        .node ci `null (#[a[0]!].append ((newChildren.append #[(← sorryStx)]).push a[2]!))
      ]
    | _ => panic "Unexpected syntax structure"

  | d+1, w, .node i k a => do
    if (isTactic stx).isSome then
      return .node i k (← a.mapM (fun c => stripTacticsDepth c d w))
    else
      return .node i k (← a.mapM (fun c => stripTacticsDepth c depth w))

  | 0, w, .node i k a => do
    return .node i k (← a.mapM (fun c => stripTacticsDepth c 0 w))

  | _, _, s => return s


partial def expandSorrysDepth (stx : Syntax) : StateT Nat MetaM Syntax := do
  let fuel ← get
  match fuel, stx with
  | 0, .node _ `Lean.Parser.Tactic.tacticSeq _ => sorrySeqStx

  | f, .node i `Lean.Parser.Tactic.tacticSeq1Indented a => do
    let childSeq := a[0]!
    match childSeq with
    | .node ci `null ca => do
      let mut newChildren := #[]
      for c in ca do
        if c.getKind == `null then
          newChildren := newChildren.push c
        else
          let curFuel ← get
          if curFuel > 0 then
            let expanded ← expandSorrysDepth c
            newChildren := newChildren.push expanded
          else
            newChildren := newChildren.push (← sorryStx)
            break
      return .node i `Lean.Parser.Tactic.tacticSeq1Indented #[
        .node ci `null (newChildren.append #[← sorryStx])
      ]
    | _ => panic "Unexpected syntax structure"

  | f, .node i `Lean.Parser.Tactic.tacticSeqBracketed a => do
    let childSeq := a[1]!
    match childSeq with
    | .node ci `null ca => do
      let mut newChildren := #[]
      for c in ca do
        if c.getKind == `null then
          newChildren := newChildren.push c
        else
          let curFuel ← get
          if curFuel > 0 then
            let expanded ← expandSorrysDepth c
            newChildren := newChildren.push expanded
          else
            newChildren := newChildren.push (← sorryStx)
            break
      return .node i `Lean.Parser.Tactic.tacticSeq1Indented #[
        .node ci `null (newChildren.append #[← sorryStx])
      ]
    | _ => panic "Unexpected syntax structure"

  | 0, .node i k a => do
    return .node i k (← a.mapM (fun c => expandSorrysDepth c))
  | f+1, .node i k a => do
    if (isTactic stx).isSome then
      set f
      return .node i k (← a.mapM (fun c => expandSorrysDepth c))
    else
      return .node i k (← a.mapM (fun c => expandSorrysDepth c))
  | _, s => return s


def isRealChild (c : Syntax) : Bool :=
  c.getKind != `null

def countChildren (children : Array Syntax) : Nat :=
  children.foldl (fun acc c => acc + if isRealChild c then 1 else 0) 0


partial def expandSorrysBreadth (stx : Syntax) : StateT Nat MetaM Syntax := do
  let fuel ← get
  match fuel, stx with
  | 0, .node _ `Lean.Parser.Tactic.tacticSeq _ => sorrySeqStx

  | f, .node i `Lean.Parser.Tactic.tacticSeq1Indented a => do
    let childSeq := a[0]!
    match childSeq with
    | .node ci `null ca => do
      let childCount := countChildren ca
      let baseAllocation := fuel / childCount
      let mut remainingFuel := fuel % childCount
      let mut newChildren := #[]
      for c in ca do
        if c.getKind == `null then
          newChildren := newChildren.push c
        else
          let mut allocation := baseAllocation
          if 0 < remainingFuel then
            allocation := allocation + 1
            remainingFuel := remainingFuel - 1
          if 0 < allocation then
            let expanded ← (expandSorrysBreadth c).run allocation
            newChildren := newChildren.push expanded
          else
            newChildren := newChildren.push (← sorryStx)
            break
      return .node i `Lean.Parser.Tactic.tacticSeq1Indented #[
        .node ci `null (newChildren.append #[← sorryStx])
      ]
    | _ => panic "Unexpected syntax structure"

  | f, .node i `Lean.Parser.Tactic.tacticSeqBracketed a => do
    let childSeq := a[1]!
    match childSeq with
    | .node ci `null ca => do
      let mut newChildren := #[]
      for c in ca do
        if c.getKind == `null then
          newChildren := newChildren.push c
        else
          let curFuel ← get
          if curFuel > 0 then
            let expanded ← expandSorrysDepth c
            newChildren := newChildren.push expanded
          else
            newChildren := newChildren.push (← sorryStx)
            break
      return .node i `Lean.Parser.Tactic.tacticSeq1Indented #[
        .node ci `null (newChildren.append #[← sorryStx])
      ]
    | _ => panic "Unexpected syntax structure"

  | 0, .node i k a => do
    return .node i k (← a.mapM (fun c => expandSorrysDepth c))
  | f+1, .node i k a => do
    if (isTactic stx).isSome then
      set f
      return .node i k (← a.mapM (fun c => expandSorrysDepth c))
    else
      return .node i k (← a.mapM (fun c => expandSorrysDepth c))
  | _, s => return s




def foo : MetaM Syntax := `(term| by
  cases n with
  | zero => simp
  | succ n =>
    have bar := Nat.add_comm
    have foo : True := by trivial
    simp_all)




def stripBreadth (m: MetaM Syntax)(d w : Nat) : MetaM Format := do
  let stx ← m
  let newStx ← stripTacticsBreadth stx d w
  let rendered ← Lean.PrettyPrinter.ppCategory `term newStx
  return rendered



def stripDepth (m: MetaM Syntax)(d w : Nat) : MetaM Format := do
  let stx ← m
  let newStx ← stripTacticsDepth stx d w
  let rendered ← Lean.PrettyPrinter.ppCategory `term newStx
  return rendered

def expandDepth (m: MetaM Syntax)(d : Nat) : MetaM Format := do
  let stx ← m
  let (newStx, _) ← (expandSorrysDepth stx).run d
  let rendered ← Lean.PrettyPrinter.ppCategory `term newStx
  return rendered

def foo1 : MetaM Syntax := `(term| by
  intros a b
  have h1 := h2
  have h2 := h1
  exact bar
)

#eval foo1

def foo2 : MetaM Syntax := `(term| by
  sorry
)

#eval (stripBreadth foo1 2 0)

#eval (stripDepth foo1 1 3)


def baz : MetaM Syntax := `(term| by
  {
  intros a
  sorry
  })

#eval baz

def bar : MetaM Syntax := `(term| by
  intros Γ e τ ρ k hwt hws
  induction k, ρ, e using eval.induct generalizing τ Γ

  -- k = 0
  case case1 => constructor

  -- k != 0, ENum
  case case2 =>
    simp [eval]
    cases hwt
    constructor; apply WV.TVInt

  -- k != 0, EBool
  case case3 =>
    simp [eval]
    cases hwt
    constructor; apply WV.TVBool

  -- k != 0, EVar
  case case4 =>
    simp [eval]
    cases hwt
    apply WR.TOk
    apply lookup_safe hws

  -- k !=0, EOp
  case case5 e1 e2 ih1 ih2=>
    simp [eval]
    cases hwt
    case TOp ih1_wt ih2_wt heq =>
      have eval1 := ih1 ih1_wt hws
      have eval2 := ih2 ih2_wt hws
      apply op_safe_r eval1 eval2 (by simp_all)

  -- k != 0, ELam
  case case6 v t e =>
    simp [eval]
    cases hwt
    case TLam h_e_wt =>
      constructor
      apply WV.TVClos hws h_e_wt

  -- k != 0, EApp
  case case7 e1 e2 ih1 ih2 ih3 =>
    simp [eval]
    cases hwt
    case TApp e1_wt e2_wt =>
      have ih1' := ih1 e2_wt hws
      have ih2' := ih2 e1_wt hws
      have ih1v := wr_any ih1'
      have ih2v := wr_any ih2'
      cases ih1v
      case inl h => rw [h]; constructor
      cases ih2v
      case inl hv1 h2 =>
        obtain ⟨v1, eq1, wv1⟩ := hv1
        simp_all [combine]; constructor
      case inr hv1 hv2 =>
        obtain ⟨v1, eq1, wv1⟩ := hv1
        obtain ⟨v2, eq2, wv2⟩ := hv2
        rw [eq1, eq2]
        simp [combine]
        cases wv1 with
        | TVClos ws wsub =>
          simp
          rename_i τ' ρ Γ' v' e'
          sorry

  -- k != 0, EIf a (True case)
  case case8 e e1 e2 h ih1 ih2 =>
    simp [eval]
    cases hwt with
    | TIf tbool te1 te2 =>
      rw [h]
      simp
      apply ih2 te1 hws

  -- k != 0, EIf a (False case)
  case case9 e e1 e2 h ih1 ih2 =>
    simp [eval]
    rw [h]
    simp
    cases hwt with
    | TIf tbool te1 te2 => apply ih2 te2 hws

  -- k != 0, EIf (Timeout case)
  case case10 e e1 e2 h1 h2 ih =>
    simp [eval]
    cases hwt with
    | TIf tbool te1 te2 =>
      have timeout := ih tbool hws
      have := wr_any timeout
      cases this with
      | inl hl => rw [hl]; constructor
      | inr hr =>
        cases hr with
        | intro v heq =>
          cases heq with
          | intro heq hwt =>
            cases hwt with
            | TVBool =>
              rename_i b
              cases b <;> contradiction
)

#eval (expandDepth bar 10)

#eval (stripBreadth bar 0 3)

#eval (stripDepth bar 2 7)
