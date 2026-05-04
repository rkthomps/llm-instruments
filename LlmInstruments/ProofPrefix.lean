

import LlmInstruments.TheoremCharacterization

import Lean
open Lean


namespace LlmInstruments

def sorrySeqStx : MetaM Syntax := `(tacticSeq| sorry)

def sorryStx : MetaM Syntax := `(tactic| sorry)

#eval sorrySeqStx



/--
A wrapper around the Lean `Syntax` type that we can use to represent syntax with hidden parts.
-/
inductive HiddenTacticSyntax where
  | raw (stx : Syntax)
  | node (i : Lean.SourceInfo) (k : SyntaxNodeKind) (args : Array HiddenTacticSyntax)
  /-- Hide children hideIdx onward. Note that this index also applies to "null" children
      invariant: there will always be at least one non-null child in hiddenChildren -/
  | hiddenChildren (i : Lean.SourceInfo) (args : Array HiddenTacticSyntax) (hideIdx : Nat)
deriving Inhabited, Repr

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
  depth : Nat
  childIdx: Nat
  expandResult : HiddenTacticSyntax
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
    if remainingChildren <= 1 then
      let mut candidates := #[]
      for (a, i) in args[:hideIdx].toArray.zipWithIndex do
        let newReconstructFn childHidden := reconstructFn (.node info `null (args.set! i childHidden))
        candidates := candidates.append (← getExpandCandidates a (depth + 1) newReconstructFn)
      let visitIdx ← get
      set (visitIdx + 1)
      let expandResult := reconstructFn (HiddenTacticSyntax.node info `null args)
      return candidates.append #[{ inOrderIdx := visitIdx, expandResult := expandResult, depth := depth, childIdx := hideIdx }]
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
        return candidates.append #[{ inOrderIdx := visitIdx, expandResult := expandResult, depth := depth, childIdx := hideIdx }]
      | none => panic "Invariant violation: there should be at least one non-null child"



abbrev SelectFn := (arr : Array ExpandCandidate) → (hArr : 0 < arr.size) → StateT StdGen Id ExpandCandidate

def iterateExpand (numExpands : Nat) (hStx : HiddenTacticSyntax)
  (select : SelectFn) : StateT StdGen Id HiddenTacticSyntax :=
  match numExpands with
  | 0 => pure hStx
  | n+1 => do
    let candidates := Id.run ((getExpandCandidates hStx 0 id).run' 0)
    if h : 0 = candidates.size then
      dbg_trace s!"No more candidates to expand after {numExpands} iterations."
      pure hStx
    else
      let selectedCandidate ← select candidates (by omega)
      iterateExpand n selectedCandidate.expandResult select


def expand (stx : Syntax) (numExpands : Nat) (select : SelectFn) (seed : Nat := 0) : MetaM Syntax := do
  let gen := mkStdGen seed
  let initialHidden := createInitialHiddenTacticSyntax stx
  -- dbg_trace s!"Initial hidden syntax: {repr initialHidden}"
  let finalHidden := Id.run ((iterateExpand numExpands initialHidden select).run' gen)
  -- dbg_trace s!"Final hidden syntax: {repr finalHidden}"
  hiddenSyntaxToSyntaxWithSorry finalHidden


instance : Ord (Int × Int) := lexOrd
instance : Ord (Int × (Int × Int)) := lexOrd

def minFn {α : Type} [Ord α] (scoreFn : ExpandCandidate → α) : SelectFn := fun arr harr =>
  let first := arr.get ⟨0, by omega⟩
  let min := arr.foldl (fun best c => if compare (scoreFn c) (scoreFn best) == .lt then c else best) first
  return min


def selectDepth : SelectFn := minFn fun c => (-1 * Int.ofNat c.depth, -1 * Int.ofNat c.childIdx, Int.ofNat c.inOrderIdx)
def selectBreadth : SelectFn := minFn fun c => (Int.ofNat c.depth, Int.ofNat c.childIdx, Int.ofNat c.inOrderIdx)


def selectDepthWeighted (depthWeight temperature : Float) : SelectFn := fun arr harr => do
  let first := arr.get ⟨0, by omega⟩
  let scoreFn c := depthWeight * Float.ofNat c.depth
  let firstScore := scoreFn first
  let scores := arr.map scoreFn
  let maxScore := scores.foldl (fun acc s => if s > acc then s else acc) (firstScore)
  let minScore := scores.foldl (fun acc s => if s < acc then s else acc) (firstScore)
  let normalizedScores := scores.map (fun s => if maxScore == minScore then 1.0 else (s - minScore) / (maxScore - minScore))
  if temperature == 0.0 then
    return arr.foldl (fun best c => if scoreFn c > scoreFn best then c else best) first
  let expScores := normalizedScores.map (fun s => Float.exp (s / temperature))
  let totalScore := expScores.foldl (fun acc s => acc + s) 0
  let precision := 1 <<< 30
  let gen ← get
  let (r, gen') := randNat gen 0 (precision - 1)
  set gen'
  let u : Float := Float.ofNat r / Float.ofNat precision
  let mut cumulative := 0.0
  for (c, expS) in arr.zip expScores do
    cumulative := cumulative + expS / totalScore
    if u < cumulative then
      return c
  panic! "Should never reach here"



def showExpanded (select : SelectFn) (numExpands : Nat) (mstx : MetaM Syntax) (seed : Nat := 0) : MetaM Format := do
  let stx ← mstx
  let newStx ← expand stx numExpands select seed
  -- dbg_trace "{newStx}"
  Lean.PrettyPrinter.ppCategory `term newStx



def test_straight : MetaM Syntax := `(term| by
  intros a b
  have h1 := h2
  have h2 := h1
  exact bar
)

#eval (showExpanded selectDepth 4 test_straight)
#eval (showExpanded selectBreadth 4 test_straight)
#eval (showExpanded (selectDepthWeighted 1.0 0.5) 4 test_straight)


def test1 : MetaM Syntax := `(term| by
  cases n with
  | zero =>
    simp
    cases h with
    | intro h1 h2 => simp
  | succ n =>
    have bar := Nat.add_comm
    have foo : True := by trivial
    simp_all)

#eval (showExpanded selectDepth 3 test1)
#eval (showExpanded selectBreadth 8 test1)
#eval (showExpanded (selectDepthWeighted 1.0 0.1) 4 (seed := 4) test1)

def foo : MetaM Syntax := `(term| by
  cases n with
  | zero => simp
  | succ n =>
    have bar := Nat.add_comm
    have foo : True := by trivial
    simp_all)


#eval (showExpanded selectDepth 6 foo)
#eval (showExpanded selectBreadth 3 foo)


def foo1 : MetaM Syntax := `(term| by
  intros a b
  have h1 := h2
  have h2 := h1
  exact bar
)

#eval foo1


#eval (showExpanded selectDepth 3 foo1)
#eval (showExpanded selectBreadth 0 foo1)


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

#eval (showExpanded selectDepth 50 bar)
#eval (showExpanded selectBreadth 50 bar)
