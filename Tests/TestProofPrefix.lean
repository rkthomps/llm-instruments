import Lean
import LlmInstruments.ProofPrefix

open Lean

namespace Tests

open LlmInstruments

def test_straight : MetaM Syntax := `(term| by
  intros a b
  have h1 := h2
  have h2 := h1
  exact bar
)

#eval (showExpanded selectDepth 4 test_straight)
#eval (showExpanded selectBreadth 4 test_straight)
#eval (showExpanded (selectDepthWeighted 1.0 0.0) 4 test_straight)


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
#eval (showExpanded (selectDepthWeighted (-1.0) 0.0) 2 (seed := 4) test1)

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

#eval (showExpanded (selectDepthWeighted (-1) 1.0) 30 (seed := 4) bar)
