
import Lean

namespace RegExp
open Lean Elab

inductive Char where
  | z
  | o
deriving Repr

notation "c(0)" => Char.z
notation "c(1)" => Char.o

abbrev String := List Char


inductive RegExp : Type where
  | emp : RegExp
  | eps : RegExp
  | char : Char → RegExp
  | star : RegExp → RegExp
  | union : RegExp → RegExp → RegExp
  | concat : RegExp → RegExp → RegExp
deriving Nonempty, Inhabited, Repr


instance : Coe Char RegExp where
  coe c := RegExp.char c

notation "∅" => RegExp.emp
notation "ε" => RegExp.eps
notation r1 " <||> " r2  => RegExp.union r1 r2
notation r1 " <·> " r2 => RegExp.concat r1 r2
notation r "*" => RegExp.star r


inductive accepts : RegExp → String → Prop where
  | eps : accepts ε []
  | char (c : Char) : accepts c [c]
  | unionLeft r1 r2 s : accepts r1 s → accepts (r1 <||> r2) s
  | unionRight r1 r2 s : accepts r2 s → accepts (r1 <||> r2) s
  | concat r1 r2 s1 s2:
    accepts r1 s1 →
    accepts r2 s2 →
    accepts (r1 <·> r2) (s1 ++ s2)
  | starEmpty r : accepts (r*) []
  | starNonempty r s1 s2 :
    accepts r s1 →
    accepts (r*) s2 →
    accepts (r*) (s1 ++ s2)


def exp_all := (c(0) <||> c(1))*

def Language := String → Prop

def empty : Language := λ s => False
def all : Language := λ s => True

def is_regular (l : Language) := ∃ r, ∀ s, l s ↔ accepts r s

def union_lang (l₁ l₂ : Language) := λ s => l₁ s ∨ l₂ s

def concat_lang (l₁ l₂ : Language) := λ s => ∃ s₁ s₂, s = s₁ ++ s₂ ∧ l₁ s₁ ∧ l₂ s₂

def reverse_lang (l : Language) := λ (s : String) => ∃ s', s.reverse = s' ∧ l s'


theorem cons_app : forall (a : α) (l : List α), a :: l = [a] ++ l := by
  simp


theorem accepts_concat : ∀ r₁ r₂ s₁ s₂, accepts r₁ s₁ → accepts r₂ s₂ → accepts (r₁ <·> r₂) (s₁ ++ s₂) := by
  intros r₁ r₂ s₁ s₂ h₁ h₂
  constructor
  . assumption
  . assumption


theorem accepts_unionLeft : ∀ r₁ r₂ s, accepts r₁ s → accepts (r₁ <||> r₂) s := by
  intros r₁ r₂ s h
  constructor
  . assumption

theorem accepts_star_empty : ∀ r, accepts (r*) [] := by
  intro r
  constructor


theorem rejects_emp : ∀ s, ¬ accepts ∅ s := by
  intro s h
  cases h


theorem accepts_not_emp : ∀ r, (∃ s, accepts r s) → r ≠ ∅ := by
  intro r h
  obtain ⟨ s, h' ⟩ := h
  cases h' <;> simp_all


theorem empty_regular : is_regular empty := by
  simp [is_regular, empty]
  exists ∅
  apply rejects_emp


theorem star_r : ∀ r s, accepts r s → accepts (r*) s := by
  intros r s h
  rw [← List.append_nil s]
  constructor
  . assumption
  . constructor


theorem union_comm : ∀ r₁ r₂ s, accepts (r₁ <||> r₂) s ↔ accepts (r₂ <||> r₁) s := by
  intros r₁ r₂ s
  constructor
  . intro h
    cases h with
    | unionLeft _ _ _ ha => apply accepts.unionRight; assumption
    | unionRight _ _ _ ha => apply accepts.unionLeft; assumption
  . intro h
    cases h with
    | unionLeft _ _ _ ha => apply accepts.unionRight; assumption
    | unionRight _ _ _ ha => apply accepts.unionLeft; assumption


theorem accepts_char : ∀ (c : Char) s, accepts c s → s = [c] := by
  intros c s h
  cases h; simp


theorem cat_char_disjoint : ∀ (c₁ c₂ : Char) r s₁ s₂,
  c₁ ≠ c₂ →
  (accepts (c₁ <·> r) s₁) →
  (accepts (c₂ <·> r) s₂) →
  s₁ ≠ s₂ := by
  intros c₁ c₂ r s₁ s₂ h₁ h₂ h₃
  cases h₂ with
  | concat _ _ s₁' s₂' h₁' h₂' =>
    cases h₃ with
    | concat _ _ s₁'' s₂'' h₁'' h₂'' =>
      have hc₁ := accepts_char c₁ s₁' h₁'
      have hc₂ := accepts_char c₂ s₂'

      have h := accepts_char c₁ s₁' h₁'
      have h' := accepts_char c₂ s₁'' h₁''
      simp_all



theorem accepts_exp_all : ∀ s, accepts exp_all s := by
  intros s
  induction s with
  | nil => simp[exp_all]; constructor
  | cons h t ih =>
    simp[exp_all]
    rw [cons_app]
    apply accepts.starNonempty
    · cases h with
      | z =>
        apply accepts.unionLeft
        apply accepts.char
      | o =>
        apply accepts.unionRight
        apply accepts.char
    · assumption



theorem all_regular : is_regular all := by
  simp [is_regular, all]
  exists exp_all
  apply accepts_exp_all




theorem union_regular : ∀ (l₁ l₂ : Language),
  is_regular l₁ →
  is_regular l₂ →
  is_regular (union_lang l₁ l₂) := by
  intros l₁ l₂ h₁ h₂
  simp [is_regular, union_lang] at *
  obtain ⟨ r₁, hr₁ ⟩ := h₁
  obtain ⟨ r₂, hr₂ ⟩ := h₂
  exists r₁ <||> r₂
  intro s
  constructor
  · case mp => intro h; cases h with
    | inl h => apply accepts.unionLeft; apply (hr₁ s).mp h
    | inr h => apply accepts.unionRight; apply (hr₂ s).mp h
  . case mpr => intro h; cases h with
    | unionLeft _ _ _ ha => left; apply (hr₁ s).mpr ha
    | unionRight _ _ _ ha => right; apply (hr₂ s).mpr ha


theorem concat_regular : ∀ (l₁ l₂ : Language),
  is_regular l₁ →
  is_regular l₂ →
  is_regular (concat_lang l₁ l₂) := by
  intros l₁ l₂ h₁ h₂
  simp [is_regular, concat_lang] at *
  obtain ⟨ r₁, hr₁ ⟩ := h₁
  obtain ⟨ r₂, hr₂ ⟩ := h₂
  exists r₁ <·> r₂
  intro s
  constructor
  · case mp =>
    intro h
    obtain ⟨ s₁, s₂, h₁, h₂, h₃ ⟩ := h
    rw [h₁]
    apply accepts.concat <;> simp_all
  · case mpr =>
    · intro h
      cases h with
      | concat _ _ s₁ s₂ h₁ h₂ =>
        exists s₁
        exists s₂
        simp_all


def reverse : RegExp → RegExp
  | .emp => ∅
  | .eps => ε
  | .char c => c
  | .star r => (reverse r)*
  | .union r₁ r₂ => (reverse r₁) <||> (reverse r₂)
  | .concat r₁ r₂ => (reverse r₂) <·> (reverse r₁)

def reverse_inv : ∀ r, reverse (reverse r) = r := by
  intros r
  induction r <;> simp [reverse] <;> simp_all

theorem reverse_invert_emp : ∀ r, reverse r = (∅ : RegExp) → r = (∅ : RegExp) := by
  intros r h ; induction r <;> congr <;> contradiction

theorem reverse_invert_eps : ∀ r, reverse r = ε → r = ε := by
  intros r h ; induction r <;> congr <;> contradiction

theorem reverse_invert_char : ∀ r (c : Char), reverse r = c → r = c := by
  intros r c h ; induction r <;> (try contradiction)
  case char c' => simp [reverse] at h; simp_all

theorem reverse_invert_union : ∀ (r r₁ r₂ : RegExp),
  (reverse r = r₁ <||> r₂) → r = (reverse r₁) <||> (reverse r₂) := by
  intros r ; induction r <;> (intros; try contradiction)
  . case union r₁ r₂ ih₁ ih₂ r₁' r₂' h =>
    simp [reverse] at h
    cases h with
    | intro h1 h2 =>
      rw [← h1]
      rw [← h2]
      rw [reverse_inv]
      rw [reverse_inv]

theorem reverse_invert_cat : ∀ (r r₁ r₂ : RegExp),
  (reverse r = r₁ <·> r₂) → r = (reverse r₂) <·> (reverse r₁) := by
  intros r ; induction r <;> (intros; try contradiction)
  . case concat r₁ r₂ ih₁ ih₂ r₁' r₂' h =>
    simp [reverse] at h
    cases h with
    | intro h1 h2 =>
      rw [← h1]
      rw [← h2]
      rw [reverse_inv]
      rw [reverse_inv]

theorem reverse_invert_star : ∀ r r', reverse r = r'* → r = (reverse r')* := by
  intros r; induction r <;> (intros; try contradiction)
  . case star r' ih r'' h =>
    simp [reverse] at h
    rw [← h]
    rw [reverse_inv]



theorem lazy_star : ∀ r s₁ s₂, accepts (r*) s₁ → accepts r s₂ → accepts (r*) (s₁ ++ s₂) := by
  intros r s₁ s₂ h₁ h₂
  generalize h : (r*) = myr at h₁
  induction h₁ <;> (try contradiction)
  . case starEmpty r' =>
    simp; rw [← h]; apply star_r; assumption
  . case starNonempty r' s s₁' s₂' hs he ih =>
    rw [List.append_assoc]
    constructor
    . assumption
    . apply ih; assumption


theorem reverse_correct_mp : ∀ r s, accepts r s → accepts (reverse r) (s.reverse) := by
  intros r s h
  induction h with
  | eps => simp [reverse]; constructor
  | char c => simp [reverse]; constructor
  | unionLeft r₁ r₂ s' h ih =>
    simp [reverse]; apply accepts.unionLeft; assumption
  | unionRight r₁ r₂ s' h ih =>
    simp [reverse]; apply accepts.unionRight; assumption
  | concat r₁ r₂ s₁ s₂ h₁ h₂ ih₁ ih₂ =>
    simp [reverse]; apply accepts.concat <;> assumption
  | starEmpty r => simp; constructor
  | starNonempty r s₁ s₂ h₁ h₂ ih₁ ih₂ =>
    simp
    simp[reverse]
    apply lazy_star
    . apply ih₂
    . apply ih₁



theorem reverse_correct_mpr : ∀ r r' s s',
  reverse r = r' →
  s.reverse = s' →
  accepts r' s' → accepts r s := by
  intros r f' s s' h₁ h₂ h₃
  induction h₃ generalizing r s with
  | eps =>
    have heps := reverse_invert_eps r h₁
    simp_all; constructor
  | char c =>
    have hc := reverse_invert_char r c h₁
    have hs : s = [c] := by
      have := congrArg List.reverse h₂
      simpa using this
    rw [hc, hs]
    exact accepts.char c
  | unionLeft r1 r2 s' h ih =>
    have hunion := reverse_invert_union r r1 r2 h₁
    rw [hunion]
    apply accepts.unionLeft
    apply ih
    apply reverse_inv
    assumption
  | unionRight r1 r2 s' h ih =>
    have hunion := reverse_invert_union r r1 r2 h₁
    rw [hunion]
    apply accepts.unionRight
    apply ih
    apply reverse_inv
    assumption
  | concat r₁ r₂ s₁ s₂ h₁' h₂' ih₁ ih₂ =>
    have hconcat := reverse_invert_cat r r₁ r₂ h₁
    rw [hconcat]
    have h₂ : s = (s₁ ++ s₂).reverse := by rw [← h₂]; simp
    rw [h₂, List.reverse_append]
    apply accepts.concat
    . apply ih₂; apply reverse_inv; simp
    . apply ih₁; apply reverse_inv; simp
  | starEmpty r' =>
    have hstar := reverse_invert_star r r' h₁
    rw [hstar]
    simp at h₂
    simp_all
    constructor
  | starNonempty r' s₁ s₂ h₁' h₂' ih₁ ih₂ =>
    have hstar := reverse_invert_star r r' h₁
    rw [hstar]
    have h₂ : s = (s₁ ++ s₂).reverse := by rw [← h₂]; simp
    rw [h₂, List.reverse_append]
    apply lazy_star
    . apply ih₂; exact (reverse_inv (r'*)); simp
    . apply ih₁; exact (reverse_inv r'); simp


theorem reverse_correct : ∀ r s, accepts r s ↔ accepts (reverse r) (s.reverse) := by
  intros r s
  constructor
  . apply reverse_correct_mp
  . apply reverse_correct_mpr r (reverse r) s (s.reverse) <;> simp


theorem reverse_regular : ∀ l, is_regular l → is_regular (reverse_lang l) := by
  intros l h
  simp_all [is_regular, reverse_lang]
  obtain ⟨ r, h' ⟩ := h
  exists (reverse r)
  intro s
  constructor
  . case mp =>
    intro h
    have hrev := (reverse_correct r s.reverse).mp
    simp at hrev
    apply hrev
    apply (h' (s.reverse)).mp
    assumption
  . case mpr =>
    intro h
    apply (h' (s.reverse)).mpr
    have hrev := (reverse_correct r s.reverse).mpr
    apply hrev
    simp
    assumption


end RegExp


namespace Finset
structure Finset where
  decider : Nat → Prop
  ceiling : ∃ c, ∀ n, c < n → ¬ decider n

def singleton (n : Nat) : Finset :=
⟨ λ m => m = n, (by exists n; intros; omega) ⟩

def subset (s₁ s₂ : Finset) := ∀ n, s₁.decider n → s₂.decider n


def intersection (f₁ : Finset) (f₂ : Finset) : Finset :=
  let newDecider := λ n => f₁.decider n ∧ f₂.decider n
  ⟨ newDecider, (by
    obtain ⟨ c₁, h₁ ⟩ := f₁.ceiling
    obtain ⟨ c₂, h₂ ⟩ := f₂.ceiling
    exists (min c₁ c₂)
    show ∀ n, min c₁ c₂ < n → ¬ (f₁.decider n ∧ f₂.decider n)
    intro n hm
    rw [Nat.min_def] at hm
    cases Nat.le_total c₁ c₂ with
    | inl hl =>
      simp_all
    | inr hr =>
      have ht := Nat.le_iff_lt_or_eq.mp hr
      cases ht with
      | inl hl' =>
        have hm' : ¬ (c₁ ≤ c₂) := by omega
        simp [hm'] at hm
        have hf := h₂ n hm
        simp [hf]
      | inr hr' =>
        simp [hr'] at hm
        have hf := h₁ n hm
        simp [hf]
  )⟩

theorem intersection_subset_l : ∀ f₁ f₂, subset (intersection f₁ f₂) f₁ := by
  intros f₁ f₂ n h
  simp [intersection] at h
  exact h.left

theorem intersection_subset_r : ∀ f₁ f₂, subset (intersection f₁ f₂) f₂ := by
  intros f₁ f₂ n h
  simp [intersection] at h
  exact h.right

def finset_eq (f₁ f₂ : Finset) := ∀ n, f₁.decider n ↔ f₂.decider n

def union (f₁ : Finset) (f₂ : Finset) : Finset :=
  let newDecider := λ n => f₁.decider n ∨ f₂.decider n
  ⟨ newDecider, (by
    obtain ⟨ c₁, h₁ ⟩ := f₁.ceiling
    obtain ⟨ c₂, h₂ ⟩ := f₂.ceiling
    exists (max c₁ c₂)
    show ∀ n, max c₁ c₂ < n → ¬ (f₁.decider n ∨ f₂.decider n)
    intro n hm
    simp
    constructor
    . case left => apply h₁; omega
    . case right => apply h₂; omega
  )⟩


theorem intersection_over_union : ∀ f₁ f₂ f₃,
  finset_eq (intersection (union f₁ f₂) f₃) (union (intersection f₁ f₃) (intersection f₂ f₃)) := by
  intros f₁ f₂ f₃
  unfold finset_eq
  intro n
  constructor <;> intro h <;> cases h <;> simp_all[union, intersection]


theorem union_over_intersection : ∀ f₁ f₂ f₃,
  finset_eq (union (intersection f₁ f₂) f₃) (intersection (union f₁ f₃) (union f₂ f₃)) := by
  intros f₁ f₂ f₃
  unfold finset_eq
  intro n
  constructor
  . case mp =>
    intro h
    simp [union, intersection] at *
    cases h with
    | inl hl => simp_all
    | inr hr => simp_all
  . case mpr =>
    intro h
    simp [union, intersection] at *
    cases h with
    | intro hl hr =>
      cases hl <;> cases hr <;> simp_all


theorem subset_eq : ∀ f₁ f₂, subset f₁ f₂ → subset f₂ f₁ → finset_eq f₁ f₂ := by
  intro f₁ f₂ h₁ h₂
  simp [finset_eq]
  intro n; constructor <;> simp_all[subset]





def nonempty (f : Finset) := ∃ n, f.decider n


end Finset


namespace NFA

open Finset

structure NFA where
  states : Finset

  start : Nat
  start_valid : states.decider start

  transition : Nat → RegExp.Char → Finset
  transition_valid : ∀ q c, subset (transition q c) states

  accept : Finset
  accept_valid : subset accept states


def power_transition (f : Finset) (c : RegExp.Char) (nfa : NFA) : Finset :=
  let newDecider := λ n => ∃ m, f.decider m ∧ (nfa.transition m c).decider n
  ⟨ newDecider, (by
    obtain ⟨ ceil, h ⟩ := nfa.states.ceiling
    show ∃ bound, ∀ n, bound < n → ¬ ∃ m, f.decider m ∧ (nfa.transition m c).decider n
    exists ceil
    intros n hceil
    simp
    intros x hfd
    have ht := nfa.transition_valid x c
    simp [subset] at ht
    intro hn
    have hf := ht n hn
    have hf' := h n hceil
    contradiction
  )⟩


theorem power_transition_singleton : ∀ n c nfa,
  power_transition (singleton n) c nfa = nfa.transition n c := by
  intros n c nfa
  simp[power_transition, Finset.singleton]


-- takes a nfa, string, set of current states
inductive AcceptsNFACore : NFA → RegExp.String → Finset → Prop where
  | eps nfa qs : nonempty (intersection nfa.accept qs) → AcceptsNFACore nfa [] qs
  | char (nfa : NFA) (h : RegExp.Char) (tl : RegExp.String) (qs : Finset) :
    AcceptsNFACore nfa tl (power_transition qs h nfa) →
    AcceptsNFACore nfa (h :: tl) qs

def AcceptsNFA (nfa : NFA) (s : RegExp.String) : Prop :=
  AcceptsNFACore nfa s (Finset.singleton nfa.start)

def finset1 := Finset.singleton 0

def all_nfa : NFA :=
  let states := finset1
  let start := 0
  let transition := λ (q : Nat) (c : RegExp.Char) => match q with
    | _ => match c with
      | _ => finset1
  let accept := finset1
  ⟨ states,
    start,
    (by simp[states, finset1, Finset.singleton]),
    transition,
    (by intros q c; simp[subset]),
    accept,
    (by simp[subset])
  ⟩

theorem all_idempotent : ∀ c q, all_nfa.transition c q = finset1 := by
  simp[all_nfa]


theorem all_accepts : ∀ s, AcceptsNFA all_nfa s := by
  intro s
  induction s with
  | nil =>
    simp [AcceptsNFA]
    apply AcceptsNFACore.eps
    simp [nonempty]
    exists all_nfa.start
  | cons h tl ih =>
    simp [AcceptsNFA]
    apply AcceptsNFACore.char
    rw [power_transition_singleton]
    simp[AcceptsNFA] at ih
    rw [all_idempotent]
    simp[finset1]
    apply ih


theorem myNewTheorem : True := by trivial

end NFA
