


namespace BinaryTree

variable (α : Type)

inductive BinaryTree (α : Type) where
  | leaf
  | node (d : α) (l : BinaryTree α) (r : BinaryTree α)


def BinaryTree.size : BinaryTree α → Nat
  | .leaf => 0
  | .node _ l r => l.size + r.size


def BinaryTree.height : BinaryTree α → Nat
  | .leaf => 0
  | .node _ l r => 1 + max l.size r.size


theorem height_lte_size (t : BinaryTree α) : t.height ≤ t.size := by
  sorry



/-
This section contains theorems with errors.
The purpose of these errors is to test our ability to find invalid Prefixs / Substrings.
-/

/-
Error Categories:

## No Prefix
- unsolved goals
- Alternative `...` not provided

## Potential Prefix
- simp made no progress

## Certain Prefix
- No goals to be solved

-/


/-
## Ignore

### Alternative `...` not provided
Not providing induction alternatives does not necessarily yield an
invalid prefix.
-/
theorem height_lte_size_test_1 (t : BinaryTree α) : t.height ≤ t.size := by
  induction t with
  | leaf => simp [BinaryTree.height]


def height_lte_size_test_1_expected : Option String := none


/-
Not solving all goals does not necessarily yield an invalid prefix.
### unsolved goals
-/
theorem height_lte_size_test_2 : ∀ (t : BinaryTree α), t.height ≤ t.size := by
  intros t

def height_lte_size_test_2_expected : Option String := none



/-
## Certain Prefix

### no goals to be solved
-/
theorem height_lte_size_test_3 : ∀ (t : BinaryTree α), t.height ≤ t.size := by
  intros t





end BinaryTree
