






import Lean

open Lean
open List


-- def List.bind (l : List α) (f : α → List β) : List β :=
--   match l with
--   | [] => []
--   | x :: xs =>
--     f x ++ xs.bind f

instance : Monad List where
  pure := List.pure
  bind := List.bind


inductive Tree where
  | leaf
  | node (children : List Tree)


#check range


mutual
def Tree.childrenSize : List Tree → Nat
  | [] => 0
  | x :: xs => x.size + Tree.childrenSize xs

def Tree.size : Tree → Nat
  | leaf => 0
  | .node cs => 1 + Tree.childrenSize cs
end


mutual
def Tree.numSetsOfChildrenOfSize (size : Nat) (children : List Tree) : Nat :=
  -- For each size [0..size], I could allocate that size to child 0
  match size with
  | 0 => 1 -- Assignt each child 0
  | n + 1 =>
    match children with
    | [] => 0
    | [x] => x.numSubtreesOfSize size
    | x :: xs =>
      let sizesWithFirstChildAssignment : List Nat := do
        let firstChildSize ← range (size + 1)
        let numFirstChildTrees := x.numSubtreesOfSize firstChildSize
        let numRestChildTrees := Tree.numSetsOfChildrenOfSize (size - firstChildSize) xs
        return numFirstChildTrees * numRestChildTrees
      sizesWithFirstChildAssignment.foldl Nat.add 0

def Tree.numSubtreesOfSize (t : Tree) (size : Nat) : Nat :=
  match size, t with
  | 0, _ => 1
  | _ + 1, leaf => 0
  | n' + 1, node cs => Tree.numSetsOfChildrenOfSize n' cs
end


inductive MemoizedSizeTree where
  | leaf
  | node (counts : Array Nat) (cs : List MemoizedSizeTree)


def MemoizedSizeTree.numSubtreesOfSize (t : MemoizedSizeTree) (size : Nat) : Nat :=
  match size, t with
  | 0, _ => 1
  | _ + 1, leaf => 0
  | n + 1, node counts _ => counts.get! size

#check List.replicate

def emptyChildrenMemoizedList (size : Nat) : List Nat :=
  match size with
  | 0 => [1]
  | n + 1 => [1] ++ (List.replicate size 0)


def memoizeChildPartitions (children : List MemoizedSizeTree) (size : Nat) : List Nat :=
  match children with
  | [] => [1] ++ (List.replicate size 0)
  | [x] => do
    let curSize ← range (size + 1)
    return x.numSubtreesOfSize curSize
  | x :: xs =>
    let memoizedXs := (memoizeChildPartitions xs size).toArray
    do
      let curSize ← range (size + 1)
      let numFirstChildTrees := x.numSubtreesOfSize curSize
      let numRestChildTrees := memoizedXs.get! (size - curSize)
      return numFirstChildTrees * numRestChildTrees


def numChildPartitions (children : List MemoizedSizeTree) (size : Nat) : Nat :=
  (memoizeChildPartitions children size).foldl Nat.add 0


mutual

def buildMemoizedChildren (ts : List Tree) (size : Nat) : List MemoizedSizeTree :=
  match ts with
  | [] => []
  | x :: xs =>
    buildMemoizedTree x size :: buildMemoizedChildren xs size

def buildMemoizedTree (t : Tree) (size : Nat) : MemoizedSizeTree :=
  match t with
  | .leaf => .leaf
  | .node cs =>
    let memoizedChildren := buildMemoizedChildren cs size
    let sizeList : List Nat := do
      let size ← range (size + 1)
      match size with
      | 0 => return 1
      | n + 1 => return (numChildPartitions memoizedChildren n)
    .node sizeList.toArray memoizedChildren

end

def MemoizedSizeTree.counts (t : MemoizedSizeTree) : Option (Array Nat) :=
  match t with
  | .leaf => .none
  | .node counts _ => counts

def Tree.memoize (t : Tree) := buildMemoizedTree t (t.size)

def binOfSize : Nat → Tree
  | 0 => .leaf
  | n + 1 => .node [binOfSize n, binOfSize n]


def bin1 : Tree := .node [.leaf]
#eval bin1.numSubtreesOfSize 1
#eval bin1.numSubtreesOfSize 0
#eval bin1.numSubtreesOfSize 2

def bin2 : Tree := .node [bin1, bin1]
#eval bin2.numSubtreesOfSize 1
#eval bin2.numSubtreesOfSize 2
#eval bin2.numSubtreesOfSize 3

def bin3 : Tree := .node [bin2, bin2]
#eval bin3.numSubtreesOfSize 1
#eval bin3.numSubtreesOfSize 2
#eval bin3.numSubtreesOfSize 3
#eval bin3.numSubtreesOfSize 4
#eval bin3.numSubtreesOfSize 5
#eval bin3.numSubtreesOfSize 6
#eval bin3.numSubtreesOfSize 7
#eval bin3.numSubtreesOfSize 8

#eval (binOfSize 8).memoize.counts
#eval (binOfSize 8).size



inductive WeightedTree where
  | leaf
  | node (children : List (WeightedTree × Nat))


mutual
def WeightedTree.materializeChildren : List (WeightedTree × Nat) → List Tree
  | [] => []
  | (t, _) :: ts => t.materialize :: (WeightedTree.materializeChildren ts)

def WeightedTree.materialize : WeightedTree → Tree
  | leaf => Tree.leaf
  | visableNode cs => Tree.node (WeightedTree.materializeChildren cs)
  | hiddenNode _ => Tree.leaf
end

def WeightedTree.samplePrefix (wt : WeightedTree) : Option Tree :=
  match size with
  | 0 => leaf
  | n + 1 =>
    match wt with
    | leaf => leaf
    | node


def Tree.samplePrefixOfSize (t : Tree) (size n : Nat) : Tree :=
  sorry



def samplePrefixsOfSize (stx : Syntax) (size n : Nat) : List Syntax :=
  sorry


def samplePrefixs (stx : Syntax) (n : Nat) : List Syntax :=
  sorry
