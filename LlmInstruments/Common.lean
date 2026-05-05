

def Array.enumerate {α} (arr : Array α) : Array (Nat × α) :=
  let rangeArr := Array.range arr.size
  rangeArr.zip arr
