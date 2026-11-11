/-- Finite sum of `f` over the natural numbers below `n`. -/
def sum {M : Type _} [Zero M] [Add M] (f : Nat → M) (n : Nat) : M :=
  Fin.foldr n (fun i acc => f i.val + acc) 0

@[inherit_doc] prefix:max "∑ " => sum
