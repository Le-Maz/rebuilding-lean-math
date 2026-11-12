namespace DiscreteCalc

/-- Forward difference of `f` at `n`: `fwd f n = f (n + 1) - f n`. -/
@[grind]
def fwd {α} [Sub α] (f : Nat → α) (n : Nat) : α :=
  f (n + 1) - f n

@[inherit_doc] prefix:max "Δ " => fwd

/-- The iterated forward difference of `f` of order `k` at `n`. -/
def fwdIter {α} [Sub α] (f : Nat → α) : Nat → Nat → α
  | 0, n => f n
  | k + 1, n => Δ (fwdIter f k) n

@[inherit_doc] notation:max "Δ^[" k "] " f:max => fwdIter f k

/-- Finite sum of `f` over the natural numbers below `n`. -/
def sum {M : Type _} [Zero M] [Add M] (f : Nat → M) (n : Nat) : M :=
  Fin.foldr n (fun i acc => f i.val + acc) 0

@[inherit_doc] prefix:max "∑ " => sum

/-- The iterated finite sum of `f` of order `k` at `n`. -/
def sumIter {α} [Zero α] [Add α] (f : Nat → α) : Nat → Nat → α
  | 0, n => f n
  | k + 1, n => ∑ (sumIter f k) n

@[inherit_doc] notation:max "∑^[" k "] " f:max => sumIter f k

end DiscreteCalc
