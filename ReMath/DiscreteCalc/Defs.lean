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

/-- Sum of `f 0, …, f (m - 1)` over `Fin m`, folded from the right. -/
def finSum {α} [Zero α] [Add α] (m : Nat) (f : Fin m → α) : α :=
  Fin.foldr m (fun k acc => f k + acc) 0

/-- Indefinite sum of `f` up to `n`: `f 0 + … + f (n - 1)`, the discrete counterpart of an integral. -/
def indefSum {M : Type _} [Zero M] [Add M] (f : Nat → M) (n : Nat) : M :=
  finSum n fun i => f i.val

@[inherit_doc] prefix:max "∑ " => indefSum

/-- The iterated indefinite sum of `f` of order `k` at `n`. -/
def indefSumIter {α} [Zero α] [Add α] (f : Nat → α) : Nat → Nat → α
  | 0, n => f n
  | k + 1, n => ∑ (indefSumIter f k) n

@[inherit_doc] notation:max "∑^[" k "] " f:max => indefSumIter f k

end DiscreteCalc
