import ReMath.Fwd.Defs

@[simp]
theorem fwdIter_zero {α} [Sub α] (f : Nat → α) (n : Nat) :
  Δ^[0] f n = f n := rfl

@[simp]
theorem fwdIter_succ {α} [Sub α] (f : Nat → α) (k n : Nat) :
  Δ^[k+1] f n = Δ (Δ^[k] f) n := rfl
