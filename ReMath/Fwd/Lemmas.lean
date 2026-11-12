import ReMath.Fwd.Defs
import ReMath.Alg.Defs
import ReMath.Alg.Lemmas

/-- The discrete product rule. -/
theorem fwd_add {M : Type _} [Alg.Ring M] (f g : Nat → M) (n : Nat) :
    Δ (fun i => f i + g i) n = Δ f n + Δ g n := by
  change _ - _ = (_ - _) + (_ - _)
  simp only [Alg.sub_add, Alg.add_sub_assoc]
  simp only [Alg.sub_eq_add_neg]
  ac_rfl

/-- The discrete product rule. -/
theorem fwd_mul {M : Type _} [Alg.Ring M] (f g : Nat → M) (n : Nat) :
    Δ (fun i => f i * g i) n = f (n + 1) * Δ g n + Δ f n * g n := by
  change f (n + 1) * g (n + 1) - f n * g n =
    f (n + 1) * (g (n + 1) - g n) + (f (n + 1) - f n) * g n
  rw [Alg.mul_sub, Alg.sub_mul, Alg.add_comm, Alg.sub_add_sub_cancel]

@[simp]
theorem fwdIter_zero {α} [Sub α] (f : Nat → α) (n : Nat) :
  Δ^[0] f n = f n := rfl

@[simp]
theorem fwdIter_succ {α} [Sub α] (f : Nat → α) (k n : Nat) :
  Δ^[k+1] f n = Δ (Δ^[k] f) n := rfl
