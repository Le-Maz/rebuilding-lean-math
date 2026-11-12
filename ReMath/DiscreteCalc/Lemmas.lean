import ReMath.DiscreteCalc.Defs
import ReMath.Alg.Defs
import ReMath.Alg.Lemmas

namespace DiscreteCalc

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

@[simp]
theorem sum_zero {M : Type _} [Zero M] [Add M] (f : Nat → M) :
    ∑ f 0 = 0 := by
  simp [sum]

theorem sum_succ {M : Type _} [Zero M] [Add M] (f : Nat → M) (n : Nat) :
    ∑ f (n + 1) = f 0 + ∑ (fun i => f (i + 1)) n := by
  simp [sum, Fin.foldr_succ]

theorem sum_succ' {M : Type _} [Alg.AddMonoid M] (f : Nat → M) (n : Nat) :
    ∑ f (n + 1) = ∑ f n + f n := by
  induction n generalizing f with
  | zero =>
    simp [sum, Fin.foldr_succ]
  | succ n ih =>
    rw [sum_succ, ih]
    rw [← Alg.add_assoc, ← sum_succ]

theorem sum_const {M : Type _} [Alg.AddMonoid M] (x : M) (n : Nat) :
    ∑ (fun _ => x) n = n • x := by
  induction n with
  | zero =>
    simp [sum_zero, Alg.zero_nsmul]
  | succ n ih =>
    rw [sum_succ', Alg.succ_nsmul]
    congr 1

theorem nsmul_sum {M : Type _} [Alg.AddCommMonoid M] (f : Nat → M) (k n : Nat) :
    k • ∑ f n = ∑ (fun i => k • f i) n := by
  induction n with
  | zero =>
    simp [sum_zero, Alg.nsmul_zero]
  | succ n ih =>
    rw [sum_succ', sum_succ']
    rw [Alg.nsmul_add, ih]

theorem mul_sum {M : Type _} [Alg.Semiring M] (f : Nat → M) (x : M) (n : Nat) :
    x * ∑ f n = ∑ (fun i => x * f i) n := by
  induction n with
  | zero =>
    simp [sum_zero]
  | succ n ih =>
    rw [sum_succ', sum_succ']
    rw [Alg.mul_add, ih]

/-- The sum of forward differences telescopes. -/
theorem sum_fwd {M : Type _} [Alg.Ring M] (f : Nat → M) (n : Nat) :
    ∑ Δ f n = f n - f 0 := by
  induction n with
  | zero =>
    rw [sum_zero, Alg.sub_self]
  | succ n ih =>
    rw [sum_succ', ih]
    exact Alg.sub_add_sub_cancel (f n) (f 0) (f (n + 1))

/-- The forward difference of a sum recovers the summand. -/
theorem fwd_sum {M : Type _} [Alg.Ring M] (f : Nat → M) (n : Nat) :
    Δ ∑ f n = f n := by
  change ∑ f (n + 1) - ∑ f n = f n
  rw [sum_succ']
  exact Alg.add_sub_cancel_left (∑ f n) (f n)

end DiscreteCalc
