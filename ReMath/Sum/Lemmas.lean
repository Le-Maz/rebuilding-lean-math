import ReMath.Alg.Defs
import ReMath.Alg.Lemmas
import ReMath.Sum.Defs

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

theorem nsmul_sum {M : Type _} [Alg.Semiring M] (f : Nat → M) (k n : Nat) :
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
