import ReMath.Alg.Defs
import ReMath.Alg.Core
import ReMath.Alg.Lemmas
import ReMath.DiscreteCalc.Defs
import ReMath.DiscreteCalc.Lemmas

namespace DiscreteCalc

private theorem Nat.pow_sub_pow_succ (a b n : Nat) (hab : a ≥ b) :
    a ^ (n + 1) - b ^ (n + 1) =
      (a - b) * a ^ n + b * (a ^ n - b ^ n) := by
  have h₁ : b ^ n ≤ a ^ n := Nat.pow_le_pow_left hab n
  have h₂ : a * b ^ n ≤ a * a ^ n := Nat.mul_le_mul_left a h₁
  calc
    _ = a * a ^ n - b * b ^ n := by simp [← Nat.pow_succ']
    _ = (a * a ^ n - a * b ^ n) + (a * b ^ n - b * b ^ n) := by
      rw [← Nat.sub_add_cancel h₂, Nat.add_sub_cancel]
      rw [Nat.add_sub_assoc (Nat.mul_le_mul_right _ hab)]
    _ = a * (a ^ n - b ^ n) + (a - b) * b ^ n := by
      rw [Nat.mul_sub, Nat.sub_mul]
    _ = (a - b) * a ^ n + b * (a ^ n - b ^ n) := by
      have ha : a - b + b = a := Nat.sub_add_cancel hab
      have hp : a ^ n - b ^ n + b ^ n = a ^ n :=
        Nat.sub_add_cancel h₁
      calc
        _ = ((a - b) + b) * (a ^ n - b ^ n) + (a - b) * b ^ n :=
          by rw [← ha]; simp
        _ = (a - b) * (a ^ n - b ^ n) +
            b * (a ^ n - b ^ n) + (a - b) * b ^ n :=
          by rw [Nat.add_mul]
        _ = (a - b) * (a ^ n - b ^ n) +
            (a - b) * b ^ n + b * (a ^ n - b ^ n) :=
          by ac_rfl
        _ = (a - b) * a ^ n + b * (a ^ n - b ^ n) :=
          by rw [← Nat.mul_add, hp]

/-- Shifting the summation index of the geometric-like sum multiplies it by `a`. -/
private theorem sum_shift (a b n : Nat) :
    ∑ (fun i => a ^ (i + 1) * b ^ (n - (i + 1))) n =
      a * ∑ (fun i => a ^ i * b ^ (n - 1 - i)) n := by
  rw [mul_sum]
  congr 1
  funext i
  have h : n - (i + 1) = n - 1 - i := by omega
  rw [h, Nat.pow_succ]
  grind only

theorem Nat.pow_sub_pow (a b n : Nat) (hab : a ≥ b) :
    a ^ n - b ^ n =
      (a - b) * ∑ (fun i => a ^ i * b ^ (n - 1 - i)) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [sum_succ]
    simp only [Nat.mul_add, Nat.pow_zero, Nat.one_mul, Nat.add_sub_cancel,
      Nat.sub_zero]
    simp only [Nat.pow_sub_pow_succ a b n hab, sum_shift]
    generalize ∑ (fun i => a ^ i * b ^ (n - 1 - i)) n = S at *
    simp only [Nat.sub_mul, Nat.mul_sub]
    have h0 : b ^ n ≤ a ^ n := by
      apply Nat.pow_le_pow_left
      exact hab
    have h1 : b * b ^ n ≤ b * a ^ n :=
      Nat.mul_le_mul_left b h0
    have h2 : b * a ^ n ≤ a * a ^ n :=
      Nat.mul_le_mul_right (a ^ n) hab
    have h3 : b * b ^ n ≤ a * b ^ n :=
      Nat.mul_le_mul_right (b ^ n) hab
    have h4 : a * b ^ n ≤ a * a ^ n :=
      Nat.mul_le_mul_left a h0
    rw [← Nat.add_sub_assoc h1, Nat.sub_add_cancel h2]
    rw [← Nat.mul_assoc b a S, Nat.mul_comm b a, Nat.mul_assoc a b S]
    rw [← Nat.mul_sub, ← Nat.sub_mul, ← Nat.sub_mul, ← ih]
    simp only [Nat.sub_mul, Nat.mul_sub]
    omega

theorem Nat.fwd_pow (n k : Nat) :
    Δ (· ^ k) n = ∑ (fun i => (n + 1) ^ i * n ^ (k - 1 - i)) k := by
  change (n + 1) ^ k - n ^ k = _
  rw [Nat.pow_sub_pow (n + 1) n k (Nat.le_succ n)]
  simp

theorem Nat.fwd_sq (n : Nat) : Δ (· ^ 2) n = 2 * n + 1 := by
  rw [Nat.fwd_pow n 2]
  simp [sum_succ]
  lia

theorem Nat.fwd_cb (n : Nat) : Δ (· ^ 3) n = 3 * n^2 + 3 * n + 1 := by
  rw [Nat.fwd_pow n 3]
  simp [sum_succ]
  lia

/-- The difference between consecutive squares, `(n + 1)^2 - n^2`, is odd. -/
theorem Nat.not_two_dvd_fwd_sq (n : Nat) : ¬ 2 ∣ Δ (· ^ 2) n :=
  have h : ¬ 2 ∣ 2 * n + 1 := fun h0 =>
    have h1 : 2 ∣ 2 * n := Nat.dvd_mul_right 2 n
    have h2 : 2 ∣ 1 := Nat.dvd_add_iff_right h1 |>.mpr h0
    have h3 : ¬ 2 ∣ 1 := of_decide_eq_true rfl
    absurd h2 h3
  Nat.fwd_sq n ▸ h

end DiscreteCalc
