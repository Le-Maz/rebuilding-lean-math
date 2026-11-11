import ReMath.Alg.Defs

namespace Alg

@[simp]
theorem natCast_mul_eq_nsmul {M} [Semiring M] (n : Nat) (a : M) :
    (n : M) * a = n • a := by
  induction n with
  | zero =>
    simp only [zero_nsmul, natCast_zero, zero_mul]
  | succ n ih =>
    simp only [succ_nsmul, natCast_succ, ih, right_distrib, one_mul]

/-- Multiplying on the right by a natural cast is the scalar action. -/
@[simp]
theorem mul_natCast_eq_nsmul {M} [Semiring M] (a : M) (n : Nat) :
    a * (n : M) = n • a := by
  induction n with
  | zero =>
    simp only [natCast_zero, mul_zero, zero_nsmul]
  | succ n ih =>
    simp only [natCast_succ, left_distrib, mul_one, ih, succ_nsmul]

@[simp]
theorem nsmul_one_eq_natCast {M} [Semiring M] (n : Nat) :
    n • (1 : M) = (n : M) := by
  rw [← natCast_mul_eq_nsmul, mul_one]

@[simp ←]
theorem add_nsmul {M} [AddMonoid M] (n m : Nat) (a : M) :
    (n + m) • a = n • a + m • a := by
  induction m with
  | zero =>
    simp [add_zero, zero_nsmul]
  | succ m ih =>
    rw [Nat.add_succ, succ_nsmul, ih, succ_nsmul, add_assoc]

@[simp]
theorem smul_smul {M} [AddMonoid M] (n m : Nat) (a : M) :
    n • (m • a) = (n * m) • a := by
  induction n with
  | zero =>
    simp only [zero_nsmul, Nat.zero_mul]
  | succ n ih =>
    simp only [succ_nsmul, Nat.succ_mul, ih, ← add_nsmul]

@[simp]
theorem natCast_mul {M} [Semiring M] (n m : Nat) :
    ((n : M) * (m : M)) = ((n * m : Nat) : M) := by
  rw [natCast_mul_eq_nsmul, ← nsmul_one_eq_natCast m, smul_smul,
    nsmul_one_eq_natCast]

@[simp]
theorem nsmul_natCast {M} [Semiring M] (n m : Nat) :
    n • (m : M) = ((n * m : Nat) : M) := by
  rw [← natCast_mul_eq_nsmul, natCast_mul]

/-- A scalar on the left factor moves outside the product. -/
@[simp]
theorem nsmul_mul {M} [Semiring M] (n : Nat) (a b : M) :
    (n • a) * b = n • (a * b) := by
  rw [← natCast_mul_eq_nsmul, mul_assoc, natCast_mul_eq_nsmul]

/-- A scalar on the right factor moves outside the product. -/
@[simp]
theorem mul_nsmul {M} [Semiring M] (a : M) (n : Nat) (b : M) :
    a * (n • b) = n • (a * b) := by
  rw [← mul_natCast_eq_nsmul, ← mul_assoc, mul_natCast_eq_nsmul]

@[simp]
theorem nsmul_zero {M} [AddMonoid M] (n : Nat) :
    n • (0 : M) = 0 := by
  induction n with
  | zero =>
    simp only [zero_nsmul]
  | succ n ih =>
    simp only [succ_nsmul, ih, add_zero]

/-- A natural scalar distributes over addition. -/
@[simp]
theorem nsmul_add {M} [Semiring M] (n : Nat) (a b : M) :
    n • (a + b) = n • a + n • b := by
  rw [← natCast_mul_eq_nsmul, left_distrib, natCast_mul_eq_nsmul,
    natCast_mul_eq_nsmul]

@[simp]
theorem add_nsmul_assoc {M} [AddMonoid M] (n m : Nat) (a b : M) :
    n • a + (m • a + b) = (n + m) • a + b := by
  rw [← add_assoc, ← add_nsmul]

@[simp]
theorem natCast_pow {M} [Semiring M] (m n : Nat) :
    (m : M) ^ n = ((m ^ n : Nat) : M) := by
  induction n with
  | zero =>
    simp [natCast_zero, natCast_succ]
  | succ n ih =>
    rw [npow_succ, ih, natCast_mul, Nat.pow_succ]

end Alg
