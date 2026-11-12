import ReMath.Alg.Defs

namespace Alg

section AddMonoid

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
theorem nsmul_zero {M} [AddMonoid M] (n : Nat) :
    n • (0 : M) = 0 := by
  induction n with
  | zero =>
    simp only [zero_nsmul]
  | succ n ih =>
    simp only [succ_nsmul, ih, add_zero]

@[simp]
theorem add_nsmul_assoc {M} [AddMonoid M] (n m : Nat) (a b : M) :
    n • a + (m • a + b) = (n + m) • a + b := by
  rw [← add_assoc, ← add_nsmul]

instance {M} [AddMonoid M] : @Std.Associative M (· + ·) := ⟨add_assoc⟩
instance {M} [AddMonoid M] : @Std.LawfulIdentity M (· + ·) 0 where
  left_id := zero_add
  right_id := add_zero
instance {M} [AddMonoid M] : @Std.LawfulLeftIdentity Nat M (· • ·) 1 where
  left_id _ := by rw [succ_nsmul, zero_nsmul, zero_add]

end AddMonoid

section AddCommMonoid

instance {M} [AddCommMonoid M] : @Std.Commutative M (· + ·) := ⟨add_comm⟩
instance {M} [AddCommMonoid M] : Lean.Grind.AddCommMonoid M where
  add_zero := add_zero
  add_comm := add_comm
  add_assoc := add_assoc

@[simp]
theorem nsmul_add {M} [AddCommMonoid M] (n : Nat) (a b : M) :
    n • (a + b) = n • a + n • b := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    simp only [succ_nsmul, ih]
    ac_rfl

end AddCommMonoid

section AddCommGroup

instance {M} [AddCommGroup M] : Lean.Grind.AddCommGroup M where
  neg_add_cancel := neg_add_cancel
  sub_eq_add_neg := sub_eq_add_neg

end AddCommGroup

section Semiring

@[simp]
theorem natCast_mul_eq_nsmul {M} [Semiring M] (n : Nat) (a : M) :
    (n : M) * a = n • a := by
  induction n with
  | zero =>
    simp only [zero_nsmul, natCast_zero, zero_mul]
  | succ n ih =>
    simp only [succ_nsmul, natCast_succ, ih, add_mul, one_mul]

/-- Multiplying on the right by a natural cast is the scalar action. -/
@[simp]
theorem mul_natCast_eq_nsmul {M} [Semiring M] (a : M) (n : Nat) :
    a * (n : M) = n • a := by
  induction n with
  | zero =>
    simp only [natCast_zero, mul_zero, zero_nsmul]
  | succ n ih =>
    simp only [natCast_succ, mul_add, mul_one, ih, succ_nsmul]

@[simp]
theorem nsmul_one_eq_natCast {M} [Semiring M] (n : Nat) :
    n • (1 : M) = (n : M) := by
  rw [← natCast_mul_eq_nsmul, mul_one]

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
theorem natCast_pow {M} [Semiring M] (m n : Nat) :
    (m : M) ^ n = ((m ^ n : Nat) : M) := by
  induction n with
  | zero =>
    simp [natCast_zero, natCast_succ]
  | succ n ih =>
    rw [pow_succ, ih, natCast_mul, Nat.pow_succ]

theorem ofNat_eq_natCast {M} [Semiring M] (n : Nat) :
    (OfNat.ofNat n : M) = NatCast.natCast n := by
  rcases n with rfl | rfl | n
  · simp
  · change 1 = NatCast.natCast 1
    simp [natCast_succ]
  · change NatCast.natCast (n + 2) = NatCast.natCast (n + 2)
    simp [natCast_succ]

instance {M} [Semiring M] : Lean.Grind.Semiring M where
  add_zero := add_zero
  zero_mul := zero_mul
  add_comm := add_comm
  add_assoc := add_assoc
  mul_assoc := mul_assoc
  mul_one := mul_one
  one_mul := one_mul
  left_distrib := mul_add
  right_distrib := add_mul
  mul_zero := mul_zero
  pow_zero := pow_zero
  pow_succ := pow_succ
  ofNat_succ a := by
    rw [ofNat_eq_natCast, ofNat_eq_natCast, natCast_succ]
  ofNat_eq_natCast := ofNat_eq_natCast
  nsmul_eq_natCast_mul n a :=
    (natCast_mul_eq_nsmul n a).symm

end Semiring

instance {M} [CommSemiring M] : Lean.Grind.CommSemiring M where
  mul_comm := mul_comm

section Ring

/-- A ring element plus its negation is zero. -/
theorem add_neg_cancel {M} [Ring M] (a : M) : a + -a = 0 := by
  rw [add_comm]
  exact neg_add_cancel a

@[simp]
theorem sub_self {M} [Ring M] (x : M) : x - x = 0 := by
  rw [Alg.sub_eq_add_neg, Alg.add_neg_cancel]

/-- Negation fixes zero. -/
@[simp]
theorem neg_zero {M} [Ring M] : -(0 : M) = 0 := by
  have h := neg_add_cancel (0 : M)
  rw [add_zero] at h
  exact h

@[simp]
theorem sub_zero {M} [Ring M] (x : M) : x - 0 = x := by
  rw [Alg.sub_eq_add_neg, neg_zero, add_zero]

/-- Consecutive differences telescope: `(a - b) + (c - a) = c - b`. -/
theorem sub_add_sub_cancel {M} [Ring M] (a b c : M) :
    (a - b) + (c - a) = c - b := by
  rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, add_comm a (-b),
    add_comm c (-a), add_assoc, ← add_assoc a (-a) c, add_neg_cancel,
    zero_add, add_comm]

/-- Adding then subtracting the same element cancels it. -/
theorem add_sub_cancel_left {M} [Ring M] (a b : M) : a + b - a = b := by
  rw [sub_eq_add_neg, add_comm a b, add_assoc, add_neg_cancel, add_zero]

/-- An additive inverse is unique: if `a + b = 0` then `b = -a`. -/
theorem neg_eq_of_add_eq_zero {M} [Ring M] {a b : M} (h : a + b = 0) :
    b = -a := by
  calc
    b = 0 + b := (zero_add b).symm
    _ = -a + a + b := by rw [neg_add_cancel]
    _ = -a + (a + b) := add_assoc _ _ _
    _ = -a := by rw [h, add_zero]

theorem mul_neg {M} [Ring M] (a b : M) : a * -b = -(a * b) :=
  neg_eq_of_add_eq_zero (by rw [← mul_add, add_neg_cancel, mul_zero])

theorem neg_mul {M} [Ring M] (a b : M) : -a * b = -(a * b) :=
  neg_eq_of_add_eq_zero (by rw [← add_mul, add_neg_cancel, zero_mul])

/-- Multiplication distributes over subtraction on the left. -/
theorem mul_sub {M} [Ring M] (a b c : M) : a * (b - c) = a * b - a * c := by
  rw [sub_eq_add_neg, sub_eq_add_neg, mul_add, mul_neg]

/-- Multiplication distributes over subtraction on the right. -/
theorem sub_mul {M} [Ring M] (a b c : M) : (a - b) * c = a * c - b * c := by
  rw [sub_eq_add_neg, sub_eq_add_neg, add_mul, neg_mul]

/-- Negation reverses addition (in a ring the order does not matter). -/
theorem neg_add {M} [Ring M] (a b : M) : -(a + b) = -a + -b := by
  have h : a + b + (-a + -b) = 0 := by
    rw [add_assoc, ← add_assoc b, add_comm b (-a), add_assoc, add_neg_cancel,
      add_zero, add_neg_cancel]
  exact (neg_eq_of_add_eq_zero h).symm

/-- Negation reverses addition (in a ring the order does not matter). -/
theorem sub_add {M} [Ring M] (a b c : M) : a - (b + c) = a - b - c := by
  simp [sub_eq_add_neg, neg_add, add_assoc]

/-- Negation reverses addition (in a ring the order does not matter). -/
theorem add_sub_assoc {M} [Ring M] (a b c : M) : a + (b - c) = a + b - c := by
  simp [sub_eq_add_neg, add_assoc]

theorem natCast_zsmul {M} [AddGroup M] (n : Nat) (a : M) :
    (n : Int) • a = n • a := by
  induction n with
  | zero =>
    simp [zero_zsmul, zero_nsmul]
  | succ n ih =>
    rw [Int.natCast_succ, succ_zsmul, ih, succ_nsmul]

instance {M} [Ring M] : Lean.Grind.Ring M where
  neg_add_cancel := neg_add_cancel
  sub_eq_add_neg := sub_eq_add_neg
  neg_zsmul := neg_zsmul
  zsmul_natCast_eq_nsmul := natCast_zsmul
  intCast_ofNat n := by
    rw [ofNat_eq_natCast]
    exact intCast_ofNat n
  intCast_neg := intCast_neg

end Ring

instance {M} [CommRing M] : Lean.Grind.CommRing M where
  mul_comm := mul_comm

instance {M} [Field M] : Lean.Grind.Field M where
  div_eq_mul_inv := div_eq_mul_inv
  zero_ne_one := zero_ne_one
  inv_zero := inv_zero
  mul_inv_cancel := mul_inv_cancel _
  zpow_zero := zpow_zero
  zpow_succ := zpow_succ
  zpow_neg := zpow_neg

end Alg
