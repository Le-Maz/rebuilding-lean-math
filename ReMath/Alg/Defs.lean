namespace Alg

/-- Additive monoid with a canonical `SMul Nat` action. -/
class AddMonoid (M : Type _) extends Zero M, Add M, SMul Nat M where
  add_zero (a : M) : a + 0 = a
  zero_add (a : M) : 0 + a = a
  add_assoc (a b c : M) : (a + b) + c = a + (b + c)
  zero_nsmul (a : M) : 0 • a = 0
  succ_nsmul (n : Nat) (a : M) : (n + 1) • a = n • a + a

class AddCommMonoid (M : Type _) extends AddMonoid M where
  add_comm (a b : M) : a + b = b + a

export AddMonoid (add_zero zero_add add_assoc zero_nsmul succ_nsmul)
export AddCommMonoid (add_comm)

attribute [simp] add_zero zero_add add_assoc zero_nsmul succ_nsmul add_comm

/-- Multiplicative monoid with a canonical `Pow M Nat` action. -/
class MulMonoid (M : Type _) extends One M, Mul M, Pow M Nat where
  mul_one (a : M) : a * 1 = a
  one_mul (a : M) : 1 * a = a
  mul_assoc (a b c : M) : (a * b) * c = a * (b * c)
  npow_zero (a : M) : a ^ 0 = 1
  npow_succ (n : Nat) (a : M) : a ^ (n + 1) = a ^ n * a

class MulCommMonoid (M : Type _) extends MulMonoid M where
  mul_comm (a b : M) : a * b = b * a

export MulMonoid (mul_one one_mul mul_assoc npow_zero npow_succ)
export MulCommMonoid (mul_comm)

attribute [simp] mul_one one_mul mul_assoc npow_zero npow_succ mul_comm

/-- A semiring with a canonical `NatCast` action. -/
class Semiring (M : Type _) extends AddCommMonoid M, MulMonoid M, NatCast M where
  zero_mul (a : M) : 0 * a = 0
  mul_zero (a : M) : a * 0 = 0
  left_distrib (a b c : M) : a * (b + c) = a * b + a * c
  right_distrib (a b c : M) : (b + c) * a = b * a + c * a
  natCast_zero : natCast 0 = 0
  natCast_succ (n : Nat) : natCast (n + 1) = natCast n + 1

export Semiring (zero_mul mul_zero left_distrib right_distrib
  natCast_zero natCast_succ)

attribute [simp] zero_mul mul_zero natCast_zero

@[simp]
theorem ofNat_zero {M} [AddMonoid M] : (Zero.zero : M) = (0 : M) := rfl

@[simp]
theorem ofNat_one {M} [MulMonoid M] : (One.one : M) = (1 : M) := rfl

end Alg
