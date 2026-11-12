namespace Alg

class NSMul (M : Type _) where
  nsmul : SMul Nat M

instance {M} [this : NSMul M] : SMul Nat M := this.nsmul

class ZSMul (M : Type _) where
  zsmul : SMul Int M

instance {M} [this : ZSMul M] : SMul Int M := this.zsmul

/-- Additive monoid with a canonical `SMul Nat` action. -/
class AddMonoid (M : Type _) extends Zero M, Add M, NSMul M where
  add_zero (a : M) : a + 0 = a
  zero_add (a : M) : 0 + a = a
  add_assoc (a b c : M) : (a + b) + c = a + (b + c)
  zero_nsmul (a : M) : 0 • a = 0
  succ_nsmul (n : Nat) (a : M) : (n + 1) • a = n • a + a

class AddCommMonoid (M : Type _) extends AddMonoid M where
  add_comm (a b : M) : a + b = b + a

export AddMonoid (add_zero zero_add add_assoc zero_nsmul succ_nsmul)
export AddCommMonoid (add_comm)

attribute [simp] add_zero zero_add zero_nsmul succ_nsmul

class AddGroup (M : Type _) extends AddMonoid M, Neg M, Sub M, ZSMul M where
  neg_add_cancel (a : M) : -a + a = 0
  sub_eq_add_neg (a b : M) : a - b = a + -b

  zero_zsmul (a : M) : (0 : Int) • a = 0
  succ_zsmul (z : Int) (a : M) :
    (z + 1) • a = z • a + a
  neg_zsmul (z : Int) (a : M) :
    (-z) • a = -(z • a)

export AddGroup (neg_add_cancel sub_eq_add_neg zero_zsmul succ_zsmul neg_zsmul)

class AddCommGroup (M : Type _) extends AddGroup M, AddCommMonoid M

/-- Multiplicative monoid with a canonical `Pow M Nat` action. -/
class MulMonoid (M : Type _) extends One M, Mul M, Pow M Nat where
  mul_one (a : M) : a * 1 = a
  one_mul (a : M) : 1 * a = a
  mul_assoc (a b c : M) : (a * b) * c = a * (b * c)
  pow_zero (a : M) : a ^ 0 = 1
  pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a

class MulCommMonoid (M : Type _) extends MulMonoid M where
  mul_comm (a b : M) : a * b = b * a

export MulMonoid (mul_one one_mul mul_assoc pow_zero pow_succ)
export MulCommMonoid (mul_comm)

attribute [simp] mul_one one_mul mul_assoc pow_zero pow_succ

/-- A semiring with a canonical `NatCast` action. -/
class Semiring (M : Type _) extends AddCommMonoid M, MulMonoid M, NatCast M where
  zero_mul (a : M) : 0 * a = 0
  mul_zero (a : M) : a * 0 = 0
  mul_add (a b c : M) : a * (b + c) = a * b + a * c
  add_mul (a b c : M) : (a + b) * c = a * c + b * c
  natCast_zero : natCast 0 = 0
  natCast_succ (n : Nat) : natCast (n + 1) = natCast n + 1

class CommSemiring (M : Type _) extends Semiring M, MulCommMonoid M

export Semiring (zero_mul mul_zero mul_add add_mul natCast_zero natCast_succ)

attribute [simp] zero_mul mul_zero natCast_zero

@[simp]
theorem ofNat_zero {M} [AddMonoid M] : (Zero.zero : M) = (0 : M) := rfl

@[simp]
theorem ofNat_one {M} [MulMonoid M] : (One.one : M) = (1 : M) := rfl

instance {M} [inst : Semiring M] : (n : Nat) → OfNat M n
  | 0 => ⟨Zero.zero⟩
  | 1 => ⟨One.one⟩
  | n => ⟨NatCast.natCast n⟩

class Ring (M : Type _) extends Semiring M, AddCommGroup M, IntCast M where
  intCast_ofNat (n : Nat) : intCast n = natCast n
  intCast_neg (z : Int) : intCast (-z) = -intCast z

export Ring (intCast_ofNat intCast_neg)

class CommRing (M : Type _) extends Ring M, CommSemiring M

/-- Total inverse, division and integer powers on a commutative ring. -/
class InvRing (M : Type _) extends CommRing M, Inv M, Div M, HPow M Int M where
  inv_zero : (0 : M)⁻¹ = 0
  div_eq_mul_inv (a b : M) : a / b = a * b⁻¹
  zpow_zero : ∀ a : M, a ^ (0 : Int) = 1
  zpow_succ : ∀ (a : M) (n : Nat), a ^ (n + 1 : Int) = a ^ (n : Int) * a
  zpow_neg : ∀ (a : M) (n : Int), a ^ (-n) = (a ^ n)⁻¹

export InvRing (inv_zero div_eq_mul_inv zpow_zero zpow_succ zpow_neg)

class Field (M : Type _) extends InvRing M where
  zero_ne_one : (0 : M) ≠ 1
  mul_inv_cancel (a : M) (ha : a ≠ 0) : a * a⁻¹ = 1

export Field (zero_ne_one mul_inv_cancel)

attribute [simp] inv_zero

/--
A module over a semiring `R`: an additive commutative monoid `M` with a
scalar action of `R` compatible with the ring and monoid structures.
-/
class Module (R M : Type _) [Semiring R] [AddCommMonoid M] extends SMul R M where
  one_smul (a : M) : (1 : R) • a = a
  mul_smul (r s : R) (a : M) : (r * s) • a = r • s • a
  smul_zero (r : R) : r • (0 : M) = 0
  smul_add (r : R) (a b : M) : r • (a + b) = r • a + r • b
  add_smul (r s : R) (a : M) : (r + s) • a = r • a + s • a
  zero_smul (a : M) : (0 : R) • a = 0

export Module (one_smul mul_smul smul_zero smul_add add_smul zero_smul)

attribute [simp] one_smul smul_zero zero_smul

/-- A vector space is a module over a field with an additive group of vectors. -/
class VectorSpace (K V : Type _) [Field K] [AddCommGroup V] extends Module K V

end Alg
