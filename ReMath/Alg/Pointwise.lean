import ReMath.Alg.Defs

namespace Alg

/-- Functions `ι → α` carrying pointwise algebraic structure. -/
def Pointwise (ι α : Type _) := ι → α

namespace Pointwise

variable {ι α : Type _}

/-- Wraps a function as a pointwise vector. -/
def mk (f : ι → α) : Pointwise ι α := f

/-- Two pointwise vectors are equal when all their entries are. -/
@[ext] theorem ext {f g : Pointwise ι α} (h : ∀ i, f i = g i) : f = g :=
  funext h

/-- Pointwise zero. -/
instance [Zero α] : Zero (Pointwise ι α) := ⟨fun _ => 0⟩

/-- Pointwise one. -/
instance [One α] : One (Pointwise ι α) := ⟨fun _ => 1⟩

/-- Pointwise addition. -/
instance [Add α] : Add (Pointwise ι α) := ⟨fun f g i => f i + g i⟩

/-- Pointwise multiplication. -/
instance [Mul α] : Mul (Pointwise ι α) := ⟨fun f g i => f i * g i⟩

/-- Pointwise negation. -/
instance [Neg α] : Neg (Pointwise ι α) := ⟨fun f i => -f i⟩

/-- Pointwise subtraction. -/
instance [Sub α] : Sub (Pointwise ι α) := ⟨fun f g i => f i - g i⟩

/-- Pointwise inverse. Total, so it needs no laws on `α`. -/
instance [Inv α] : Inv (Pointwise ι α) := ⟨fun f i => (f i)⁻¹⟩

/-- Pointwise division. -/
instance [Div α] : Div (Pointwise ι α) := ⟨fun f g i => f i / g i⟩

/-- Pointwise natural-number cast. -/
instance [NatCast α] : NatCast (Pointwise ι α) := ⟨fun n _ => (n : α)⟩

/-- Pointwise integer cast. -/
instance [IntCast α] : IntCast (Pointwise ι α) := ⟨fun z _ => (z : α)⟩

/-- Pointwise natural power. -/
instance [Pow α Nat] : Pow (Pointwise ι α) Nat := ⟨fun f n i => f i ^ n⟩

/-- Pointwise integer power. -/
instance [HPow α Int α] : HPow (Pointwise ι α) Int (Pointwise ι α) :=
  ⟨fun f z i => HPow.hPow (f i) z⟩

/-- Pointwise natural-number scalar action. -/
instance [NSMul α] : NSMul (Pointwise ι α) := ⟨⟨fun n f i => n • f i⟩⟩

/-- Pointwise integer scalar action. -/
instance [ZSMul α] : ZSMul (Pointwise ι α) := ⟨⟨fun z f i => z • f i⟩⟩

@[simp] theorem zero_apply [Zero α] (i : ι) : (0 : Pointwise ι α) i = 0 := rfl

@[simp] theorem one_apply [One α] (i : ι) : (1 : Pointwise ι α) i = 1 := rfl

@[simp] theorem add_apply [Add α] (f g : Pointwise ι α) (i : ι) :
    (f + g) i = f i + g i := rfl

@[simp] theorem mul_apply [Mul α] (f g : Pointwise ι α) (i : ι) :
    (f * g) i = f i * g i := rfl

@[simp] theorem neg_apply [Neg α] (f : Pointwise ι α) (i : ι) :
    (-f) i = -f i := rfl

@[simp] theorem sub_apply [Sub α] (f g : Pointwise ι α) (i : ι) :
    (f - g) i = f i - g i := rfl

instance [AddMonoid α] : AddMonoid (Pointwise ι α) where
  add_zero f := ext fun i => add_zero (f i)
  zero_add f := ext fun i => zero_add (f i)
  add_assoc f g h := ext fun i => add_assoc (f i) (g i) (h i)
  zero_nsmul f := ext fun i => zero_nsmul (f i)
  succ_nsmul n f := ext fun i => succ_nsmul n (f i)

instance [AddCommMonoid α] : AddCommMonoid (Pointwise ι α) where
  add_comm f g := ext fun i => add_comm (f i) (g i)

instance [AddGroup α] : AddGroup (Pointwise ι α) where
  neg_add_cancel f := ext fun i => neg_add_cancel (f i)
  sub_eq_add_neg f g := ext fun i => sub_eq_add_neg (f i) (g i)
  zero_zsmul f := ext fun i => zero_zsmul (f i)
  succ_zsmul z f := ext fun i => succ_zsmul z (f i)
  neg_zsmul z f := ext fun i => neg_zsmul z (f i)

instance [AddCommGroup α] : AddCommGroup (Pointwise ι α) where
  add_comm f g := ext fun i => add_comm (f i) (g i)

instance [MulMonoid α] : MulMonoid (Pointwise ι α) where
  mul_one f := ext fun i => mul_one (f i)
  one_mul f := ext fun i => one_mul (f i)
  mul_assoc f g h := ext fun i => mul_assoc (f i) (g i) (h i)
  pow_zero f := ext fun i => pow_zero (f i)
  pow_succ f n := ext fun i => pow_succ (f i) n

instance [MulCommMonoid α] : MulCommMonoid (Pointwise ι α) where
  mul_comm f g := ext fun i => mul_comm (f i) (g i)

instance [Semiring α] : Semiring (Pointwise ι α) where
  zero_mul f := ext fun i => zero_mul (f i)
  mul_zero f := ext fun i => mul_zero (f i)
  mul_add f g h := ext fun i => mul_add (f i) (g i) (h i)
  add_mul f g h := ext fun i => add_mul (f i) (g i) (h i)
  natCast_zero := ext fun _ => natCast_zero
  natCast_succ n := ext fun _ => natCast_succ n

instance [CommSemiring α] : CommSemiring (Pointwise ι α) where
  mul_comm f g := ext fun i => mul_comm (f i) (g i)

instance [Ring α] : Ring (Pointwise ι α) where
  intCast_ofNat n := ext fun _ => intCast_ofNat n
  intCast_neg z := ext fun _ => intCast_neg z

instance [CommRing α] : CommRing (Pointwise ι α) where

end Pointwise

end Alg
