import ReMath.Alg.Defs

namespace Alg

namespace Vector

/-- Null vector. -/
instance {α} [Zero α] {n : Nat} :
    Zero (Vector α n) where
  zero := Vector.ofFn fun _ => 0

/-- Pointwise addition of vectors. -/
instance {α} [Add α] {n : Nat} :
    Add (Vector α n) where
  add a b := Vector.ofFn fun i => a[i] + b[i]

/-- Pointwise natural number scalar multiplication of vectors. -/
instance {α} [NSMul α] {n : Nat} :
    NSMul (Vector α n) where
  nsmul := ⟨fun k a => Vector.ofFn fun i => k • a[i]⟩

/-- Pointwise negation of vectors. -/
instance {α} [Neg α] {n : Nat} :
    Neg (Vector α n) where
  neg a := Vector.ofFn fun i => -a[i]

/-- Pointwise subtraction of vectors. -/
instance {α} [Sub α] {n : Nat} :
    Sub (Vector α n) where
  sub a b := Vector.ofFn fun i => a[i] - b[i]

/-- Pointwise integer scalar multiplication of vectors. -/
instance {α} [ZSMul α] {n : Nat} :
    ZSMul (Vector α n) where
  zsmul := ⟨fun k a => Vector.ofFn fun i => k • a[i]⟩

/-- Constant one vector. -/
instance {α} [One α] {n : Nat} :
    One (Vector α n) where
  one := Vector.ofFn fun _ => 1

/-- Pointwise multiplication of vectors. -/
instance {α} [Mul α] {n : Nat} :
    Mul (Vector α n) where
  mul a b := Vector.ofFn fun i => a[i] * b[i]

/-- Pointwise inverse of vectors. -/
instance {α} [Inv α] {n : Nat} :
    Inv (Vector α n) where
  inv a := Vector.ofFn fun i => (a[i])⁻¹

/-- Pointwise division of vectors. -/
instance {α} [Div α] {n : Nat} :
    Div (Vector α n) where
  div a b := Vector.ofFn fun i => a[i] / b[i]

/-- Constant vector of a natural number cast. -/
instance {α} [NatCast α] {n : Nat} :
    NatCast (Vector α n) where
  natCast k := Vector.ofFn fun _ => (k : α)

/-- Constant vector of an integer cast. -/
instance {α} [IntCast α] {n : Nat} :
    IntCast (Vector α n) where
  intCast k := Vector.ofFn fun _ => (k : α)

/-- Pointwise natural power of vectors. -/
instance {α} [Pow α Nat] {n : Nat} :
    Pow (Vector α n) Nat where
  pow a k := Vector.ofFn fun i => a[i] ^ k

/-- Pointwise integer power of vectors. -/
instance {α} [HPow α Int α] {n : Nat} :
    HPow (Vector α n) Int (Vector α n) where
  hPow a k := Vector.ofFn fun i => HPow.hPow a[i] k

@[simp]
theorem getElem_zero {α} [Zero α] {n : Nat}
    (i : Fin n) :
    (0 : Vector α n)[i.val] = 0 := by
  change (Vector.ofFn _)[i.val] = _
  exact Vector.getElem_ofFn i.isLt

@[simp]
theorem getElem_add {α} [Add α] {n : Nat}
    (a b : Vector α n) (i : Fin n) :
    (a + b)[i.val] = a[i.val] + b[i.val] := by
  change (Vector.ofFn _)[i.val] = _
  exact Vector.getElem_ofFn i.isLt

@[simp]
theorem getElem_nsmul {α} [NSMul α] {n : Nat}
    (k : Nat) (a : Vector α n) (i : Fin n) :
    (k • a)[i.val] = k • a[i.val] := by
  change (Vector.ofFn _)[i.val] = _
  exact Vector.getElem_ofFn i.isLt

@[simp]
theorem getElem_neg {α} [Neg α] {n : Nat}
    (a : Vector α n) (i : Fin n) :
    (-a)[i.val] = -a[i.val] := by
  change (Vector.ofFn _)[i.val] = _
  exact Vector.getElem_ofFn i.isLt

@[simp]
theorem getElem_sub {α} [Sub α] {n : Nat}
    (a b : Vector α n) (i : Fin n) :
    (a - b)[i.val] = a[i.val] - b[i.val] := by
  change (Vector.ofFn _)[i.val] = _
  exact Vector.getElem_ofFn i.isLt

@[simp]
theorem getElem_zsmul {α} [ZSMul α] {n : Nat}
    (k : Int) (a : Vector α n) (i : Fin n) :
    (k • a)[i.val] = k • a[i.val] := by
  change (Vector.ofFn _)[i.val] = _
  exact Vector.getElem_ofFn i.isLt

@[simp]
theorem getElem_one {α} [One α] {n : Nat}
    (i : Fin n) :
    (1 : Vector α n)[i.val] = 1 := by
  change (Vector.ofFn _)[i.val] = _
  exact Vector.getElem_ofFn i.isLt

@[simp]
theorem getElem_mul {α} [Mul α] {n : Nat}
    (a b : Vector α n) (i : Fin n) :
    (a * b)[i.val] = a[i.val] * b[i.val] := by
  change (Vector.ofFn _)[i.val] = _
  exact Vector.getElem_ofFn i.isLt

@[simp]
theorem getElem_inv {α} [Inv α] {n : Nat}
    (a : Vector α n) (i : Fin n) :
    (a⁻¹)[i.val] = (a[i.val])⁻¹ := by
  change (Vector.ofFn _)[i.val] = _
  exact Vector.getElem_ofFn i.isLt

@[simp]
theorem getElem_div {α} [Div α] {n : Nat}
    (a b : Vector α n) (i : Fin n) :
    (a / b)[i.val] = a[i.val] / b[i.val] := by
  change (Vector.ofFn _)[i.val] = _
  exact Vector.getElem_ofFn i.isLt

@[simp]
theorem getElem_natCast {α} [NatCast α] {n : Nat}
    (k : Nat) (i : Fin n) :
    (Nat.cast k : Vector α n)[i.val] = Nat.cast k := by
  change (Vector.ofFn _)[i.val] = _
  exact Vector.getElem_ofFn i.isLt

@[simp]
theorem getElem_intCast {α} [IntCast α] {n : Nat}
    (k : Int) (i : Fin n) :
    (Int.cast k : Vector α n)[i.val] = Int.cast k := by
  change (Vector.ofFn _)[i.val] = _
  exact Vector.getElem_ofFn i.isLt

@[simp]
theorem getElem_pow {α} [Pow α Nat] {n : Nat}
    (a : Vector α n) (k : Nat) (i : Fin n) :
    (a ^ k)[i.val] = a[i.val] ^ k := by
  change (Vector.ofFn _)[i.val] = _
  exact Vector.getElem_ofFn i.isLt

@[simp]
theorem getElem_zpow {α} [HPow α Int α] {n : Nat}
    (a : Vector α n) (k : Int) (i : Fin n) :
    (HPow.hPow a k : Vector α n)[i.val] = HPow.hPow a[i.val] k := by
  change (Vector.ofFn _)[i.val] = _
  exact Vector.getElem_ofFn i.isLt

/-- Two vectors are equal if all their entries are equal. -/
theorem ext_fin {α} {n : Nat} {a b : Vector α n}
    (h : ∀ i : Fin n, a[i] = b[i]) : a = b :=
  Vector.ext fun i hi => h ⟨i, hi⟩

instance {α} [AddMonoid α] {n : Nat} :
    AddMonoid (Vector α n) where
  add_zero a := ext_fin fun i => by
    simp only [Fin.getElem_fin, getElem_add, getElem_zero]
    exact add_zero _
  zero_add a := ext_fin fun i => by
    simp only [Fin.getElem_fin, getElem_add, getElem_zero]
    exact zero_add _
  add_assoc a b c := ext_fin fun i => by
    simp only [Fin.getElem_fin, getElem_add]
    exact add_assoc _ _ _
  zero_nsmul a := ext_fin fun i => by
    simp only [Fin.getElem_fin, getElem_nsmul, getElem_zero]
    exact zero_nsmul _
  succ_nsmul k a := ext_fin fun i => by
    simp only [Fin.getElem_fin, getElem_nsmul, getElem_add]
    exact succ_nsmul _ _

instance {α} [AddCommMonoid α] {n : Nat} :
    AddCommMonoid (Vector α n) where
  add_comm a b := ext_fin fun i => by
    simp only [Fin.getElem_fin, getElem_add]
    exact add_comm _ _

instance {α} [AddGroup α] {n : Nat} :
    AddGroup (Vector α n) where
  neg_add_cancel a := ext_fin fun i => by
    simp only [Fin.getElem_fin, getElem_add, getElem_neg, getElem_zero]
    exact neg_add_cancel _
  sub_eq_add_neg a b := ext_fin fun i => by
    simp only [Fin.getElem_fin, getElem_add, getElem_neg, getElem_sub]
    exact sub_eq_add_neg _ _
  zero_zsmul a := ext_fin fun i => by
    simp only [Fin.getElem_fin, getElem_zsmul, getElem_zero]
    exact zero_zsmul _
  succ_zsmul k a := ext_fin fun i => by
    simp only [Fin.getElem_fin, getElem_zsmul, getElem_add]
    exact succ_zsmul _ _
  neg_zsmul k a := ext_fin fun i => by
    simp only [Fin.getElem_fin, getElem_zsmul, getElem_neg]
    exact neg_zsmul _ _

instance {α} [AddCommGroup α] {n : Nat} :
    AddCommGroup (Vector α n) where
  add_comm a b := ext_fin fun i => by
    simp only [Fin.getElem_fin, getElem_add]
    exact add_comm _ _

instance {α} [MulMonoid α] {n : Nat} :
    MulMonoid (Vector α n) where
  mul_one a := ext_fin fun i => by
    simp only [Fin.getElem_fin, getElem_mul, getElem_one]
    exact mul_one _
  one_mul a := ext_fin fun i => by
    simp only [Fin.getElem_fin, getElem_mul, getElem_one]
    exact one_mul _
  mul_assoc a b c := ext_fin fun i => by
    simp only [Fin.getElem_fin, getElem_mul]
    exact mul_assoc _ _ _
  pow_zero a := ext_fin fun i => by
    simp only [Fin.getElem_fin, getElem_pow, getElem_one]
    exact pow_zero _
  pow_succ a k := ext_fin fun i => by
    simp only [Fin.getElem_fin, getElem_pow, getElem_mul]
    exact pow_succ _ _

instance {α} [MulCommMonoid α] {n : Nat} :
    MulCommMonoid (Vector α n) where
  mul_comm a b := ext_fin fun i => by
    simp only [Fin.getElem_fin, getElem_mul]
    exact mul_comm _ _

instance {α} [Semiring α] {n : Nat} :
    Semiring (Vector α n) where
  zero_mul a := ext_fin fun i => by
    simp only [Fin.getElem_fin, getElem_mul, getElem_zero]
    exact zero_mul _
  mul_zero a := ext_fin fun i => by
    simp only [Fin.getElem_fin, getElem_mul, getElem_zero]
    exact mul_zero _
  mul_add a b c := ext_fin fun i => by
    simp only [Fin.getElem_fin, getElem_mul, getElem_add]
    exact mul_add _ _ _
  add_mul a b c := ext_fin fun i => by
    simp only [Fin.getElem_fin, getElem_mul, getElem_add]
    exact add_mul _ _ _
  natCast_zero := ext_fin fun i => by
    simp only [Fin.getElem_fin, getElem_natCast, getElem_zero]
    exact natCast_zero
  natCast_succ k := ext_fin fun i => by
    simp only [Fin.getElem_fin, getElem_natCast, getElem_add, getElem_one]
    exact natCast_succ k

instance {α} [CommSemiring α] {n : Nat} :
    CommSemiring (Vector α n) where
  mul_comm a b := ext_fin fun i => by
    simp only [Fin.getElem_fin, getElem_mul]
    exact mul_comm _ _

instance {α} [Ring α] {n : Nat} :
    Ring (Vector α n) where
  intCast_ofNat k := ext_fin fun i => by
    simp only [Fin.getElem_fin, getElem_intCast, getElem_natCast]
    exact intCast_ofNat k
  intCast_neg z := ext_fin fun i => by
    simp only [Fin.getElem_fin, getElem_intCast, getElem_neg]
    exact intCast_neg z

instance {α} [CommRing α] {n : Nat} :
    CommRing (Vector α n) where

instance {α} [InvRing α] {n : Nat} :
    InvRing (Vector α n) where
  inv_zero := ext_fin fun i => by
    simp only [Fin.getElem_fin, getElem_inv]
    exact ((congrArg Inv.inv (getElem_zero (α := α) (n := n) i)).trans
      inv_zero).trans (getElem_zero (α := α) (n := n) i).symm
  div_eq_mul_inv a b := ext_fin fun i => by
    simp only [Fin.getElem_fin, getElem_div, getElem_mul, getElem_inv]
    exact div_eq_mul_inv _ _
  zpow_zero a := ext_fin fun i => by
    simp only [Fin.getElem_fin, getElem_zpow]
    exact (zpow_zero _).trans (getElem_one (α := α) (n := n) i).symm
  zpow_succ a k := ext_fin fun i => by
    simp only [Fin.getElem_fin, getElem_zpow, getElem_mul]
    exact zpow_succ _ _
  zpow_neg a z := ext_fin fun i => by
    simp only [Fin.getElem_fin, getElem_zpow, getElem_inv]
    exact zpow_neg _ _

end Vector

end Alg
