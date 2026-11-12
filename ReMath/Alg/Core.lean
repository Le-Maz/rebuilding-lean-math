import ReMath.Alg.Defs

instance : Alg.Semiring Nat where
  add_zero := Nat.add_zero
  zero_add := Nat.zero_add
  add_assoc := Nat.add_assoc
  nsmul := inferInstance
  zero_nsmul := Nat.zero_mul
  succ_nsmul := Nat.succ_mul
  add_comm := Nat.add_comm
  mul_one := Nat.mul_one
  one_mul := Nat.one_mul
  mul_assoc := Nat.mul_assoc
  pow_zero := Nat.pow_zero
  pow_succ := Nat.pow_succ
  zero_mul := Nat.zero_mul
  mul_zero := Nat.mul_zero
  mul_add := Nat.mul_add
  add_mul := Nat.add_mul
  natCast_zero := rfl
  natCast_succ _ := rfl

instance : Alg.Ring Int where
  add_zero := Int.add_zero
  zero_add := Int.zero_add
  add_assoc := Int.add_assoc
  nsmul := inferInstance
  zero_nsmul := Int.zero_mul
  succ_nsmul n a := by
    change (n + 1) * a = n * a + a
    rw [Int.add_mul, Int.one_mul]
  add_comm := Int.add_comm
  mul_one := Int.mul_one
  one_mul := Int.one_mul
  mul_assoc := Int.mul_assoc
  pow_zero := Int.pow_zero
  pow_succ := Int.pow_succ
  zero_mul := Int.zero_mul
  mul_zero := Int.mul_zero
  mul_add := Int.mul_add
  add_mul := Int.add_mul
  natCast_zero := rfl
  natCast_succ _ := rfl
  neg_add_cancel := Int.add_left_neg
  sub_eq_add_neg _ _ := Int.sub_eq_add_neg
  zsmul := inferInstance
  zero_zsmul := Int.zero_mul
  succ_zsmul z a := by
    change (z + 1) * a = z * a + a
    rw [Int.add_mul, Int.one_mul]
  neg_zsmul := Int.neg_mul
  intCast_ofNat _ := rfl
  intCast_neg _ := rfl

instance : Alg.Field Rat where
  add_zero := Rat.add_zero
  zero_add := Rat.zero_add
  add_assoc := Rat.add_assoc
  nsmul := inferInstance
  zero_nsmul := Rat.zero_mul
  succ_nsmul n a := by
    change (n + 1 : Nat) * a = n * a + a
    rw [Rat.natCast_add, Rat.add_mul]
    change _ + 1 * a = _
    rw [Rat.one_mul]
  add_comm := Rat.add_comm
  mul_one := Rat.mul_one
  one_mul := Rat.one_mul
  mul_assoc := Rat.mul_assoc
  pow_zero := Rat.pow_zero
  pow_succ := Rat.pow_succ
  zero_mul := Rat.zero_mul
  mul_zero := Rat.mul_zero
  mul_add := Rat.mul_add
  add_mul := Rat.add_mul
  mul_comm := Rat.mul_comm
  natCast_zero := rfl
  natCast_succ n := Rat.natCast_add n 1
  neg_add_cancel := Rat.neg_add_cancel
  sub_eq_add_neg := Rat.sub_eq_add_neg
  zsmul := inferInstance
  zero_zsmul := Rat.zero_mul
  succ_zsmul z a := by
    change (z + 1 : Int) * a = z * a + a
    rw [Rat.intCast_add, Rat.add_mul]
    change _ + 1 * a = _
    rw [Rat.one_mul]
  neg_zsmul z a := Rat.neg_mul (↑z) a
  intCast_ofNat _ := rfl
  intCast_neg _ := rfl
  zero_ne_one := by decide
  inv_zero := Rat.inv_zero
  mul_inv_cancel := Rat.mul_inv_cancel
  div_eq_mul_inv := Rat.div_def
  zpow_zero := Rat.zpow_zero
  zpow_succ := Rat.pow_succ
  zpow_neg := Rat.zpow_neg
