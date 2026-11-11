import ReMath.Alg.Defs

instance : Alg.Ring Int where
  add_zero := Int.add_zero
  zero_add := Int.zero_add
  add_assoc := Int.add_assoc
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
