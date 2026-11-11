import ReMath.Alg.Defs

instance : Alg.Semiring Nat where
  add_zero := Nat.add_zero
  zero_add := Nat.zero_add
  add_assoc := Nat.add_assoc
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
