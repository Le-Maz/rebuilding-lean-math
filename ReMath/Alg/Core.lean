import ReMath.Alg.Defs
open Fin.NatCast Fin.IntCast

instance : Alg.CommSemiring Nat where
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
  mul_comm := Nat.mul_comm
  natCast_zero := rfl
  natCast_succ _ := rfl

/-- Casting a remainder of naturals into `Int` commutes with `%`. -/
private theorem int_natCast_mod_eq (n m : Nat) :
    ((m % n : Nat) : Int) = (m : Int) % (n : Int) := by
  first
    | rfl
    | norm_cast
    | simp

/-- The value of the cast of an integer into `Fin n` is its remainder mod `n`. -/
private theorem fin_val_intCast_emod (n : Nat) [NeZero n] (z : Int) :
    (((z : Fin n)).val : Int) = z % n := by
  have hpos : 0 < n := Nat.pos_of_neZero n
  rw [Fin.intCast_def]
  split
  · rename_i h
    show ((z.natAbs % n : Nat) : Int) = z % n
    rw [int_natCast_mod_eq, Int.natAbs_of_nonneg h]
  · rename_i h
    show (((n - z.natAbs % n) % n : Nat) : Int) = z % n
    have hr : z.natAbs % n < n := Nat.mod_lt _ hpos
    have hdm := Nat.div_add_mod z.natAbs n
    have hdm' : (n : Int) * ((z.natAbs / n : Nat) : Int)
        + ((z.natAbs % n : Nat) : Int) = (z.natAbs : Int) := by
      exact_mod_cast hdm
    have hz : (z.natAbs : Int) = -z := by omega
    rw [int_natCast_mod_eq]
    apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    apply Int.emod_eq_zero_of_dvd
    refine ⟨1 + ((z.natAbs / n : Nat) : Int), ?_⟩
    rw [Int.mul_add, Int.mul_one]
    generalize (n : Int) * ((z.natAbs / n : Nat) : Int) = P at *
    generalize z.natAbs % n = r at *
    omega

/-- Casting `z + 1` into `Fin n` adds one in `Fin n`. -/
private theorem fin_intCast_add_one (n : Nat) [NeZero n] (z : Int) :
    ((z + 1 : Int) : Fin n) = (z : Fin n) + 1 := by
  apply Fin.ext
  have h1 := fin_val_intCast_emod n (z + 1)
  have h2 := fin_val_intCast_emod n z
  have h1v : (1 : Fin n).val = 1 % n := rfl
  have key : ((((z + 1 : Int) : Fin n)).val : Int)
      = ((((z : Fin n) + 1).val : Nat) : Int) := by
    rw [h1, Fin.val_add, h1v]
    push_cast
    rw [h2]
    exact Int.add_emod z 1 n
  exact_mod_cast key

/-- Multiplication in `Fin n` distributes over addition on the right. -/
private theorem fin_add_mul {n} (a b c : Fin n) : (a + b) * c = a * c + b * c := by
  apply Fin.ext
  simp [Fin.val_mul, Fin.val_add]
  simp [Nat.add_mul]

/-- Negation in `Fin n` is an involution. -/
private theorem fin_neg_neg (n : Nat) [NeZero n] (x : Fin n) : - -x = x := by
  apply Fin.ext
  have hx := x.isLt
  simp only [Fin.val_neg]
  by_cases h : x.val = 0
  · have hx0 : x = 0 := Fin.ext (by simp [h])
    subst hx0
    simp [Fin.neg_def]
  · have hx0 : x ≠ 0 := fun h' => h (by simp [h'])
    have hn : -x ≠ 0 := by
      intro hn
      have := congrArg Fin.val hn
      simp [Fin.val_neg, hx0] at this <;> omega
    rw [if_neg hn, if_neg hx0]
    omega

/-- Casting `-z` into `Fin n` negates the cast of `z`. -/
private theorem fin_intCast_neg (n : Nat) [NeZero n] (z : Int) :
    ((-z : Int) : Fin n) = -(z : Fin n) := by
  simp only [Fin.intCast_def, Int.natAbs_neg]
  by_cases h0 : z = 0
  · subst h0
    apply Fin.ext
    simp [Fin.val_neg]
  · by_cases hp : 0 ≤ z
    · have hn : ¬ 0 ≤ -z := by omega
      rw [if_neg hn, if_pos hp]
    · have hn : 0 ≤ -z := by omega
      rw [if_pos hn, if_neg hp, fin_neg_neg]

/-- Addition in `Fin n` is associative. -/
private theorem fin_add_assoc (n : Nat) [NeZero n] (a b c : Fin n) :
    a + b + c = a + (b + c) := by
  apply Fin.ext
  simp [Fin.val_add, Nat.add_assoc]

/-- Addition in `Fin n` is commutative. -/
private theorem fin_add_comm (n : Nat) [NeZero n] (a b : Fin n) :
    a + b = b + a := by
  apply Fin.ext
  simp [Fin.val_add, Nat.add_comm]

/-- Adding `a` to `-a` gives zero in `Fin n`. -/
private theorem fin_neg_add (n : Nat) [NeZero n] (a : Fin n) : -a + a = 0 := by
  apply Fin.ext
  simp [Fin.val_add, Fin.val_neg]
  by_cases h0 : a = 0 <;> simp [h0]

/-- Negation commutes with multiplication on the left in `Fin n`. -/
private theorem fin_neg_mul (n : Nat) [NeZero n] (a b : Fin n) :
    -a * b = -(a * b) := by
  have h1 : -a * b + a * b = 0 := by
    rw [← fin_add_mul, fin_neg_add, Fin.zero_mul]
  have h2 : a * b + -(a * b) = 0 := by
    rw [fin_add_comm n (a * b)]
    exact fin_neg_add n _
  calc -a * b = -a * b + 0 := by rw [Fin.add_zero]
    _ = -a * b + (a * b + -(a * b)) := by rw [h2]
    _ = (-a * b + a * b) + -(a * b) := (fin_add_assoc n _ _ _).symm
    _ = -(a * b) := by rw [h1, Fin.zero_add]

instance (n : Nat) [NeZero n] : Alg.CommRing (Fin n) where
  nsmul := ⟨fun k i => (k : Fin n) * i⟩
  zsmul := ⟨fun k i => (k : Fin n) * i⟩
  add_zero := Fin.add_zero
  zero_add := Fin.zero_add
  add_assoc := fin_add_assoc n
  zero_nsmul := Fin.zero_mul
  succ_nsmul k a := by
    change ((k + 1 : Nat) : Fin n) * a = (k : Fin n) * a + a
    apply Fin.ext
    simp [Fin.val_add, Fin.val_mul]
    change (k + 1) % n * a.val % n = (k % n * a.val + a) % n
    rw [Nat.mod_mul_mod, Nat.add_mul, Nat.one_mul]
    simp [Nat.add_mod]
  add_comm := fin_add_comm n
  mul_one := Fin.mul_one
  one_mul := Fin.one_mul
  mul_assoc := Fin.mul_assoc
  pow_zero _ := rfl
  pow_succ _ _ := rfl
  zero_mul := Fin.zero_mul
  mul_zero := Fin.mul_zero
  mul_add a b c := by
    have := fin_add_mul b c a
    rw [Fin.mul_comm, this]
    ac_rfl
  add_mul := fin_add_mul
  natCast_zero := rfl
  natCast_succ x := by
    apply Fin.ext
    rw [Fin.val_add]
    change (x + 1) % n = (x % n + _) % n
    simp
    cases n with
    | zero => omega
    | succ n =>
      cases n with
      | zero => omega
      | succ n => rfl
  neg_add_cancel a := by
    apply Fin.ext
    simp [Fin.val_add, Fin.val_neg]
    by_cases h0 : a = 0 <;> simp [h0]
  sub_eq_add_neg a b := by
    apply Fin.ext
    simp [Fin.sub_def, Fin.neg_def]
    simp [Fin.val_add]
    ac_rfl
  zero_zsmul := Fin.zero_mul
  succ_zsmul z a := by
    change ((z + 1 : Int) : Fin n) * a = (z : Fin n) * a + a
    rw [fin_intCast_add_one, fin_add_mul, Fin.one_mul]
    rfl
  mul_comm := Fin.mul_comm
  neg_zsmul i a := by
    change (((-i) : Int) : Fin n) * a = -((i : Fin n) * a)
    rw [fin_intCast_neg, fin_neg_mul]
  intCast_neg x := fin_intCast_neg n x
  intCast_ofNat _ := rfl

instance : Alg.CommRing Int where
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
  mul_comm := Int.mul_comm
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
    rw [Rat.one_mul, Rat.intCast_natCast]
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
