namespace Rat

theorem half_pos {ε : Rat} (hε : 0 < ε) : 0 < ε / 2 := by
  rw [Rat.div_def ε 2]
  refine Rat.mul_pos hε ?_
  rw [Rat.inv_pos]
  decide

theorem add_halves (ε : Rat) : ε / 2 + ε / 2 = ε := by
  rw [Rat.div_def, ← Rat.mul_add]
  have : (2 : Rat)⁻¹ + 2⁻¹ = 1 := by decide +kernel
  rw [this, Rat.mul_one]

theorem add_lt_add {a b c d : Rat} (hab : a < b) (hcd : c < d) : a + c < b + d := by
  have h1 : a + c < a + d := Rat.add_lt_add_left.mpr hcd
  have h2 : d + a < d + b := Rat.add_lt_add_left.mpr hab
  rw [Rat.add_comm d a, Rat.add_comm d b] at h2
  exact Std.lt_trans h1 h2

/-- Adding inequalities on both sides. -/
theorem add_le_add {a b c d : Rat} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d :=
  Rat.le_trans (Rat.add_le_add_right.mpr h1) (Rat.add_le_add_left.mpr h2)

/-- A rational is at most its absolute value. -/
theorem le_abs_self (x : Rat) : x ≤ Rat.abs x := by
  unfold Rat.abs
  by_cases h : 0 ≤ x
  · rw [if_pos h]; exact Rat.le_refl
  · rw [if_neg h]
    have h1 : x ≤ 0 := Rat.le_of_lt (Rat.not_le.mp h)
    have h2 : -0 ≤ -x := Rat.neg_le_neg h1
    have h3 : (-0 : Rat) = 0 := by decide
    rw [h3] at h2
    exact Rat.le_trans h1 h2

/-- The negation of a rational is at most its absolute value. -/
theorem neg_le_abs (x : Rat) : -x ≤ Rat.abs x := by
  unfold Rat.abs
  by_cases h : 0 ≤ x
  · rw [if_pos h]
    have h2 : -x ≤ -0 := Rat.neg_le_neg h
    have h3 : (-0 : Rat) = 0 := by decide
    rw [h3] at h2
    exact Rat.le_trans h2 h
  · rw [if_neg h]; exact Rat.le_refl

/-- Triangle inequality for the absolute value. -/
theorem abs_triangle (x y : Rat) : Rat.abs (x + y) ≤ Rat.abs x + Rat.abs y := by
  by_cases h : 0 ≤ x + y
  · have e : Rat.abs (x + y) = x + y := by unfold Rat.abs; rw [if_pos h]
    rw [e]
    exact add_le_add (le_abs_self x) (le_abs_self y)
  · have e : Rat.abs (x + y) = -(x + y) := by unfold Rat.abs; rw [if_neg h]
    rw [e, Rat.neg_add]
    exact add_le_add (neg_le_abs x) (neg_le_abs y)

/-- Multiplying strict inequalities between nonnegative rationals. -/
theorem mul_lt_mul {a b c d : Rat} (hab : a < b) (hcd : c < d)
    (ha : 0 ≤ a) (hc : 0 ≤ c) : a * c < b * d := by
  have hd : 0 < d := Std.lt_of_le_of_lt hc hcd
  have h1 : a * c ≤ a * d := Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt hcd) ha
  have h2 : a * d < b * d := Rat.mul_lt_mul_of_pos_right hab hd
  exact Std.lt_of_le_of_lt h1 h2

/-- Multiplying by a positive rational and dividing by it cancels. -/
theorem mul_div_cancel_pos {B : Rat} (ε : Rat) (hB : 0 < B) : B * (ε / B) = ε := by
  have hne : B ≠ 0 := by
    intro h
    rw [h] at hB
    exact Rat.lt_irrefl hB
  rw [Rat.div_def, Rat.mul_comm ε B⁻¹, ← Rat.mul_assoc, Rat.mul_inv_cancel B hne, Rat.one_mul]

/-- A product of rationals is zero only if a factor is zero. -/
theorem mul_ne_zero' {a b : Rat} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  intro h
  rcases Rat.mul_eq_zero.mp h with h | h
  · exact ha h
  · exact hb h

/-- A nonnegative rational times a nonpositive one is nonpositive. -/
theorem mul_nonpos_of_nonneg_of_nonpos {a b : Rat} (ha : 0 ≤ a) (hb : b ≤ 0) :
    a * b ≤ 0 := by
  have h3 : (-0 : Rat) = 0 := by decide
  have h2 : -0 ≤ -b := Rat.neg_le_neg hb
  rw [h3] at h2
  have h4 := Rat.mul_nonneg ha h2
  rw [Rat.mul_comm a (-b), Rat.neg_mul, Rat.mul_comm b a] at h4
  have h5 := Rat.neg_le_neg h4
  rw [Rat.neg_neg, h3] at h5
  exact h5

/-- A product of two nonpositive rationals is nonnegative. -/
theorem mul_nonneg_of_nonpos_of_nonpos {a b : Rat} (ha : a ≤ 0) (hb : b ≤ 0) :
    0 ≤ a * b := by
  have h3 : (-0 : Rat) = 0 := by decide
  have h1 : -0 ≤ -a := Rat.neg_le_neg ha
  have h2 : -0 ≤ -b := Rat.neg_le_neg hb
  rw [h3] at h1 h2
  have h4 := Rat.mul_nonneg h1 h2
  rw [Rat.neg_mul, Rat.mul_comm a (-b), Rat.neg_mul, Rat.neg_neg, Rat.mul_comm b a] at h4
  exact h4

/-- The absolute value is multiplicative. -/
theorem abs_mul (a b : Rat) : Rat.abs (a * b) = Rat.abs a * Rat.abs b := by
  by_cases ha : 0 ≤ a
  <;> by_cases hb : 0 ≤ b
  <;> by_cases hab : 0 ≤ a * b
  <;> simp only [Rat.abs, ha, hb, hab]
  <;> simp only [ite_true, ite_false]
  · have _ := Rat.mul_nonneg ha hb
    contradiction
  · have hb' : b ≤ 0 := Rat.le_of_lt (Rat.not_le.mp hb)
    have h3 : (-0 : Rat) = 0 := by decide
    have hz : a * b = 0 := Rat.le_antisymm (mul_nonpos_of_nonneg_of_nonpos ha hb') hab
    rw [Rat.mul_comm a (-b), Rat.neg_mul, Rat.mul_comm b a, hz, h3]
  · rw [Rat.mul_comm a b, ← Rat.neg_mul b a]
    exact Rat.mul_comm (-b) a
  · have ha' : a ≤ 0 := Rat.le_of_lt (Rat.not_le.mp ha)
    have h3 : (-0 : Rat) = 0 := by decide
    have h4 : b * a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb ha'
    rw [Rat.mul_comm b a] at h4
    have hz : a * b = 0 := Rat.le_antisymm h4 hab
    rw [Rat.neg_mul, hz, h3]
  · exact (Rat.neg_mul a b).symm
  · rw [Rat.neg_mul, Rat.mul_comm a (-b)]
    rw [Rat.neg_mul, Rat.neg_neg]
    exact Rat.mul_comm a b
  · have ha' : a ≤ 0 := Rat.le_of_lt (Rat.not_le.mp ha)
    have hb' : b ≤ 0 := Rat.le_of_lt (Rat.not_le.mp hb)
    exact absurd (mul_nonneg_of_nonpos_of_nonpos ha' hb') hab

/-- Multiplication distributes through the difference of products. -/
theorem mul_sub_split (a b c d : Rat) :
    a * c - b * d = a * (c - d) + d * (a - b) := by
  simp only [Rat.sub_eq_add_neg, Rat.mul_add]
  simp only [Rat.mul_comm d (-b), Rat.neg_mul]
  simp only [Rat.mul_comm a (-d), Rat.neg_mul]
  rw [← Rat.add_assoc, Rat.add_assoc _ _ (d * a)]
  simp only [Rat.neg_add_cancel, Rat.add_zero]

end Rat
