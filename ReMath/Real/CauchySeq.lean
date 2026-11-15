import ReMath.Rat.Lemmas

/-- A Cauchy sequence of rationals. -/
structure CauchySeq where
  /-- The terms of the sequence. -/
  run : Nat → Rat
  /-- The Cauchy condition. -/
  cauchy :
    ∀ ε : Rat, 0 < ε → ∃ N : Nat,
    ∀ {m n : Nat}, N < m → N < n →
    Rat.abs (run m - run n) < ε

namespace CauchySeq

/-- Two Cauchy sequences are equivalent when their difference tends to zero. -/
def Equiv (a b : CauchySeq) : Prop :=
  ∀ ε : Rat, 0 < ε → ∃ N : Nat,
    ∀ {n : Nat}, N < n → Rat.abs (a.run n - b.run n) < ε

theorem equiv_refl (a : CauchySeq) : Equiv a a := by
  intro ε hε
  refine ⟨0, fun {n} _ => ?_⟩
  rw [Rat.sub_self, Rat.abs_zero]
  exact hε

theorem equiv_symm {a b : CauchySeq} (h : Equiv a b) : Equiv b a := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun {n} hn => ?_⟩
  rw [Rat.abs_sub_comm]
  exact hN hn

theorem equiv_trans {a b c : CauchySeq} (h1 : Equiv a b) (h2 : Equiv b c) :
    Equiv a c := by
  intro ε hε
  have hε2 : 0 < ε / 2 := Rat.half_pos hε
  obtain ⟨N1, hN1⟩ := h1 (ε / 2) hε2
  obtain ⟨N2, hN2⟩ := h2 (ε / 2) hε2
  refine ⟨max N1 N2, fun {n} hn => ?_⟩
  have hn1 : N1 < n := by omega
  have hn2 : N2 < n := by omega
  rw [← Rat.sub_add_cancel (a := a.run n) (b := b.run n)]
  rw [
    Rat.sub_eq_add_neg _ (c.run n),
    Rat.add_assoc _ _ (-c.run n),
    ← Rat.sub_eq_add_neg _ (c.run n)
  ]
  have s := Rat.add_lt_add (hN1 hn1) (hN2 hn2)
  rw [Rat.add_halves] at s
  exact Std.lt_of_le_of_lt (Rat.abs_triangle _ _) s

theorem equiv_iseqv : Equivalence Equiv := ⟨equiv_refl, equiv_symm, equiv_trans⟩

instance instSetoid : Setoid CauchySeq where
  r := Equiv
  iseqv := equiv_iseqv

instance : Trans (· ≤ · : Rat → Rat → Prop) (· < ·) (· < ·) := ⟨Std.lt_of_le_of_lt⟩

/-- Every Cauchy sequence is bounded by a positive rational. -/
theorem bounded (x : CauchySeq) : ∃ B : Rat, 0 < B ∧ ∀ n, Rat.abs (x.run n) < B := by
  obtain ⟨N, hN⟩ := x.cauchy 1 (by decide)
  have hprefix : ∀ K : Nat, ∃ B : Rat, 0 < B ∧ ∀ n, n ≤ K → Rat.abs (x.run n) < B := by
    intro K
    induction K with
    | zero =>
      have h : Rat.abs (x.run 0) + 0 < Rat.abs (x.run 0) + 1 :=
        Rat.add_lt_add_left.mpr (by decide)
      rw [Rat.add_zero] at h
      refine ⟨Rat.abs (x.run 0) + 1, Std.lt_of_le_of_lt Rat.abs_nonneg h, ?_⟩
      intro n hn
      have : n = 0 := by omega
      subst this
      exact h
    | succ K ih =>
      obtain ⟨B, hB, hbd⟩ := ih
      have h : B + 0 < B + (Rat.abs (x.run (K + 1)) + 1) := by
        refine Rat.add_lt_add_left.mpr ?_
        have h' : Rat.abs (x.run (K + 1)) + 0 < Rat.abs (x.run (K + 1)) + 1 :=
          Rat.add_lt_add_left.mpr (by decide)
        rw [Rat.add_zero] at h'
        exact Std.lt_of_le_of_lt Rat.abs_nonneg h'
      rw [Rat.add_zero] at h
      refine ⟨B + (Rat.abs (x.run (K + 1)) + 1), Std.lt_trans hB h, ?_⟩
      intro n hn
      by_cases hle : n ≤ K
      · exact Std.lt_trans (hbd n hle) h
      · have : n = K + 1 := by omega
        subst this
        have h' : Rat.abs (x.run (K + 1)) + 0 < Rat.abs (x.run (K + 1)) + 1 :=
          Rat.add_lt_add_left.mpr (by decide)
        rw [Rat.add_zero] at h'
        have hB' : 0 + (Rat.abs (x.run (K + 1)) + 1) < B + (Rat.abs (x.run (K + 1)) + 1) :=
          Rat.add_lt_add_right.mpr hB
        rw [Rat.zero_add] at hB'
        exact Std.lt_trans h' hB'
  obtain ⟨B, hB, hbd⟩ := hprefix (N + 1)
  have hB1 : B < B + 1 := by
    have h : B + 0 < B + 1 := Rat.add_lt_add_left.mpr (by decide)
    rwa [Rat.add_zero] at h
  refine ⟨B + 1, Std.lt_trans hB hB1, ?_⟩
  intro n
  by_cases hn : n ≤ N + 1
  · exact Std.lt_trans (hbd n hn) hB1
  · have hnN : N < n := by omega
    have hd := hN hnN (Nat.lt_succ_self N)
    have hk := hbd (N + 1) (Nat.le_refl _)
    have s := Rat.add_lt_add hd hk
    rw [Rat.add_comm 1 B] at s
    have tri := Rat.abs_triangle (x.run n - x.run (N + 1)) (x.run (N + 1))
    rw [Rat.sub_add_cancel] at tri
    exact Std.lt_of_le_of_lt tri s

def ofRat (x : Rat) : CauchySeq where
  run := fun _ => x
  cauchy := by
    intro ε hε
    refine ⟨0, ?_⟩
    intro m n hm hn
    rw [Rat.sub_self, Rat.abs_zero]
    exact hε

instance instIntCast : IntCast CauchySeq where
  intCast z := ofRat z

instance instNatCast : NatCast CauchySeq where
  natCast n := ofRat n

instance instOfNat (n : Nat) : OfNat CauchySeq n := ⟨ofRat n⟩

instance instZero : Zero CauchySeq := ⟨ofRat 0⟩

instance instAdd : Add CauchySeq where
  add x y := mk (fun n => x.run n + y.run n) <| by
    intro ε hε
    let ⟨Nx, hx⟩ := x.cauchy (ε / 2) (Rat.half_pos hε)
    let ⟨Ny, hy⟩ := y.cauchy (ε / 2) (Rat.half_pos hε)
    refine ⟨max Nx Ny, ?_⟩
    intro m n hm hn
    rw [Nat.max_lt] at hm hn
    have hx' := hx hm.left hn.left
    have hy' := hy hm.right hn.right
    calc (x.run m + y.run m - (x.run n + y.run n)).abs
      _ = (x.run m + y.run m + (-x.run n + -y.run n)).abs := by simp only [Rat.sub_eq_add_neg, Rat.neg_add]
      _ = ((x.run m + -x.run n) + (y.run m + -y.run n)).abs := by ac_rfl
      _ = ((x.run m - x.run n) + (y.run m - y.run n)).abs := by simp only [Rat.sub_eq_add_neg]
      _ ≤ (x.run m - x.run n).abs + (y.run m - y.run n).abs := Rat.abs_triangle _ _
      _ < ε := Rat.add_halves ε ▸ Rat.add_lt_add hx' hy'

/-- Addition respects equivalence of Cauchy sequences. -/
theorem add_equiv {a₁ a₂ b₁ b₂ : CauchySeq} (ha : Equiv a₁ a₂) (hb : Equiv b₁ b₂) :
    Equiv (a₁ + b₁) (a₂ + b₂) := by
  intro ε hε
  have ⟨N₁, h₁⟩ := ha (ε / 2) (Rat.half_pos hε)
  have ⟨N₂, h₂⟩ := hb (ε / 2) (Rat.half_pos hε)
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  rw [Nat.max_lt] at hn
  have h₁' := h₁ hn.left
  have h₂' := h₂ hn.right
  calc ((a₁ + b₁).run n - (a₂ + b₂).run n).abs
    _ = ((a₁.run n + b₁.run n) - (a₂.run n + b₂.run n)).abs := rfl
    _ = ((a₁.run n + b₁.run n) + (-a₂.run n + -b₂.run n)).abs := by simp only [Rat.sub_eq_add_neg, Rat.neg_add]
    _ = ((a₁.run n + -a₂.run n) + (b₁.run n + -b₂.run n)).abs := by ac_rfl
    _ ≤ (a₁.run n + -a₂.run n).abs + (b₁.run n + -b₂.run n).abs := Rat.abs_triangle _ _
    _ = (a₁.run n - a₂.run n).abs + (b₁.run n - b₂.run n).abs := by simp only [Rat.sub_eq_add_neg]
    _ < ε := Rat.add_halves ε ▸ Rat.add_lt_add h₁' h₂'

instance instNeg : Neg CauchySeq where
  neg x := mk (fun n => -x.run n) <| by
    intro ε hε
    let ⟨Nx, hx⟩ := x.cauchy ε hε
    refine ⟨Nx, ?_⟩
    intro m n hm hn
    rw [Rat.sub_eq_add_neg, Rat.neg_neg, Rat.add_comm, ← Rat.sub_eq_add_neg]
    exact hx hn hm

/-- Negation respects equivalence of Cauchy sequences. -/
theorem neg_equiv {a b : CauchySeq} (h : Equiv a b) : Equiv (-a) (-b) := by
  intro ε hε
  have ⟨N, h⟩ := h ε hε
  refine ⟨N, ?_⟩
  intro n hn
  change (-a.run n - -b.run n).abs < ε
  rw [Rat.sub_eq_add_neg, ← Rat.neg_add, ← Rat.sub_eq_add_neg, Rat.abs_neg]
  exact h hn

instance instOne : One CauchySeq := ⟨ofRat 1⟩

instance instMul : Mul CauchySeq where
  mul x y := mk (fun n => x.run n * y.run n) <| by
    intro ε hε
    obtain ⟨Bx, hBx, hbx⟩ := bounded x
    obtain ⟨By, hBy, hby⟩ := bounded y
    have hε2 : 0 < ε / 2 := Rat.half_pos hε
    have hdx : 0 < ε / 2 / By := by
      rw [Rat.div_def]
      exact Rat.mul_pos hε2 (Rat.inv_pos.mpr hBy)
    have hdy : 0 < ε / 2 / Bx := by
      rw [Rat.div_def]
      exact Rat.mul_pos hε2 (Rat.inv_pos.mpr hBx)
    obtain ⟨Nx, hx⟩ := x.cauchy (ε / 2 / By) hdx
    obtain ⟨Ny, hy⟩ := y.cauchy (ε / 2 / Bx) hdy
    refine ⟨max Nx Ny, ?_⟩
    intro m n hm hn
    rw [Nat.max_lt] at hm hn
    have t1 : Rat.abs (x.run m) * Rat.abs (y.run m - y.run n) < ε / 2 := by
      have := Rat.mul_lt_mul (hbx m) (hy hm.right hn.right) Rat.abs_nonneg Rat.abs_nonneg
      rwa [Rat.mul_div_cancel_pos _ hBx] at this
    have t2 : Rat.abs (y.run n) * Rat.abs (x.run m - x.run n) < ε / 2 := by
      have := Rat.mul_lt_mul (hby n) (hx hm.left hn.left) Rat.abs_nonneg Rat.abs_nonneg
      rwa [Rat.mul_div_cancel_pos _ hBy] at this
    have s := Rat.add_lt_add t1 t2
    rw [Rat.add_halves, ← Rat.abs_mul, ← Rat.abs_mul] at s
    rw [Rat.mul_sub_split]
    exact Std.lt_of_le_of_lt (Rat.abs_triangle _ _) s

/-- Multiplication respects equivalence of Cauchy sequences. -/
theorem mul_equiv {a₁ a₂ b₁ b₂ : CauchySeq} (ha : Equiv a₁ a₂) (hb : Equiv b₁ b₂) :
    Equiv (a₁ * b₁) (a₂ * b₂) := by
  intro ε hε
  obtain ⟨Ba, hBa, hba⟩ := bounded a₁
  obtain ⟨Bb, hBb, hbb⟩ := bounded b₂
  have hε2 : 0 < ε / 2 := Rat.half_pos hε
  have hda : 0 < ε / 2 / Bb := by
    rw [Rat.div_def]
    exact Rat.mul_pos hε2 (Rat.inv_pos.mpr hBb)
  have hdb : 0 < ε / 2 / Ba := by
    rw [Rat.div_def]
    exact Rat.mul_pos hε2 (Rat.inv_pos.mpr hBa)
  obtain ⟨N₁, h₁⟩ := ha (ε / 2 / Bb) hda
  obtain ⟨N₂, h₂⟩ := hb (ε / 2 / Ba) hdb
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  rw [Nat.max_lt] at hn
  have t1 : Rat.abs (a₁.run n) * Rat.abs (b₁.run n - b₂.run n) < ε / 2 := by
    have := Rat.mul_lt_mul (hba n) (h₂ hn.right) Rat.abs_nonneg Rat.abs_nonneg
    rwa [Rat.mul_div_cancel_pos _ hBa] at this
  have t2 : Rat.abs (b₂.run n) * Rat.abs (a₁.run n - a₂.run n) < ε / 2 := by
    have := Rat.mul_lt_mul (hbb n) (h₁ hn.left) Rat.abs_nonneg Rat.abs_nonneg
    rwa [Rat.mul_div_cancel_pos _ hBb] at this
  have s := Rat.add_lt_add t1 t2
  rw [Rat.add_halves, ← Rat.abs_mul, ← Rat.abs_mul] at s
  change (a₁.run n * b₁.run n - a₂.run n * b₂.run n).abs < ε
  rw [Rat.mul_sub_split]
  exact Std.lt_of_le_of_lt (Rat.abs_triangle _ _) s

@[simp] theorem zero_run (n : Nat) : (0 : CauchySeq).run n = 0 := rfl

/-- A nonzero rational has a reciprocal that cancels it on the left. -/
theorem rat_inv_mul_self {a : Rat} (h : a ≠ 0) : a⁻¹ * a = 1 := by
  rw [Rat.mul_comm]
  exact Rat.mul_inv_cancel a h

/-- A rational whose absolute value exceeds a positive bound is nonzero. -/
theorem ne_zero_of_lt_abs {δ a : Rat} (hδ : 0 < δ) (h : δ < Rat.abs a) : a ≠ 0 :=
  Rat.ne_zero_of_abs_pos (Std.lt_trans hδ h)

/-- The difference of reciprocals, scaled by the product of the originals. -/
theorem inv_sub_inv_mul {a b : Rat} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a⁻¹ - b⁻¹) * (a * b) = b - a := by
  rw [Rat.sub_mul, Rat.inv_mul_cancel_left ha, Rat.inv_mul_mul_cancel hb]

/-- A Cauchy sequence that is not equivalent to zero is eventually bounded away from zero. -/
theorem exists_bound_of_not_equiv_zero {x : CauchySeq} (h : ¬ Equiv x 0) :
    ∃ δ : Rat, 0 < δ ∧ ∃ N : Nat, ∀ n, N < n → δ < Rat.abs (x.run n) := by
  refine Classical.byContradiction fun hc => ?_
  apply h
  intro ε hε
  have hε2 : 0 < ε / 2 := Rat.half_pos hε
  obtain ⟨N0, hN0⟩ := x.cauchy (ε / 2) hε2
  have hfreq : ∃ n, N0 < n ∧ Rat.abs (x.run n) ≤ ε / 2 := by
    refine Classical.byContradiction fun hno => ?_
    apply hc
    refine ⟨ε / 2, hε2, N0, fun n hn => ?_⟩
    refine Classical.byContradiction fun hle => ?_
    exact hno ⟨n, hn, Std.not_lt.mp hle⟩
  obtain ⟨n, hn, hxn⟩ := hfreq
  refine ⟨N0, fun {m} hm => ?_⟩
  show Rat.abs (x.run m - 0) < ε
  rw [Rat.sub_eq_add_neg, Rat.neg_zero, Rat.add_zero]
  have hd := hN0 hm hn
  have tri := Rat.abs_triangle (x.run m - x.run n) (x.run n)
  rw [Rat.sub_add_cancel] at tri
  have s : Rat.abs (x.run m - x.run n) + Rat.abs (x.run n) < ε / 2 + ε / 2 :=
    Std.lt_of_le_of_lt (Rat.add_le_add_left.mpr hxn) (Rat.add_lt_add_right.mpr hd)
  rw [Rat.add_halves] at s
  exact Std.lt_of_le_of_lt tri s

theorem inv_cauchy {x : CauchySeq} (h : ¬ Equiv x 0) :
    ∀ ε : Rat, 0 < ε → ∃ N : Nat,
      ∀ {m n : Nat}, N < m → N < n →
      Rat.abs ((x.run m)⁻¹ - (x.run n)⁻¹) < ε := by
  intro ε hε
  obtain ⟨δ, hδ, N0, hN0⟩ := exists_bound_of_not_equiv_zero h
  obtain ⟨N1, hN1⟩ := x.cauchy (ε * (δ * δ)) (Rat.mul_pos hε (Rat.mul_pos hδ hδ))
  refine ⟨max N0 N1, ?_⟩
  intro m n hm hn
  rw [Nat.max_lt] at hm hn
  exact Rat.inv_sub_inv_lt hδ hδ hε (hN0 m hm.left) (hN0 n hn.left) (hN1 hn.right hm.right)

open Classical in
/--
The inverse of a Cauchy sequence. Sequences equivalent to zero have no
inverse, so they are sent to zero.
-/
noncomputable instance instInv : Inv CauchySeq where
  inv x :=
    if h : Equiv x 0 then 0
    else mk (fun n => (x.run n)⁻¹) (inv_cauchy h)

open Classical in
theorem inv_run_of_not_equiv {x : CauchySeq} (h : ¬ Equiv x 0) (n : Nat) :
    (x⁻¹).run n = (x.run n)⁻¹ := by
  show (if h : Equiv x 0 then (0 : CauchySeq)
    else mk (fun n => (x.run n)⁻¹) (inv_cauchy h)).run n = _
  rw [dif_neg h]

open Classical in
theorem inv_run_of_equiv {x : CauchySeq} (h : Equiv x 0) (n : Nat) :
    (x⁻¹).run n = 0 := by
  show (if h : Equiv x 0 then (0 : CauchySeq)
    else mk (fun n => (x.run n)⁻¹) (inv_cauchy h)).run n = _
  rw [dif_pos h]
  rfl

/-- Inversion respects equivalence of Cauchy sequences. -/
theorem inv_equiv {a b : CauchySeq} (h : Equiv a b) : Equiv a⁻¹ b⁻¹ := by
  by_cases ha : Equiv a 0
  · have hb : Equiv b 0 := equiv_trans (equiv_symm h) ha
    intro ε hε
    refine ⟨0, fun {n} _ => ?_⟩
    rw [inv_run_of_equiv ha, inv_run_of_equiv hb, Rat.sub_self, Rat.abs_zero]
    exact hε
  · have hb : ¬ Equiv b 0 := fun hb => ha (equiv_trans h hb)
    obtain ⟨δa, hδa, Na, hNa⟩ := exists_bound_of_not_equiv_zero ha
    obtain ⟨δb, hδb, Nb, hNb⟩ := exists_bound_of_not_equiv_zero hb
    intro ε hε
    obtain ⟨N, hN⟩ := (equiv_symm h) (ε * (δa * δb)) (Rat.mul_pos hε (Rat.mul_pos hδa hδb))
    refine ⟨max N (max Na Nb), fun {n} hn => ?_⟩
    rw [Nat.max_lt, Nat.max_lt] at hn
    rw [inv_run_of_not_equiv ha, inv_run_of_not_equiv hb]
    exact Rat.inv_sub_inv_lt hδa hδb hε (hNa n hn.2.1) (hNb n hn.2.2) (hN hn.1)

end CauchySeq
