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

instance instZero : Zero CauchySeq where
  zero := mk (fun _ => 0) <| by
    intro ε hε
    refine ⟨0, ?_⟩
    intro m n hm hn
    rw [Rat.sub_self, Rat.abs_zero]
    exact hε

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

instance instNeg : Neg CauchySeq where
  neg x := mk (fun n => -x.run n) <| by
    intro ε hε
    let ⟨Nx, hx⟩ := x.cauchy ε hε
    refine ⟨Nx, ?_⟩
    intro m n hm hn
    rw [Rat.sub_eq_add_neg, Rat.neg_neg, Rat.add_comm, ← Rat.sub_eq_add_neg]
    exact hx hn hm

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

end CauchySeq
