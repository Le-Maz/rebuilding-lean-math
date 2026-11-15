import ReMath.Rat.Lemmas
import ReMath.Real.CauchySeq

def Real := Quotient CauchySeq.instSetoid

namespace Real

def mk := Quotient.mk CauchySeq.instSetoid

instance instZero : Zero Real where
  zero := mk 0

instance instAdd : Add Real where
  add x y := x.liftOn₂ y (mk <| · + ·) <| by
    intro a₁ b₁ a₂ b₂ ha hb
    apply Quotient.sound
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

instance instNeg : Neg Real where
  neg x := x.liftOn (mk <| -·) <| by
    intro a b h
    apply Quotient.sound
    intro ε hε
    have ⟨N, h⟩ := h ε hε
    refine ⟨N, ?_⟩
    intro n hn
    change (-a.run n - -b.run n).abs < ε
    rw [Rat.sub_eq_add_neg, ← Rat.neg_add, ← Rat.sub_eq_add_neg, Rat.abs_neg]
    exact h hn

instance instMul : Mul Real where
  mul x y := x.liftOn₂ y (mk <| · * ·) <| by
    intro a₁ b₁ a₂ b₂ ha hb
    apply Quotient.sound
    intro ε hε
    obtain ⟨Ba, hBa, hba⟩ := CauchySeq.bounded a₁
    obtain ⟨Bb, hBb, hbb⟩ := CauchySeq.bounded b₂
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

instance instSub : Sub Real where
  sub a b := a + -b

end Real
