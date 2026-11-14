import ReMath.Set.Subnum

/--
`α` is strictly subnumerous to `β` when `α` is subnumerous to `β` but `β` is not subnumerous to `α`.
-/
class StrictSubnum (α β : Sort _) : Prop where
  fw : Subnum α β
  bw : ¬ Subnum β α

namespace StrictSubnum

/-- Strict subnumerosity is irreflexive. -/
theorem irrefl (α : Sort _) : ¬ StrictSubnum α α :=
  fun h => h.bw h.fw

/-- Strict subnumerosity is transitive. -/
theorem trans {α β γ : Sort _}
    (h₁ : StrictSubnum α β) (h₂ : StrictSubnum β γ) : StrictSubnum α γ where
  fw := h₁.fw.trans h₂.fw
  bw := fun h => h₁.bw (h₂.fw.trans h)

/-- Enables `calc` chains over `StrictSubnum`. -/
instance instTrans : Trans StrictSubnum StrictSubnum StrictSubnum := ⟨trans⟩

/-- Strict subnumerosity is asymmetric. -/
theorem asymm {α β : Sort _} (h : StrictSubnum α β) : ¬ StrictSubnum β α :=
  fun h' => h.bw h'.fw

/-- A strict relation implies the non-strict one. -/
theorem le {α β : Sort _} (h : StrictSubnum α β) : Subnum α β :=
  h.fw

/-- Strict then non-strict subnumerosity gives strict subnumerosity. -/
theorem trans_subnum {α β γ : Sort _}
    (h₁ : StrictSubnum α β) (h₂ : Subnum β γ) : StrictSubnum α γ where
  fw := h₁.fw.trans h₂
  bw := fun h => h₁.bw (h₂.trans h)

/-- Enables `calc` chains of the form `StrictSubnum α β`, `Subnum β γ`. -/
instance instTransStrictSubnum : Trans StrictSubnum Subnum StrictSubnum :=
  ⟨trans_subnum⟩

/-- Non-strict then strict subnumerosity gives strict subnumerosity. -/
theorem subnum_trans {α β γ : Sort _}
    (h₁ : Subnum α β) (h₂ : StrictSubnum β γ) : StrictSubnum α γ where
  fw := h₁.trans h₂.fw
  bw := fun h => h₂.bw (h.trans h₁)

/-- Enables `calc` chains of the form `Subnum α β`, `StrictSubnum β γ`. -/
instance instTransSubnumStrict : Trans Subnum StrictSubnum StrictSubnum :=
  ⟨subnum_trans⟩

/-- Strict subnumerosity is invariant under equinumerosity of both sides. -/
theorem congr {α₁ α₂ β₁ β₂ : Sort _}
    (hα : Equinum α₁ α₂) (hβ : Equinum β₁ β₂) :
    StrictSubnum α₁ β₁ ↔ StrictSubnum α₂ β₂ :=
  ⟨fun h => ⟨(Subnum.congr hα hβ).mp h.fw,
             fun h' => h.bw ((Subnum.congr hβ hα).mpr h')⟩,
   fun h => ⟨(Subnum.congr hα hβ).mpr h.fw,
             fun h' => h.bw ((Subnum.congr hβ hα).mp h')⟩⟩

/-- Strict subnumerosity is exactly subnumerosity without equinumerosity. -/
theorem iff_subnum_not_equinum {α β : Sort _} :
    StrictSubnum α β ↔ Subnum α β ∧ ¬ Equinum α β :=
  ⟨fun h => ⟨h.fw, fun he => h.bw (Subnum.of_equinum he.symm)⟩,
   fun ⟨h₁, h₂⟩ => ⟨h₁, fun h₃ => h₂ (Subnum.antisymm h₁ h₃)⟩⟩

/-- Strictly subnumerous types are not equinumerous. -/
theorem not_equinum {α β : Sort _} (h : StrictSubnum α β) : ¬ Equinum α β :=
  fun he => h.bw (Subnum.of_equinum he.symm)

/-- Strictly subnumerous types are distinct. -/
theorem ne {α β : Sort u} (h : StrictSubnum α β) : α ≠ β := by
  intro he
  subst he
  exact irrefl _ h

/-- Trichotomy: any two types are strictly ordered one way or the other, or equinumerous. -/
theorem trichotomy (α β : Sort _) :
    StrictSubnum α β ∨ Equinum α β ∨ StrictSubnum β α := by
  rcases Subnum.total α β with h | h
  · by_cases h' : Subnum β α
    · exact Or.inr (Or.inl (Subnum.antisymm h h'))
    · exact Or.inl ⟨h, h'⟩
  · by_cases h' : Subnum α β
    · exact Or.inr (Or.inl (Subnum.antisymm h' h))
    · exact Or.inr (Or.inr ⟨h, h'⟩)

end StrictSubnum
