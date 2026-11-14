import ReMath.Set.Subnum

/--
`α` is strictly subnumerous to `β` when `α` is subnumerous to `β` but `β` is not subnumerous to `α`.
-/
structure StrictSubnum (α β : Sort _) : Prop where
  subnum : α ≼ β
  not_subnum : ¬ β ≼ α

/-- `α ≺ β` means `α` is strictly subnumerous to `β`. -/
infix:50 " ≺ " => StrictSubnum

namespace StrictSubnum

/-- Strict subnumerosity is irreflexive. -/
theorem irrefl (α : Sort _) : ¬ α ≺ α :=
  fun h => h.not_subnum h.subnum

/-- Strict subnumerosity is transitive. -/
theorem trans {α β γ : Sort _}
    (h₁ : α ≺ β) (h₂ : β ≺ γ) : α ≺ γ where
  subnum := h₁.subnum.trans h₂.subnum
  not_subnum := fun h => h₁.not_subnum (h₂.subnum.trans h)

/-- Enables `calc` chains over `StrictSubnum`. -/
instance instTrans : Trans StrictSubnum StrictSubnum StrictSubnum := ⟨trans⟩

/-- Strict subnumerosity is asymmetric. -/
theorem asymm {α β : Sort _} (h : α ≺ β) : ¬ β ≺ α :=
  fun h' => h.not_subnum h'.subnum

/-- A strict relation implies the non-strict one. -/
theorem le {α β : Sort _} (h : α ≺ β) : α ≼ β :=
  h.subnum

/-- Strict then non-strict subnumerosity gives strict subnumerosity. -/
theorem trans_subnum {α β γ : Sort _}
    (h₁ : α ≺ β) (h₂ : β ≼ γ) : α ≺ γ where
  subnum := h₁.subnum.trans h₂
  not_subnum := fun h => h₁.not_subnum (h₂.trans h)

/-- Enables `calc` chains of the form `α ≺ β`, `β ≼ γ`. -/
instance instTransStrictSubnum : Trans StrictSubnum Subnum StrictSubnum :=
  ⟨trans_subnum⟩

/-- Non-strict then strict subnumerosity gives strict subnumerosity. -/
theorem subnum_trans {α β γ : Sort _}
    (h₁ : α ≼ β) (h₂ : β ≺ γ) : α ≺ γ where
  subnum := h₁.trans h₂.subnum
  not_subnum := fun h => h₂.not_subnum (h.trans h₁)

/-- Enables `calc` chains of the form `α ≼ β`, `β ≺ γ`. -/
instance instTransSubnumStrict : Trans Subnum StrictSubnum StrictSubnum :=
  ⟨subnum_trans⟩

/-- Strict subnumerosity is invariant under equinumerosity of both sides. -/
theorem congr {α₁ α₂ β₁ β₂ : Sort _}
    (hα : α₁ ≈ α₂) (hβ : β₁ ≈ β₂) :
    α₁ ≺ β₁ ↔ α₂ ≺ β₂ :=
  ⟨fun h => ⟨(Subnum.congr hα hβ).mp h.subnum,
             fun h' => h.not_subnum ((Subnum.congr hβ hα).mpr h')⟩,
   fun h => ⟨(Subnum.congr hα hβ).mpr h.subnum,
             fun h' => h.not_subnum ((Subnum.congr hβ hα).mp h')⟩⟩

/-- Strict subnumerosity followed by equinumerosity is strict subnumerosity. -/
theorem trans_equinum {α β γ : Sort _}
    (h₁ : α ≺ β) (h₂ : β ≈ γ) : α ≺ γ :=
  (congr (Equinum.refl α) h₂).mp h₁

/-- Equinumerosity followed by strict subnumerosity is strict subnumerosity. -/
theorem equinum_trans {α β γ : Sort _}
    (h₁ : α ≈ β) (h₂ : β ≺ γ) : α ≺ γ :=
  (congr h₁ (Equinum.refl γ)).mpr h₂

/-- Enables `calc` chains of the form `α ≺ β`, `β ≈ γ`. -/
instance instTransStrictSubnumEquinum : Trans StrictSubnum Equinum StrictSubnum :=
  ⟨trans_equinum⟩

/-- Enables `calc` chains of the form `α ≈ β`, `β ≺ γ`. -/
instance instTransEquinumStrictSubnum : Trans Equinum StrictSubnum StrictSubnum :=
  ⟨equinum_trans⟩

/-- Strict subnumerosity is exactly subnumerosity without equinumerosity. -/
theorem iff_subnum_not_equinum {α β : Sort _} :
    α ≺ β ↔ α ≼ β ∧ ¬ α ≈ β :=
  ⟨fun h => ⟨h.subnum, fun he => h.not_subnum (Subnum.of_equinum (Equinum.symm he))⟩,
   fun ⟨h₁, h₂⟩ => ⟨h₁, fun h₃ => h₂ (Subnum.antisymm h₁ h₃)⟩⟩

/-- Strictly subnumerous types are not equinumerous. -/
theorem not_equinum {α β : Sort _} (h : α ≺ β) : ¬ α ≈ β :=
  fun he => h.not_subnum (Subnum.of_equinum (Equinum.symm he))

/-- Strictly subnumerous types are distinct. -/
theorem ne {α β : Sort _} (h : α ≺ β) : α ≠ β := by
  intro he
  subst he
  exact irrefl _ h

/-- If `α` is not subnumerous to `β`, then `β` is strictly subnumerous to `α`. -/
theorem of_not_subnum {α β : Sort _} (h : ¬ α ≼ β) : β ≺ α where
  subnum := (Subnum.total α β).resolve_left h
  not_subnum := h

/-- `α` is not subnumerous to `β` exactly when `β` is strictly subnumerous to `α`. -/
theorem not_subnum_iff {α β : Sort _} : ¬ α ≼ β ↔ β ≺ α :=
  ⟨of_not_subnum, fun h => h.not_subnum⟩

/-- Trichotomy: any two types are strictly ordered one way or the other, or equinumerous. -/
theorem trichotomy (α β : Sort _) :
    α ≺ β ∨ α ≈ β ∨ β ≺ α := by
  rcases Subnum.total α β with h | h
  · by_cases h' : β ≼ α
    · exact Or.inr (Or.inl (Subnum.antisymm h h'))
    · exact Or.inl ⟨h, h'⟩
  · by_cases h' : α ≼ β
    · exact Or.inr (Or.inl (Subnum.antisymm h' h))
    · exact Or.inr (Or.inr ⟨h, h'⟩)

/-- `Fin n` is strictly subnumerous to `Fin m` whenever `n < m`. -/
theorem fin_to_fin {n m : Nat} (h : n < m) : Fin n ≺ Fin m :=
  StrictSubnum.of_not_subnum (Subnum.not_fin_of_lt h)

/-- `Fin n` is strictly subnumerous to `Fin m` exactly when `n < m`. -/
theorem fin_iff {n m : Nat} : Fin n ≺ Fin m ↔ n < m :=
  ⟨fun h => Nat.lt_of_not_le fun hle =>
      StrictSubnum.not_subnum h (Subnum.fin_iff.mpr hle),
    fin_to_fin⟩

/-- `Fin n` is strictly subnumerous to `Nat`, as it sits strictly below `Fin (n + 1)`. -/
theorem fin_to_nat (n : Nat) : Fin n ≺ Nat :=
  calc Fin n
    _ ≺ Fin (n + 1) := fin_to_fin (Nat.lt_add_one n)
    _ ≼ Nat := Subnum.fin_to_nat (n + 1)

end StrictSubnum
