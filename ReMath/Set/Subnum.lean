import ReMath.Function.Basic
import ReMath.Set.Equinum

/-- `α` is subnumerous to `β` when there is an injection from `α` into `β`. -/
class Subnum (α β : Sort _) : Prop where
  exists_inj : ∃ f : α → β, Function.Injective f

namespace Subnum

/-- Every type is subnumerous to itself, via the identity. -/
@[refl]
theorem refl (α : Sort _) : Subnum α α :=
  ⟨fun x => x, fun _ _ h => h⟩

/-- Subnumerosity is transitive: compose the injections. -/
theorem trans {α β γ : Sort _}
    (h₁ : Subnum α β) (h₂ : Subnum β γ) : Subnum α γ := by
  obtain ⟨f, hf⟩ := h₁.exists_inj
  obtain ⟨g, hg⟩ := h₂.exists_inj
  exact ⟨g ∘ f, hg.comp hf⟩

/-- Enables `calc` chains over `Subnum`. -/
instance instTrans : Trans Subnum Subnum Subnum := ⟨trans⟩

/-- Equinumerous types are subnumerous: a bijection is an injection. -/
theorem of_equinum {α β : Sort _} (h : Equinum α β) : Subnum α β := by
  obtain ⟨f, hf⟩ := h.exists_bij
  exact ⟨f, hf.left⟩

/-- Subnumerosity is invariant under equinumerosity of both sides. -/
theorem congr {α₁ α₂ β₁ β₂ : Sort _}
    (hα : Equinum α₁ α₂) (hβ : Equinum β₁ β₂) : Subnum α₁ β₁ ↔ Subnum α₂ β₂ :=
  ⟨fun h => ((of_equinum hα.symm).trans h).trans (of_equinum hβ),
   fun h => ((of_equinum hα).trans h).trans (of_equinum hβ.symm)⟩

/-- Schröder-Bernstein: mutual subnumerosity gives equinumerosity. -/
theorem antisymm {α β : Sort _}
    (h₁ : Subnum α β) (h₂ : Subnum β α) : Equinum α β := by
  obtain ⟨_, hf⟩ := h₁.exists_inj
  obtain ⟨_, hg⟩ := h₂.exists_inj
  exact Equinum.of_injective hf hg

/-- Any two types are comparable under subnumerosity. -/
theorem total (α β : Sort _) : Subnum α β ∨ Subnum β α :=
  Or.imp (fun h => ⟨h⟩) (fun h => ⟨h⟩) Function.exists_injective_or

end Subnum
