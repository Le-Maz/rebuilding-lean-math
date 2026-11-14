import ReMath.Function.Basic
import ReMath.Function.Pidgeonhole
import ReMath.Set.Equinum

/-- `α` is subnumerous to `β` when there is an injection from `α` into `β`. -/
structure Subnum (α β : Sort _) : Prop where
  exists_inj : ∃ f : α → β, Function.Injective f

/-- `α ≼ β` means `α` is subnumerous to `β`. -/
infix:50 " ≼ " => Subnum

namespace Subnum

/-- Every type is subnumerous to itself, via the identity. -/
@[refl]
theorem refl (α : Sort _) : α ≼ α :=
  ⟨fun x => x, fun _ _ h => h⟩

/-- Subnumerosity is transitive: compose the injections. -/
theorem trans {α β γ : Sort _}
    (h₁ : α ≼ β) (h₂ : β ≼ γ) : α ≼ γ := by
  obtain ⟨f, hf⟩ := h₁.exists_inj
  obtain ⟨g, hg⟩ := h₂.exists_inj
  exact ⟨g ∘ f, hg.comp hf⟩

/-- Enables `calc` chains over `Subnum`. -/
instance instTrans : Trans Subnum Subnum Subnum := ⟨trans⟩

/-- Equinumerous types are subnumerous: a bijection is an injection. -/
theorem of_equinum {α β : Sort _} (h : α ≈ β) : α ≼ β := by
  obtain ⟨f, hf⟩ := h.exists_bij
  exact ⟨f, hf.left⟩

/-- Subnumerosity is invariant under equinumerosity of both sides. -/
theorem congr {α₁ α₂ β₁ β₂ : Sort _}
    (hα : α₁ ≈ α₂) (hβ : β₁ ≈ β₂) : α₁ ≼ β₁ ↔ α₂ ≼ β₂ :=
  ⟨fun h => ((of_equinum hα.symm).trans h).trans (of_equinum hβ),
   fun h => ((of_equinum hα).trans h).trans (of_equinum hβ.symm)⟩

/-- Subnumerosity followed by equinumerosity is subnumerosity. -/
theorem trans_equinum {α β γ : Sort _}
    (h₁ : α ≼ β) (h₂ : β ≈ γ) : α ≼ γ :=
  h₁.trans (of_equinum h₂)

/-- Equinumerosity followed by subnumerosity is subnumerosity. -/
theorem equinum_trans {α β γ : Sort _}
    (h₁ : α ≈ β) (h₂ : β ≼ γ) : α ≼ γ :=
  (of_equinum h₁).trans h₂

/-- Enables `calc` chains of the form `α ≼ β`, `β ≈ γ`. -/
instance instTransSubnumEquinum : Trans Subnum Equinum Subnum := ⟨trans_equinum⟩

/-- Enables `calc` chains of the form `α ≈ β`, `β ≼ γ`. -/
instance instTransEquinumSubnum : Trans Equinum Subnum Subnum := ⟨equinum_trans⟩

/-- Schröder-Bernstein: mutual subnumerosity gives equinumerosity. -/
theorem antisymm {α β : Sort _}
    (h₁ : α ≼ β) (h₂ : β ≼ α) : Equinum α β := by
  obtain ⟨_, hf⟩ := h₁.exists_inj
  obtain ⟨_, hg⟩ := h₂.exists_inj
  exact Equinum.of_injective hf hg

/-- Any two types are comparable under subnumerosity. -/
theorem total (α β : Sort _) : α ≼ β ∨ β ≼ α :=
  Or.imp (fun h => ⟨h⟩) (fun h => ⟨h⟩) Function.exists_injective_or

/-- `Fin n` is subnumerous to `Fin m` whenever `n ≤ m`, via `Fin.castLE`. -/
theorem fin_to_fin {n m : Nat} (h : n ≤ m) : Fin n ≼ Fin m where
  exists_inj := ⟨Fin.castLE h, fun _ _ hxy => by
    have hxy' := congrArg Fin.val hxy
    simp [Fin.val_castLE] at hxy'
    exact Fin.val_inj.mp hxy'⟩

/-- If `Fin n` is subnumerous to `Fin m`, then `n ≤ m`. -/
theorem fin_le {n m : Nat} (h : Fin n ≼ Fin m) : n ≤ m := by
  obtain ⟨f, hf⟩ := h.exists_inj
  exact Pigeonhole.le_of_injective_fin hf

/-- `Fin n` is subnumerous to `Fin m` exactly when `n ≤ m`. -/
theorem fin_iff {n m : Nat} : Fin n ≼ Fin m ↔ n ≤ m :=
  ⟨fin_le, fin_to_fin⟩

/-- Pigeonhole principle: `Fin n` does not inject into a strictly smaller `Fin m`. -/
theorem not_fin_of_lt {n m : Nat} (h : m < n) : ¬ Fin n ≼ Fin m :=
  fun hs => Nat.not_le.mpr h (fin_le hs)

/-- `Fin n` is subnumerous to `Nat`, via `Fin.val`. -/
theorem fin_to_nat (n : Nat) : Fin n ≼ Nat where
  exists_inj := ⟨Fin.val, fun _ _ hxy => Fin.val_inj.mp hxy⟩

end Subnum

namespace Equinum

/-- Equinumerous finite ordinals have the same size. -/
theorem eq_of_fin {n m : Nat} (h : Fin n ≈ Fin m) : n = m :=
  Nat.le_antisymm
    (Subnum.fin_le (Subnum.of_equinum h))
    (Subnum.fin_le (Subnum.of_equinum (Equinum.symm h)))

/-- `Fin n` and `Fin m` are equinumerous exactly when `n = m`. -/
theorem fin_iff {n m : Nat} : Fin n ≈ Fin m ↔ n = m :=
  ⟨eq_of_fin, fun h => by subst h; exact Equinum.refl _⟩

end Equinum
