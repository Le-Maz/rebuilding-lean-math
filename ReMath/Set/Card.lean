import ReMath.Function.Bijective
import ReMath.Set.Equinum

/-- The class of type cardinalities -/
def Cardinality.{u} : Type u := Quotient Equinum.setoid.{u}

namespace Cardinality

/-- The cardinality of a type, as its equinumerosity class. -/
def mk.{u} : Sort u → Cardinality.{u} := Quotient.mk Equinum.setoid

/-- `x ≤ y` for cardinalities: some representative of `x` injects into one of `y`. -/
def le (x y : Cardinality) : Prop :=
  x.liftOn₂ y (fun α β => ∃ f : α → β, Function.Injective f) <| by
    intro α₁ β₁ α₂ β₂ hα hβ
    have hα : Equinum α₁ α₂ := hα
    have hβ : Equinum β₁ β₂ := hβ
    obtain ⟨e, he⟩ := hα.exists_bij
    obtain ⟨e', he'⟩ := hα.symm.exists_bij
    obtain ⟨k, hk⟩ := hβ.exists_bij
    obtain ⟨k', hk'⟩ := hβ.symm.exists_bij
    apply propext
    constructor
    · rintro ⟨f, hf⟩
      exact ⟨k ∘ f ∘ e', hk.left.comp (hf.comp he'.left)⟩
    · rintro ⟨f, hf⟩
      exact ⟨k' ∘ f ∘ e, hk'.left.comp (hf.comp he.left)⟩

/-- Enables the `≤` notation on cardinalities. -/
instance instLE : LE Cardinality := ⟨le⟩

/-- For types `α` and `β`, `mk α ≤ mk β` iff there is an injection `α → β`. -/
theorem mk_le_mk_iff {α β : Sort _} :
    mk α ≤ mk β ↔ ∃ f : α → β, Function.Injective f :=
  Iff.rfl

/-- `≤` on cardinalities is reflexive. -/
@[refl]
theorem le_refl (x : Cardinality) : x ≤ x :=
  Quotient.inductionOn x fun α =>
    show ∃ f : α → α, Function.Injective f from
      ⟨fun x => x, fun _ _ h => h⟩

/-- `≤` on cardinalities is transitive: compose the injections. -/
theorem le_trans (x y z : Cardinality) : x ≤ y → y ≤ z → x ≤ z :=
  Quotient.inductionOn₃ x y z fun α β γ =>
    show (∃ f : α → β, Function.Injective f) →
        (∃ f : β → γ, Function.Injective f) →
        ∃ f : α → γ, Function.Injective f from
      fun ⟨f, hf⟩ ⟨g, hg⟩ => ⟨g ∘ f, hg.comp hf⟩

/-- Enables `calc` chains over `le`. -/
instance instTransLe : Trans le le le := ⟨le_trans _ _ _⟩

/-- `≤` on cardinalities is antisymmetric; this is Schröder-Bernstein. -/
theorem le_antisymm (x y : Cardinality) : x ≤ y → y ≤ x → x = y :=
  Quotient.inductionOn₂ x y fun α β =>
    show (∃ f : α → β, Function.Injective f) →
        (∃ g : β → α, Function.Injective g) →
        mk α = mk β from
      fun ⟨_, hf⟩ ⟨_, hg⟩ => Quotient.sound (Equinum.of_injective hf hg)

/-- Any two cardinalities are comparable. -/
theorem le_total (x y : Cardinality) : x ≤ y ∨ y ≤ x :=
  Quotient.inductionOn₂ x y fun α β =>
    show (∃ f : α → β, Function.Injective f) ∨ (∃ g : β → α, Function.Injective g) from
      Function.exists_injective_or

/-- `≤` on cardinalities is a preorder. -/
instance instIsPreorder : Std.IsPreorder Cardinality where
  le_refl := le_refl
  le_trans := le_trans

/-- `≤` on cardinalities is a partial order. -/
instance instIsPartialOrder : Std.IsPartialOrder Cardinality where
  le_antisymm := le_antisymm

/-- `≤` on cardinalities is a linear order. -/
instance instIsLinearOrder : Std.IsLinearOrder Cardinality where
  le_total := le_total

end Cardinality
