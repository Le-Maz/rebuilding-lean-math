import ReMath.Set.Equinum
import ReMath.Set.Subnum

/-- The class of type cardinalities -/
def Cardinality.{u} : Type u := Quotient Equinum.setoid.{u}

namespace Cardinality

/-- The cardinality of a type, as its equinumerosity class. -/
def mk.{u} : Sort u → Cardinality.{u} := Quotient.mk Equinum.setoid

/-- `x ≤ y` for cardinalities: some representative of `x` is subnumerous to one of `y`. -/
def le (a b : Cardinality) : Prop :=
  a.liftOn₂ b Subnum <| by
    intro α₁ β₁ α₂ β₂ hα hβ
    exact propext (Subnum.congr hα hβ)

/-- Enables the `≤` notation on cardinalities. -/
instance instLE : LE Cardinality := ⟨le⟩

/-- For types `α` and `β`, `mk α ≤ mk β` iff `α` is subnumerous to `β`. -/
theorem mk_le_mk_iff {α β : Sort _} : mk α ≤ mk β ↔ Subnum α β := Iff.rfl

/-- For types `α` and `β`, `mk α ≤ mk β` iff there is an injection `α → β`. -/
theorem mk_le_mk_iff_exists_injective {α β : Sort _} :
    mk α ≤ mk β ↔ ∃ f : α → β, Function.Injective f :=
  ⟨fun h => Subnum.exists_inj (self := h), fun h => ⟨h⟩⟩

/-- `≤` on cardinalities is reflexive. -/
@[refl]
theorem le_refl (x : Cardinality) : x ≤ x :=
  Quotient.inductionOn x fun α => show Subnum α α from Subnum.refl α

/-- `≤` on cardinalities is transitive. -/
theorem le_trans (x y z : Cardinality) : x ≤ y → y ≤ z → x ≤ z :=
  Quotient.inductionOn₃ x y z fun α β γ =>
    show Subnum α β → Subnum β γ → Subnum α γ from Subnum.trans

/-- `≤` on cardinalities is antisymmetric; this is Schröder-Bernstein. -/
theorem le_antisymm (x y : Cardinality) : x ≤ y → y ≤ x → x = y :=
  Quotient.inductionOn₂ x y fun α β =>
    show Subnum α β → Subnum β α → mk α = mk β from
      fun h₁ h₂ => Quotient.sound (Subnum.antisymm h₁ h₂)

/-- Any two cardinalities are comparable. -/
theorem le_total (x y : Cardinality) : x ≤ y ∨ y ≤ x :=
  Quotient.inductionOn₂ x y fun α β =>
    show Subnum α β ∨ Subnum β α from Subnum.total α β

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

/-- The cardinality `0`, represented by the empty type. -/
instance instZero : Zero Cardinality where
  zero := mk PEmpty

/-- Addition of cardinalities, as the cardinality of the sum type. -/
instance instAdd.{u} : Add Cardinality.{max 1 u} where
  add a b := a.liftOn₂ b (fun α β => mk <| α ⊕' β) <| by
    intro α₁ β₁ α₂ β₂ hα hβ
    apply Quotient.sound
    change Equinum α₁ α₂ at hα
    change Equinum β₁ β₂ at hβ
    let ⟨f, hf⟩ := hα.exists_bij
    let ⟨g, hg⟩ := hβ.exists_bij
    let F : (α₁ ⊕' β₁) → (α₂ ⊕' β₂)
      | .inl l => .inl (f l)
      | .inr r => .inr (g r)
    refine ⟨F, ?_⟩
    constructor
    · intro x₁ x₂ h
      subst F
      cases x₁ <;> cases x₂ <;> simp at h ⊢
      · rw [hf.left.eq_iff] at h
        exact h
      · rw [hg.left.eq_iff] at h
        exact h
    · intro y
      cases y with
      | inl l =>
        obtain ⟨a, ha⟩ := hf.right l
        exact ⟨.inl a, by show PSum.inl (f a) = PSum.inl l; rw [ha]⟩
      | inr r =>
        obtain ⟨b, hb⟩ := hg.right r
        exact ⟨.inr b, by show PSum.inr (g b) = PSum.inr r; rw [hb]⟩

/-- Multiplication of a cardinality by a natural number as a repeated sum. -/
instance instSMulNat : SMul Nat Cardinality := ⟨nsmulRec⟩

/-- The cardinality `1`, represented by the unit type. -/
instance instOne : One Cardinality where
  one := mk PUnit

/-- Multiplication of cardinalities, as the cardinality of the product type. -/
instance instMul.{u} : Mul Cardinality.{max 1 u} where
  mul a b := a.liftOn₂ b (fun α β => mk <| α ×' β) <| by
    intro α₁ β₁ α₂ β₂ hα hβ
    apply Quotient.sound
    change Equinum α₁ α₂ at hα
    change Equinum β₁ β₂ at hβ
    let ⟨f, hf⟩ := hα.exists_bij
    let ⟨g, hg⟩ := hβ.exists_bij
    let F : (α₁ ×' β₁) → (α₂ ×' β₂) := fun p => ⟨f p.1, g p.2⟩
    refine ⟨F, ?_⟩
    constructor
    · intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
      have h₁ : f a₁ = f a₂ := congrArg PProd.fst h
      have h₂ : g b₁ = g b₂ := congrArg PProd.snd h
      obtain rfl := hf.left h₁
      obtain rfl := hg.left h₂
      rfl
    · intro ⟨a, b⟩
      obtain ⟨x, hx⟩ := hf.right a
      obtain ⟨y, hy⟩ := hg.right b
      exact ⟨⟨x, y⟩, by show PProd.mk (f x) (g y) = PProd.mk a b; rw [hx, hy]⟩

/-- Exponentiation of a cardinality by a natural number as a repeated product. -/
instance instNPow : Pow Cardinality Nat := ⟨fun a n => npowRec n a⟩

/-- Exponentiation of cardinalities, as the cardinality of the function type. -/
instance instPow.{u} : Pow Cardinality.{max 1 u} Cardinality.{max 1 u} where
  pow a b := a.liftOn₂ b (fun α β => mk <| β → α) <| by
    intro α₁ β₁ α₂ β₂ hα hβ
    apply Quotient.sound
    change Equinum α₁ α₂ at hα
    change Equinum β₁ β₂ at hβ
    obtain ⟨f, hf⟩ := hα.exists_bij
    obtain ⟨g, hg⟩ := hβ.exists_bij
    let f' : α₂ → α₁ := fun a => Classical.choose (hf.right a)
    let g' : β₂ → β₁ := fun b => Classical.choose (hg.right b)
    have hf' : ∀ a, f (f' a) = a := fun a => Classical.choose_spec (hf.right a)
    have hg' : ∀ b, g (g' b) = b := fun b => Classical.choose_spec (hg.right b)
    let F : (β₁ → α₁) → (β₂ → α₂) := fun k b => f (k (g' b))
    have key : ∀ (k : β₁ → α₁) (x : β₁), F k (g x) = f (k x) := by
      intro k x
      show f (k (g' (g x))) = f (k x)
      rw [hg.left (hg' (g x))]
    refine ⟨F, ?_⟩
    constructor
    · intro k₁ k₂ h
      funext x
      have e := congrFun h (g x)
      rw [key, key] at e
      exact hf.left e
    · intro y
      refine ⟨fun x => f' (y (g x)), ?_⟩
      funext b
      show f (f' (y (g (g' b)))) = y b
      rw [hf', hg']

end Cardinality
