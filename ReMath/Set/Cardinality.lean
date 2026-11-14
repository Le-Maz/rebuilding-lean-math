import ReMath.Set.Equinum
import ReMath.Set.Subnum
import ReMath.Set.StrictSubnum

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

/-- Enables `calc` chains of the form `x ≤ y`, `y ≤ z`. -/
instance instTransLe : Trans (· ≤ · : Cardinality → Cardinality → Prop) (· ≤ ·) (· ≤ ·) :=
  ⟨le_trans _ _ _⟩

/-- `≤` on cardinalities is antisymmetric; this is Schröder-Bernstein. -/
theorem le_antisymm (x y : Cardinality) : x ≤ y → y ≤ x → x = y :=
  Quotient.inductionOn₂ x y fun α β =>
    show Subnum α β → Subnum β α → mk α = mk β from
      fun h₁ h₂ => Quotient.sound (Subnum.antisymm h₁ h₂)

/-- `≤` on cardinalities is antisymmetric, as an instance of `Std.Antisymm`. -/
instance instAntisymmLe : Std.Antisymm (· ≤ · : Cardinality → Cardinality → Prop) :=
  ⟨le_antisymm⟩

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

/-- `x < y` for cardinalities: some representative of `x` is strictly subnumerous to one of `y`. -/
def lt (a b : Cardinality) : Prop :=
  a.liftOn₂ b StrictSubnum <| by
    intro α₁ β₁ α₂ β₂ hα hβ
    exact propext (StrictSubnum.congr hα hβ)

/-- Enables the `<` notation on cardinalities. -/
instance instLT : LT Cardinality := ⟨lt⟩

/-- For types `α` and `β`, `mk α < mk β` iff `α` is strictly subnumerous to `β`. -/
theorem mk_lt_mk_iff {α β : Sort _} : mk α < mk β ↔ StrictSubnum α β := Iff.rfl

/-- `x < y` iff `x ≤ y` and not `y ≤ x`. -/
theorem lt_iff_le_not_ge (x y : Cardinality) : x < y ↔ x ≤ y ∧ ¬ y ≤ x :=
  Quotient.inductionOn₂ x y fun α β =>
    show StrictSubnum α β ↔ Subnum α β ∧ ¬ Subnum β α from
      ⟨fun h => ⟨h.subnum, h.not_subnum⟩, fun h => ⟨h.1, h.2⟩⟩

/-- `<` on cardinalities is irreflexive. -/
theorem lt_irrefl (x : Cardinality) : ¬ x < x :=
  Quotient.inductionOn x fun α => show ¬ StrictSubnum α α from StrictSubnum.irrefl α

/-- `<` on cardinalities is transitive. -/
theorem lt_trans (x y z : Cardinality) : x < y → y < z → x < z :=
  Quotient.inductionOn₃ x y z fun α β γ =>
    show StrictSubnum α β → StrictSubnum β γ → StrictSubnum α γ from StrictSubnum.trans

/-- `<` on cardinalities is asymmetric. -/
theorem lt_asymm (x y : Cardinality) : x < y → ¬ y < x :=
  fun h h' => lt_irrefl x (lt_trans x y x h h')

/-- A strict inequality implies the non-strict one. -/
theorem le_of_lt {x y : Cardinality} (h : x < y) : x ≤ y :=
  ((lt_iff_le_not_ge x y).mp h).1

/-- A strict inequality rules out the reverse non-strict one. -/
theorem not_le_of_lt {x y : Cardinality} (h : x < y) : ¬ y ≤ x :=
  ((lt_iff_le_not_ge x y).mp h).2

/-- `x < y` and `y ≤ z` give `x < z`. -/
theorem lt_of_lt_of_le {x y z : Cardinality} (h₁ : x < y) (h₂ : y ≤ z) : x < z :=
  (lt_iff_le_not_ge x z).mpr
    ⟨le_trans x y z (le_of_lt h₁) h₂, fun h => not_le_of_lt h₁ (le_trans y z x h₂ h)⟩

/-- `x ≤ y` and `y < z` give `x < z`. -/
theorem lt_of_le_of_lt {x y z : Cardinality} (h₁ : x ≤ y) (h₂ : y < z) : x < z :=
  (lt_iff_le_not_ge x z).mpr
    ⟨le_trans x y z h₁ (le_of_lt h₂), fun h => not_le_of_lt h₂ (le_trans z x y h h₁)⟩

/-- Enables `calc` chains of the form `x < y`, `y < z`. -/
instance instTransLtLt : Trans (· < · : Cardinality → Cardinality → Prop) (· < ·) (· < ·) :=
  ⟨fun h₁ h₂ => lt_trans _ _ _ h₁ h₂⟩

/-- Enables `calc` chains of the form `x < y`, `y ≤ z`. -/
instance instTransLtLe : Trans (· < · : Cardinality → Cardinality → Prop) (· ≤ ·) (· < ·) :=
  ⟨lt_of_lt_of_le⟩

/-- Enables `calc` chains of the form `x ≤ y`, `y < z`. -/
instance instTransLeLt : Trans (· ≤ · : Cardinality → Cardinality → Prop) (· < ·) (· < ·) :=
  ⟨lt_of_le_of_lt⟩

/-- `x < y` iff `x ≤ y` and `x ≠ y`. -/
theorem lt_iff_le_and_ne (x y : Cardinality) : x < y ↔ x ≤ y ∧ x ≠ y :=
  ⟨fun h => ⟨le_of_lt h, fun e => lt_irrefl y (e ▸ h)⟩,
   fun ⟨h₁, h₂⟩ => (lt_iff_le_not_ge x y).mpr
     ⟨h₁, fun h => h₂ (le_antisymm x y h₁ h)⟩⟩

/-- A strict inequality implies the cardinalities are distinct. -/
theorem ne_of_lt {x y : Cardinality} (h : x < y) : x ≠ y :=
  ((lt_iff_le_and_ne x y).mp h).2

/-- Trichotomy: any two cardinalities satisfy exactly one of `<`, `=`, `>`. -/
theorem lt_trichotomy (x y : Cardinality) : x < y ∨ x = y ∨ y < x :=
  Quotient.inductionOn₂ x y fun α β => by
    rcases StrictSubnum.trichotomy α β with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (Quotient.sound h))
    · exact Or.inr (Or.inr h)

/-- `x ≤ y` iff `x < y` or `x = y`. -/
theorem le_iff_lt_or_eq (x y : Cardinality) : x ≤ y ↔ x < y ∨ x = y :=
  ⟨fun h => (lt_trichotomy x y).elim Or.inl fun h' =>
      h'.elim Or.inr fun h'' => absurd h (not_le_of_lt h''),
   fun h => h.elim le_of_lt fun e => e ▸ le_refl x⟩

/-- `¬ x < y` iff `y ≤ x`. -/
theorem not_lt (x y : Cardinality) : ¬ x < y ↔ y ≤ x :=
  ⟨fun h => (le_total x y).elim
      (fun h' => (le_iff_lt_or_eq x y).mp h' |>.elim (fun l => absurd l h)
        fun e => e ▸ le_refl x)
      id,
   fun h l => not_le_of_lt l h⟩

/-- `<` on cardinalities is determined by `≤`. -/
instance instLawfulOrderLT : Std.LawfulOrderLT Cardinality where
  lt_iff := lt_iff_le_not_ge

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
