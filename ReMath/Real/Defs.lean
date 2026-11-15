import ReMath.Rat.Lemmas
import ReMath.Real.CauchySeq

def Real := Quotient CauchySeq.instSetoid

namespace Real

def mk := Quotient.mk CauchySeq.instSetoid

def ofRat (x : Rat) : Real := mk <| CauchySeq.ofRat x

instance instIntCast : IntCast Real where
  intCast z := ofRat z

instance instNatCast : NatCast Real where
  natCast n := ofRat n

instance instOfNat (n : Nat) : OfNat Real n := ⟨ofRat n⟩

instance instZero : Zero Real := ⟨ofRat 0⟩

instance instAdd : Add Real where
  add x y := x.liftOn₂ y (mk <| · + ·) <| by
    intro a₁ b₁ a₂ b₂ ha hb
    apply Quotient.sound
    exact CauchySeq.add_equiv ha hb

instance instNeg : Neg Real where
  neg x := x.liftOn (mk <| -·) <| by
    intro a b h
    apply Quotient.sound
    exact CauchySeq.neg_equiv h

instance instOne : One Real := ⟨ofRat 1⟩

instance instMul : Mul Real where
  mul x y := x.liftOn₂ y (mk <| · * ·) <| by
    intro a₁ b₁ a₂ b₂ ha hb
    apply Quotient.sound
    exact CauchySeq.mul_equiv ha hb

/-- Inversion of reals. The inverse of zero is zero. -/
noncomputable instance instInv : Inv Real where
  inv x := x.liftOn (mk <| ·⁻¹) <| by
    intro a b h
    apply Quotient.sound
    exact CauchySeq.inv_equiv h

instance instSub : Sub Real where
  sub a b := a + -b

/-- Division of reals, defined as multiplication by the inverse. -/
noncomputable instance instDiv : Div Real where
  div x y := x * y⁻¹

end Real
