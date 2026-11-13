import ReMath.Alg.Defs
import ReMath.Alg.Lemmas

namespace Alg

structure Ideal (R : Type _) [Semiring R] where
  carrier : R → Prop
  zero_mem : carrier 0
  add_mem : ∀ {a b}, carrier a → carrier b → carrier (a + b)
  mul_mem_left : ∀ (r : R) {a}, carrier a → carrier (r * a)
  mul_mem_right : ∀ (r : R) {a}, carrier a → carrier (a * r)

@[ext]
theorem Ideal.ext {R} [Semiring R]
    {I J : Ideal R}
    (h : ∀ x, I.carrier x ↔ J.carrier x) :
    I = J := by
  cases I with | mk ic iz ia iml imr
  cases J with | mk jc jz ja jml jmr
  congr
  funext x
  exact propext (h x)

instance {R} [Semiring R] : LE (Ideal R) where
  le I J := ∀ x, I.carrier x → J.carrier x

theorem Ideal.le_refl {R} [Semiring R] (I : Ideal R) :
    I ≤ I := by
  intro x hx
  exact hx

theorem Ideal.le_trans {R} [Semiring R]
    {I J K : Ideal R} (h₁ : I ≤ J) (h₂ : J ≤ K) :
    I ≤ K := by
  intro x hx
  exact h₂ x (h₁ x hx)

theorem Ideal.le_antisymm {R} [Semiring R]
    {I J : Ideal R} (h₁ : I ≤ J) (h₂ : J ≤ I) :
    I = J := by
  ext x
  exact ⟨h₁ x, h₂ x⟩

instance {R} [Semiring R] : Std.IsPartialOrder (Ideal R) where
  le_refl := Ideal.le_refl
  le_trans _ _ _ := Ideal.le_trans
  le_antisymm _ _ := Ideal.le_antisymm

def Ideal.top {R} [Semiring R] : Ideal R where
  carrier := fun _ => True
  zero_mem := trivial
  add_mem := fun _ _ => trivial
  mul_mem_left := fun _ _ _ => trivial
  mul_mem_right := fun _ _ _ => trivial

def Ideal.bot {R} [Semiring R] : Ideal R where
  carrier := fun x => x = 0
  zero_mem := rfl
  add_mem := by
    intro a b ha hb
    simp [ha, hb]
  mul_mem_left := by
    intro r a ha
    simp [ha]
  mul_mem_right := by
    intro r a ha
    simp [ha]

def Ideal.BourneRel {R} [Semiring R] (I : Ideal R) (a b : R) : Prop :=
  ∃ x y, I.carrier x ∧ I.carrier y ∧ a + x = b + y

def Ideal.SubRel {R} [Ring R] (I : Ideal R) (a b : R) : Prop :=
  I.carrier (a - b)

theorem Ideal.bourneRel_iseqv {R} [Semiring R] (I : Ideal R) :
    Equivalence I.BourneRel where
  refl a := by
    exact ⟨0, 0, I.zero_mem, I.zero_mem, rfl⟩
  symm {a b} hab := by
    obtain ⟨x, y, hx, hy, hxy⟩ := hab
    exact ⟨y, x, hy, hx, hxy.symm⟩
  trans {a b c} hab hbc := by
    obtain ⟨x, y, hx, hy, hxy⟩ := hab
    obtain ⟨u, v, hu, hv, huv⟩ := hbc
    refine ⟨x + u, v + y, ?_⟩
    refine ⟨I.add_mem hx hu, I.add_mem hv hy, ?_⟩
    calc a + (x + u)
      _ = (a + x) + u := by simp [add_assoc]
      _ = (b + y) + u := by rw [hxy]
      _ = (b + u) + y := by ac_rfl
      _ = (c + v) + y := by rw [huv]
      _ = c + (v + y) := by simp [add_assoc]

theorem Ideal.neg_mem {R} [Ring R] (I : Ideal R) {a : R} (h : I.carrier a) : I.carrier (-a) := by
  have : -a = (-1) * a := by simp [neg_mul]
  exact this ▸ I.mul_mem_left (-1) h

theorem Ideal.subRel_eq_bourneRel {R} [Ring R] (I : Ideal R) : I.SubRel = I.BourneRel := by
  ext a b
  constructor
  · intro h
    refine ⟨0, a - b, I.zero_mem, h, ?_⟩
    calc a + 0
      _ = a + (-b + b) := by simp [neg_add_cancel]
      _ = b + (a + -b) := by ac_rfl
      _ = b + (a - b) := by simp [sub_eq_add_neg]
  · intro h
    obtain ⟨x, y, hx, hy, heq⟩ := h
    unfold Ideal.SubRel
    have : a - b = y - x := sub_eq_sub_iff a b y x |>.mpr heq
    rw [this, sub_eq_add_neg]
    exact I.add_mem hy (I.neg_mem hx)

def Ideal.setoid {R} [Semiring R] (I : Ideal R) : Setoid R where
  r := I.BourneRel
  iseqv := I.bourneRel_iseqv

def Ideal.IsProper {R} [Semiring R] (I : Ideal R) : Prop :=
  ¬ I.carrier 1

def Ideal.IsMaximal {R} [Semiring R] (I : Ideal R) : Prop :=
  I.IsProper ∧
  ∀ J : Ideal R, I ≤ J → J = I ∨ J = Ideal.top

def Ideal.Quot {R} [Semiring R] (I : Ideal R) : Type _ := Quotient I.setoid
def Ideal.mkQuot {R} [Semiring R] (I : Ideal R) : R → I.Quot := Quotient.mk I.setoid

instance {R} [Semiring R] (I : Ideal R) : Zero I.Quot where
  zero := I.mkQuot 0

instance {R} [Semiring R] (I : Ideal R) : One I.Quot where
  one := I.mkQuot 1

instance {R} [Semiring R] (I : Ideal R) : Add I.Quot where
  add x y :=
    x.liftOn₂ y (fun a b => Ideal.mkQuot I (a + b)) <| by
      intro a b c d hac hbd
      apply Quotient.sound
      obtain ⟨x, y, hx, hy, hxy⟩ := hac
      obtain ⟨u, v, hu, hv, huv⟩ := hbd
      refine ⟨x + u, y + v, ?_⟩
      refine ⟨I.add_mem hx hu, I.add_mem hy hv, ?_⟩
      calc a + b + (x + u)
        _ = (a + x) + (b + u) := by ac_rfl
        _ = (c + y) + (d + v) := by rw [hxy, huv]
        _ = (c + d) + (y + v) := by ac_rfl

instance {R} [Semiring R] (I : Ideal R) : NatCast I.Quot where
  natCast n := I.mkQuot (↑n)

theorem Ideal.nsmul_mem {R} [Semiring R] (I : Ideal R)
    {x : R} (hx : I.carrier x) (n : Nat) :
    I.carrier (n • x) := by
  induction n with
  | zero =>
    simpa using I.zero_mem
  | succ n ih =>
    rw [succ_nsmul]
    exact I.add_mem ih hx

theorem Ideal.zsmul_mem {R} [Ring R] (I : Ideal R)
    {x : R} (hx : I.carrier x) (z : Int) :
    I.carrier (z • x) := by
  cases z with
  | ofNat n =>
    simp only [ofNat_zsmul]
    exact I.nsmul_mem hx n
  | negSucc n =>
    rw [negSucc_zsmul]
    exact I.neg_mem (I.nsmul_mem hx (n + 1))

instance {R} [Semiring R] (I : Ideal R) : NSMul I.Quot where
  nsmul := ⟨fun n => Quotient.lift (fun x => I.mkQuot (n • x)) (by
    intro a b hab
    apply Quotient.sound
    obtain ⟨x, y, hx, hy, hxy⟩ := hab
    refine ⟨n • x, n • y, ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · exact I.nsmul_mem hx n
    · exact I.nsmul_mem hy n
    · rw [← nsmul_add, ← nsmul_add, hxy])⟩

instance {R} [Ring R] (I : Ideal R) : ZSMul I.Quot where
  zsmul := ⟨fun z => Quotient.lift (fun x => I.mkQuot (z • x)) (by
    intro a b hab
    apply Quotient.sound
    obtain ⟨x, y, hx, hy, hxy⟩ := hab
    refine ⟨z • x, z • y, ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · exact I.zsmul_mem hx z
    · exact I.zsmul_mem hy z
    · rw [← zsmul_add, ← zsmul_add, hxy])⟩

instance {R} [Semiring R] (I : Ideal R) : Mul I.Quot where
  mul x y :=
    x.liftOn₂ y (fun a b => Ideal.mkQuot I (a * b)) <| by
      intro a b c d hac hbd
      apply Quotient.sound
      obtain ⟨x, y, hx, hy, hxy⟩ := hac
      obtain ⟨u, v, hu, hv, huv⟩ := hbd
      refine ⟨x * b + c * u, c * v + y * b, ?_⟩
      refine ⟨I.add_mem (I.mul_mem_right b hx) (I.mul_mem_left c hu), ?_⟩
      refine ⟨I.add_mem (I.mul_mem_left c hv) (I.mul_mem_right b hy), ?_⟩
      calc a * b + (x * b + c * u)
        _ = (a * b + x * b) + c * u := by simp [add_assoc]
        _ = (a + x) * b + c * u := by rw [← add_mul]
        _ = (c + y) * b + c * u := by rw [hxy]
        _ = (c * b + y * b) + c * u := by rw [add_mul]
        _ = (c * b + c * u) + y * b := by ac_rfl
        _ = c * (b + u) + y * b := by rw [← mul_add]
        _ = c * (d + v) + y * b := by rw [huv]
        _ = (c * d + c * v) + y * b := by rw [mul_add]
        _ = c * d + (c * v + y * b) := by simp [add_assoc]

instance {R} [Semiring R] (I : Ideal R) : Pow I.Quot Nat where
  pow a n := Nat.rec 1 (fun _ b => b * a) n

instance {R} [Ring R] (I : Ideal R) : Neg I.Quot where
  neg x :=
    x.liftOn (fun a => I.mkQuot (-a)) <| by
      intro a b hab
      apply Quotient.sound
      obtain ⟨x, y, hx, hy, hxy⟩ := hab
      refine ⟨-x, -y, ?_⟩
      refine ⟨I.neg_mem hx, I.neg_mem hy, ?_⟩
      calc -a + (-x)
        _ = -(a + x) := by simp [neg_add]
        _ = -(b + y) := by rw [hxy]
        _ = -b + (-y) := by simp [neg_add]

instance {R} [Ring R] (I : Ideal R) : Sub (I.Quot) where
  sub x y := x + -y

instance {R} [Ring R] (I : Ideal R) : IntCast I.Quot where
  intCast z := I.mkQuot (↑z)

instance {R} [Semiring R] (I : Ideal R) : Semiring I.Quot where
  add_zero a := by
    refine Quotient.inductionOn a fun a => ?_
    exact congrArg I.mkQuot (add_zero a)

  zero_add a := by
    refine Quotient.inductionOn a fun a => ?_
    exact congrArg I.mkQuot (zero_add a)

  add_assoc a b c := by
    refine Quotient.inductionOn a fun a => ?_
    refine Quotient.inductionOn b fun b => ?_
    refine Quotient.inductionOn c fun c => ?_
    exact congrArg I.mkQuot (add_assoc a b c)

  add_comm a b := by
    refine Quotient.inductionOn a fun a => ?_
    refine Quotient.inductionOn b fun b => ?_
    exact congrArg I.mkQuot (add_comm a b)

  mul_one a := by
    refine Quotient.inductionOn a fun a => ?_
    exact congrArg I.mkQuot (mul_one a)

  one_mul a := by
    refine Quotient.inductionOn a fun a => ?_
    exact congrArg I.mkQuot (one_mul a)

  mul_assoc a b c := by
    refine Quotient.inductionOn a fun a => ?_
    refine Quotient.inductionOn b fun b => ?_
    refine Quotient.inductionOn c fun c => ?_
    exact congrArg I.mkQuot (mul_assoc a b c)

  zero_mul a := by
    refine Quotient.inductionOn a fun a => ?_
    exact congrArg I.mkQuot (zero_mul a)

  mul_zero a := by
    refine Quotient.inductionOn a fun a => ?_
    exact congrArg I.mkQuot (mul_zero a)

  mul_add a b c := by
    refine Quotient.inductionOn a fun a => ?_
    refine Quotient.inductionOn b fun b => ?_
    refine Quotient.inductionOn c fun c => ?_
    exact congrArg I.mkQuot (mul_add a b c)

  add_mul a b c := by
    refine Quotient.inductionOn a fun a => ?_
    refine Quotient.inductionOn b fun b => ?_
    refine Quotient.inductionOn c fun c => ?_
    exact congrArg I.mkQuot (add_mul a b c)

  natCast_zero := by
    exact congrArg I.mkQuot natCast_zero

  natCast_succ n := by
    change I.mkQuot ↑(n + 1) =
      I.mkQuot (↑n + 1)
    exact congrArg I.mkQuot (natCast_succ n)

  zero_nsmul a := by
    refine Quotient.inductionOn a fun a => ?_
    exact congrArg I.mkQuot (zero_nsmul a)
  succ_nsmul n a := by
    refine Quotient.inductionOn a fun a => ?_
    exact congrArg I.mkQuot (succ_nsmul n a)
  pow_zero _ := rfl
  pow_succ _ _ := rfl

instance {R} [Ring R] (I : Ideal R) : Ring I.Quot where
  intCast_ofNat n := by
    exact congrArg I.mkQuot (intCast_ofNat n)

  intCast_neg z := by
    change I.mkQuot (IntCast.intCast (-z)) = -I.mkQuot (↑z)
    rw [intCast_neg]
    rfl

  neg_add_cancel a := by
    refine Quotient.inductionOn a fun a => ?_
    exact congrArg I.mkQuot (neg_add_cancel a)

  sub_eq_add_neg a b := rfl

  zero_zsmul a := by
    refine Quotient.inductionOn a fun a => ?_
    exact congrArg I.mkQuot (zero_zsmul a)

  succ_zsmul n a := by
    refine Quotient.inductionOn a fun a => ?_
    exact congrArg I.mkQuot (succ_zsmul n a)

  neg_zsmul z a := by
    induction a using Quotient.inductionOn with | _ a =>
    exact congrArg I.mkQuot (neg_zsmul z a)

end Alg
