import ReMath.Alg.Defs
import ReMath.Alg.Vector
import ReMath.DiscreteCalc.Defs
import ReMath.DiscreteCalc.Lemmas

namespace Alg

/--
A matrix with `n` rows and `m` columns, stored as a flat vector.
-/
structure Matrix (α : Type _) (n m : Nat) where
  data : Vector α (n * m)

namespace Matrix

open DiscreteCalc

/-- Combine an innermost coordinate and remaining index into a flat index. -/
def pairIdx {n m : Nat}
    (i : Fin n × Fin m) :
    Fin (n * m) := by
  refine ⟨i.snd.val * n + i.fst.val, ?_⟩
  calc
    _ + 1 ≤ i.snd.val * n + n :=
      Nat.add_le_add_left i.fst.isLt _
    _ = (i.snd.val + 1) * n := by
      rw [Nat.succ_mul]
    _ ≤ m * n :=
      Nat.mul_le_mul_right n i.snd.isLt
    _ = n * m := Nat.mul_comm _ _

/-- Split a flat index into its innermost coordinate and remaining index. -/
def unpairIdx {n m : Nat}
    (i : Fin (n * m)) :
    Fin n × Fin m := by
  have hpos : 0 < n := by
    have := Fin.pos i
    exact Nat.pos_of_mul_pos_right (by simpa using this)
  exact
    (⟨i.val % n, Nat.mod_lt _ hpos⟩,
     ⟨i.val / n, by
       apply (Nat.div_lt_iff_lt_mul hpos).mpr
       calc
         i.val < n * m := i.isLt
         _ = m * n := Nat.mul_comm _ _⟩)

/-- Bundling and then unbundling recovers the original index. -/
@[simp]
theorem unpairIdx_pairIdx {n m : Nat}
    (i : Fin n × Fin m) :
    unpairIdx (pairIdx i) = i := by
  apply Prod.ext
  · apply Fin.ext
    simp [unpairIdx, pairIdx, Nat.add_mod, Nat.mod_eq_of_lt]
  · apply Fin.ext
    have hn : 0 < n := Fin.pos i.fst
    simp [unpairIdx, pairIdx, Nat.mul_comm, Nat.mul_add_div hn]

/-- Unbundling and then bundling recovers the original index. -/
@[simp]
theorem pairIdx_unpairIdx {n m : Nat}
    (i : Fin (n * m)) :
    pairIdx (unpairIdx i) = i := by
  apply Fin.ext
  simp only [pairIdx, unpairIdx]
  simp only [Nat.mul_comm (i.val / n) n]
  simp only [Nat.add_comm (n * (i.val / n)) (i.val % n)]
  exact Nat.mod_add_div i.val n

/-- Construct a matrix from a function on flat indices. -/
def ofFn {α} {n m : Nat}
    (f : Fin (n * m) → α) : Matrix α n m :=
  ⟨Vector.ofFn f⟩

/-- Construct a matrix from a function on pairs of coordinates. -/
def ofFn₂ {α} {n m : Nat}
    (f : Fin n → Fin m → α) : Matrix α n m :=
  ofFn fun i =>
    let (i₀, i₁) := unpairIdx i
    f i₀ i₁

/-- Read an entry using its flat index. -/
def get {α} {n m : Nat}
    (matrix : Matrix α n m) (i : Fin (n * m)) : α :=
  matrix.data[i.val]'i.isLt

/-- Read an entry using its two coordinates. -/
def get₂ {α} {n m : Nat}
    (matrix : Matrix α n m) (i : Fin n) (j : Fin m) : α :=
  matrix.get (pairIdx (i, j))

/-- Constructing from flat indices and reading recovers the function. -/
@[simp]
theorem get_ofFn {α} {n m : Nat}
    (f : Fin (n * m) → α) (i : Fin (n * m)) :
    get (ofFn f) i = f i := by
  simp [get, ofFn]

/-- Constructing from coordinates and reading recovers the function. -/
@[simp]
theorem get₂_ofFn₂ {α} {n m : Nat}
    (f : Fin n → Fin m → α) (i : Fin n) (j : Fin m) :
    get₂ (ofFn₂ f) i j = f i j := by
  simp [get₂, ofFn₂]

/-- Two matrices are equal if all their entries are equal. -/
@[ext]
theorem ext {α} {n m : Nat}
    (a b : Matrix α n m)
    (h : ∀ i, get a i = get b i) :
    a = b := by
  cases a with
  | mk a =>
    cases b with
    | mk b =>
      congr 1
      apply Vector.ext
      intro i hi
      exact h ⟨i, hi⟩

/-- Two matrices are equal if all corresponding entries are equal. -/
@[ext]
theorem ext₂ {α} {n m : Nat}
    (a b : Matrix α n m)
    (h : ∀ i j, get₂ a i j = get₂ b i j) :
    a = b := by
  apply ext
  intro k
  rw [← pairIdx_unpairIdx k]
  obtain ⟨i, j⟩ := unpairIdx k
  exact h i j

/-- Read an entry using a flat natural number index. -/
instance {α : Type _} {n m : Nat} :
    GetElem (Matrix α n m) Nat α
      (fun _ i => i < n * m) where
  getElem matrix i h :=
    matrix.get ⟨i, h⟩

/-- Read an entry using a pair of natural number coordinates. -/
instance {α : Type _} {n m : Nat} :
    GetElem (Matrix α n m) (Nat × Nat) α
      (fun _ i => i.fst < n ∧ i.snd < m) where
  getElem matrix i h :=
    matrix.get₂ ⟨i.fst, h.left⟩ ⟨i.snd, h.right⟩

@[simp]
theorem getElem_flat {α : Type _} {n m : Nat}
    (matrix : Matrix α n m) (i : Nat)
    (h : i < n * m) :
    matrix[i] = matrix.get ⟨i, h⟩ := rfl

@[simp]
theorem getElem_pair {α : Type _} {n m : Nat}
    (matrix : Matrix α n m) (i j : Nat)
    (hi : i < n) (hj : j < m) :
    matrix[(i, j)]'⟨hi, hj⟩ = matrix.get₂ ⟨i, hi⟩ ⟨j, hj⟩ :=
  rfl

/-- Null matrix. -/
instance {α} [Zero α] {n m : Nat} :
    Zero (Matrix α n m) :=
  ⟨ofFn₂ fun _ _ => 0⟩

/-- Pointwise addition of matrices. -/
instance {α} [Add α] {n m : Nat} :
    Add (Matrix α n m) where
  add a b := ofFn₂ fun i j => a.get₂ i j + b.get₂ i j

/-- Pointwise natural number scalar multiplication of matrices. -/
instance {α} [NSMul α] {n m : Nat} :
    NSMul (Matrix α n m) where
  nsmul := ⟨fun k a => ofFn₂ fun i j => k • a.get₂ i j⟩

/-- Pointwise negation of matrices. -/
instance {α} [Neg α] {n m : Nat} :
    Neg (Matrix α n m) where
  neg a := ofFn₂ fun i j => -a.get₂ i j

/-- Pointwise subtraction of matrices. -/
instance {α} [Sub α] {n m : Nat} :
    Sub (Matrix α n m) where
  sub a b := ofFn₂ fun i j => a.get₂ i j - b.get₂ i j

/-- Pointwise integer scalar multiplication of matrices. -/
instance {α} [ZSMul α] {n m : Nat} :
    ZSMul (Matrix α n m) where
  zsmul := ⟨fun k a => ofFn₂ fun i j => k • a.get₂ i j⟩

/-- Rectangle matrix multiplication. -/
instance instMatrixHMul {α} [Zero α] [Add α] [Mul α] {n m p : Nat} :
    HMul (Matrix α n m) (Matrix α m p) (Matrix α n p) where
  hMul a b :=
    ofFn₂ fun i j =>
      finSum m (fun k => a.get₂ i k * b.get₂ k j)

/-- Square matrix multiplication. -/
instance instMatrixMul {α} [Zero α] [Add α] [Mul α] {n : Nat} : Mul (Matrix α n n) := ⟨instMatrixHMul.hMul⟩

/-- Matrix-vector multiplication. -/
instance {α} [Zero α] [Add α] [Mul α] {n : Nat} :
    SMul (Matrix α n n) (Vector α n) where
  smul A v :=
    Vector.ofFn fun i =>
      finSum n (fun k => A.get₂ i k * v[k.val]'k.isLt)

/-- Identity matrix. -/
instance {α} [Zero α] [One α] {n : Nat} :
    One (Matrix α n n) where
  one := ofFn₂ fun i j => if i = j then 1 else 0

/-- Natural powers of square matrices. -/
instance {α} [Zero α] [One α] [Add α] [Mul α]
    {n : Nat} :
    Pow (Matrix α n n) Nat where
  pow a k := Fin.foldr k (fun _ b => b * a) 1

/-- Diagonal matrix of a natural number cast. -/
instance {α} [Zero α] [NatCast α] {n : Nat} :
    NatCast (Matrix α n n) where
  natCast k := ofFn₂ fun i j => if i = j then (k : α) else 0

/-- Diagonal matrix of an integer cast. -/
instance {α} [Zero α] [IntCast α] {n : Nat} :
    IntCast (Matrix α n n) where
  intCast k := ofFn₂ fun i j => if i = j then (k : α) else 0

@[simp]
theorem get₂_zero {α} [Zero α] {n m : Nat}
    (i : Fin n) (j : Fin m) :
    get₂ (0 : Matrix α n m) i j = 0 := by
  change (Matrix.ofFn₂ _).get₂ _ _ = _
  simp only [get₂_ofFn₂]

@[simp]
theorem get₂_add {α} [Add α] {n m : Nat}
    (a b : Matrix α n m) (i : Fin n) (j : Fin m) :
    get₂ (a + b) i j = get₂ a i j + get₂ b i j := by
  change (Matrix.ofFn₂ _).get₂ _ _ = _
  simp only [get₂_ofFn₂]

@[simp]
theorem get₂_nsmul {α} [NSMul α] {n m : Nat}
    (k : Nat) (a : Matrix α n m) (i : Fin n) (j : Fin m) :
    get₂ (k • a) i j = k • get₂ a i j := by
  change (Matrix.ofFn₂ _).get₂ _ _ = _
  simp only [get₂_ofFn₂]

@[simp]
theorem get₂_neg {α} [Neg α] {n m : Nat}
    (a : Matrix α n m) (i : Fin n) (j : Fin m) :
    get₂ (-a) i j = -get₂ a i j := by
  change (Matrix.ofFn₂ _).get₂ _ _ = _
  simp only [get₂_ofFn₂]

@[simp]
theorem get₂_sub {α} [Sub α] {n m : Nat}
    (a b : Matrix α n m) (i : Fin n) (j : Fin m) :
    get₂ (a - b) i j = get₂ a i j - get₂ b i j := by
  change (Matrix.ofFn₂ _).get₂ _ _ = _
  simp only [get₂_ofFn₂]

@[simp]
theorem get₂_zsmul {α} [ZSMul α] {n m : Nat}
    (k : Int) (a : Matrix α n m) (i : Fin n) (j : Fin m) :
    get₂ (k • a) i j = k • get₂ a i j := by
  change (Matrix.ofFn₂ _).get₂ _ _ = _
  simp only [get₂_ofFn₂]

@[simp]
theorem get₂_one {α} [Zero α] [One α] {n : Nat}
    (i j : Fin n) :
    get₂ (1 : Matrix α n n) i j =
      if i = j then 1 else 0 := by
  change (Matrix.ofFn₂ _).get₂ _ _ = _
  simp only [get₂_ofFn₂]

@[simp]
theorem get₂_mul {α} [Zero α] [Add α] [Mul α]
    {n m p : Nat}
    (a : Matrix α n m) (b : Matrix α m p)
    (i : Fin n) (j : Fin p) :
    get₂ (a * b) i j = finSum m (fun k => a.get₂ i k * b.get₂ k j) := by
  change (Matrix.ofFn₂ _).get₂ _ _ = _
  simp only [get₂_ofFn₂]

@[simp]
theorem get₂_natCast {α} [Zero α] [NatCast α] {n : Nat}
    (k : Nat) (i j : Fin n) :
    get₂ (Nat.cast k : Matrix α n n) i j =
      if i = j then (k : α) else 0 := by
  change (Matrix.ofFn₂ _).get₂ _ _ = _
  simp only [get₂_ofFn₂]

@[simp]
theorem get₂_intCast {α} [Zero α] [IntCast α] {n : Nat}
    (k : Int) (i j : Fin n) :
    get₂ (Int.cast k : Matrix α n n) i j =
      if i = j then (k : α) else 0 := by
  change (Matrix.ofFn₂ _).get₂ _ _ = _
  simp only [get₂_ofFn₂]

@[simp]
theorem get_smul {α} [Zero α] [Add α] [Mul α] {n : Nat}
    (A : Matrix α n n) (v : Vector α n) (i : Fin n) :
    (A • v)[i.val]'i.isLt =
      finSum n (fun k => A.get₂ i k * v[k.val]'k.isLt) := by
  change (Vector.ofFn _)[i.val]'i.isLt = _
  simp [Vector.getElem_ofFn]

instance {α} [AddMonoid α] {n m : Nat} :
    AddMonoid (Matrix α n m) where
  add_zero := by
    intro a
    apply ext₂
    simp [add_zero]
  zero_add := by
    intro a
    apply ext₂
    simp [zero_add]
  add_assoc := by
    intro a b c
    apply ext₂
    simp [add_assoc]
  zero_nsmul := by
    intro a
    apply ext₂
    simp [zero_nsmul]
  succ_nsmul := by
    intro k a
    apply ext₂
    simp [succ_nsmul]

instance {α} [AddCommMonoid α] {n m : Nat} :
    AddCommMonoid (Matrix α n m) where
  add_comm := by
    intro a b
    apply ext₂
    simp [add_comm]

instance {α} [AddGroup α] {n m : Nat} :
    AddGroup (Matrix α n m) where
  neg_add_cancel := by
    intro a
    apply ext₂
    simp [neg_add_cancel]
  sub_eq_add_neg := by
    intro a b
    apply ext₂
    simp [sub_eq_add_neg]
  zero_zsmul := by
    intro a
    apply ext₂
    simp [zero_zsmul]
  succ_zsmul := by
    intro k a
    apply ext₂
    simp [succ_zsmul]
  neg_zsmul := by
    intro k a
    apply ext₂
    simp [neg_zsmul]

instance {α} [AddCommGroup α] {n m : Nat} :
    AddCommGroup (Matrix α n m) where

private theorem neg_zero_eq {α} [AddGroup α] : -(0 : α) = 0 :=
  (add_zero _).symm.trans (neg_add_cancel _)

instance {α} [Semiring α] {n : Nat} :
    MulMonoid (Matrix α n n) where
  mul_one a := ext₂ _ _ fun i j => by
    rw [get₂_mul]
    have h : ∀ k : Fin n, a.get₂ i k * get₂ (1 : Matrix α n n) k j =
        if k = j then a.get₂ i k else 0 := by
      intro k
      rw [get₂_one]
      by_cases hk : k = j
      · rw [if_pos hk, if_pos hk, mul_one]
      · rw [if_neg hk, if_neg hk, mul_zero]
    rw [finSum_congr h]
    exact finSum_ite_eq (fun k => a.get₂ i k) j
  one_mul a := ext₂ _ _ fun i j => by
    rw [get₂_mul]
    have h : ∀ k : Fin n, get₂ (1 : Matrix α n n) i k * a.get₂ k j =
        if i = k then a.get₂ k j else 0 := by
      intro k
      rw [get₂_one]
      by_cases hk : i = k
      · rw [if_pos hk, if_pos hk, one_mul]
      · rw [if_neg hk, if_neg hk, zero_mul]
    rw [finSum_congr h]
    exact finSum_ite_eq' (fun k => a.get₂ k j) i
  mul_assoc a b c := ext₂ _ _ fun i j => by
    simp only [get₂_mul, finSum_mul, mul_finSum, mul_assoc]
    exact finSum_comm fun l k =>
      a.get₂ i k * (b.get₂ k l * c.get₂ l j)
  pow_zero a := Fin.foldr_zero _ _
  pow_succ a k := Fin.foldr_succ _ _

instance {α} [Semiring α] {n : Nat} :
    Semiring (Matrix α n n) where
  zero_mul a := ext₂ _ _ fun i j => by
    simp only [get₂_mul, get₂_zero, zero_mul, finSum_const_zero]
  mul_zero a := ext₂ _ _ fun i j => by
    simp only [get₂_mul, get₂_zero, mul_zero, finSum_const_zero]
  mul_add a b c := ext₂ _ _ fun i j => by
    simp only [get₂_mul, get₂_add, mul_add, finSum_add]
  add_mul a b c := ext₂ _ _ fun i j => by
    simp only [get₂_mul, get₂_add, add_mul, finSum_add]
  natCast_zero := ext₂ _ _ fun i j => by
    simp only [get₂_natCast, get₂_zero, natCast_zero, ite_self]
  natCast_succ k := ext₂ _ _ fun i j => by
    simp only [get₂_natCast, get₂_add, get₂_one]
    by_cases h : i = j
    · simp only [if_pos h]
      exact natCast_succ k
    · simp only [if_neg h]
      exact (add_zero _).symm

instance {α} [Ring α] {n : Nat} :
    Ring (Matrix α n n) where
  intCast_ofNat k := ext₂ _ _ fun i j => by
    simp only [get₂_intCast, get₂_natCast]
    by_cases h : i = j
    · simp only [if_pos h]
      exact intCast_ofNat k
    · simp only [if_neg h]
  intCast_neg z := ext₂ _ _ fun i j => by
    simp only [get₂_intCast, get₂_neg]
    by_cases h : i = j
    · simp only [if_pos h]
      exact intCast_neg z
    · simp only [if_neg h]
      exact neg_zero_eq.symm

instance {α} [Semiring α] {n : Nat} : Semimodule (Matrix α n n) (Vector α n) where
  one_smul v := by
    apply Vector.ext_fin
    intro i
    simp only [Fin.getElem_fin, get_smul 1 v i, get₂_one]
    simp only [ite_mul, one_mul, zero_mul]
    simp [finSum_ite_eq']
  mul_smul A B v := by
    apply Vector.ext_fin
    intro i
    simp only [Fin.getElem_fin, get_smul, get₂_mul]
    simp only [finSum_mul, mul_finSum]
    rw [finSum_comm]
    apply finSum_congr
    intro k
    simp only [mul_assoc]
  smul_zero A := by
    apply Vector.ext_fin
    intro i
    simp [Fin.getElem_fin, Alg.Vector.getElem_zero]
  smul_add A v w := by
    apply Vector.ext_fin
    intro i
    simp [Fin.getElem_fin, get_smul, finSum_add, mul_add]
  add_smul A B v := by
    apply Vector.ext_fin
    intro i
    simp only [Fin.getElem_fin, Alg.Vector.getElem_add]
    simp only [get_smul, get₂_add, add_mul, finSum_add]
  zero_smul v := by
    apply Vector.ext_fin
    intro i
    simp only [Fin.getElem_fin, get_smul]
    simp only [get₂_zero, zero_mul, Alg.Vector.getElem_zero]
    simp only [finSum_const_zero]

instance {α} [Ring α] {n : Nat} : Module (Matrix α n n) (Vector α n) where

end Matrix

end Alg
