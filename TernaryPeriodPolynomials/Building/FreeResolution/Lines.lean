module

public import TernaryPeriodPolynomials.ArithmeticCohomology.TopVanishing.Congruence
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section


/-!
# Integer vectors up to sign, ternary forms and labels modulo three

Original work by Claude Opus 5.5.

Lines are integer vectors in `ℤ³` up to sign; `GL₃(ℤ)` acts on them by matrix multiplication
and the principal congruence subgroup `Γ(3)` acts through its integral lift. A rational symmetric
matrix `A` gives the ternary form `A[x] = xᵀ A x`, which is even and transforms by
`(hᵀ A h)[x] = A[h x]`. The label of a line is its reduction modulo three
up to sign, encoded as a natural number; it is invariant under `Γ(3)`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.FreeResolution

open GeneralEisenstein Matrix TernaryPeriodPolynomials.TopVanishing

/-- Integer column vectors. -/
abbrev Vec := Fin 3 → ℤ

/-- Equality up to sign. -/
def signSetoid : Setoid Vec where
  r x y := y = x ∨ y = -x
  iseqv := ⟨fun _ => Or.inl rfl,
    fun {x y} h => by
      rcases h with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (neg_neg x).symm,
    fun {x y z} h1 h2 => by
      rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact Or.inr rfl
      · exact Or.inl (neg_neg x)⟩

/-- Integer vectors up to sign. -/
def Line : Type := Quotient signSetoid

instance : DecidableEq Line :=
  @Quotient.decidableEq _ signSetoid (fun x y => inferInstanceAs (Decidable (y = x ∨ y = -x)))

/-- The line of a vector. -/
def Line.mk (x : Vec) : Line := Quotient.mk signSetoid x

theorem Line.mk_eq_mk {x y : Vec} : Line.mk x = Line.mk y ↔ y = x ∨ y = -x :=
  Quotient.eq

theorem Line.mk_neg (x : Vec) : Line.mk (-x) = Line.mk x :=
  Line.mk_eq_mk.mpr (Or.inr (neg_neg x).symm)

theorem Line.ind {p : Line → Prop} (h : ∀ x, p (Line.mk x)) (ℓ : Line) : p ℓ :=
  Quotient.ind h ℓ

theorem Line.mk_out (ℓ : Line) : Line.mk (Quotient.out ℓ) = ℓ := Quotient.out_eq ℓ

/-- A representative of a line differs from any other by a sign. -/
theorem Line.out_mk (x : Vec) : Quotient.out (Line.mk x) = x ∨ Quotient.out (Line.mk x) = -x := by
  have h := Line.mk_eq_mk.mp (Line.mk_out (Line.mk x))
  rcases h with h | h
  · exact Or.inl h.symm
  · right
    have h' := congrArg Neg.neg h
    rw [neg_neg] at h'
    exact h'.symm

/-! ### The action of integral matrices -/

/-- Matrix multiplication by an invertible integral matrix. -/
def mv (h : IntegralGL3) (x : Vec) : Vec := (h : Matrix (Fin 3) (Fin 3) ℤ) *ᵥ x

theorem mv_neg (h : IntegralGL3) (x : Vec) : mv h (-x) = -mv h x := Matrix.mulVec_neg x _

theorem mv_one (x : Vec) : mv 1 x = x := by
  simp [mv]

theorem mv_mul (g h : IntegralGL3) (x : Vec) : mv (g * h) x = mv g (mv h x) := by
  simp [mv, Matrix.mulVec_mulVec]

theorem mv_inv_mv (h : IntegralGL3) (x : Vec) : mv h⁻¹ (mv h x) = x := by
  rw [← mv_mul, inv_mul_cancel, mv_one]

theorem mv_mv_inv (h : IntegralGL3) (x : Vec) : mv h (mv h⁻¹ x) = x := by
  rw [← mv_mul, mul_inv_cancel, mv_one]

instance : MulAction IntegralGL3 Line where
  smul h := Quotient.map (mv h) (fun ⦃x y⦄ hxy => by
    rcases hxy with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (mv_neg h x))
  one_smul := Line.ind fun x => by
    show Line.mk (mv 1 x) = Line.mk x
    rw [mv_one]
  mul_smul g h := Line.ind fun x => by
    show Line.mk (mv (g * h) x) = Line.mk (mv g (mv h x))
    rw [mv_mul]

theorem smul_mk (h : IntegralGL3) (x : Vec) : h • Line.mk x = Line.mk (mv h x) := rfl

/-! ### Ternary forms -/

/-- Rational ternary forms, by their Gram matrices. -/
abbrev Form := Matrix (Fin 3) (Fin 3) ℚ

/-- The value `xᵀ A x` of a form at an integer vector. -/
def qf (A : Form) (x : Vec) : ℚ := ∑ i, ∑ j, A i j * (x i : ℚ) * (x j : ℚ)

theorem qf_neg (A : Form) (x : Vec) : qf A (-x) = qf A x := by
  simp only [qf, Pi.neg_apply, Int.cast_neg, mul_neg, neg_mul, neg_neg]

theorem qf_add (A B : Form) (x : Vec) : qf (A + B) x = qf A x + qf B x := by
  simp only [qf, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem qf_smul (c : ℚ) (A : Form) (x : Vec) : qf (c • A) x = c * qf A x := by
  simp only [qf, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem qf_sub (A B : Form) (x : Vec) : qf (A - B) x = qf A x - qf B x := by
  simp only [qf, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem qf_zero (x : Vec) : qf 0 x = 0 := by simp [qf]

/-- Evaluation of forms at a vector, as an additive map. -/
def qfHom (x : Vec) : Form →+ ℚ where
  toFun A := qf A x
  map_zero' := qf_zero x
  map_add' A B := qf_add A B x

theorem qf_sum {ι : Type} (s : Finset ι) (A : ι → Form) (x : Vec) :
    qf (∑ i ∈ s, A i) x = ∑ i ∈ s, qf (A i) x :=
  map_sum (qfHom x) A s

theorem qf_zero_vec (A : Form) : qf A 0 = 0 := by simp [qf]

/-- An integral matrix as a rational matrix. -/
def toQ (h : IntegralGL3) : Matrix (Fin 3) (Fin 3) ℚ :=
  (h : Matrix (Fin 3) (Fin 3) ℤ).map (Int.castRingHom ℚ)

theorem toQ_mul (g h : IntegralGL3) : toQ (g * h) = toQ g * toQ h := by
  simp only [toQ, Units.val_mul, Matrix.map_mul]

/-- The form transported by an integral matrix: `(hᵀ A h)[x] = A[h x]`. -/
def act (h : IntegralGL3) (A : Form) : Form := (toQ h)ᵀ * A * toQ h

theorem qf_act (h : IntegralGL3) (A : Form) (x : Vec) : qf (act h A) x = qf A (mv h x) := by
  simp only [qf, act, toQ, mv, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Int.coe_castRingHom, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  push_cast
  ring

theorem act_add (h : IntegralGL3) (A B : Form) : act h (A + B) = act h A + act h B := by
  simp only [act, Matrix.mul_add, Matrix.add_mul]

theorem act_smul (h : IntegralGL3) (c : ℚ) (A : Form) : act h (c • A) = c • act h A := by
  simp only [act, Matrix.mul_smul, Matrix.smul_mul]

theorem act_sub (h : IntegralGL3) (A B : Form) : act h (A - B) = act h A - act h B := by
  simp only [act, Matrix.mul_sub, Matrix.sub_mul]

theorem act_sum {ι : Type} (h : IntegralGL3) (s : Finset ι) (A : ι → Form) :
    act h (∑ i ∈ s, A i) = ∑ i ∈ s, act h (A i) := by
  simp only [act, Matrix.mul_sum, Matrix.sum_mul]

theorem act_act (g h : IntegralGL3) (A : Form) : act h (act g A) = act (g * h) A := by
  simp only [act, toQ_mul, Matrix.transpose_mul, Matrix.mul_assoc]

theorem act_transpose (h : IntegralGL3) (A : Form) (hA : Aᵀ = A) : (act h A)ᵀ = act h A := by
  simp only [act, Matrix.transpose_mul, Matrix.transpose_transpose, hA, Matrix.mul_assoc]

/-! ### Determinants of integer triples -/

/-- The determinant of three integer vectors. -/
def det3v (x y z : Vec) : ℤ :=
  x 0 * (y 1 * z 2 - y 2 * z 1) - x 1 * (y 0 * z 2 - y 2 * z 0) + x 2 * (y 0 * z 1 - y 1 * z 0)

theorem det3v_mv (h : IntegralGL3) (x y z : Vec) :
    det3v (mv h x) (mv h y) (mv h z) = (h : Matrix (Fin 3) (Fin 3) ℤ).det * det3v x y z := by
  simp only [det3v, mv, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

theorem det_ne_zero_of_unit (h : IntegralGL3) : (h : Matrix (Fin 3) (Fin 3) ℤ).det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det (h.mul_inv)
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem det3v_neg_left (x y z : Vec) : det3v (-x) y z = -det3v x y z := by
  simp only [det3v, Pi.neg_apply]; ring

theorem det3v_neg_mid (x y z : Vec) : det3v x (-y) z = -det3v x y z := by
  simp only [det3v, Pi.neg_apply]; ring

theorem det3v_neg_right (x y z : Vec) : det3v x y (-z) = -det3v x y z := by
  simp only [det3v, Pi.neg_apply]; ring

theorem det3v_self_left (x z : Vec) : det3v x x z = 0 := by
  simp only [det3v]; ring

theorem det3v_self_right (x y : Vec) : det3v x y y = 0 := by
  simp only [det3v]; ring

theorem det3v_self_outer (x y : Vec) : det3v x y x = 0 := by
  simp only [det3v]; ring

/-- The cross product, a covector with `cross x y ⬝ z = det3v x y z`. -/
def cross (x y : Vec) : Vec :=
  ![x 1 * y 2 - x 2 * y 1, x 2 * y 0 - x 0 * y 2, x 0 * y 1 - x 1 * y 0]

theorem cross_dot (x y z : Vec) :
    ∑ i, cross x y i * z i = det3v x y z := by
  simp [cross, det3v, Fin.sum_univ_three]
  ring

/-- Three lines with independent representatives. -/
def Line.Indep (a b c : Line) : Prop :=
  det3v (Quotient.out a) (Quotient.out b) (Quotient.out c) ≠ 0

theorem det3v_ne_zero_iff_of_sign {x y z x' y' z' : Vec} (hx : x' = x ∨ x' = -x)
    (hy : y' = y ∨ y' = -y) (hz : z' = z ∨ z' = -z) :
    det3v x' y' z' ≠ 0 ↔ det3v x y z ≠ 0 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;>
    simp only [det3v_neg_left, det3v_neg_mid, det3v_neg_right, neg_neg, ne_eq, neg_eq_zero]

theorem Line.indep_mk (x y z : Vec) :
    Line.Indep (Line.mk x) (Line.mk y) (Line.mk z) ↔ det3v x y z ≠ 0 :=
  det3v_ne_zero_iff_of_sign (Line.out_mk x) (Line.out_mk y) (Line.out_mk z)

theorem Line.indep_smul (h : IntegralGL3) (a b c : Line) :
    Line.Indep (h • a) (h • b) (h • c) ↔ Line.Indep a b c := by
  induction a using Line.ind with | h x => ?_
  induction b using Line.ind with | h y => ?_
  induction c using Line.ind with | h z => ?_
  rw [smul_mk, smul_mk, smul_mk, Line.indep_mk, Line.indep_mk, det3v_mv]
  exact ⟨fun h1 h2 => h1 (by rw [h2, mul_zero]),
    fun h1 => mul_ne_zero (det_ne_zero_of_unit h) h1⟩

/-- A set of lines spans: it contains three independent lines. -/
def Spans (T : Finset Line) : Prop :=
  ∃ a ∈ T, ∃ b ∈ T, ∃ c ∈ T, Line.Indep a b c

theorem Spans.mono {T T' : Finset Line} (h : Spans T) (hT : T ⊆ T') : Spans T' := by
  obtain ⟨a, ha, b, hb, c, hc, habc⟩ := h
  exact ⟨a, hT ha, b, hT hb, c, hT hc, habc⟩

theorem Line.Indep.ne12 {a b c : Line} (h : Line.Indep a b c) : a ≠ b := by
  rintro rfl
  exact h (det3v_self_left _ _)

theorem Line.Indep.ne23 {a b c : Line} (h : Line.Indep a b c) : b ≠ c := by
  rintro rfl
  exact h (det3v_self_right _ _)

theorem Line.Indep.ne13 {a b c : Line} (h : Line.Indep a b c) : a ≠ c := by
  rintro rfl
  exact h (det3v_self_outer _ _)

theorem Spans.three_le_card {T : Finset Line} (h : Spans T) : 3 ≤ T.card := by
  obtain ⟨a, ha, b, hb, c, hc, habc⟩ := h
  have hsub : ({a, b, c} : Finset Line) ⊆ T := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hcard : ({a, b, c} : Finset Line).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair habc.ne23]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨habc.ne12, habc.ne13⟩
  rw [← hcard]
  exact Finset.card_le_card hsub

/-! ### Labels modulo three -/

/-- Reduction modulo three. -/
def red (x : Vec) : Fin 3 → ZMod 3 := fun i => (x i : ZMod 3)

theorem red_neg (x : Vec) : red (-x) = -red x := by
  funext i
  simp [red]

theorem red_mv (h : IntegralGL3) (x : Vec) :
    red (mv h x) = ((h : Matrix (Fin 3) (Fin 3) ℤ).map (Int.cast : ℤ → ZMod 3)) *ᵥ red x := by
  funext i
  simp [red, mv, Matrix.mulVec, dotProduct]

/-- Base-three encoding of a residue vector. -/
def enc (y : Fin 3 → ZMod 3) : ℕ := (y 0).val + 3 * (y 1).val + 9 * (y 2).val

theorem enc_injective : Function.Injective enc := by
  intro y y' h
  have a0 := ZMod.val_lt (y 0)
  have a1 := ZMod.val_lt (y 1)
  have a2 := ZMod.val_lt (y 2)
  have b0 := ZMod.val_lt (y' 0)
  have b1 := ZMod.val_lt (y' 1)
  have b2 := ZMod.val_lt (y' 2)
  unfold enc at h
  have e0 : (y 0).val = (y' 0).val := by omega
  have e1 : (y 1).val = (y' 1).val := by omega
  have e2 : (y 2).val = (y' 2).val := by omega
  funext i
  fin_cases i
  · exact ZMod.val_injective 3 e0
  · exact ZMod.val_injective 3 e1
  · exact ZMod.val_injective 3 e2

/-- Decoding of the base-three encoding. -/
def dec (n : ℕ) : Fin 3 → ZMod 3 := ![(n : ZMod 3), ((n / 3 : ℕ) : ZMod 3), ((n / 9 : ℕ) : ZMod 3)]

theorem dec_enc (y : Fin 3 → ZMod 3) : dec (enc y) = y := by
  have a0 := ZMod.val_lt (y 0)
  have a1 := ZMod.val_lt (y 1)
  have a2 := ZMod.val_lt (y 2)
  funext i
  fin_cases i
  · show ((enc y : ℕ) : ZMod 3) = y 0
    rw [← ZMod.natCast_zmod_val (y 0)]
    rw [ZMod.natCast_eq_natCast_iff']
    unfold enc
    omega
  · show (((enc y / 3 : ℕ)) : ZMod 3) = y 1
    rw [← ZMod.natCast_zmod_val (y 1)]
    rw [ZMod.natCast_eq_natCast_iff']
    unfold enc
    omega
  · show (((enc y / 9 : ℕ)) : ZMod 3) = y 2
    rw [← ZMod.natCast_zmod_val (y 2)]
    rw [ZMod.natCast_eq_natCast_iff']
    unfold enc
    omega

/-- The label of a vector: its reduction modulo three, up to sign. -/
def labelVec (x : Vec) : ℕ := min (enc (red x)) (enc (-red x))

theorem labelVec_neg (x : Vec) : labelVec (-x) = labelVec x := by
  rw [labelVec, labelVec, red_neg, neg_neg, min_comm]

/-- The label of a line. -/
def Line.label : Line → ℕ :=
  Quotient.lift labelVec (fun x y h => by
    rcases h with rfl | rfl
    · rfl
    · exact (labelVec_neg x).symm)

theorem Line.label_mk (x : Vec) : (Line.mk x).label = labelVec x := rfl

theorem labelVec_of_red {x y : Vec} (h : red y = red x ∨ red y = -red x) :
    labelVec y = labelVec x := by
  rcases h with h | h
  · rw [labelVec, labelVec, h]
  · rw [labelVec, labelVec, h, neg_neg, min_comm]

theorem red_of_labelVec {x y : Vec} (h : labelVec y = labelVec x) :
    red y = red x ∨ red y = -red x := by
  unfold labelVec at h
  rcases min_choice (enc (red y)) (enc (-red y)) with h1 | h1 <;>
    rcases min_choice (enc (red x)) (enc (-red x)) with h2 | h2 <;> rw [h1, h2] at h
  · exact Or.inl (enc_injective h)
  · exact Or.inr (enc_injective h)
  · right
    rw [← neg_neg (red y), enc_injective h]
  · left
    have := enc_injective h
    rw [← neg_neg (red y), this, neg_neg]

/-- The residue vector of the label, up to sign. -/
theorem dec_labelVec (x : Vec) : dec (labelVec x) = red x ∨ dec (labelVec x) = -red x := by
  unfold labelVec
  rcases min_choice (enc (red x)) (enc (-red x)) with h | h <;> rw [h, dec_enc]
  · exact Or.inl rfl
  · exact Or.inr rfl

/-! ### The principal congruence subgroup -/

theorem exists_levelLift (γ : principalLevel) :
    ∃ k : IntegralGL3, k ∈ reductionThree.ker ∧ integralToRational k = γ := by
  obtain ⟨k, hk, he⟩ := Subgroup.mem_map.mp γ.2
  exact ⟨k, hk, he⟩

/-- The integral matrix of an element of `Γ(3)`. -/
def levelLift : principalLevel →* IntegralGL3 where
  toFun γ := (exists_levelLift γ).choose
  map_one' := by
    apply integralToRational_injective
    show integralToRational (exists_levelLift 1).choose = integralToRational 1
    rw [(exists_levelLift 1).choose_spec.2, map_one]
    rfl
  map_mul' γ γ' := by
    apply integralToRational_injective
    show integralToRational (exists_levelLift (γ * γ')).choose =
      integralToRational ((exists_levelLift γ).choose * (exists_levelLift γ').choose)
    rw [map_mul, (exists_levelLift (γ * γ')).choose_spec.2, (exists_levelLift γ).choose_spec.2,
      (exists_levelLift γ').choose_spec.2]
    rfl

theorem integralToRational_levelLift (γ : principalLevel) :
    integralToRational (levelLift γ) = γ :=
  (exists_levelLift γ).choose_spec.2

theorem levelLift_mem_ker (γ : principalLevel) : levelLift γ ∈ reductionThree.ker :=
  (exists_levelLift γ).choose_spec.1

/-- `Γ(3)` acts on lines through its integral lift. -/
instance : MulAction principalLevel Line := MulAction.compHom Line levelLift

theorem level_smul (γ : principalLevel) (ℓ : Line) : γ • ℓ = levelLift γ • ℓ := rfl

theorem red_mv_of_mem_ker {k : IntegralGL3} (hk : k ∈ reductionThree.ker) (x : Vec) :
    red (mv k x) = red x := by
  have h1 : reductionThree k = 1 := MonoidHom.mem_ker.mp hk
  have hmat : (k : Matrix (Fin 3) (Fin 3) ℤ).map (Int.cast : ℤ → ZMod 3) = 1 := by
    ext i j
    have h2 := congrArg (fun g : GeneralLinearGroup (Fin 3) (ZMod 3) =>
      (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) i j) h1
    simpa [reductionThree, Matrix.GeneralLinearGroup.map_apply] using h2
  rw [red_mv, hmat, Matrix.one_mulVec]

theorem label_level_smul (γ : principalLevel) (ℓ : Line) : (γ • ℓ).label = ℓ.label := by
  induction ℓ using Line.ind with | h x => ?_
  rw [level_smul, smul_mk, Line.label_mk, Line.label_mk]
  exact labelVec_of_red (Or.inl (red_mv_of_mem_ker (levelLift_mem_ker γ) x))

/-! ### Rank-one forms modulo three -/

/-- The coordinates `(y₀², y₁², y₂², y₀y₁, y₀y₂, y₁y₂)` of the rank-one form of `y`. -/
def rankOne {K : Type} [CommRing K] (y : Fin 3 → K) : Fin 6 → K :=
  ![y 0 * y 0, y 1 * y 1, y 2 * y 2, y 0 * y 1, y 0 * y 2, y 1 * y 2]

theorem rankOne_neg {K : Type} [CommRing K] (y : Fin 3 → K) : rankOne (-y) = rankOne y := by
  funext a
  fin_cases a <;> simp [rankOne]

/-- The induced action of a matrix on rank-one coordinates. -/
def symSq {K : Type} [CommRing K] (H : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 6) (Fin 6) K :=
  let row : Fin 3 → Fin 3 → Fin 6 → K := fun a b =>
    ![H a 0 * H b 0, H a 1 * H b 1, H a 2 * H b 2, H a 0 * H b 1 + H a 1 * H b 0,
      H a 0 * H b 2 + H a 2 * H b 0, H a 1 * H b 2 + H a 2 * H b 1]
  Matrix.of ![row 0 0, row 1 1, row 2 2, row 0 1, row 0 2, row 1 2]

theorem rankOne_mulVec {K : Type} [CommRing K] (H : Matrix (Fin 3) (Fin 3) K) (y : Fin 3 → K) :
    rankOne (H *ᵥ y) = symSq H *ᵥ rankOne y := by
  funext a
  fin_cases a <;>
    simp [rankOne, symSq, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

/-- The rank-one row attached to a label. -/
def labelRow (n : ℕ) : Fin 6 → ZMod 3 := rankOne (dec n)

theorem labelRow_labelVec (x : Vec) : labelRow (labelVec x) = rankOne (red x) := by
  unfold labelRow
  rcases dec_labelVec x with h | h <;> rw [h]
  rw [rankOne_neg]

end TernaryPeriodPolynomials.FreeResolution
