module

public import Mathlib

@[expose] public section


/-!
# The symmetric space `SL₃(ℝ)/SO(3)` as the positive definite ternary forms of determinant one

Formalized by Claude Sonnet 5.5.  Paper: "Let `𝒳` be the space of positive definite ternary real quadratic forms modulo positive scaling.
Determinant-one representatives give `𝒳 ≅ SL₃(ℝ)/SO(3)`, `g SO(3) ↔ Q = (g gᵗ)⁻¹`.  For `g ∈ G` we use the left action `g·Q = g^{-t} Q g⁻¹`.  The corresponding right action is
`Q ↦ gᵗ Q g`.  The analytic appendix uses the Gram matrix `g gᵗ = Q⁻¹` rather than `Q`."

Everything is in Mathlib's terms (`Matrix.PosDef`, `Matrix.SpecialLinearGroup`, `CFC.sqrt` for the square root).

* `SO3`: the subgroup `{k ∈ SL₃(ℝ) : k kᵗ = 1}` (`mem_SO3_iff_specialOrthogonalGroup`: Mathlib's `Matrix.specialOrthogonalGroup`).
* `Pos1`: `{Q : Q positive definite, det Q = 1}`; `formMap g = (g gᵗ)⁻¹` and `gramMap g = g gᵗ` are maps `SL₃(ℝ) → Pos1`.
* `formMap_surjective`, `gramMap_surjective` (square root of the Gram matrix), `formMap_eq_iff`: `(g gᵗ)⁻¹ = (h hᵗ)⁻¹ ↔ g⁻¹ h ∈ SO(3)`, `gramMap_eq_iff` likewise.
* The left action `leftAct g Q = g^{-t} Q g⁻¹` (a `MulAction SL₃(ℝ) Pos1`) and the right action `rightAct g Q = gᵗ Q g` (`rightAct_mul`, `leftAct_eq_rightAct_inv`).
* `quotEquiv : SL₃(ℝ)/SO(3) ≃ Pos1`, `g SO(3) ↦ (g gᵗ)⁻¹`, with `quotEquiv_smul` (equivariance for the left action: `(h g) SO(3) ↦ h·(g gᵗ)⁻¹`) and `quotEquivGram` for the Gram matrix,
  equivariant for congruence `g·P = g P gᵗ`.
-/

open Matrix
open scoped MatrixOrder

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities.SymmetricSpace

abbrev Mat : Type := Matrix (Fin 3) (Fin 3) ℝ
abbrev SL3 : Type := Matrix.SpecialLinearGroup (Fin 3) ℝ

theorem isUnit_coe (g : SL3) : IsUnit (g : Mat) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [g.det_coe]; exact isUnit_one)

theorem coe_mul_eq (a b : SL3) : ((a * b : SL3) : Mat) = (a : Mat) * (b : Mat) :=
  Matrix.SpecialLinearGroup.coe_mul a b

theorem coe_inv_mul_eq (k : SL3) : ((k⁻¹ : SL3) : Mat) * (k : Mat) = 1 := by
  have := congrArg Subtype.val (inv_mul_cancel k)
  rwa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at this

/-- `SO(3)`: the real orthogonal matrices of determinant one, as a subgroup of `SL₃(ℝ)`. -/
def SO3 : Subgroup SL3 where
  carrier := {k | (k : Mat) * (k : Mat)ᵀ = 1}
  one_mem' := by
    show ((1 : SL3) : Mat) * ((1 : SL3) : Mat)ᵀ = 1
    rw [Matrix.SpecialLinearGroup.coe_one, transpose_one, Matrix.mul_one]
  mul_mem' := by
    intro a b ha hb
    change (a : Mat) * (a : Mat)ᵀ = 1 at ha
    change (b : Mat) * (b : Mat)ᵀ = 1 at hb
    show ((a * b : SL3) : Mat) * ((a * b : SL3) : Mat)ᵀ = 1
    rw [coe_mul_eq, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (b : Mat), hb,
      Matrix.one_mul, ha]
  inv_mem' := by
    intro k hk
    change (k : Mat) * (k : Mat)ᵀ = 1 at hk
    show ((k⁻¹ : SL3) : Mat) * ((k⁻¹ : SL3) : Mat)ᵀ = 1
    have hk' : (k : Mat)ᵀ * (k : Mat) = 1 := mul_eq_one_comm.mp hk
    have hl := coe_inv_mul_eq k
    have hinv : ((k⁻¹ : SL3) : Mat) = (k : Mat)ᵀ := by
      calc ((k⁻¹ : SL3) : Mat) = ((k⁻¹ : SL3) : Mat) * ((k : Mat) * (k : Mat)ᵀ) := by
            rw [hk, Matrix.mul_one]
        _ = (((k⁻¹ : SL3) : Mat) * (k : Mat)) * (k : Mat)ᵀ := (Matrix.mul_assoc _ _ _).symm
        _ = (k : Mat)ᵀ := by rw [hl, Matrix.one_mul]
    rw [hinv, transpose_transpose]
    exact hk'

theorem mem_SO3_iff (k : SL3) : k ∈ SO3 ↔ (k : Mat) * (k : Mat)ᵀ = 1 := Iff.rfl

/-- `SO3` is the group of real orthogonal matrices of determinant one in Mathlib's sense. -/
theorem mem_SO3_iff_specialOrthogonalGroup (k : SL3) :
    k ∈ SO3 ↔ (k : Mat) ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff, mem_SO3_iff]
  constructor
  · intro h
    refine ⟨?_, k.det_coe⟩
    simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using h
  · rintro ⟨h, -⟩
    simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using h

/-- Positive definite real ternary matrices of determinant one. -/
def Pos1 : Type := {Q : Mat // Q.PosDef ∧ Q.det = 1}

@[ext] theorem Pos1.ext {Q R : Pos1} (h : Q.1 = R.1) : Q = R := Subtype.ext h

theorem gram_posDef (g : SL3) : ((g : Mat) * (g : Mat)ᵀ).PosDef := by
  have h := Matrix.PosDef.mul_conjTranspose_self (g : Mat)
    (Matrix.vecMul_injective_iff_isUnit.mpr (isUnit_coe g))
  simpa [conjTranspose_eq_transpose_of_trivial] using h

theorem gram_det (g : SL3) : ((g : Mat) * (g : Mat)ᵀ).det = 1 := by
  rw [det_mul, det_transpose, g.det_coe, mul_one]

/-- The Gram matrix `g gᵗ`. -/
def gramMap (g : SL3) : Pos1 := ⟨(g : Mat) * (g : Mat)ᵀ, gram_posDef g, gram_det g⟩

/-- The inverse of a positive definite matrix of determinant one. -/
def Pos1.inv (Q : Pos1) : Pos1 :=
  ⟨Q.1⁻¹, Q.2.1.inv, by rw [Matrix.det_nonsing_inv, Q.2.2]; simp⟩

theorem Pos1.inv_inv (Q : Pos1) : Q.inv.inv = Q := by
  apply Pos1.ext
  exact Matrix.nonsing_inv_nonsing_inv Q.1 (by rw [Q.2.2]; exact isUnit_one)

/-- The form `Q = (g gᵗ)⁻¹` attached to `g SO(3)`. -/
def formMap (g : SL3) : Pos1 := (gramMap g).inv

theorem formMap_val (g : SL3) : (formMap g).1 = ((g : Mat) * (g : Mat)ᵀ)⁻¹ := rfl

theorem exists_sqrt (P : Pos1) : ∃ g : SL3, (g : Mat) * (g : Mat)ᵀ = P.1 := by
  have h0 : 0 ≤ P.1 := Matrix.nonneg_iff_posSemidef.mpr P.2.1.posSemidef
  set S : Mat := CFC.sqrt P.1 with hS
  have hS0 : 0 ≤ S := CFC.sqrt_nonneg P.1
  have hSS : S * S = P.1 := CFC.sqrt_mul_sqrt_self P.1 h0
  have hSpsd : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hS0
  have hSh : Sᵀ = S := by
    have := hSpsd.isHermitian
    rw [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
    exact this
  have hdet : S.det = 1 := by
    have h1 : S.det * S.det = 1 := by rw [← det_mul, hSS, P.2.2]
    have h2 : 0 ≤ S.det := hSpsd.det_nonneg
    nlinarith
  refine ⟨⟨S, hdet⟩, ?_⟩
  change S * Sᵀ = P.1
  rw [hSh, hSS]

theorem gramMap_surjective : Function.Surjective gramMap := by
  intro P
  obtain ⟨g, hg⟩ := exists_sqrt P
  exact ⟨g, Pos1.ext hg⟩

/-- **(a), surjectivity:** every positive definite real ternary form of determinant one is `(g gᵗ)⁻¹` for some `g ∈ SL₃(ℝ)`. -/
theorem formMap_surjective : Function.Surjective formMap := by
  intro Q
  obtain ⟨g, hg⟩ := gramMap_surjective Q.inv
  exact ⟨g, by rw [formMap, hg, Pos1.inv_inv]⟩

theorem coe_eq_mul_inv_mul (g h : SL3) : (h : Mat) = (g : Mat) * ((g⁻¹ * h : SL3) : Mat) := by
  have := congrArg Subtype.val (mul_inv_cancel_left g h)
  rw [coe_mul_eq] at this
  exact this.symm

theorem isUnit_coe_transpose (g : SL3) : IsUnit (g : Mat)ᵀ := by
  rw [Matrix.isUnit_iff_isUnit_det, det_transpose, g.det_coe]; exact isUnit_one

/-- Gram matrices agree iff the two elements differ by an element of `SO(3)` on the right. -/
theorem gramMap_eq_iff (g h : SL3) : gramMap g = gramMap h ↔ g⁻¹ * h ∈ SO3 := by
  have hg := isUnit_coe g
  have hgT := isUnit_coe_transpose g
  have hh := coe_eq_mul_inv_mul g h
  set k : Mat := ((g⁻¹ * h : SL3) : Mat) with hk
  have key : (h : Mat) * (h : Mat)ᵀ = (g : Mat) * (k * kᵀ) * (g : Mat)ᵀ := by
    rw [hh, transpose_mul]
    simp only [Matrix.mul_assoc]
  constructor
  · intro e
    have e' : (g : Mat) * (g : Mat)ᵀ = (h : Mat) * (h : Mat)ᵀ := congrArg Subtype.val e
    rw [mem_SO3_iff]
    change k * kᵀ = 1
    rw [key] at e'
    have e2 : (g : Mat) * (1 : Mat) * (g : Mat)ᵀ = (g : Mat) * (k * kᵀ) * (g : Mat)ᵀ := by
      rw [Matrix.mul_one]; exact e'
    have e3 := (hgT.mul_left_inj.mp e2)
    exact ((hg.mul_right_inj.mp e3)).symm
  · intro hmem
    rw [mem_SO3_iff] at hmem
    change k * kᵀ = 1 at hmem
    apply Pos1.ext
    change (g : Mat) * (g : Mat)ᵀ = (h : Mat) * (h : Mat)ᵀ
    rw [key, hmem, Matrix.mul_one]


/-- **(a), the fibres:** `(g gᵗ)⁻¹ = (h hᵗ)⁻¹` iff `g⁻¹ h ∈ SO(3)`. -/
theorem formMap_eq_iff (g h : SL3) : formMap g = formMap h ↔ g⁻¹ * h ∈ SO3 := by
  rw [← gramMap_eq_iff]
  constructor
  · intro e
    have := congrArg Pos1.inv e
    unfold formMap at this
    rwa [Pos1.inv_inv, Pos1.inv_inv] at this
  · intro e
    exact congrArg Pos1.inv e

theorem unit_leftFactor (g : SL3) : IsUnit ((g⁻¹ : SL3) : Mat) := isUnit_coe _

/-- The left action `g · Q = g^{-t} Q g⁻¹` of `SL₃(ℝ)` on positive definite forms of determinant one. -/
def leftAct (g : SL3) (Q : Pos1) : Pos1 :=
  ⟨((g⁻¹ : SL3) : Mat)ᵀ * Q.1 * ((g⁻¹ : SL3) : Mat), by
    have h := (Matrix.IsUnit.posDef_star_left_conjugate_iff (x := Q.1) (unit_leftFactor g)).mpr Q.2.1
    simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using h, by
    rw [det_mul, det_mul, det_transpose, (g⁻¹).det_coe, Q.2.2]; simp⟩

/-- The right action `Q ↦ gᵗ Q g`. -/
def rightAct (g : SL3) (Q : Pos1) : Pos1 :=
  ⟨(g : Mat)ᵀ * Q.1 * (g : Mat), by
    have h := (Matrix.IsUnit.posDef_star_left_conjugate_iff (x := Q.1) (isUnit_coe g)).mpr Q.2.1
    simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using h, by
    rw [det_mul, det_mul, det_transpose, g.det_coe, Q.2.2]; simp⟩

theorem leftAct_eq_rightAct_inv (g : SL3) (Q : Pos1) : leftAct g Q = rightAct g⁻¹ Q := rfl

theorem rightAct_one (Q : Pos1) : rightAct 1 Q = Q := by
  apply Pos1.ext
  change ((1 : SL3) : Mat)ᵀ * Q.1 * ((1 : SL3) : Mat) = Q.1
  rw [Matrix.SpecialLinearGroup.coe_one, transpose_one, Matrix.one_mul, Matrix.mul_one]

/-- The right action: `Q · (g h) = (Q · g) · h`. -/
theorem rightAct_mul (g h : SL3) (Q : Pos1) : rightAct (g * h) Q = rightAct h (rightAct g Q) := by
  apply Pos1.ext
  change ((g * h : SL3) : Mat)ᵀ * Q.1 * ((g * h : SL3) : Mat) =
    (h : Mat)ᵀ * ((g : Mat)ᵀ * Q.1 * (g : Mat)) * (h : Mat)
  rw [coe_mul_eq, transpose_mul]
  simp only [Matrix.mul_assoc]

instance : MulAction SL3 Pos1 where
  smul := leftAct
  one_smul Q := by
    show leftAct 1 Q = Q
    rw [leftAct_eq_rightAct_inv, inv_one, rightAct_one]
  mul_smul g h Q := by
    show leftAct (g * h) Q = leftAct g (leftAct h Q)
    simp only [leftAct_eq_rightAct_inv, _root_.mul_inv_rev, rightAct_mul]

theorem smul_def (g : SL3) (Q : Pos1) : g • Q = leftAct g Q := rfl

theorem smul_val (g : SL3) (Q : Pos1) :
    (g • Q).1 = ((g⁻¹ : SL3) : Mat)ᵀ * Q.1 * ((g⁻¹ : SL3) : Mat) := rfl

theorem coe_inv_eq (h : SL3) : ((h⁻¹ : SL3) : Mat) = (h : Mat)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  have := congrArg Subtype.val (mul_inv_cancel h)
  rwa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at this

/-- The map `g ↦ (g gᵗ)⁻¹` is equivariant for left multiplication and the left action `g·Q = g^{-t} Q g⁻¹`. -/
theorem formMap_mul (h g : SL3) : formMap (h * g) = h • formMap g := by
  apply Pos1.ext
  rw [smul_val, formMap_val, formMap_val, coe_mul_eq, transpose_mul, coe_inv_eq,
    Matrix.transpose_nonsing_inv]
  have e : (h : Mat) * (g : Mat) * ((g : Mat)ᵀ * (h : Mat)ᵀ) =
      (h : Mat) * ((g : Mat) * (g : Mat)ᵀ) * (h : Mat)ᵀ := by simp only [Matrix.mul_assoc]
  rw [e, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]


/-- The congruence action `g · P = g P gᵗ` on Gram matrices (the action used by the analytic appendix and by `TernaryPoly.SymmetricSpaceOrientation.congruence`). -/
def gramAct (g : SL3) (P : Pos1) : Pos1 :=
  ⟨(g : Mat) * P.1 * (g : Mat)ᵀ, by
    have h := (Matrix.IsUnit.posDef_star_right_conjugate_iff (x := P.1) (isUnit_coe g)).mpr P.2.1
    simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using h, by
    rw [det_mul, det_mul, det_transpose, g.det_coe, P.2.2]; simp⟩

theorem gramMap_mul (h g : SL3) : gramMap (h * g) = gramAct h (gramMap g) := by
  apply Pos1.ext
  change ((h * g : SL3) : Mat) * ((h * g : SL3) : Mat)ᵀ =
    (h : Mat) * ((g : Mat) * (g : Mat)ᵀ) * (h : Mat)ᵀ
  rw [coe_mul_eq, transpose_mul]
  simp only [Matrix.mul_assoc]

/-- Inversion `Q ↦ Q⁻¹` exchanges the left action on forms with the congruence action on Gram matrices. -/
theorem inv_leftAct (g : SL3) (Q : Pos1) : (g • Q).inv = gramAct g Q.inv := by
  apply Pos1.ext
  change ((((g⁻¹ : SL3) : Mat)ᵀ * Q.1 * ((g⁻¹ : SL3) : Mat)))⁻¹ = (g : Mat) * Q.1⁻¹ * (g : Mat)ᵀ
  rw [coe_inv_eq, Matrix.transpose_nonsing_inv, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_coe g)),
    Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_coe_transpose g))]
  simp only [Matrix.mul_assoc]

/-- The map from cosets: `g SO(3) ↦ (g gᵗ)⁻¹`. -/
def quotMap : SL3 ⧸ SO3 → Pos1 :=
  Quotient.lift formMap (fun a b hab => (formMap_eq_iff a b).mpr (QuotientGroup.leftRel_apply.mp hab))

theorem quotMap_mk (g : SL3) : quotMap (g : SL3 ⧸ SO3) = formMap g := rfl

/-- **(a), the bijection:** `g SO(3) ↦ (g gᵗ)⁻¹` is a bijection `SL₃(ℝ)/SO(3) → {Q > 0, det Q = 1}`. -/
theorem quotMap_bijective : Function.Bijective quotMap := by
  constructor
  · intro x y
    induction x using QuotientGroup.induction_on with
    | H a =>
    induction y using QuotientGroup.induction_on with
    | H b =>
    intro h
    rw [quotMap_mk, quotMap_mk, formMap_eq_iff] at h
    exact QuotientGroup.eq.mpr h
  · intro Q
    obtain ⟨g, hg⟩ := formMap_surjective Q
    exact ⟨g, hg⟩

/-- `SL₃(ℝ)/SO(3) ≃ {Q positive definite, det Q = 1}`, `g SO(3) ↦ (g gᵗ)⁻¹`. -/
def quotEquiv : SL3 ⧸ SO3 ≃ Pos1 := Equiv.ofBijective quotMap quotMap_bijective

theorem quotEquiv_mk (g : SL3) : quotEquiv (g : SL3 ⧸ SO3) = formMap g := rfl

/-- **(a), equivariance:** for the left action by multiplication on cosets and `g·Q = g^{-t} Q g⁻¹` on forms. -/
theorem quotEquiv_smul (h : SL3) (x : SL3 ⧸ SO3) : quotEquiv (h • x) = h • quotEquiv x := by
  induction x using QuotientGroup.induction_on with
  | H g =>
  change formMap (h * g) = h • formMap g
  exact formMap_mul h g

/-- The Gram-matrix version: `g SO(3) ↦ g gᵗ`, equivariant for congruence `g·P = g P gᵗ`. -/
def quotMapGram : SL3 ⧸ SO3 → Pos1 :=
  Quotient.lift gramMap (fun a b hab => (gramMap_eq_iff a b).mpr (QuotientGroup.leftRel_apply.mp hab))

theorem quotMapGram_bijective : Function.Bijective quotMapGram := by
  constructor
  · intro x y
    induction x using QuotientGroup.induction_on with
    | H a =>
    induction y using QuotientGroup.induction_on with
    | H b =>
    intro h
    exact QuotientGroup.eq.mpr ((gramMap_eq_iff a b).mp h)
  · intro P
    obtain ⟨g, hg⟩ := gramMap_surjective P
    exact ⟨g, hg⟩

def quotEquivGram : SL3 ⧸ SO3 ≃ Pos1 := Equiv.ofBijective quotMapGram quotMapGram_bijective

theorem quotEquivGram_smul (h : SL3) (x : SL3 ⧸ SO3) :
    quotEquivGram (h • x) = gramAct h (quotEquivGram x) := by
  induction x using QuotientGroup.induction_on with
  | H g =>
  change gramMap (h * g) = gramAct h (gramMap g)
  exact gramMap_mul h g

/-- The two coset models differ by inversion: `(g gᵗ)⁻¹ = (g gᵗ)^{-1}`. -/
theorem quotEquiv_eq_inv_gram (x : SL3 ⧸ SO3) : quotEquiv x = (quotEquivGram x).inv := by
  induction x using QuotientGroup.induction_on with
  | H g => rfl

end TernaryPeriodPolynomials.Argument.Identities.SymmetricSpace
