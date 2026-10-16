module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.Realization
public import TernaryPeriodPolynomials.Building.FreeResolution.Main
public import TernaryPeriodPolynomials.SymmetricSpace.Rational.GluingInterior
public import TernaryPeriodPolynomials.ArithmeticGroup.GL3Congruence.Basic
public import TernaryPeriodPolynomials.SymmetricSpace.Rational.GluingAction
public import TernaryPeriodPolynomials.Topology.SingularLocal.Homology.Generators

@[expose] public section



/-!
# Bridge between the library's `Γ(3)`-complex of the well-rounded retract and the bordification

The library works with rational Gram matrices `Q`, and the congruence action `Q ↦ hᵀ Q h`
(`FreeResolution.act`); the bordification `Glued` of the library is built from trace-one forms `S` with
the action `S ↦ g S gᵀ`.  The map `nu : Q ↦ [Q⁻¹]` intertwines them: with the contragredient action
`actMat g M = (g⁻¹)ᵀ M g⁻¹` of `IntegralGL3` on positive definite real forms (`PDMat`), `nu_smul` says
`nu (g • M) = g • nu M` for the standard action of `g` on `Glued` (`integralAction`).  Consequently the
realization of affine chains is equivariant (`affSing_smul`, `realize_smul`).  Also: real forms of the
vertices (`formR`, `formR_gram_posDef`: every vertex Gram matrix is positive definite).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.Lemma33.Retract

open TernaryPoly TernaryPoly.SymmetricSpaceRationalGluing TernaryPoly.EquivariantSingularResolution
  TernaryPoly.SingularLocalHomology
  TernaryPoly.SymmetricSpaceRationalAction
  TernaryPeriodPolynomials.FreeResolution GeneralEisenstein Matrix

/-- The real general linear group element of an integral one. -/
def realU : IntegralGL3 →* SymmetricSpacePositive.RealGL :=
  Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ)

/-- The real matrix of an integral matrix. -/
def realM (g : IntegralGL3) : Mat := (realU g).val

theorem realM_apply (g : IntegralGL3) (i j : Fin 3) :
    realM g i j = ((g : Matrix (Fin 3) (Fin 3) ℤ) i j : ℝ) := rfl

theorem realM_mul (g h : IntegralGL3) : realM (g * h) = realM g * realM h := by
  simp [realM]

theorem realM_inv_mul (g : IntegralGL3) : realM g⁻¹ * realM g = 1 := by
  rw [← realM_mul, inv_mul_cancel]
  simp [realM]

theorem realM_mul_inv (g : IntegralGL3) : realM g * realM g⁻¹ = 1 := by
  rw [← realM_mul, mul_inv_cancel]
  simp [realM]

theorem isUnit_realM (g : IntegralGL3) : IsUnit (realM g) := (realU g).isUnit

/-- The real matrix of a rational form. -/
def formR (A : Form) : Mat := A.map (Rat.castHom ℝ)

theorem formR_act (h : IntegralGL3) (A : Form) :
    formR (act h A) = (realM h)ᴴ * formR A * realM h := by
  have : (realM h) = (toQ h).map (Rat.castHom ℝ) := by
    ext i j
    simp [realM_apply, toQ]
  rw [this]
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, ← Matrix.transpose_map]
  simp only [formR, act, Matrix.map_mul]

theorem formR_A0_posDef : (formR A0).PosDef := by
  have hJ : (Matrix.vecMulVec (fun _ : Fin 3 => (1 : ℝ)) (star fun _ : Fin 3 => (1 : ℝ))).PosSemidef :=
    Matrix.posSemidef_vecMulVec_self_star _
  have e : formR A0 = (1 / 2 : ℝ) • (1 : Mat) + (1 / 2 : ℝ) •
      Matrix.vecMulVec (fun _ : Fin 3 => (1 : ℝ)) (star fun _ : Fin 3 => (1 : ℝ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [formR, A0, Matrix.vecMulVec_apply] <;> norm_num
  rw [e]
  exact (Matrix.PosDef.one.smul (by norm_num : (0 : ℝ) < 1 / 2)).add_posSemidef
    (hJ.smul (by norm_num : (0 : ℝ) ≤ 1 / 2))

theorem formR_gram_posDef (v : Vtx) : (formR v.gram).PosDef := by
  rw [v.gram_eq, formR_act]
  have hU : IsUnit (realM v.frame) := isUnit_realM _
  have := (Matrix.IsUnit.posDef_star_left_conjugate_iff (x := formR A0) hU).mpr formR_A0_posDef
  simpa [Matrix.star_eq_conjTranspose] using this

/-- The contragredient congruence action `M ↦ (g⁻¹)ᵀ M g⁻¹` on matrices. -/
def actMat (g : IntegralGL3) (M : Mat) : Mat := star (realM g⁻¹) * M * realM g⁻¹

theorem actMat_one (M : Mat) : actMat 1 M = M := by
  simp [actMat, realM]

theorem actMat_mul (g h : IntegralGL3) (M : Mat) : actMat (g * h) M = actMat g (actMat h M) := by
  simp only [actMat, _root_.mul_inv_rev, realM_mul, star_mul, Matrix.mul_assoc]

theorem actMat_posDef (g : IntegralGL3) {M : Mat} (hM : M.PosDef) : (actMat g M).PosDef :=
  (Matrix.IsUnit.posDef_star_left_conjugate_iff (isUnit_realM g⁻¹)).mpr hM

theorem actMat_sum {n : ℕ} (g : IntegralGL3) (t : Fin (n + 1) → ℝ) (M : Fin (n + 1) → Mat) :
    actMat g (∑ i, t i • M i) = ∑ i, t i • actMat g (M i) := by
  simp only [actMat, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

instance : MulAction IntegralGL3 PDMat where
  smul g M := ⟨actMat g M.1, actMat_posDef g M.2⟩
  one_smul M := Subtype.ext (actMat_one M.1)
  mul_smul g h M := Subtype.ext (actMat_mul g h M.1)

theorem smul_pd_val (g : IntegralGL3) (M : PDMat) : (g • M).1 = actMat g M.1 := rfl

theorem actMat_inv (g : IntegralGL3) {M : Mat} (hM : M.PosDef) :
    (actMat g M)⁻¹ = realM g * M⁻¹ * star (realM g) := by
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det _).mp hM.isUnit
  have h1 : realM g⁻¹ * realM g = 1 := realM_inv_mul g
  have h2 : realM g * realM g⁻¹ = 1 := realM_mul_inv g
  have h3 : star (realM g) * star (realM g⁻¹) = 1 := by rw [← star_mul, h1, star_one]
  have h4 : star (realM g⁻¹) * star (realM g) = 1 := by rw [← star_mul, h2, star_one]
  apply Matrix.inv_eq_right_inv
  have h5 : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  calc actMat g M * (realM g * M⁻¹ * star (realM g))
      = star (realM g⁻¹) * M * (realM g⁻¹ * realM g) * M⁻¹ * star (realM g) := by
        simp only [actMat, Matrix.mul_assoc]
    _ = 1 := by rw [h1, Matrix.mul_one, Matrix.mul_assoc (star (realM g⁻¹)), h5, Matrix.mul_one, h4]

theorem nu_smul (g : IntegralGL3) (M : PDMat) : nu (g • M) = g • nu M := by
  change embedding (nuSpace (g • M)) = integralAction g (embedding (nuSpace M))
  unfold integralAction
  have hr : realRational (integralRational g) = realU g := realRational_integral g
  rw [leftAction_embedding, hr]
  congr 1
  apply Subtype.ext
  change SymmetricSpacePositive.normalize ((actMat g M.1)⁻¹) =
    SymmetricSpacePositive.normalize (SymmetricSpacePositive.conjugate (realU g)
      (SymmetricSpacePositive.normalize M.1⁻¹))
  have hc : (M.1⁻¹).trace ≠ 0 := (M.2.inv.trace_pos).ne'
  have e1 : SymmetricSpacePositive.normalize (SymmetricSpacePositive.conjugate (realU g)
      (SymmetricSpacePositive.normalize M.1⁻¹)) =
      SymmetricSpacePositive.normalize (SymmetricSpacePositive.conjugate (realU g) M.1⁻¹) := by
    change SymmetricSpacePositive.normalize (SymmetricSpacePositive.conjugate (realU g)
      ((M.1⁻¹).trace⁻¹ • M.1⁻¹)) = _
    rw [SymmetricSpacePositive.conjugate_smul,
      SymmetricSpacePositive.normalize_smul _ (inv_ne_zero hc)]
  rw [e1, actMat_inv g M.2]
  rfl

theorem affSing_smul (g : IntegralGL3) {n : ℕ} (y : AffSimp PDMat n) :
    g • affSing y = affSing (fun i => g • y i) := by
  apply ((TopCat.of Glued).toSSetObjEquiv _).injective
  rw [FreeActionLinearization.singularEquiv_smul]
  ext t
  change g • nu (affMap n y t) = nu (affMap n (fun i => g • y i) t)
  rw [← nu_smul]
  congr 1
  apply Subtype.ext
  rw [smul_pd_val, affMap_val, affMap_val, actMat_sum]
  rfl

theorem realize_smul (g : IntegralGL3) (n : ℕ) (c : AffChain PDMat n) :
    (chainRep IntegralGL3 (TopCat.of Glued) n).ρ g (realize n c) =
      realize n (mapAff (g • ·) n c) := by
  have h : ((chainRep IntegralGL3 (TopCat.of Glued) n).ρ g) ∘ₗ realize n =
      realize n ∘ₗ mapAff (g • ·) n := by
    apply Finsupp.lhom_ext
    intro y a
    simp only [LinearMap.comp_apply, realize_single, mapAff_single, map_smul]
    congr 1
    exact (chainElement_smul IntegralGL3 (TopCat.of Glued) n g (affSing y)).trans
      (congrArg (sing (TopCat.of Glued)) (affSing_smul g y))
  exact LinearMap.congr_fun h c

end TernaryPeriodPolynomials.Argument.Lemma33.Retract
