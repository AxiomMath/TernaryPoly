module

public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.Basic
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.HeckeSum

@[expose] public section


/-!
# The level-three dictionary: vectors of a cuspidal representation and cusp forms for `Γ₁(3)`

For a smooth vector `v` fixed by the level `{k₁₀ ≡ 0, k₁₁ ≡ 1 (mod 3)}`, of rotation weight
`2 * halfWeight`, with holomorphic scalar realization, the scalar function
`cuspScalarWeightedLinear σ halfWeight 1 v` is a cusp form of weight `-2 * halfWeight` for `Γ₁(3)`
(`levelThreeForm`), the level-three analogue of `cuspLevelOneCuspForm_of_holomorphic`.

* Invariance under `Γ₁(3)` uses that the finite image of `γ ∈ Γ₁(3)` satisfies the congruence
  condition (`planeLeviLevel_mapGL`).
* Vanishing at every cusp holds without any level: for `γ ∈ SL₂(ℤ)` the slash `f ∣ γ` is the scalar
  function of the translate `cuspFiniteRationalSlash σ γ v`, which is again a smooth vector and so
  has moderate growth (`levelThree_slash_eq`).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Manifold
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Separation (PlaneLeviLevel)

namespace TernaryPeriodPolynomials.MultiplicityOne

/-- The finite image of an element of `Γ₁(3)` satisfies the second-row congruence. -/
theorem planeLeviLevel_mapGL {γ : SpecialLinearGroup (Fin 2) ℤ}
    (hγ : γ ∈ CongruenceSubgroup.Gamma1 3) :
    PlaneLeviLevel (SpecialLinearGroup.mapGL IntegralAdeles γ) := by
  rw [CongruenceSubgroup.Gamma1_mem] at hγ
  obtain ⟨-, h11, h10⟩ := hγ
  have entry (i j : Fin 2) : (GeneralLinearGroup.map integralReduction
      (SpecialLinearGroup.mapGL IntegralAdeles γ)).val i j = ((γ.val i j : ℤ) : ZMod 3) := by
    simp only [GeneralLinearGroup.map_apply, SpecialLinearGroup.mapGL_coe_matrix,
      SpecialLinearGroup.map_apply_coe]
    change integralReduction (algebraMap ℤ IntegralAdeles (γ.val i j)) = _
    simp
  exact And.intro ((entry 1 0).trans h10) ((entry 1 1).trans h11)

/-- Level-three vectors are fixed by the rational finite image of `Γ₁(3)`. -/
theorem levelThree_fixed_gamma (σ : CuspidalRepresentation) {v : σ.H}
    (hv : v ∈ levelThreeValues σ) {γ : SpecialLinearGroup (Fin 2) ℤ}
    (hγ : γ ∈ CongruenceSubgroup.Gamma1 3) :
    σ.π (atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles)
      (SpecialLinearGroup.mapGL ℚ γ))) v = v := by
  have equality : GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles)
      (SpecialLinearGroup.mapGL ℚ γ) =
      GeneralLinearGroup.map integralEmbedding (SpecialLinearGroup.mapGL IntegralAdeles γ) := by
    apply Units.ext
    funext row column
    simp only [GeneralLinearGroup.map_apply, SpecialLinearGroup.mapGL_coe_matrix,
      SpecialLinearGroup.map_apply_coe]
    change algebraMap ℚ FiniteAdeles (algebraMap ℤ ℚ (γ.val row column)) =
      integralEmbedding (algebraMap ℤ IntegralAdeles (γ.val row column))
    simp
  rw [equality]
  exact hv _ (planeLeviLevel_mapGL hγ)

/-- The modular transformation of the scalar function under `Γ₁(3)`. -/
theorem cuspScalarWeightedRealization_modular_levelThree (σ : CuspidalRepresentation)
    (halfWeight : ℤ) (v : σ.smooth) (hv : v ∈ levelThreeClassicalVectors σ halfWeight)
    (γ : SpecialLinearGroup (Fin 2) ℤ) (hγ : γ ∈ CongruenceSubgroup.Gamma1 3)
    (point : UpperHalfPlane) :
    cuspScalarWeightedRealization σ halfWeight v 1
        ((SpecialLinearGroup.mapGL ℝ γ • point : UpperHalfPlane) : ℂ) =
      UpperHalfPlane.denom (SpecialLinearGroup.mapGL ℝ γ) point ^ (-2 * halfWeight) *
        cuspScalarWeightedRealization σ halfWeight v 1 point := by
  have determinant : (GeneralLinearGroup.det
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) (SpecialLinearGroup.mapGL ℚ γ))).val = 1 := by
    rw [binaryIntegral_specialLinear_real]
    exact (SpecialLinearGroup.map (algebraMap ℤ ℝ) γ).property
  simpa only [binaryIntegral_specialLinear_real] using
    cuspScalarWeightedRealization_modular σ halfWeight v hv.2.1 (SpecialLinearGroup.mapGL ℚ γ)
      determinant (levelThree_fixed_gamma σ hv.1 hγ) point

/-- The slash of the scalar function by a rational matrix of determinant one is the scalar function
of the finite translate; no level and no central character are needed. -/
theorem cuspFiniteRationalSlash_scalar_det_one (σ : CuspidalRepresentation) (halfWeight : ℤ)
    (v : σ.smooth)
    (rotation : ∀ angle : Circle, σ.π (atInfinity (binaryRotations angle)) v.val =
      (angle : ℂ) ^ (2 * halfWeight) • v.val)
    (rational : BinaryRationalGL)
    (determinant : (GeneralLinearGroup.det
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) rational)).val = 1) :
    cuspScalarWeightedLinear σ halfWeight 1 (cuspFiniteRationalSlash σ rational v) =
      SlashAction.map (-2 * halfWeight) (GeneralLinearGroup.map (algebraMap ℚ ℝ) rational)
        (cuspScalarWeightedLinear σ halfWeight 1 v) := by
  funext point
  have det_positive : 0 < (GeneralLinearGroup.det
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) rational)).val := by
    rw [determinant]
    exact zero_lt_one
  rw [cuspFiniteRationalSlash_weighted,
    cuspScalarWeightedRealization_det_one σ halfWeight v rotation _ determinant point,
    ModularForm.slash_apply]
  have sigma : UpperHalfPlane.σ (GeneralLinearGroup.map (algebraMap ℚ ℝ) rational) =
      ContinuousAlgEquiv.refl ℝ ℂ := by
    unfold UpperHalfPlane.σ
    rw [ite_eq_left det_positive]
  rw [sigma, ContinuousAlgEquiv.refl_apply, determinant, abs_one]
  have negative : -(-2 * halfWeight) = 2 * halfWeight := by ring
  rw [negative]
  change _ = cuspScalarWeightedRealization σ halfWeight v 1 _ * _ * _
  simp only [Complex.ofReal_one, _root_.one_zpow, mul_one]
  exact mul_comm _ _

/-- The slash by `γ ∈ SL₂(ℤ)` of the scalar function of `v` is the scalar function of the
translate `cuspFiniteRationalSlash σ γ v`. -/
theorem levelThree_slash_eq (σ : CuspidalRepresentation) (halfWeight : ℤ) (v : σ.smooth)
    (rotation : ∀ angle : Circle, σ.π (atInfinity (binaryRotations angle)) v.val =
      (angle : ℂ) ^ (2 * halfWeight) • v.val)
    (γ : SpecialLinearGroup (Fin 2) ℤ) :
    cuspScalarWeightedLinear σ halfWeight 1
        (cuspFiniteRationalSlash σ (SpecialLinearGroup.mapGL ℚ γ) v) =
      SlashAction.map (-2 * halfWeight) (SpecialLinearGroup.mapGL ℝ γ)
        (cuspScalarWeightedLinear σ halfWeight 1 v) := by
  have determinant : (GeneralLinearGroup.det
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) (SpecialLinearGroup.mapGL ℚ γ))).val = 1 := by
    rw [binaryIntegral_specialLinear_real]
    exact (SpecialLinearGroup.map (algebraMap ℤ ℝ) γ).property
  have key := cuspFiniteRationalSlash_scalar_det_one σ halfWeight v rotation
    (SpecialLinearGroup.mapGL ℚ γ) determinant
  rw [binaryIntegral_specialLinear_real] at key
  exact key

/-- The slash invariant form of a classical level-three vector. -/
def levelThreeSlashInvariant (σ : CuspidalRepresentation) (halfWeight : ℤ) (v : σ.smooth)
    (hv : v ∈ levelThreeClassicalVectors σ halfWeight) :
    SlashInvariantForm LevelThree.LevelThreeHeckeSum.levelThree (-2 * halfWeight) := by
  refine ⟨fun point => cuspScalarWeightedRealization σ halfWeight v 1 point, ?_⟩
  rintro matrix ⟨integral, hintegral, rfl⟩
  funext point
  rw [ModularForm.slash_apply]
  have determinant : (GeneralLinearGroup.det (SpecialLinearGroup.mapGL ℝ integral)).val = 1 :=
    (SpecialLinearGroup.map (algebraMap ℤ ℝ) integral).property
  simp only [UpperHalfPlane.σ, determinant, zero_lt_one, ite_true,
    ContinuousAlgEquiv.refl_apply, abs_one, Complex.ofReal_one, _root_.one_zpow, mul_one]
  rw [cuspScalarWeightedRealization_modular_levelThree σ halfWeight v hv integral hintegral point,
    mul_right_comm, ← zpow_add₀ (UpperHalfPlane.denom_ne_zero _ point), add_neg_cancel,
    zpow_zero, one_mul]

/-- The scalar function of a classical level-three vector vanishes at every cusp of `Γ₁(3)`. -/
theorem levelThreeSlashInvariant_zero_at_cusps (σ : CuspidalRepresentation) (halfWeight : ℤ)
    (negative : halfWeight < 0) (v : σ.smooth)
    (hv : v ∈ levelThreeClassicalVectors σ halfWeight) {c : OnePoint ℝ}
    (is_cusp : IsCusp c LevelThree.LevelThreeHeckeSum.levelThree) :
    c.IsZeroAt (levelThreeSlashInvariant σ halfWeight v hv) (-2 * halfWeight) := by
  have included : LevelThree.LevelThreeHeckeSum.levelThree ≤
      (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range := by
    rintro matrix ⟨integralMatrix, _, equality⟩
    exact ⟨integralMatrix, equality⟩
  apply (OnePoint.isZeroAt_iff_forall_SL2Z (is_cusp.mono included)).mpr
  intro matrix _
  change UpperHalfPlane.IsZeroAtImInfty (SlashAction.map (-2 * halfWeight)
    (SpecialLinearGroup.mapGL ℝ matrix)
    (fun point => cuspScalarWeightedRealization σ halfWeight v 1 point))
  have key := levelThree_slash_eq σ halfWeight v hv.2.1 matrix
  have zero : UpperHalfPlane.IsZeroAtImInfty (cuspScalarWeightedLinear σ halfWeight 1
      (cuspFiniteRationalSlash σ (SpecialLinearGroup.mapGL ℚ matrix) v)) :=
    cuspScalarWeightedRealization_zero_at_infty σ halfWeight negative
      (cuspFiniteRationalSlash σ (SpecialLinearGroup.mapGL ℚ matrix) v) 1
  rw [key] at zero
  exact zero

/-- **The cusp form of a classical level-three vector.** -/
def levelThreeForm (σ : CuspidalRepresentation) (halfWeight : ℤ) (negative : halfWeight < 0)
    (v : σ.smooth) (hv : v ∈ levelThreeClassicalVectors σ halfWeight) :
    CuspForm LevelThree.LevelThreeHeckeSum.levelThree (-2 * halfWeight) :=
  ⟨levelThreeSlashInvariant σ halfWeight v hv, hv.2.2,
    levelThreeSlashInvariant_zero_at_cusps σ halfWeight negative v hv⟩

theorem levelThreeForm_coe (σ : CuspidalRepresentation) (halfWeight : ℤ) (negative : halfWeight < 0)
    (v : σ.smooth) (hv : v ∈ levelThreeClassicalVectors σ halfWeight) :
    (levelThreeForm σ halfWeight negative v hv : UpperHalfPlane → ℂ) =
      cuspScalarWeightedLinear σ halfWeight 1 v :=
  rfl

/-- The linear map from classical level-three vectors to cusp forms for `Γ₁(3)`. -/
def levelThreeToCuspForm (σ : CuspidalRepresentation) (halfWeight : ℤ) (negative : halfWeight < 0) :
    levelThreeClassicalVectors σ halfWeight →ₗ[ℂ]
      CuspForm LevelThree.LevelThreeHeckeSum.levelThree (-2 * halfWeight) where
  toFun x := levelThreeForm σ halfWeight negative x.1 x.2
  map_add' x y := by
    apply DFunLike.ext
    intro point
    change cuspScalarWeightedLinear σ halfWeight 1 (x + y).1 point =
      cuspScalarWeightedLinear σ halfWeight 1 x.1 point +
        cuspScalarWeightedLinear σ halfWeight 1 y.1 point
    simp only [Submodule.coe_add, map_add, Pi.add_apply]
  map_smul' c x := by
    apply DFunLike.ext
    intro point
    change cuspScalarWeightedLinear σ halfWeight 1 (c • x).1 point =
      c • cuspScalarWeightedLinear σ halfWeight 1 x.1 point
    simp only [Submodule.coe_smul, map_smul, Pi.smul_apply]

theorem levelThreeToCuspForm_coe (σ : CuspidalRepresentation) (halfWeight : ℤ)
    (negative : halfWeight < 0) (x : levelThreeClassicalVectors σ halfWeight) :
    (levelThreeToCuspForm σ halfWeight negative x : UpperHalfPlane → ℂ) =
      cuspScalarWeightedLinear σ halfWeight 1 x.1 :=
  rfl

end TernaryPeriodPolynomials.MultiplicityOne
