module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtScalar
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtModular
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.DictionaryInjective
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.HeckeSum

@[expose] public section


/-!
# The level-three dictionary for an integer rotation weight

Formalized by Claude Sonnet 5.5 (AxiomCode).

Twins, for an integer rotation weight `wt` (odd or even), of the level-three dictionary: smooth
level-three vectors of rotation weight `wt` with holomorphic scalar function
`cuspScalarWeightedLinearWt σ wt 1 v` correspond to cusp forms of weight `-wt` for `Γ₁(3)`, and the
correspondence is injective.

* `levelThreeClassicalVectorsWt` is the space of such vectors;
* `levelThreeFormWt` and `levelThreeToCuspFormWt` give the cusp form and the linear map;
* `cuspScalarWeightedRealization_positiveWt` is the realization at a real matrix of positive
  determinant, with the determinant factor `wtFactor (-wt) det`;
* `levelThreeToCuspForm_injectiveWt` is the injectivity.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Manifold
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.MultiplicityOne
  (levelThreeValues levelThree_realization_exists_positive_nonzero)

namespace TernaryPeriodPolynomials.EvenLevelThree

/-- Smooth level-three vectors of rotation weight `wt` with holomorphic scalar realization. -/
def levelThreeClassicalVectorsWt (σ : CuspidalRepresentation) (wt : ℤ) :
    Submodule ℂ σ.smooth where
  carrier := {v | v.val ∈ levelThreeValues σ ∧
    (∀ angle : Circle, σ.π (atInfinity (binaryRotations angle)) v.val =
      (angle : ℂ) ^ wt • v.val) ∧
    MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (cuspScalarWeightedLinearWt σ wt 1 v)}
  zero_mem' := by
    refine ⟨(levelThreeValues σ).zero_mem, ?_, ?_⟩
    · intro angle
      simp
    · rw [map_zero]
      exact mdifferentiable_const
  add_mem' first second := by
    refine ⟨(levelThreeValues σ).add_mem first.1 second.1, ?_, ?_⟩
    · intro angle
      simp only [Submodule.coe_add, map_add, first.2.1 angle, second.2.1 angle, smul_add]
    · rw [map_add]
      exact first.2.2.add second.2.2
  smul_mem' scalar v member := by
    refine ⟨(levelThreeValues σ).smul_mem scalar member.1, ?_, ?_⟩
    · intro angle
      simp only [Submodule.coe_smul, map_smul, member.2.1 angle]
      exact smul_comm _ _ _
    · rw [map_smul]
      exact member.2.2.const_smul scalar

/-- The realization at a real matrix of positive determinant, for an integer rotation weight. -/
theorem cuspScalarWeightedRealization_positiveWt (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val →
      cusp.centralCharacter (realAdeleUnit unit) = 1)
    (wt : ℤ) (vector : cusp.smooth)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ wt • vector.val)
    (matrix : BinaryRealGL) (positive : 0 < matrix.val.det) (point : UpperHalfPlane) :
    cuspScalarWeightedRealizationWt cusp wt vector (atInfinity matrix) point =
      ((wtFactor (-wt) matrix.val.det : ℝ) : ℂ) * UpperHalfPlane.denom matrix point ^ wt *
        cuspScalarWeightedRealizationWt cusp wt vector 1
          ((matrix • point : UpperHalfPlane) : ℂ) := by
  have normalized_det :
      (GeneralLinearGroup.det (invertibleMatrix (binaryDetNormalizedMatrix matrix.val))).val = 1 := by
    change (invertibleMatrix (binaryDetNormalizedMatrix matrix.val)).val.det = 1
    rw [invertibleMatrix_val _ (by rw [binaryDetNormalizedMatrix_det _ positive]; norm_num),
      binaryDetNormalizedMatrix_det _ positive]
  rw [cuspScalarWeightedRealization_det_normalizeWt cusp central_positive wt vector matrix positive,
    cuspScalarWeightedRealization_det_oneWt cusp wt vector rotation _ normalized_det,
    binaryDetNormalized_smul matrix positive, binaryDetNormalized_denom matrix positive, mul_zpow]
  have power : ((Real.sqrt matrix.val.det : ℂ)⁻¹) ^ wt =
      ((wtFactor (-wt) matrix.val.det : ℝ) : ℂ) := by
    rw [wtFactor_eq_sqrt_zpow (-wt) positive, Complex.ofReal_zpow, _root_.zpow_neg, _root_.inv_zpow]
  rw [power]

/-- The slash invariant form of a classical level-three vector of rotation weight `wt`. -/
def levelThreeSlashInvariantWt (σ : CuspidalRepresentation) (wt : ℤ) (v : σ.smooth)
    (hv : v ∈ levelThreeClassicalVectorsWt σ wt) :
    SlashInvariantForm LevelThree.LevelThreeHeckeSum.levelThree (-wt) := by
  refine ⟨fun point => cuspScalarWeightedRealizationWt σ wt v 1 point, ?_⟩
  rintro matrix ⟨integral, hintegral, rfl⟩
  funext point
  rw [ModularForm.slash_apply]
  have determinant : (GeneralLinearGroup.det (SpecialLinearGroup.mapGL ℝ integral)).val = 1 :=
    (SpecialLinearGroup.map (algebraMap ℤ ℝ) integral).property
  simp only [UpperHalfPlane.σ, determinant, zero_lt_one, ite_true,
    ContinuousAlgEquiv.refl_apply, abs_one, Complex.ofReal_one, _root_.one_zpow, mul_one]
  rw [cuspScalarWeightedRealization_modular_levelThreeWt σ wt v hv.1 hv.2.1 integral hintegral
      point,
    mul_right_comm, ← zpow_add₀ (UpperHalfPlane.denom_ne_zero _ point), add_neg_cancel,
    zpow_zero, one_mul]

/-- The scalar function of a classical level-three vector vanishes at every cusp of `Γ₁(3)`. -/
theorem levelThreeSlashInvariant_zero_at_cuspsWt (σ : CuspidalRepresentation) (wt : ℤ)
    (negative : wt < 0) (v : σ.smooth) (hv : v ∈ levelThreeClassicalVectorsWt σ wt)
    {c : OnePoint ℝ} (is_cusp : IsCusp c LevelThree.LevelThreeHeckeSum.levelThree) :
    c.IsZeroAt (levelThreeSlashInvariantWt σ wt v hv) (-wt) := by
  have included : LevelThree.LevelThreeHeckeSum.levelThree ≤
      (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range := by
    rintro matrix ⟨integralMatrix, _, equality⟩
    exact ⟨integralMatrix, equality⟩
  apply (OnePoint.isZeroAt_iff_forall_SL2Z (is_cusp.mono included)).mpr
  intro matrix _
  change UpperHalfPlane.IsZeroAtImInfty (SlashAction.map (-wt)
    (SpecialLinearGroup.mapGL ℝ matrix)
    (fun point => cuspScalarWeightedRealizationWt σ wt v 1 point))
  have key := levelThree_slash_eqWt σ wt v hv.2.1 matrix
  have zero : UpperHalfPlane.IsZeroAtImInfty (cuspScalarWeightedLinearWt σ wt 1
      (cuspFiniteRationalSlash σ (SpecialLinearGroup.mapGL ℚ matrix) v)) :=
    cuspScalarWeightedRealization_zero_at_inftyWt σ wt negative
      (cuspFiniteRationalSlash σ (SpecialLinearGroup.mapGL ℚ matrix) v) 1
  rw [key] at zero
  exact zero

/-- **The cusp form of a classical level-three vector of rotation weight `wt`.** -/
def levelThreeFormWt (σ : CuspidalRepresentation) (wt : ℤ) (negative : wt < 0)
    (v : σ.smooth) (hv : v ∈ levelThreeClassicalVectorsWt σ wt) :
    CuspForm LevelThree.LevelThreeHeckeSum.levelThree (-wt) :=
  ⟨levelThreeSlashInvariantWt σ wt v hv, hv.2.2,
    levelThreeSlashInvariant_zero_at_cuspsWt σ wt negative v hv⟩

theorem levelThreeForm_coeWt (σ : CuspidalRepresentation) (wt : ℤ) (negative : wt < 0)
    (v : σ.smooth) (hv : v ∈ levelThreeClassicalVectorsWt σ wt) :
    (levelThreeFormWt σ wt negative v hv : UpperHalfPlane → ℂ) =
      cuspScalarWeightedLinearWt σ wt 1 v :=
  rfl

/-- The linear map from classical level-three vectors of rotation weight `wt` to cusp forms of
weight `-wt` for `Γ₁(3)`. -/
def levelThreeToCuspFormWt (σ : CuspidalRepresentation) (wt : ℤ) (negative : wt < 0) :
    levelThreeClassicalVectorsWt σ wt →ₗ[ℂ]
      CuspForm LevelThree.LevelThreeHeckeSum.levelThree (-wt) where
  toFun x := levelThreeFormWt σ wt negative x.1 x.2
  map_add' x y := by
    apply DFunLike.ext
    intro point
    change cuspScalarWeightedLinearWt σ wt 1 (x + y).1 point =
      cuspScalarWeightedLinearWt σ wt 1 x.1 point +
        cuspScalarWeightedLinearWt σ wt 1 y.1 point
    simp only [Submodule.coe_add, map_add, Pi.add_apply]
  map_smul' c x := by
    apply DFunLike.ext
    intro point
    change cuspScalarWeightedLinearWt σ wt 1 (c • x).1 point =
      c • cuspScalarWeightedLinearWt σ wt 1 x.1 point
    simp only [Submodule.coe_smul, map_smul, Pi.smul_apply]

theorem levelThreeToCuspForm_coeWt (σ : CuspidalRepresentation) (wt : ℤ)
    (negative : wt < 0) (x : levelThreeClassicalVectorsWt σ wt) :
    (levelThreeToCuspFormWt σ wt negative x : UpperHalfPlane → ℂ) =
      cuspScalarWeightedLinearWt σ wt 1 x.1 :=
  rfl

/-- A nonzero classical level-three vector of rotation weight `wt` has a nonzero scalar
function. -/
theorem levelThree_scalar_exists_nonzeroWt (σ : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → σ.centralCharacter (realAdeleUnit unit) = 1)
    (wt : ℤ) (v : σ.smooth) (hv : v ∈ levelThreeClassicalVectorsWt σ wt)
    (nonzero : v ≠ 0) :
    ∃ point : UpperHalfPlane, cuspScalarWeightedRealizationWt σ wt v 1 point ≠ 0 := by
  obtain ⟨real, positive, real_nonzero⟩ :=
    levelThree_realization_exists_positive_nonzero σ v hv.1 nonzero
  refine ⟨real • UpperHalfPlane.I, ?_⟩
  intro zero
  have identity := cuspScalarWeightedRealization_positiveWt σ central_positive wt v hv.2.1
    real positive UpperHalfPlane.I
  rw [zero, mul_zero] at identity
  exact real_nonzero (by simpa only [UpperHalfPlane.coe_I, cuspScalarWeightedRealization_IWt] using
    identity)

/-- **Injectivity of the dictionary**: a classical level-three vector with zero cusp form is
zero. -/
theorem levelThreeForm_eq_zeroWt (σ : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → σ.centralCharacter (realAdeleUnit unit) = 1)
    (wt : ℤ) (negative : wt < 0) (v : σ.smooth)
    (hv : v ∈ levelThreeClassicalVectorsWt σ wt)
    (zero : levelThreeFormWt σ wt negative v hv = 0) : v = 0 := by
  by_contra nonzero
  obtain ⟨point, point_nonzero⟩ := levelThree_scalar_exists_nonzeroWt σ central_positive wt
    v hv nonzero
  apply point_nonzero
  have equal := congrArg (fun form : CuspForm LevelThree.LevelThreeHeckeSum.levelThree
    (-wt) => (form : UpperHalfPlane → ℂ) point) zero
  exact equal

theorem levelThreeToCuspForm_injectiveWt (σ : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → σ.centralCharacter (realAdeleUnit unit) = 1)
    (wt : ℤ) (negative : wt < 0) :
    Function.Injective (levelThreeToCuspFormWt σ wt negative) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  apply Subtype.ext
  exact levelThreeForm_eq_zeroWt σ central_positive wt negative x.1 x.2 hx

end TernaryPeriodPolynomials.EvenLevelThree
