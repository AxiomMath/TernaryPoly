module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.SobolevBounds
public import Mathlib.Analysis.LocallyConvex.WithSeminorms

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevBounds
open scoped Matrix.Norms.Elementwise NNReal

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms

def binaryDomain : Set BinaryMatrix := {matrix | matrix.det ≠ 0}

theorem binaryDomain_isOpen : IsOpen binaryDomain := isOpen_ne.preimage continuous_id.matrix_det

theorem smooth_singleton {size : ℕ} {Target : Type}
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (function : Matrix.GeneralLinearGroup (Fin size) ℝ → Target)
    (smoothFunction : Smooth (fun matrices : Fin 1 → Matrix.GeneralLinearGroup (Fin size) ℝ =>
      function (matrices 0))) :
    ContDiffOn ℝ ⊤ (fun matrix : Matrix (Fin size) (Fin size) ℝ => function (invertibleMatrix matrix))
      {matrix | matrix.det ≠ 0} := by
  change ContDiffOn ℝ ⊤
    (fun matrices : Fin 1 → Matrix (Fin size) (Fin size) ℝ =>
      function (invertibleMatrix (matrices 0)))
    (TernaryPeriodPolynomials.PlaneEisensteinContinuation.SmoothBounds.matrixDomain size 1) at smoothFunction
  have smoothDiagonal : ContDiff ℝ ⊤
      (fun matrix : Matrix (Fin size) (Fin size) ℝ => fun _ : Fin 1 => matrix) :=
    contDiff_pi.mpr (fun _ => contDiff_id)
  have mapsTo : Set.MapsTo
      (fun matrix : Matrix (Fin size) (Fin size) ℝ => fun _ : Fin 1 => matrix)
      {matrix | matrix.det ≠ 0} (TernaryPeriodPolynomials.PlaneEisensteinContinuation.SmoothBounds.matrixDomain size 1) :=
    fun _ membership _ => membership
  exact smoothFunction.comp smoothDiagonal.contDiffOn mapsTo

theorem smooth_orbit_contDiffOn (data : CuspidalRepresentation) (vector : data.smooth) :
    ContDiffOn ℝ ⊤
      (fun matrix : BinaryMatrix => data.π (atInfinity (invertibleMatrix matrix)) vector.val)
      binaryDomain :=
  smooth_singleton (fun matrix => data.π (atInfinity matrix) vector.val)
    (((data.smooth_exact vector.val).mp vector.property).1)

theorem smooth_orbit_contDiffAt_one (data : CuspidalRepresentation) (vector : data.smooth) :
    ContDiffAt ℝ ⊤
      (fun matrix : BinaryMatrix => data.π (atInfinity (invertibleMatrix matrix)) vector.val) 1 := by
  have membership : (1 : BinaryMatrix) ∈ binaryDomain := by simp [binaryDomain]
  exact (smooth_orbit_contDiffOn data vector 1 membership).contDiffAt
    (binaryDomain_isOpen.mem_nhds membership)

theorem orbitDerivative_add (data : CuspidalRepresentation) (order : ℕ) (first second : data.smooth) :
    orbitDerivative data order (first + second).val =
      orbitDerivative data order first.val + orbitDerivative data order second.val := by
  have equality :
      (fun matrix : BinaryMatrix => data.π (atInfinity (invertibleMatrix matrix)) (first + second).val) =
      (fun matrix => data.π (atInfinity (invertibleMatrix matrix)) first.val) +
        (fun matrix => data.π (atInfinity (invertibleMatrix matrix)) second.val) := by
    funext matrix
    exact map_add _ _ _
  exact (congrArg (fun function : BinaryMatrix → data.H => iteratedFDeriv ℝ order function 1) equality).trans
    (iteratedFDeriv_add_apply ((smooth_orbit_contDiffAt_one data first).of_le le_top)
      ((smooth_orbit_contDiffAt_one data second).of_le le_top))

theorem orbitDerivative_smul (data : CuspidalRepresentation) (order : ℕ) (scalar : ℂ)
    (vector : data.smooth) :
    orbitDerivative data order (scalar • vector).val = scalar • orbitDerivative data order vector.val := by
  have equality :
      (fun matrix : BinaryMatrix => data.π (atInfinity (invertibleMatrix matrix)) (scalar • vector).val) =
      scalar • (fun matrix => data.π (atInfinity (invertibleMatrix matrix)) vector.val) := by
    funext matrix
    exact map_smul _ _ _
  exact (congrArg (fun function : BinaryMatrix → data.H => iteratedFDeriv ℝ order function 1) equality).trans
    (iteratedFDeriv_const_smul_apply ((smooth_orbit_contDiffAt_one data vector).of_le le_top))

noncomputable def orbitDerivativeLinear (data : CuspidalRepresentation) (order : ℕ) :
    data.smooth →ₗ[ℂ] ContinuousMultilinearMap ℝ (fun _ : Fin order => BinaryMatrix) data.H where
  toFun vector := orbitDerivative data order vector.val
  map_add' := orbitDerivative_add data order
  map_smul' := orbitDerivative_smul data order

noncomputable instance binaryMultilinearComplexNormedSpace (data : CuspidalRepresentation) (order : ℕ) :
    NormedSpace ℂ (ContinuousMultilinearMap ℝ (fun _ : Fin order => BinaryMatrix) data.H) :=
  ContinuousMultilinearMap.normedSpace

noncomputable def orbitSeminorm (data : CuspidalRepresentation) (order : ℕ) : Seminorm ℂ data.smooth :=
  (normSeminorm ℂ (ContinuousMultilinearMap ℝ (fun _ : Fin order => BinaryMatrix) data.H)).comp
    (orbitDerivativeLinear data order)

noncomputable def sobolevSeminorm (data : CuspidalRepresentation) (order : ℕ) : Seminorm ℂ data.smooth :=
  ∑ derivativeOrder ∈ Finset.range (order + 1), orbitSeminorm data derivativeOrder

theorem orbitSeminorm_apply (data : CuspidalRepresentation) (order : ℕ) (vector : data.smooth) :
    orbitSeminorm data order vector = ‖orbitDerivative data order vector.val‖ := rfl

theorem sobolevSeminorm_apply (data : CuspidalRepresentation) (order : ℕ) (vector : data.smooth) :
    sobolevSeminorm data order vector = orbitSobolevNorm data order vector.val := by
  classical
  unfold sobolevSeminorm orbitSobolevNorm
  generalize Finset.range (order + 1) = indices
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert index indices nonmembership inductionHypothesis =>
    rw [Finset.sum_insert nonmembership, Finset.sum_insert nonmembership,
      add_apply, inductionHypothesis, orbitSeminorm_apply]

theorem sobolevSeminorm_mono (data : CuspidalRepresentation) : Monotone (sobolevSeminorm data) := by
  intro first second inequality vector
  rw [sobolevSeminorm_apply, sobolevSeminorm_apply]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.add_le_add_right inequality 1)) (fun _ _ _ => norm_nonneg _)

theorem sobolevSeminorm_eq_zero (data : CuspidalRepresentation) (order : ℕ) (vector : data.smooth) :
    sobolevSeminorm data order vector = 0 ↔ vector = 0 := by
  constructor
  · intro zeroNorm
    apply Subtype.ext
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    exact (norm_le_orbitSobolevNorm data order vector.val).trans
      ((sobolevSeminorm_apply data order vector).symm.trans zeroNorm).le
  · rintro rfl
    exact map_zero _

def fixedSmooth (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL) :
    Submodule ℂ data.smooth :=
  (TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.fixedSubspace data level).comap data.smooth.subtype

noncomputable def fixedSeminorms (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL) :
    SeminormFamily ℂ (fixedSmooth data level) ℕ :=
  fun order => (sobolevSeminorm data order).comp (fixedSmooth data level).subtype

theorem fixedSeminorms_apply (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (order : ℕ) (vector : fixedSmooth data level) :
    fixedSeminorms data level order vector = orbitSobolevNorm data order vector.val.val :=
  sobolevSeminorm_apply data order vector.val

theorem fixedSeminorms_mono (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL) :
    Monotone (fixedSeminorms data level) := by
  intro first second inequality
  exact Seminorm.comp_mono (fixedSmooth data level).subtype (sobolevSeminorm_mono data inequality)

@[instance_reducible] noncomputable def fixedTopology (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL) :
    TopologicalSpace (fixedSmooth data level) := (fixedSeminorms data level).moduleFilterBasis.topology

theorem fixedTopology_withSeminorms (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL) :
    letI := fixedTopology data level
    WithSeminorms (fixedSeminorms data level) := by
  let _ := fixedTopology data level
  exact ⟨rfl⟩

theorem fixed_continuous_iff_sobolev_bound (data : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) {Target : Type}
    [NormedAddCommGroup Target] [NormedSpace ℂ Target]
    (linear : fixedSmooth data level →ₗ[ℂ] Target) :
    letI := fixedTopology data level
    Continuous linear ↔ ∃ order : ℕ, ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ vector : fixedSmooth data level,
        ‖linear vector‖ ≤ constant * orbitSobolevNorm data order vector.val.val := by
  let _ := fixedTopology data level
  have seminormTopology := fixedTopology_withSeminorms data level
  constructor
  · intro continuity
    let targetSeminorm : Seminorm ℂ (fixedSmooth data level) := (normSeminorm ℂ Target).comp linear
    have seminormContinuity : Continuous targetSeminorm := continuity.norm
    obtain ⟨indices, constant, _, bound⟩ :=
      Seminorm.bound_of_continuous seminormTopology targetSeminorm seminormContinuity
    let order := indices.sup id
    have domination : indices.sup (fixedSeminorms data level) ≤ fixedSeminorms data level order := by
      apply Finset.sup_le
      intro index membership
      exact fixedSeminorms_mono data level (Finset.le_sup (f := id) membership)
    refine ⟨order, constant, constant.property, ?_⟩
    intro vector
    have boundAt := bound vector
    change ‖linear vector‖ ≤ (constant : ℝ) * (indices.sup (fixedSeminorms data level)) vector at boundAt
    rw [← fixedSeminorms_apply data level order vector]
    exact boundAt.trans (mul_le_mul_of_nonneg_left (domination vector) constant.property)
  · rintro ⟨order, constant, nonnegativeConstant, estimate⟩
    apply seminormTopology.continuous_normedSpace_rng Target linear
    refine ⟨{order}, (⟨constant, nonnegativeConstant⟩ : ℝ≥0), ?_⟩
    intro vector
    change ‖linear vector‖ ≤ constant * (({order} : Finset ℕ).sup (fixedSeminorms data level)) vector
    rw [Finset.sup_singleton, fixedSeminorms_apply]
    exact estimate vector

noncomputable def fixedRealization (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL) :
    fixedSmooth data level →ₗ[ℂ] lp (fun _ : BinaryAdelicGL => ℂ) ⊤ :=
  (TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm.boundedRealization data).comp (fixedSmooth data level).subtype

theorem fixedRealization_continuous_iff (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL) :
    letI := fixedTopology data level
    Continuous (fixedRealization data level) ↔ ∃ order : ℕ, ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ vector : data.smooth, vector.val ∈ TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.fixedSubspace data level →
        TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm.cuspSupNorm vector ≤ constant * orbitSobolevNorm data order vector.val := by
  let _ := fixedTopology data level
  rw [fixed_continuous_iff_sobolev_bound]
  constructor
  · rintro ⟨order, constant, nonnegativeConstant, estimate⟩
    exact ⟨order, constant, nonnegativeConstant, fun vector membership => estimate ⟨vector, membership⟩⟩
  · rintro ⟨order, constant, nonnegativeConstant, estimate⟩
    exact ⟨order, constant, nonnegativeConstant, fun vector => estimate vector.val vector.property⟩

def fixedHilbertInclusion (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL) :
    fixedSmooth data level →ₗ[ℂ] data.H := data.smooth.subtype.comp (fixedSmooth data level).subtype

theorem fixedHilbertInclusion_continuous (data : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) :
    letI := fixedTopology data level
    Continuous (fixedHilbertInclusion data level) := by
  let _ := fixedTopology data level
  apply (fixed_continuous_iff_sobolev_bound data level (fixedHilbertInclusion data level)).mpr
  exact ⟨0, 1, zero_le_one, fun vector => by
    change ‖vector.val.val‖ ≤ 1 * orbitSobolevNorm data 0 vector.val.val
    rw [one_mul]
    exact norm_le_orbitSobolevNorm data 0 vector.val.val⟩

theorem fixedTopology_properties (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL) :
    letI := fixedTopology data level
    T2Space (fixedSmooth data level) ∧ FirstCountableTopology (fixedSmooth data level) ∧
      IsTopologicalAddGroup (fixedSmooth data level) ∧ ContinuousSMul ℂ (fixedSmooth data level) := by
  let _ := fixedTopology data level
  have seminormTopology := fixedTopology_withSeminorms data level
  refine ⟨?_, seminormTopology.firstCountableTopology, seminormTopology.isTopologicalAddGroup,
    seminormTopology.continuousSMul⟩
  exact T2Space.of_injective_continuous (f := fixedHilbertInclusion data level)
    (Subtype.val_injective.comp Subtype.val_injective) (fixedHilbertInclusion_continuous data level)

theorem hasSum_of_fixedRealization_continuous {degree : ℕ} (data : InducingData degree)
    (continuity : letI := fixedTopology data.cusp TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.finiteCongruence
      Continuous (fixedRealization data.cusp TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.finiteCongruence))
    {sectionFamily : ℂ → AdelicGL → ℂ} (flatSection : IsFlatSection data sectionFamily)
    (basePoint : AdelicGL) (parameter : ℂ) (rightHalfPlane : -(degree : ℝ) / 2 < parameter.re) :
    HasSum (eisensteinSummand sectionFamily parameter basePoint)
      (TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarSeries.literalSum sectionFamily parameter basePoint) := by
  obtain ⟨order, constant, nonnegativeConstant, estimate⟩ :=
    (fixedRealization_continuous_iff data.cusp TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.finiteCongruence).mp continuity
  exact hasSum_of_sobolev_estimate flatSection order constant nonnegativeConstant estimate
    basePoint parameter rightHalfPlane

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms
