module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.GeneralStageFamilies
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Good.LineUniformDecay

@[expose] public section


/-!
# Uniform cusp bounds for source cochains on compact vertex sets

For a source cocycle, the monomial coefficients at fixed vertices are plane-induced sections, and
`HasSmoothCuspLift` makes their cusp vectors analytic jointly in the three vertices and the real
argument. Together with the `GL₂(ℝ)`-equivariance of cusp vectors this makes the `GL₂(ℝ)`-orbit of
the cusp vectors jointly analytic, so by `GeneralStageFamilies` the cusp sup norm is continuous in
(vertices, argument). Hence it is bounded on every compact set of vertex tuples: the uniformity over
bounded-shape simplices needed for the prism transfer.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth
  TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation
  TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors
  TernaryPeriodPolynomials.PlaneEisensteinContinuation.SmoothBounds
  TernaryPeriodPolynomials.PlaneEisensteinContinuation.InducedAnalyticFamilies
open scoped Matrix.Norms.Elementwise NNReal

namespace TernaryPeriodPolynomials.AnalyticClasses

variable {n : ℕ}

/-- The cusp vector of the `m`-th coefficient of a source cochain at three vertices and a real
argument. -/
def cochainCuspVector (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (m : Fin 3 →₀ ℕ)
    (vertices : Fin 3 → RealGL3) (real : RealGL3) : data.cusp.smooth :=
  planeCuspVector (cocycle.1 vertices m) (atInfinity real)

/-- The vertex parameter space: four real `3 × 3` matrices (three vertices and the argument). -/
abbrev VertexMatrices := Fin 4 → PlaneMatrix

/-- The cusp-vector family over vertex matrices. -/
def cochainFamily (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (m : Fin 3 →₀ ℕ) (e : VertexMatrices) :
    data.cusp.smooth :=
  cochainCuspVector data source cocycle m (fun i => invertibleMatrix (e i.castSucc))
    (invertibleMatrix (e (Fin.last 3)))

theorem cochainFamily_contDiffOn (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (m : Fin 3 →₀ ℕ) :
    ContDiffOn ℝ ⊤ (fun e => (cochainFamily data source cocycle m e).val) (matrixDomain 3 4) := by
  obtain ⟨v, hv, heval⟩ := cocycle.2.1 m 1
  have equality : ∀ x : Fin 4 → RealGL3,
      cochainCuspVector data source cocycle m (fun i => x i.castSucc) (x (Fin.last 3)) = v x := by
    intro x
    apply planeCuspVector_unique
    intro A
    rw [heval x A, one_mul]
    rfl
  have hfun : (fun e => (cochainFamily data source cocycle m e).val) =
      fun e : VertexMatrices => (v (fun i => invertibleMatrix (e i))).val := by
    funext e
    exact congrArg Subtype.val (equality (fun i => invertibleMatrix (e i)))
  rw [hfun]
  exact hv

/-- The joint scalar normalization `|det A|^c`. -/
def jointNormalization (exponent : ℂ) (A : BinaryMatrix) : ℂ :=
  Complex.exp (exponent * (Real.log |A.det| : ℂ))

/-- Left multiplication of the argument by the plane block of `A`. -/
def vertexUpdate (point : BinaryMatrix × VertexMatrices) : VertexMatrices :=
  fun i => if i = Fin.last 3 then planeBlock point.1 1 * point.2 i else point.2 i

/-- The joint domain. -/
def vertexJointDomain : Set (BinaryMatrix × VertexMatrices) :=
  {point | point.1.det ≠ 0 ∧ ∀ i, (point.2 i).det ≠ 0}

theorem vertexJointDomain_isOpen : IsOpen vertexJointDomain := by
  have h1 : IsOpen {point : BinaryMatrix × VertexMatrices | point.1.det ≠ 0} :=
    isOpen_ne.preimage continuous_fst.matrix_det
  have h2 : IsOpen {point : BinaryMatrix × VertexMatrices | ∀ i, (point.2 i).det ≠ 0} :=
    (matrixDomain_isOpen 3 4).preimage continuous_snd
  exact h1.inter h2

theorem vertexUpdate_contDiff : ContDiff ℝ ⊤ vertexUpdate := by
  apply contDiff_pi.mpr
  intro i
  by_cases hi : i = Fin.last 3
  · subst hi
    simp only [vertexUpdate, ite_true]
    apply contDiff_pi.mpr
    intro row
    apply contDiff_pi.mpr
    intro column
    have hcomp : ContDiff ℝ ⊤ (fun point : BinaryMatrix × VertexMatrices => point.2 (Fin.last 3)) :=
      (contDiff_apply ℝ PlaneMatrix (Fin.last 3)).comp contDiff_snd
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, planeBlock] <;> fun_prop
  · simp only [vertexUpdate, hi, ite_false]
    exact (contDiff_apply ℝ PlaneMatrix i).comp contDiff_snd

theorem vertexUpdate_mapsTo : Set.MapsTo vertexUpdate vertexJointDomain (matrixDomain 3 4) := by
  intro point membership i
  by_cases hi : i = Fin.last 3
  · simp only [vertexUpdate, hi, ite_true]
    rw [Matrix.det_mul, planeBlock_det]
    exact mul_ne_zero membership.1 (membership.2 _)
  · simp only [vertexUpdate, hi, ite_false]
    exact membership.2 i

theorem jointNormalization_contDiffOn (exponent : ℂ) :
    ContDiffOn ℝ ⊤ (fun point : BinaryMatrix × VertexMatrices => jointNormalization exponent point.1)
      vertexJointDomain := by
  have hdet : ContDiff ℝ ⊤ (fun point : BinaryMatrix × VertexMatrices => point.1.det) := by
    simp only [Matrix.det_fin_two]
    fun_prop
  have smoothLog : ContDiffOn ℝ ⊤ (fun point : BinaryMatrix × VertexMatrices => Real.log |point.1.det|)
      vertexJointDomain := by
    simp only [Real.log_abs]
    exact hdet.contDiffOn.log (fun _ membership => membership.1)
  exact Complex.contDiff_exp.comp_contDiffOn
    (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn smoothLog))

/-- The `GL₂(ℝ)`-orbit of the cochain family, written through the family itself. -/
theorem cochainFamily_orbit (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (m : Fin 3 →₀ ℕ)
    (point : BinaryMatrix × VertexMatrices) (membership : point ∈ vertexJointDomain) :
    generalFamilyOrbit data.cusp (fun e => (cochainFamily data source cocycle m e).val) point =
      jointNormalization (-binaryInductionExponent n .plane cohomologicalPoint) point.1 •
        (cochainFamily data source cocycle m (vertexUpdate point)).val := by
  set B := invertibleMatrix point.1 with hB
  set g := invertibleMatrix (point.2 (Fin.last 3)) with hg
  set verts : Fin 3 → RealGL3 := fun i => invertibleMatrix (point.2 i.castSucc) with hverts
  have hf := cocycle.1 verts m
  have levi := planeCuspVector_binaryLevi hf (atInfinity B) (atInfinity g)
  have hupdate_verts : (fun i : Fin 3 => invertibleMatrix (vertexUpdate point i.castSucc)) = verts := by
    funext i
    have hi : (i.castSucc : Fin 4) ≠ Fin.last 3 := Fin.castSucc_ne_last i
    simp only [vertexUpdate, hi, ite_false, hverts]
  have hupdate_last : invertibleMatrix (vertexUpdate point (Fin.last 3)) = planeLevi B 1 * g := by
    simp only [vertexUpdate, ite_true]
    apply Units.ext
    have hdet : (planeBlock point.1 1 * point.2 (Fin.last 3)).det ≠ 0 := by
      rw [Matrix.det_mul, planeBlock_det]
      exact mul_ne_zero membership.1 (membership.2 _)
    rw [invertibleMatrix_val _ hdet]
    change planeBlock point.1 1 * point.2 (Fin.last 3) =
      planeBlock (B.val) (1 : ℝˣ).val * g.val
    rw [hB, hg, invertibleMatrix_val _ membership.1, invertibleMatrix_val _ (membership.2 _)]
    rfl
  have hcombine : planeLevi (atInfinity B) 1 * atInfinity g = atInfinity (planeLevi B 1 * g) := by
    rw [Height.atInfinity_mul, planeLevi_atInfinity]
  have hfamily : cochainFamily data source cocycle m (vertexUpdate point) =
      planeCuspVector hf (planeLevi (atInfinity B) 1 * atInfinity g) := by
    rw [cochainFamily, hupdate_verts, hupdate_last, hcombine]
    rfl
  have hnorm : normPower (Matrix.GeneralLinearGroup.det (atInfinity B))
      (binaryInductionExponent n .plane cohomologicalPoint) =
      jointNormalization (binaryInductionExponent n .plane cohomologicalPoint) point.1 := by
    rw [normPower, Norm.adeleNorm_det_atInfinity, hB, invertibleMatrix_val _ membership.1]
    rfl
  change data.cusp.π (atInfinity B) (cochainFamily data source cocycle m point.2).val = _
  rw [hfamily, levi]
  change data.cusp.π (atInfinity B) (planeCuspVector hf (atInfinity g)).val =
    jointNormalization (-binaryInductionExponent n .plane cohomologicalPoint) point.1 •
      (normPower (Matrix.GeneralLinearGroup.det (atInfinity B))
        (binaryInductionExponent n .plane cohomologicalPoint) •
          data.cusp.π (atInfinity B) (planeCuspVector hf (atInfinity g)).val)
  rw [hnorm, smul_smul]
  have hprod : jointNormalization (-binaryInductionExponent n .plane cohomologicalPoint) point.1 *
      jointNormalization (binaryInductionExponent n .plane cohomologicalPoint) point.1 = 1 := by
    simp only [jointNormalization, ← Complex.exp_add]
    rw [← add_mul, neg_add_cancel, zero_mul, Complex.exp_zero]
  rw [hprod, one_smul]

theorem cochainFamily_orbit_analyticAt (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (m : Fin 3 →₀ ℕ)
    (e : VertexMatrices) (he : e ∈ matrixDomain 3 4) :
    AnalyticAt ℝ (generalFamilyOrbit data.cusp (fun e => (cochainFamily data source cocycle m e).val))
      (1, e) := by
  have membership : ((1 : BinaryMatrix), e) ∈ vertexJointDomain := ⟨by simp, he⟩
  have smooth : ContDiffOn ℝ ⊤ (fun point : BinaryMatrix × VertexMatrices =>
      jointNormalization (-binaryInductionExponent n .plane cohomologicalPoint) point.1 •
        (cochainFamily data source cocycle m (vertexUpdate point)).val) vertexJointDomain :=
    (jointNormalization_contDiffOn _).smul
      ((cochainFamily_contDiffOn data source cocycle m).comp vertexUpdate_contDiff.contDiffOn
        vertexUpdate_mapsTo)
  have smoothOrbit : ContDiffOn ℝ ⊤
      (generalFamilyOrbit data.cusp (fun e => (cochainFamily data source cocycle m e).val))
      vertexJointDomain :=
    smooth.congr (fun point hpoint => cochainFamily_orbit data source cocycle m point hpoint)
  exact (smoothOrbit.contDiffAt (vertexJointDomain_isOpen.mem_nhds membership)).analyticAt

theorem cochainFamily_fixed (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (m : Fin 3 →₀ ℕ) (e : VertexMatrices) :
    (cochainFamily data source cocycle m e).val ∈
      BinaryLevel.fixedSubspace data.cusp BinaryLevel.finiteCongruence := by
  have hf := cocycle.1 (fun i => invertibleMatrix (e i.castSucc)) m
  have fixed := matrixCuspVector_fixed hf 1 (e (Fin.last 3))
  have equality : matrixCuspVector hf 1 (e (Fin.last 3)) = cochainFamily data source cocycle m e := by
    unfold matrixCuspVector cochainFamily cochainCuspVector
    congr 1
    rw [map_one, CompactAveraging.atFinite_one, one_mul]
  rw [← equality]
  exact fixed

/-- **Continuity of the cusp sup norm of a source cochain in the vertices and the argument.** -/
theorem cochainFamily_cuspSupNorm_continuousOn (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (m : Fin 3 →₀ ℕ) :
    ContinuousOn (fun e => CuspSupNorm.cuspSupNorm (cochainFamily data source cocycle m e))
      (matrixDomain 3 4) := by
  intro e he
  exact (cuspSupNorm_continuousAt_of_jointAnalytic data.cusp (continuousStages data)
    (cochainFamily data source cocycle m) e
    (cochainFamily_orbit_analyticAt data source cocycle m e he)
    (cochainFamily_fixed data source cocycle m)).continuousWithinAt

/-- **Continuity of the bounded realization of a source cochain in the vertices and the argument.** -/
theorem cochainCuspVector_boundedRealization_continuous (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (m : Fin 3 →₀ ℕ) :
    Continuous (fun x : Fin 4 → RealGL3 => CuspSupNorm.boundedRealization data.cusp
      (cochainCuspVector data source cocycle m (fun i => x i.castSucc) (x (Fin.last 3)))) := by
  let valMap : (Fin 4 → RealGL3) → VertexMatrices := fun x i => (x i).val
  have valContinuous : Continuous valMap := continuous_pi fun i => Units.continuous_val.comp (continuous_apply i)
  have equality : (fun x : Fin 4 → RealGL3 => CuspSupNorm.boundedRealization data.cusp
      (cochainCuspVector data source cocycle m (fun i => x i.castSucc) (x (Fin.last 3)))) =
      (fun e => CuspSupNorm.boundedRealization data.cusp (cochainFamily data source cocycle m e)) ∘ valMap := by
    funext x
    simp only [Function.comp, cochainFamily, valMap, invertibleMatrix_units]
  rw [equality, continuous_iff_continuousAt]
  intro x
  apply ContinuousAt.comp _ valContinuous.continuousAt
  exact boundedRealization_continuousAt_of_jointAnalytic data.cusp (continuousStages data)
    (cochainFamily data source cocycle m) (valMap x)
    (cochainFamily_orbit_analyticAt data source cocycle m (valMap x)
      (fun i => Matrix.GeneralLinearGroup.det_ne_zero (x i)))
    (cochainFamily_fixed data source cocycle m)

/-- **Uniform cusp bound on compact vertex sets.** -/
theorem cochainCuspVector_bounded (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (m : Fin 3 →₀ ℕ)
    {K : Set (Fin 4 → RealGL3)} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, CuspSupNorm.cuspSupNorm
      (cochainCuspVector data source cocycle m (fun i => x i.castSucc) (x (Fin.last 3))) ≤ C := by
  let valMap : (Fin 4 → RealGL3) → VertexMatrices := fun x i => (x i).val
  have valContinuous : Continuous valMap := continuous_pi fun i => Units.continuous_val.comp (continuous_apply i)
  have imageCompact : IsCompact (valMap '' K) := hK.image valContinuous
  have imageDomain : valMap '' K ⊆ matrixDomain 3 4 := by
    rintro _ ⟨x, -, rfl⟩ i
    exact Matrix.GeneralLinearGroup.det_ne_zero (x i)
  obtain ⟨C, hC⟩ := imageCompact.exists_bound_of_continuousOn
    ((cochainFamily_cuspSupNorm_continuousOn data source cocycle m).mono imageDomain)
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  have bound := hC (valMap x) ⟨x, hx, rfl⟩
  have equality : cochainFamily data source cocycle m (valMap x) =
      cochainCuspVector data source cocycle m (fun i => x i.castSucc) (x (Fin.last 3)) := by
    unfold cochainFamily
    simp only [valMap, invertibleMatrix_units]
  rw [equality, Real.norm_of_nonneg (CuspSupNorm.cuspSupNorm_nonneg _)] at bound
  exact bound.trans (le_max_left _ _)

end TernaryPeriodPolynomials.AnalyticClasses
