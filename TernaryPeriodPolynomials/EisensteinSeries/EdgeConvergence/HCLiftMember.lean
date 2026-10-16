module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.HCLiftOrbit

@[expose] public section


/-!
# The Cauchy lift of the local vectors is a smooth vector of the cusp representation

Original work by Claude Sonnet 5.5.

The criterion `data.cusp.smooth_exact`: the orbit of `liftVector x` under `GL₂(ℝ)` is smooth
(`orbit_smooth`: by the orbit identity it is `|det g|^{-e(s₀)}` times the Cauchy lift of the family
with one more vertex, evaluated at the vertex `lineLevi(1, g)` and at the translation
`lineLevi(1, g) · ρ · x_last`, and the latter is a smooth function of the tuple of vertices and
translation by `liftVector_smooth`), and the vector is fixed by the open compact subgroup
`LineOrbitLevel.level (κ · x_last)` (`liftAt_fixed`).
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous Matrix MeasureTheory
  Metric
open scoped Matrix.Norms.Elementwise NNReal
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence.HCLift

theorem contDiff_lineBlock_mul (right : Matrix (Fin 3) (Fin 3) ℝ) :
    ContDiff ℝ ⊤ (fun A : SmoothJets.MatrixTuples 2 1 =>
      RightOrbitAnalyticity.lineBlock 1 (A 0) * right) := by
  apply contDiff_pi.mpr
  intro row
  apply contDiff_pi.mpr
  intro column
  fin_cases row <;> fin_cases column <;>
    simp [RightOrbitAnalyticity.lineBlock, Matrix.mul_apply,
      Fin.sum_univ_three] <;> fun_prop

theorem contDiff_lineBlock :
    ContDiff ℝ ⊤ (fun A : SmoothJets.MatrixTuples 2 1 =>
      RightOrbitAnalyticity.lineBlock 1 (A 0)) := by
  apply contDiff_pi.mpr
  intro row
  apply contDiff_pi.mpr
  intro column
  fin_cases row <;> fin_cases column <;> simp [RightOrbitAnalyticity.lineBlock] <;> fun_prop

/-- The tuple of matrices with the line block `lineBlock 1 (A 0)` as the first vertex, the
vertices `vertices` next, and the translation `lineBlock 1 (A 0) · right`. -/
def lineTuple {arity : ℕ} (vertices : Fin arity → RealGL3) (right : Matrix (Fin 3) (Fin 3) ℝ)
    (A : SmoothJets.MatrixTuples 2 1) : SmoothJets.MatrixTuples 3 (arity + 1 + 1) :=
  Fin.snoc (α := fun _ => Matrix (Fin 3) (Fin 3) ℝ)
    (Fin.cons (α := fun _ => Matrix (Fin 3) (Fin 3) ℝ) (RightOrbitAnalyticity.lineBlock 1 (A 0))
      (fun i => (vertices i).val))
    (RightOrbitAnalyticity.lineBlock 1 (A 0) * right)

theorem contDiff_lineTuple {arity : ℕ} (vertices : Fin arity → RealGL3)
    (right : Matrix (Fin 3) (Fin 3) ℝ) : ContDiff ℝ ⊤ (lineTuple vertices right) := by
  apply contDiff_pi.mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [lineTuple, Fin.snoc_last]
    exact contDiff_lineBlock_mul right
  · refine Fin.cases ?_ (fun k => ?_) j
    · simp only [lineTuple, Fin.snoc_castSucc, Fin.cons_zero]
      exact contDiff_lineBlock
    · simp only [lineTuple, Fin.snoc_castSucc, Fin.cons_succ]
      exact contDiff_const

/-- Smoothness of a smooth function of tuples along the line Levi vertex and translation. -/
theorem smooth_lineLevi_comp {arity : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : (Fin (arity + 1 + 1) → RealGL3) → E) (smooth : Smooth function)
    (vertices : Fin arity → RealGL3) (translation : RealGL3) :
    Smooth (fun B : Fin 1 → BinaryRealGL => function (Fin.snoc (α := fun _ => RealGL3)
      (Fin.cons (α := fun _ => RealGL3) (lineLevi 1 (B 0)) vertices)
      (lineLevi 1 (B 0) * translation))) := by
  have maps : Set.MapsTo (lineTuple vertices translation.val) (SmoothJets.domain 2 1)
      (SmoothJets.domain 3 (arity + 1 + 1)) := by
    intro A membership i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [lineTuple, Fin.snoc_last]
      rw [Matrix.det_mul, RightOrbitAnalyticity.lineBlock_det]
      exact mul_ne_zero (membership 0) (GeneralLinearGroup.det_ne_zero _)
    · refine Fin.cases ?_ (fun k => ?_) j
      · simp only [lineTuple, Fin.snoc_castSucc, Fin.cons_zero]
        rw [RightOrbitAnalyticity.lineBlock_det]
        exact membership 0
      · simp only [lineTuple, Fin.snoc_castSucc, Fin.cons_succ]
        exact GeneralLinearGroup.det_ne_zero _
  apply (smooth.comp (contDiff_lineTuple vertices translation.val).contDiffOn maps).congr
  intro A membership
  have nonzero : (A 0).det ≠ 0 := membership 0
  have block := RightOrbitAnalyticity.invertibleMatrix_lineBlock (A 0) nonzero
  have blockDet : (RightOrbitAnalyticity.lineBlock 1 (A 0)).det ≠ 0 := by
    rw [RightOrbitAnalyticity.lineBlock_det]
    exact nonzero
  change function (Fin.snoc (α := fun _ => RealGL3)
      (Fin.cons (α := fun _ => RealGL3) (lineLevi 1 (invertibleMatrix (A 0))) vertices)
      (lineLevi 1 (invertibleMatrix (A 0)) * translation)) =
    function (fun i => invertibleMatrix (lineTuple vertices translation.val A i))
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [lineTuple, Fin.snoc_last]
    rw [SmoothTranslations.invertibleMatrix_mul_right _ blockDet, block]
  · refine Fin.cases ?_ (fun k => ?_) j
    · simp only [lineTuple, Fin.snoc_castSucc, Fin.cons_zero]
      exact block.symm
    · simp only [lineTuple, Fin.snoc_castSucc, Fin.cons_succ]
      exact (SmoothContinuity.invertibleMatrix_coe _).symm

section Member

variable {degree arity : ℕ} (data : InducingData degree)
  (holomorphic : PlaneEisensteinHolomorphic data)
  (family : (Fin arity → RealGL3) → AdelicGL → ℂ)
  (induced : ∀ vertices, IsInduced data .plane cohomologicalPoint (family vertices))
  (weight : (Fin arity → RealGL3) → ℝ)

/-- The `GL₂(ℝ)` orbit of the Cauchy lift is the Cauchy lift of the family with one more vertex,
times a power of the determinant. -/
theorem orbit_eq_extended (lift : HasSmoothCuspLift data .plane cohomologicalPoint family)
    (weightSmooth : Smooth weight) (circleRadius : ℝ) (circlePositive : 0 < circleRadius)
    (halfPlane : closedBall cohomologicalPoint circleRadius ⊆ EdgeInputs.localHalfPlane degree)
    (lam : ℂ → ℂ) (lamContinuous : ContinuousOn lam (sphere cohomologicalPoint circleRadius))
    (compact : AdelicGL) (compactMembership : inMaximalCompact compact)
    (x : Fin (arity + 1) → RealGL3) (matrix : BinaryRealGL) :
    data.cusp.π (atInfinity matrix)
        (liftVector data holomorphic family induced weight circleRadius lam compact x) =
      normPower (GeneralLinearGroup.det (atInfinity matrix))
          (-binaryInductionExponent degree .line cohomologicalPoint) •
        liftVector data holomorphic (dropFirst family) (dropFirst_induced data family induced)
          (extendedWeight weight) circleRadius lam (atFinite (finiteGroup compact))
          (Fin.snoc (α := fun _ => RealGL3)
            (Fin.cons (α := fun _ => RealGL3) (lineLevi 1 matrix) (fun i => x i.castSucc))
            (lineLevi 1 matrix * (realGroup compact * x (Fin.last arity)))) := by
  rw [liftVector_eq_liftAt data holomorphic family induced weight circleRadius lam compact x,
    orbit_identity data holomorphic family induced weight lift weightSmooth circleRadius
      circlePositive halfPlane lam lamContinuous compact compactMembership,
    liftVector_eq_liftAt data holomorphic (dropFirst family)
      (dropFirst_induced data family induced) (extendedWeight weight) circleRadius lam
      (atFinite (finiteGroup compact))]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-- The `GL₂(ℝ)` orbit of the Cauchy lift is smooth. -/
theorem orbit_smooth (lift : HasSmoothCuspLift data .plane cohomologicalPoint family)
    (weightSmooth : Smooth weight) (circleRadius : ℝ) (circlePositive : 0 < circleRadius)
    (halfPlane : closedBall cohomologicalPoint circleRadius ⊆ EdgeInputs.localHalfPlane degree)
    (lam : ℂ → ℂ) (lamContinuous : ContinuousOn lam (sphere cohomologicalPoint circleRadius))
    (compact : AdelicGL) (compactMembership : inMaximalCompact compact)
    (x : Fin (arity + 1) → RealGL3) :
    Smooth (fun B : Fin 1 → BinaryRealGL => data.cusp.π (atInfinity (B 0))
      (liftVector data holomorphic family induced weight circleRadius lam compact x)) := by
  have extendedSmooth := liftVector_smooth data holomorphic (dropFirst family)
    (dropFirst_induced data family induced) (extendedWeight weight)
    (hasSmoothCuspLift_dropFirst data .plane cohomologicalPoint family lift)
    (smooth_extendedWeight weight weightSmooth) circleRadius circlePositive halfPlane lam
    lamContinuous (atFinite (finiteGroup compact))
    (inMaximalCompact_atFinite compact compactMembership)
  have composed := smooth_lineLevi_comp
    (liftVector data holomorphic (dropFirst family) (dropFirst_induced data family induced)
      (extendedWeight weight) circleRadius lam (atFinite (finiteGroup compact))) extendedSmooth
    (fun i => x i.castSucc) (realGroup compact * x (Fin.last arity))
  have scalarSmooth := SmoothNormPower.real_power_smooth (size := 2) (0 : Fin 1)
    (-binaryInductionExponent degree .line cohomologicalPoint)
  have product := scalarSmooth.smul composed
  have equality : (fun B : Fin 1 → BinaryRealGL => data.cusp.π (atInfinity (B 0))
      (liftVector data holomorphic family induced weight circleRadius lam compact x)) =
      fun B : Fin 1 → BinaryRealGL =>
        normPower (GeneralLinearGroup.det (atInfinity (B 0)))
            (-binaryInductionExponent degree .line cohomologicalPoint) •
          liftVector data holomorphic (dropFirst family) (dropFirst_induced data family induced)
            (extendedWeight weight) circleRadius lam (atFinite (finiteGroup compact))
            (Fin.snoc (α := fun _ => RealGL3)
              (Fin.cons (α := fun _ => RealGL3) (lineLevi 1 (B 0)) (fun i => x i.castSucc))
              (lineLevi 1 (B 0) * (realGroup compact * x (Fin.last arity)))) :=
    funext fun B => orbit_eq_extended data holomorphic family induced weight lift weightSmooth
      circleRadius circlePositive halfPlane lam lamContinuous compact compactMembership x (B 0)
  rw [equality]
  exact product

/-- **Membership in the smooth vectors.** -/
theorem liftVector_mem_smooth (lift : HasSmoothCuspLift data .plane cohomologicalPoint family)
    (weightSmooth : Smooth weight) (circleRadius : ℝ) (circlePositive : 0 < circleRadius)
    (halfPlane : closedBall cohomologicalPoint circleRadius ⊆ EdgeInputs.localHalfPlane degree)
    (lam : ℂ → ℂ) (lamContinuous : ContinuousOn lam (sphere cohomologicalPoint circleRadius))
    (compact : AdelicGL) (compactMembership : inMaximalCompact compact)
    (x : Fin (arity + 1) → RealGL3) :
    liftVector data holomorphic family induced weight circleRadius lam compact x ∈
      data.cusp.smooth := by
  apply (data.cusp.smooth_exact _).mpr
  refine ⟨orbit_smooth data holomorphic family induced weight lift weightSmooth circleRadius
    circlePositive halfPlane lam lamContinuous compact compactMembership x,
    LineOrbitLevel.level (compact * atInfinity (x (Fin.last arity))),
    LineOrbitLevel.level_isOpen _, LineOrbitLevel.level_isCompact _, ?_⟩
  intro unit
  exact liftAt_fixed data holomorphic family induced weight lift weightSmooth circleRadius
    circlePositive halfPlane lam lamContinuous compact compactMembership
    (fun index => x index.castSucc) (x (Fin.last arity)) unit

end Member

end TernaryPeriodPolynomials.EdgeConvergence.HCLift
