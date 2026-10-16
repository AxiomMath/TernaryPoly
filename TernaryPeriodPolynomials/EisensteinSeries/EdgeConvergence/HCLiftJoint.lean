module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.HCRealScalar
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.HCLiftMember

@[expose] public section


/-!
# The joint orbit of the Cauchy lift of one plane section is real analytic

Original work by Claude Sonnet 5.5.

`LocalLiftOrbit`: for a single plane section, the Cauchy lift `W(x)` of the local Hilbert vectors at
`κ · x` (a family of smooth vectors indexed by `x ∈ GL₃(ℝ)`) has an analytic joint orbit
`(b, x) ↦ π(b) W(x)` on `GL₂(ℝ) × GL₃(ℝ)`. By the orbit identity (`HCLift.orbit_eq_extended`),
`π(b) W(x) = |det b|^{-e(s₀)}` times the Cauchy lift of the family with one more vertex, evaluated at
the vertex `lineLevi(1, b)` and the translation `lineLevi(1, b) · ρ · x`; the latter is a polynomial
function of `(b, x)`, and the Cauchy lift is real analytic in its vertices and translation
(`HCLift.liftVector_smooth`).
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix Metric
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth
  (PlaneMatrix JointMatrix BinaryMatrix jointDomain jointDomain_isOpen)
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence

namespace HCLift

/-- The tuple of two matrices (the line block of `p.1` as vertex, the line block times
`rotation · p.2` as translation). -/
def jointTuple (rotation : Matrix (Fin 3) (Fin 3) ℝ) (p : BinaryMatrix × PlaneMatrix) :
    SmoothJets.MatrixTuples 3 (0 + 1 + 1) :=
  Fin.snoc (α := fun _ => Matrix (Fin 3) (Fin 3) ℝ)
    (Fin.cons (α := fun _ => Matrix (Fin 3) (Fin 3) ℝ) (RightOrbitAnalyticity.lineBlock 1 p.1)
      (fun i : Fin 0 => i.elim0))
    (RightOrbitAnalyticity.lineBlock 1 p.1 * (rotation * p.2))

theorem contDiff_jointTuple (rotation : Matrix (Fin 3) (Fin 3) ℝ) :
    ContDiff ℝ ⊤ (jointTuple rotation) := by
  apply contDiff_pi.mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [jointTuple, Fin.snoc_last]
    apply contDiff_pi.mpr
    intro row
    apply contDiff_pi.mpr
    intro column
    fin_cases row <;> fin_cases column <;>
      simp [RightOrbitAnalyticity.lineBlock, Matrix.mul_apply,
        Fin.sum_univ_three] <;> fun_prop
  · refine Fin.cases ?_ (fun k => ?_) j
    · simp only [jointTuple, Fin.snoc_castSucc, Fin.cons_zero]
      apply contDiff_pi.mpr
      intro row
      apply contDiff_pi.mpr
      intro column
      fin_cases row <;> fin_cases column <;> simp [RightOrbitAnalyticity.lineBlock] <;> fun_prop
    · exact k.elim0

/-- Smoothness along the joint (line block, translation) of a smooth function of tuples of two
real matrices. -/
theorem jointOrbit_contDiffOn {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : (Fin (0 + 1 + 1) → RealGL3) → E) (smooth : Smooth function)
    (vertices : Fin 0 → RealGL3) (rotation : RealGL3) :
    ContDiffOn ℝ ⊤ (fun p : JointMatrix => function (Fin.snoc (α := fun _ => RealGL3)
      (Fin.cons (α := fun _ => RealGL3) (lineLevi 1 (invertibleMatrix p.1)) vertices)
      (lineLevi 1 (invertibleMatrix p.1) * (rotation * invertibleMatrix p.2)))) jointDomain := by
  have maps : Set.MapsTo (jointTuple rotation.val) jointDomain
      (SmoothJets.domain 3 (0 + 1 + 1)) := by
    intro p membership i
    obtain ⟨binaryInvertible, planeInvertible⟩ := membership
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [jointTuple, Fin.snoc_last]
      rw [Matrix.det_mul, RightOrbitAnalyticity.lineBlock_det, Matrix.det_mul]
      exact mul_ne_zero binaryInvertible
        (mul_ne_zero (GeneralLinearGroup.det_ne_zero _) planeInvertible)
    · refine Fin.cases ?_ (fun k => ?_) j
      · simp only [jointTuple, Fin.snoc_castSucc, Fin.cons_zero]
        rw [RightOrbitAnalyticity.lineBlock_det]
        exact binaryInvertible
      · exact k.elim0
  apply (smooth.comp (contDiff_jointTuple rotation.val).contDiffOn maps).congr
  intro p membership
  obtain ⟨binaryInvertible, planeInvertible⟩ := membership
  have block := RightOrbitAnalyticity.invertibleMatrix_lineBlock p.1 binaryInvertible
  have blockDet : (RightOrbitAnalyticity.lineBlock 1 p.1).det ≠ 0 := by
    rw [RightOrbitAnalyticity.lineBlock_det]
    exact binaryInvertible
  change function (Fin.snoc (α := fun _ => RealGL3)
      (Fin.cons (α := fun _ => RealGL3) (lineLevi 1 (invertibleMatrix p.1)) vertices)
      (lineLevi 1 (invertibleMatrix p.1) * (rotation * invertibleMatrix p.2))) =
    function (fun i => invertibleMatrix (jointTuple rotation.val p i))
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [jointTuple, Fin.snoc_last]
    have product : rotation.val * p.2 = (rotation * invertibleMatrix p.2).val := by
      rw [Units.val_mul, PlaneEisensteinContinuation.OrbitSmooth.invertibleMatrix_val _
        planeInvertible]
    rw [product, SmoothTranslations.invertibleMatrix_mul_right _ blockDet, block]
  · refine Fin.cases ?_ (fun k => ?_) j
    · simp only [jointTuple, Fin.snoc_castSucc, Fin.cons_zero]
      exact block.symm
    · exact k.elim0

end HCLift

/-- **Remaining input at arity `0` (`LocalLiftOrbit`).** -/
theorem localLiftOrbit {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) : LocalLiftOrbit data holomorphic := by
  intro multiplier radius radiusPositive halfPlane multiplierContinuous sectionValue compact
    compactMembership
  have lift₀ : HasSmoothCuspLift data .plane cohomologicalPoint
      (fun _ : Fin 0 → RealGL3 => sectionValue.val) := sectionValue.property.2.2.1
  have weightSmooth : Smooth (fun _ : Fin 0 → RealGL3 => (0 : ℝ)) := contDiffOn_const
  refine ⟨fun x => ⟨HCLift.liftVector data holomorphic (fun _ => sectionValue.val)
    (fun _ => sectionValue.property) (fun _ => 0) radius multiplier compact x,
    HCLift.liftVector_mem_smooth data holomorphic (fun _ => sectionValue.val)
      (fun _ => sectionValue.property) (fun _ => 0) lift₀ weightSmooth radius radiusPositive
      halfPlane multiplier multiplierContinuous compact compactMembership x⟩, ?_, ?_⟩
  · intro x
    change EndpointLift.endpointLift cohomologicalPoint radius multiplier _ = _
    congr 1
    funext parameter
    unfold localFamilyValue
    exact HCLift.localValue_congr data parameter (funext fun y => by simp [HCLift.twistedAt,
      HCLift.flatAt]) _ _ _
  · have extendedSmooth := HCLift.liftVector_smooth data holomorphic
      (HCLift.dropFirst (fun _ : Fin 0 → RealGL3 => sectionValue.val))
      (HCLift.dropFirst_induced data (fun _ : Fin 0 → RealGL3 => sectionValue.val)
        (fun _ => sectionValue.property))
      (HCLift.extendedWeight (fun _ : Fin 0 → RealGL3 => (0 : ℝ)))
      (HCLift.hasSmoothCuspLift_dropFirst data .plane cohomologicalPoint _ lift₀)
      (HCLift.smooth_extendedWeight _ weightSmooth) radius radiusPositive halfPlane multiplier
      multiplierContinuous (atFinite (finiteGroup compact))
      (HCLift.inMaximalCompact_atFinite compact compactMembership)
    have composed := HCLift.jointOrbit_contDiffOn
      (HCLift.liftVector data holomorphic
        (HCLift.dropFirst (fun _ : Fin 0 → RealGL3 => sectionValue.val))
        (HCLift.dropFirst_induced data (fun _ : Fin 0 → RealGL3 => sectionValue.val)
          (fun _ => sectionValue.property))
        (HCLift.extendedWeight (fun _ : Fin 0 → RealGL3 => (0 : ℝ))) radius multiplier
        (atFinite (finiteGroup compact))) extendedSmooth (fun i => i.elim0) (realGroup compact)
    have scalarSmooth : ContDiffOn ℝ ⊤ (fun p : JointMatrix =>
        normPower (GeneralLinearGroup.det (atInfinity (invertibleMatrix p.1)))
          (-binaryInductionExponent degree .line cohomologicalPoint)) jointDomain := by
      have base : ContDiffOn ℝ ⊤ (fun A : SmoothJets.MatrixTuples 2 1 =>
          normPower (GeneralLinearGroup.det (atInfinity (invertibleMatrix (A 0))))
            (-binaryInductionExponent degree .line cohomologicalPoint)) (SmoothJets.domain 2 1) :=
        SmoothNormPower.real_power_smooth (size := 2) (0 : Fin 1)
          (-binaryInductionExponent degree .line cohomologicalPoint)
      have projection : ContDiff ℝ ⊤ (fun p : JointMatrix => fun _ : Fin 1 => p.1) :=
        contDiff_pi.mpr (fun _ => contDiff_fst)
      have maps : Set.MapsTo (fun p : JointMatrix => fun _ : Fin 1 => p.1) jointDomain
          (SmoothJets.domain 2 1) := by
        intro p membership i
        exact membership.1
      have h := base.comp projection.contDiffOn maps
      exact h.congr fun p _ => rfl
    have combined := ContDiffOn.smul (𝕜 := ℝ) (𝕜' := ℂ) scalarSmooth composed
    refine combined.congr (fun p _ => ?_)
    change data.cusp.π (atInfinity (invertibleMatrix p.1)) (HCLift.liftVector data holomorphic
      (fun _ => sectionValue.val) (fun _ => sectionValue.property) (fun _ => 0) radius multiplier
      compact (fun _ => invertibleMatrix p.2)) = _
    rw [HCLift.orbit_eq_extended data holomorphic (fun _ : Fin 0 → RealGL3 => sectionValue.val)
      (fun _ => sectionValue.property) (fun _ => 0) lift₀ weightSmooth radius radiusPositive
      halfPlane multiplier multiplierContinuous compact compactMembership]
    have vertexEquality : (fun _ : Fin 0 => invertibleMatrix p.2) =
        (fun i : Fin 0 => i.elim0 : Fin 0 → RealGL3) := Subsingleton.elim _ _
    simp only [vertexEquality]
    rfl

end TernaryPeriodPolynomials.EdgeConvergence
