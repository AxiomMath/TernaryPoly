module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.HCLiftShift

@[expose] public section


/-!
# Taylor bounds of the orbits at maximal compact arguments, uniform in the parameter

Original work by Claude Sonnet 5.5.

For a family of plane sections with a smooth cusp lift at the cohomological point `s₀`, the orbit
functions `x ↦ v_s(y · x)` of the plane cusp lift vectors of the twisted flat family
(`HCLift.twistedAt`) at a parameter `s` and a maximal compact argument `y` are real analytic, with a
Taylor expansion at any real tuple on a common ball and geometrically bounded coefficients. The ball
and the constant depend on neither the argument `y` in the maximal compact (this is
`FamilyCuspTaylor.maximalCompact_uniform` for one fixed parameter) nor the parameter `s` in a compact
set. The point is that the orbit at the parameter `s` is `exp((s - s₀)(log Ξ + weight))` times the orbit
at `s₀` (`HCLift.matrixOrbit_twistedAt`), hence jointly analytic in the parameter and the real
variables; the argument is that of `AdelicFamilyTaylor.local_uniform` with the parameter as one more
analytic variable.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous Matrix Filter Topology
open scoped Matrix.Norms.Elementwise NNReal
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.EdgeConvergence.SectionMultipliers
open CompactTaylorBounds

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence.HCLift

/-- Analyticity from smoothness on an open set (the smooth order is the analytic order). -/
theorem analyticAt_of_contDiffOn {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {function : E → F} {set : Set E}
    (isOpen : IsOpen set) (smooth : ContDiffOn ℝ ⊤ function set) {point : E} (membership : point ∈ set) :
    AnalyticAt ℝ function point :=
  ((contDiffOn_omega_iff_analyticOn isOpen.uniqueDiffOn).mp smooth).analyticAt
    (isOpen.mem_nhds membership)

/-- Left multiplication of tuples of matrices, as a continuous bilinear map. -/
def leftMultiply {arity : ℕ} : SmoothJets.MatrixTuples 3 arity.succ →L[ℝ]
    SmoothJets.MatrixTuples 3 arity.succ →L[ℝ] SmoothJets.MatrixTuples 3 arity.succ :=
  TranslatedJets.leftMulLinear.toContinuousLinearMap

theorem leftMultiply_apply {arity : ℕ} (left right : SmoothJets.MatrixTuples 3 arity.succ)
    (index : Fin arity.succ) : leftMultiply left right index = left index * right index :=
  rfl

section Uniform

variable {degree arity : ℕ} (data : InducingData degree)
  (holomorphic : PlaneEisensteinHolomorphic data)
  (family : (Fin arity → RealGL3) → AdelicGL → ℂ)
  (induced : ∀ vertices, IsInduced data .plane cohomologicalPoint (family vertices))
  (weight : (Fin arity → RealGL3) → ℝ)

/-- The orbit function of the twisted family at the parameter `parameter` and the argument
`element`, as a function of tuples of matrices. -/
def orbitAt (parameter : ℂ) (element : AdelicGL) :
    SmoothJets.MatrixTuples 3 arity.succ → data.cusp.H :=
  FamilyCuspTaylor.matrixOrbit data .plane parameter
    (twistedAt data holomorphic family induced weight parameter)
    (twistedAt_induced data holomorphic family induced weight parameter) element

/-- The orbit function at a reference argument of finite part `reference`, for the pair
(parameter, left multiplier) and a tuple of matrices. -/
def jointFunction (reference : FiniteGL) :
    (ℂ × SmoothJets.MatrixTuples 3 arity.succ) × SmoothJets.MatrixTuples 3 arity.succ →
      data.cusp.H :=
  fun pair =>
    (Complex.exp ((pair.1.1 - cohomologicalPoint) *
        (weight (fun i => invertibleMatrix (leftMultiply pair.1.2 pair.2 i.castSucc)) : ℂ)) *
      Complex.exp ((pair.1.1 - cohomologicalPoint) *
        (heightLog (atFinite reference * atInfinity
          (invertibleMatrix (leftMultiply pair.1.2 pair.2 (Fin.last arity)))) : ℂ))) •
    FamilyCuspTaylor.matrixOrbit data .plane cohomologicalPoint family induced
      (atFinite reference) (leftMultiply pair.1.2 pair.2)

theorem jointFunction_contDiffOn (lift : HasSmoothCuspLift data .plane cohomologicalPoint family)
    (weightSmooth : Smooth weight) (reference : FiniteGL) :
    ContDiffOn ℝ ⊤ (jointFunction data family induced weight reference)
      {pair | leftMultiply pair.1.2 pair.2 ∈ SmoothJets.domain 3 arity.succ} := by
  have hq : ContDiff ℝ ⊤ (fun pair : (ℂ × SmoothJets.MatrixTuples 3 arity.succ) ×
      SmoothJets.MatrixTuples 3 arity.succ => leftMultiply pair.1.2 pair.2) :=
    (leftMultiply (arity := arity)).isBoundedBilinearMap.contDiff.comp
      ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd)
  have hθ : ContDiffOn ℝ ⊤ (FamilyCuspTaylor.matrixOrbit data .plane cohomologicalPoint family
      induced (atFinite reference)) (SmoothJets.domain 3 arity.succ) :=
    FamilyCuspLift.joint_smooth data .plane cohomologicalPoint family induced lift
      (atFinite reference)
  have hw : ContDiffOn ℝ ⊤ (fun N : SmoothJets.MatrixTuples 3 arity.succ =>
      weight (fun i => invertibleMatrix (N i.castSucc))) (SmoothJets.domain 3 arity.succ) :=
    smooth_comp_castSucc weight weightSmooth
  have hh : ContDiffOn ℝ ⊤ (fun N : SmoothJets.MatrixTuples 3 arity.succ =>
      heightLog (atFinite reference * atInfinity (invertibleMatrix (N (Fin.last arity)))))
      (SmoothJets.domain 3 arity.succ) :=
    smooth_comp_coordinate (Fin.last arity)
      (fun x : Fin 1 → RealGL3 => heightLog (atFinite reference * atInfinity (x 0)))
      (heightLog_law.smooth (atFinite reference))
  have hz : ContDiff ℝ ⊤ (fun pair : (ℂ × SmoothJets.MatrixTuples 3 arity.succ) ×
      SmoothJets.MatrixTuples 3 arity.succ => pair.1.1 - cohomologicalPoint) :=
    (contDiff_fst.comp contDiff_fst).sub contDiff_const
  have hθq := hθ.comp hq.contDiffOn
    (s := {pair : (ℂ × SmoothJets.MatrixTuples 3 arity.succ) × SmoothJets.MatrixTuples 3 arity.succ |
      leftMultiply pair.1.2 pair.2 ∈ SmoothJets.domain 3 arity.succ})
    (fun pair membership => membership)
  have hwq := hw.comp hq.contDiffOn
    (s := {pair : (ℂ × SmoothJets.MatrixTuples 3 arity.succ) × SmoothJets.MatrixTuples 3 arity.succ |
      leftMultiply pair.1.2 pair.2 ∈ SmoothJets.domain 3 arity.succ})
    (fun pair membership => membership)
  have hhq := hh.comp hq.contDiffOn
    (s := {pair : (ℂ × SmoothJets.MatrixTuples 3 arity.succ) × SmoothJets.MatrixTuples 3 arity.succ |
      leftMultiply pair.1.2 pair.2 ∈ SmoothJets.domain 3 arity.succ})
    (fun pair membership => membership)
  have first : ContDiffOn ℝ ⊤ (fun pair : (ℂ × SmoothJets.MatrixTuples 3 arity.succ) ×
      SmoothJets.MatrixTuples 3 arity.succ =>
      Complex.exp ((pair.1.1 - cohomologicalPoint) *
        (weight (fun i => invertibleMatrix (leftMultiply pair.1.2 pair.2 i.castSucc)) : ℂ)))
      {pair | leftMultiply pair.1.2 pair.2 ∈ SmoothJets.domain 3 arity.succ} :=
    (hz.contDiffOn.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hwq)).cexp
  have second : ContDiffOn ℝ ⊤ (fun pair : (ℂ × SmoothJets.MatrixTuples 3 arity.succ) ×
      SmoothJets.MatrixTuples 3 arity.succ =>
      Complex.exp ((pair.1.1 - cohomologicalPoint) *
        (heightLog (atFinite reference * atInfinity
          (invertibleMatrix (leftMultiply pair.1.2 pair.2 (Fin.last arity)))) : ℂ)))
      {pair | leftMultiply pair.1.2 pair.2 ∈ SmoothJets.domain 3 arity.succ} :=
    (hz.contDiffOn.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hhq)).cexp
  exact (first.mul second).smul hθq

/-- On tuples of invertible matrices the joint function is the orbit function at an argument whose
finite part is congruent to `reference`. -/
theorem orbitAt_eq_jointFunction (parameter : ℂ) (reference : FiniteGL) (argument : AdelicGL)
    (membership : reference⁻¹ * finiteGroup argument ∈ finiteLevel)
    (matrices : SmoothJets.MatrixTuples 3 arity.succ)
    (invertible : matrices ∈ SmoothJets.domain 3 arity.succ) :
    orbitAt data holomorphic family induced weight parameter argument matrices =
      jointFunction data family induced weight reference
        ((parameter, fun index => (AdelicFamilyTaylor.leftUnits argument index).val), matrices) := by
  let vectorFunction : (Fin arity → RealGL3) → AdelicGL → data.cusp.H :=
    fun vertices point => (FamilyCuspLift.vector data .plane parameter
      (twistedAt data holomorphic family induced weight parameter)
      (twistedAt_induced data holomorphic family induced weight parameter) vertices point).val
  have equality := AdelicFamilyTaylor.finite_local_formula vectorFunction
    (fun vertices level point => congrArg Subtype.val
      (FamilyCuspLift.finite_invariant data .plane parameter
        (twistedAt data holomorphic family induced weight parameter)
        (twistedAt_induced data holomorphic family induced weight parameter) vertices point level))
    reference argument membership (fun index => invertibleMatrix (matrices index))
  have units : (fun index => invertibleMatrix
      (leftMultiply (fun index => (AdelicFamilyTaylor.leftUnits argument index).val) matrices index)) =
      fun index => AdelicFamilyTaylor.leftUnits argument index * invertibleMatrix (matrices index) :=
    funext fun index => TranslatedJets.invertibleMatrix_mul_left _ _ (invertible index)
  have jointEquality : jointFunction data family induced weight reference
      ((parameter, fun index => (AdelicFamilyTaylor.leftUnits argument index).val), matrices) =
      orbitAt data holomorphic family induced weight parameter (atFinite reference)
        (leftMultiply (fun index => (AdelicFamilyTaylor.leftUnits argument index).val) matrices) :=
    (matrixOrbit_twistedAt data holomorphic family induced weight parameter (atFinite reference)
      (leftMultiply (fun index => (AdelicFamilyTaylor.leftUnits argument index).val) matrices)).symm
  rw [jointEquality]
  calc orbitAt data holomorphic family induced weight parameter argument matrices
      = AdelicFamilyTaylor.orbit vectorFunction argument
          (fun index => invertibleMatrix (matrices index)) := rfl
    _ = AdelicFamilyTaylor.orbit vectorFunction (atFinite reference)
          (fun index => AdelicFamilyTaylor.leftUnits argument index *
            invertibleMatrix (matrices index)) := equality
    _ = AdelicFamilyTaylor.orbit vectorFunction (atFinite reference)
          (fun index => invertibleMatrix (leftMultiply
            (fun index => (AdelicFamilyTaylor.leftUnits argument index).val) matrices index)) := by
        rw [units]
    _ = orbitAt data holomorphic family induced weight parameter (atFinite reference)
          (leftMultiply (fun index => (AdelicFamilyTaylor.leftUnits argument index).val)
            matrices) := rfl

/-- The local uniform Taylor bound: near a pair (parameter, argument), the orbit functions of the
twisted family have a Taylor expansion at the real tuple `real` on a common ball with a common
geometric bound. -/
theorem local_uniform_orbit (lift : HasSmoothCuspLift data .plane cohomologicalPoint family)
    (weightSmooth : Smooth weight) (real : Fin (arity + 1) → RealGL3) (point : ℂ × AdelicGL) :
    ∃ radius : ℝ≥0, 0 < radius ∧ ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ᶠ pair in 𝓝 point,
        HasFPowerSeriesOnBall (orbitAt data holomorphic family induced weight pair.1 pair.2)
          (coefficients (orbitAt data holomorphic family induced weight pair.1 pair.2)
            (fun index => (real index).val)) (fun index => (real index).val) radius ∧
        ∀ order, ‖coefficients (orbitAt data holomorphic family induced weight pair.1 pair.2)
          (fun index => (real index).val) order‖ ≤ constant * (radius : ℝ)⁻¹ ^ order := by
  let center : SmoothJets.MatrixTuples 3 arity.succ := fun index => (real index).val
  let reference : FiniteGL := finiteGroup point.2
  let coordinates : AdelicGL → SmoothJets.MatrixTuples 3 arity.succ :=
    fun argument index => (AdelicFamilyTaylor.leftUnits argument index).val
  have inDomain : leftMultiply (coordinates point.2) center ∈ SmoothJets.domain 3 arity.succ := by
    intro index
    change ((AdelicFamilyTaylor.leftUnits point.2 index).val * (real index).val).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (GeneralLinearGroup.det_ne_zero _) (GeneralLinearGroup.det_ne_zero _)
  have jointOpen : IsOpen {pair : (ℂ × SmoothJets.MatrixTuples 3 arity.succ) ×
      SmoothJets.MatrixTuples 3 arity.succ |
      leftMultiply pair.1.2 pair.2 ∈ SmoothJets.domain 3 arity.succ} := by
    have continuous : Continuous (fun pair : (ℂ × SmoothJets.MatrixTuples 3 arity.succ) ×
        SmoothJets.MatrixTuples 3 arity.succ => leftMultiply pair.1.2 pair.2) :=
      (leftMultiply (arity := arity)).isBoundedBilinearMap.continuous.comp
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
    exact (SmoothJets.domain_open 3 arity.succ).preimage continuous
  have jointAnalytic : AnalyticAt ℝ (jointFunction data family induced weight reference)
      ((point.1, coordinates point.2), center) :=
    analyticAt_of_contDiffOn jointOpen
      (jointFunction_contDiffOn data family induced weight lift weightSmooth reference) inDomain
  obtain ⟨largeRadius, largePositive, constant, nonnegative, bounded⟩ :=
    CompactTaylorBounds.local_uniform jointAnalytic
  have centerMembership : center ∈ SmoothJets.domain 3 arity.succ :=
    fun _ => GeneralLinearGroup.det_ne_zero _
  obtain ⟨epsilon, epsilonPositive, inDomainBall⟩ :=
    Metric.mem_nhds_iff.mp ((SmoothJets.domain_open 3 arity.succ).mem_nhds centerMembership)
  let domainRadius : ℝ≥0 := ⟨epsilon, epsilonPositive.le⟩
  let radius := min largeRadius domainRadius
  have positive : 0 < radius := lt_min largePositive epsilonPositive
  have coordinatesContinuous : Continuous coordinates := continuous_pi (fun index =>
    Units.continuous_val.comp ((continuous_apply index).comp AdelicFamilyTaylor.leftUnits_continuous))
  have nearReal : ∀ᶠ pair in 𝓝 point,
      ((pair.1, coordinates pair.2), center) ∈
        Metric.ball ((point.1, coordinates point.2), center) largeRadius :=
    (((continuous_fst.prodMk (coordinatesContinuous.comp continuous_snd)).prodMk
      continuous_const).continuousAt (x := point)).preimage_mem_nhds
      (Metric.ball_mem_nhds _ (by exact_mod_cast largePositive))
  have nearFinite : ∀ᶠ pair in 𝓝 point, reference⁻¹ * finiteGroup pair.2 ∈ finiteLevel :=
    (FiniteLevelTopology.finiteLevel_isOpen.preimage
      (continuous_const.mul (InducedContinuity.finiteGroup_continuous.comp
        continuous_snd))).mem_nhds (by
          dsimp [reference]
          simp)
  refine ⟨radius, positive, constant, nonnegative, ?_⟩
  filter_upwards [nearReal, nearFinite] with pair realNear finiteNear
  have restricted := TaylorFamilies.restrict_snd largePositive
    (bounded ((pair.1, coordinates pair.2), center) realNear).1 constant
    (bounded ((pair.1, coordinates pair.2), center) realNear).2
  have smaller := TaylorFamilies.weaken positive (min_le_left _ _) nonnegative le_rfl restricted
  apply TaylorFamilies.congr positive constant smaller
  intro matrices membership
  have invertible : matrices ∈ SmoothJets.domain 3 arity.succ := inDomainBall
    (Metric.ball_subset_ball (show (radius : ℝ) ≤ epsilon from
      NNReal.coe_le_coe.mpr (min_le_right _ _)) membership)
  exact (orbitAt_eq_jointFunction data holomorphic family induced weight pair.1 reference pair.2
    finiteNear matrices invertible).symm

/-- **Uniform Taylor bounds.** For a compact set of parameters, the orbit functions of the twisted
family at the maximal compact arguments have a Taylor expansion at `real` on a common ball with a
common geometric bound. -/
theorem exists_uniform_bounds (lift : HasSmoothCuspLift data .plane cohomologicalPoint family)
    (weightSmooth : Smooth weight) (real : Fin (arity + 1) → RealGL3) {parameters : Set ℂ}
    (compact : IsCompact parameters) :
    ∃ radius : ℝ≥0, 0 < radius ∧ ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ parameter ∈ parameters, ∀ element, inMaximalCompact element →
        HasFPowerSeriesOnBall (orbitAt data holomorphic family induced weight parameter element)
          (coefficients (orbitAt data holomorphic family induced weight parameter element)
            (fun index => (real index).val)) (fun index => (real index).val) radius ∧
        ∀ order, ‖coefficients (orbitAt data holomorphic family induced weight parameter element)
          (fun index => (real index).val) order‖ ≤ constant * (radius : ℝ)⁻¹ ^ order := by
  obtain ⟨radius, positive, constant, nonnegative, bounded⟩ := TaylorFamilies.uniform_on_compact
    (fun pair : ℂ × AdelicGL => orbitAt data holomorphic family induced weight pair.1 pair.2)
    (fun index => (real index).val) (parameters ×ˢ {element | inMaximalCompact element})
    (compact.prod MaximalCompact.isCompact)
    (fun point _ => local_uniform_orbit data holomorphic family induced weight lift weightSmooth
      real point)
  exact ⟨radius, positive, constant, nonnegative, fun parameter membership element compactElement =>
    bounded (parameter, element) ⟨membership, compactElement⟩⟩

end Uniform

end TernaryPeriodPolynomials.EdgeConvergence.HCLift
