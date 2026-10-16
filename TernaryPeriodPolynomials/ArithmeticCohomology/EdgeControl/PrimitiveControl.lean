module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EdgeControl.Controlled
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.RealizeIntervalIntegral
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.GeneralStageFamilies
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineMixedCuspidalValues
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.HilbertCoordinates
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Iwasawa.PrismEquivariance

@[expose] public section


/-!
# Control of finite-level families with jointly analytic Hilbert orbits

Let `F : E → cuspidalTensorValues cusp V` be a finite-level family whose Hilbert coordinates have a
`GL₂(ℝ)`-orbit that is jointly analytic at `(1, c)` for every `c`. Then the orbit is jointly
analytic at every `(g, c)`, the family of real translates `(c, g) ↦ π(g) F(c)` again has a jointly
analytic orbit, and the stage realizations give continuity of the sup-norm realizations in `(c, g)`.
Hence `F` along any continuous path is a controlled family. This applies to Codexiom's radical
primitive of the chosen relative representative.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EdgeControl

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Joint orbit analyticity moves from the identity to any invertible matrix.** -/
theorem generalFamilyOrbit_analyticAt_of_one (cusp : CuspidalRepresentation) (family : E → cusp.H)
    (center : E) (analytic : AnalyticAt ℝ (generalFamilyOrbit cusp family) (1, center))
    (g : BinaryRealGL) : AnalyticAt ℝ (generalFamilyOrbit cusp family) (g.val, center) := by
  let shift : BinaryMatrix × E →L[ℝ] BinaryMatrix × E :=
    (leftMultiplication g⁻¹.val).prodMap (ContinuousLinearMap.id ℝ E)
  let action := (BinaryLevel.unitaryOperator cusp (atInfinity g)).restrictScalars ℝ
  have atShift : shift (g.val, center) = (1, center) := by
    change (g⁻¹.val * g.val, center) = (1, center)
    rw [g.inv_mul]
  have analytic' : AnalyticAt ℝ (generalFamilyOrbit cusp family) (shift (g.val, center)) := by
    rw [atShift]; exact analytic
  have composite : AnalyticAt ℝ (action ∘ generalFamilyOrbit cusp family ∘ shift) (g.val, center) :=
    (action.analyticAt _).comp (analytic'.comp (shift.analyticAt _))
  apply composite.congr
  have hopen : IsOpen (Prod.fst ⁻¹' binaryDomain : Set (BinaryMatrix × E)) :=
    binaryDomain_isOpen.preimage continuous_fst
  filter_upwards [hopen.mem_nhds (show (g.val, center) ∈ Prod.fst ⁻¹' binaryDomain from
    g.det_ne_zero)] with point hpoint
  exact realOrbit_inverse_translation cusp (family point.2) g point.1 hpoint

/-- The real translates of a family of smooth vectors, as a family over `E × M₂(ℝ)`. -/
def translatedFamily (cusp : CuspidalRepresentation) (family : E → cusp.smooth)
    (point : E × BinaryMatrix) : cusp.smooth :=
  ⟨realOrbit cusp (family point.1).val point.2,
    cusp.smooth_stable _ _ (family point.1).property⟩

/-- **The translated family has a jointly analytic orbit.** -/
theorem translatedFamily_analyticAt (cusp : CuspidalRepresentation) (family : E → cusp.smooth)
    (analytic : ∀ center, AnalyticAt ℝ (generalFamilyOrbit cusp (fun e => (family e).val)) (1,
        center))
    (center : E) (g : BinaryRealGL) :
    AnalyticAt ℝ (generalFamilyOrbit cusp (fun point => (translatedFamily cusp family point).val))
      (1, (center, g.val)) := by
  let B : BinaryMatrix →L[ℝ] BinaryMatrix →L[ℝ] BinaryMatrix :=
    LinearMap.toContinuousLinearMap leftMultiplicationLinear
  have hpair : AnalyticAt ℝ (fun p : BinaryMatrix × (E × BinaryMatrix) => (p.1, p.2.2))
      (1, (center, g.val)) :=
    ((ContinuousLinearMap.fst ℝ BinaryMatrix (E × BinaryMatrix)).analyticAt _).prod
      (((ContinuousLinearMap.snd ℝ E BinaryMatrix).comp
        (ContinuousLinearMap.snd ℝ BinaryMatrix (E × BinaryMatrix))).analyticAt _)
  have hmul : AnalyticAt ℝ (fun p : BinaryMatrix × (E × BinaryMatrix) => p.1 * p.2.2)
      (1, (center, g.val)) :=
    AnalyticAt.comp (g := fun q : BinaryMatrix × BinaryMatrix => B q.1 q.2)
      (f := fun p : BinaryMatrix × (E × BinaryMatrix) => (p.1, p.2.2))
      (B.analyticAt_bilinear _) hpair
  have hinner : AnalyticAt ℝ (fun p : BinaryMatrix × (E × BinaryMatrix) => (p.1 * p.2.2, p.2.1))
      (1, (center, g.val)) :=
    hmul.prod (((ContinuousLinearMap.fst ℝ E BinaryMatrix).comp
      (ContinuousLinearMap.snd ℝ BinaryMatrix (E × BinaryMatrix))).analyticAt _)
  have atPoint : AnalyticAt ℝ (generalFamilyOrbit cusp (fun e => (family e).val))
      ((fun p : BinaryMatrix × (E × BinaryMatrix) => (p.1 * p.2.2, p.2.1)) (1, (center, g.val))) :=
          by
    change AnalyticAt ℝ _ ((1 : BinaryMatrix) * g.val, center)
    rw [one_mul]
    exact generalFamilyOrbit_analyticAt_of_one cusp _ center (analytic center) g
  have composite := AnalyticAt.comp (g := generalFamilyOrbit cusp (fun e => (family e).val))
    (f := fun p : BinaryMatrix × (E × BinaryMatrix) => (p.1 * p.2.2, p.2.1)) atPoint hinner
  apply composite.congr
  have hopen : IsOpen {p : BinaryMatrix × (E × BinaryMatrix) | p.1.det ≠ 0 ∧ p.2.2.det ≠ 0} :=
    (isOpen_ne.preimage continuous_fst.matrix_det).inter
      (isOpen_ne.preimage (continuous_snd.comp continuous_snd).matrix_det)
  have hmem : ((1 : BinaryMatrix), (center, g.val)) ∈
      {p : BinaryMatrix × (E × BinaryMatrix) | p.1.det ≠ 0 ∧ p.2.2.det ≠ 0} :=
    ⟨by simp, g.det_ne_zero⟩
  filter_upwards [hopen.mem_nhds hmem] with p hp
  exact (realOrbit_realOrbit cusp (family p.2.1).val p.1 p.2.2 hp.1 hp.2).symm

/-- **Continuity of the sup-norm realizations of real translates.** -/
theorem translatedFamily_continuous (cusp : CuspidalRepresentation)
    (stageContinuity : AnalyticScalar.ContinuousStages cusp) (family : E → cusp.smooth)
    (analytic : ∀ center, AnalyticAt ℝ (generalFamilyOrbit cusp (fun e => (family e).val)) (1,
        center))
    (fixed : ∀ e, (family e).val ∈ BinaryLevel.fixedSubspace cusp BinaryLevel.finiteCongruence) :
    Continuous (fun point : E × BinaryRealGL => CuspSupNorm.boundedRealization cusp
      ⟨cusp.π (atInfinity point.2) (family point.1).val,
        cusp.smooth_stable _ _ (family point.1).property⟩) := by
  have equality : (fun point : E × BinaryRealGL => CuspSupNorm.boundedRealization cusp
      ⟨cusp.π (atInfinity point.2) (family point.1).val,
        cusp.smooth_stable _ _ (family point.1).property⟩) =
      (fun point => CuspSupNorm.boundedRealization cusp (translatedFamily cusp family point)) ∘
        (fun point : E × BinaryRealGL => (point.1, point.2.val)) := by
    funext point
    simp only [Function.comp, translatedFamily, realOrbit, invertibleMatrix_units]
  rw [equality, continuous_iff_continuousAt]
  intro point
  apply ContinuousAt.comp _ (continuous_fst.prodMk (Units.continuous_val.comp
      continuous_snd)).continuousAt
  exact boundedRealization_continuousAt_of_jointAnalytic cusp stageContinuity
    (translatedFamily cusp family) (point.1, point.2.val)
    (translatedFamily_analyticAt cusp family analytic point.1 point.2)
    (fun p => realOrbit_fixed cusp _ (fixed p.1) p.2)

/-- Spherical vectors are fixed by the finite congruence subgroup. -/
theorem spherical_fixed (cusp : CuspidalRepresentation) (vector : cusp.H)
    (spherical : vector ∈ cuspSphericalValues cusp) :
    vector ∈ BinaryLevel.fixedSubspace cusp BinaryLevel.finiteCongruence := by
  rintro ⟨element, integral, -, rfl⟩
  exact spherical integral

variable {V : Type} [AddCommGroup V] [Module ℂ V] {index : Type} [Fintype index]

/-- **A finite-level family with jointly analytic Hilbert orbits is controlled along continuous
paths.** -/
theorem controlled_of_hilbertAnalytic (cusp : CuspidalRepresentation)
    (stageContinuity : AnalyticScalar.ContinuousStages cusp) (basis : Module.Basis index ℂ V)
    (family : E → cuspidalTensorValues cusp V)
    (finite : ∀ e, family e ∈ cuspidalTensorFiniteLevel cusp V)
    (analytic : ∀ center, AnalyticAt ℝ (fun point : BinaryMatrix × E =>
      binaryHilbertTranslation cusp (atInfinity (invertibleMatrix point.1))
        (cuspidalTensorHilbertEmbedding cusp basis (family point.2))) (1, center))
    {X : Type*} [TopologicalSpace X] {path : X → E} (hpath : Continuous path) :
    Controlled cusp (fun x => family (path x)) := by
  classical
  have coordinate (i : index) : Continuous (fun point : E × BinaryRealGL =>
      testRealization cusp (basis.coord i) point.2 (family point.1)) := by
    let smoothFamily : E → cusp.smooth := fun e => cuspidalTensorFunctional cusp (basis.coord i)
        (family e)
    have orbitAnalytic (center : E) :
        AnalyticAt ℝ (generalFamilyOrbit cusp (fun e => (smoothFamily e).val)) (1, center) := by
      have projected := ((ContinuousLinearMap.proj i : (index → cusp.H) →L[ℂ]
          cusp.H).restrictScalars
        ℝ).analyticAt _ |>.comp (analytic center)
      exact projected
    have continuity := translatedFamily_continuous cusp stageContinuity smoothFamily orbitAnalytic
      (fun e => spherical_fixed cusp _
        (cuspidalTensorFunctional_spherical cusp (basis.coord i) (family e) (finite e)))
    refine continuity.congr (fun point => ?_)
    unfold testRealization
    simp only [LinearMap.comp_apply]
    rw [cuspidalTensorFunctional_translation]
  have decomposition (functional : V →ₗ[ℂ] ℂ) :
      functional = ∑ i, functional (basis i) • basis.coord i := by
    apply basis.ext
    intro j
    simp
  have general (functional : V →ₗ[ℂ] ℂ) : Continuous (fun point : E × BinaryRealGL =>
      testRealization cusp functional point.2 (family point.1)) := by
    rw [decomposition functional]
    simp only [testRealization_sum_functional]
    exact continuous_finsetSum _ (fun i _ => (coordinate i).const_smul (functional (basis i)))
  have controlled : Controlled cusp family := general
  exact controlled.comp hpath

end TernaryPeriodPolynomials.EdgeControl
