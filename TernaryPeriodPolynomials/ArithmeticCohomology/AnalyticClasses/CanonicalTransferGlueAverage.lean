module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.CanonicalTransferGlue
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.CanonicalReduction
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Real.LineTransferBounds
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineFiniteGlobalIntegrability

@[expose] public section


/-!
# Finite averages of the canonical projected integrals

For a family of finite-level values `X(u)` whose scalar tests are continuous in `u` and dominated,
uniformly in the adelic argument, by an integrable function of `u`, the integral over `u` of the
finite good-line average of `X(u)` is the finite good-line average of the `u`-integral (Fubini on
`ℝ² × (𝔸_f^{(3)})²`; joint measurability by the Carathéodory criterion, using the continuous
`p`-adic form of the finite integrand of a spherical vector). Applied to the canonical projected
terms, which are transferred integrands of the real good-line transfer of the binary cocycle `B`
of the canonical relative cocycle, the integrated canonical projected average is the finite
average of the mixed radical edge of the real transfer, and the integrated canonical average of a
radical simplex is the finite average of the real transfer at the radical pair. The analytic
input is the regularity of `A ↦ B(A)`: continuity of scalar tests and boundedness on compact
sets, uniformly in the adelic argument.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.ArchimedeanConstant
open TernaryPeriodPolynomials.EdgeControl

variable {n : ℕ} {index : Type} [Fintype index]

/-! ### The finite average of scalar tests -/

/-- The finite good-line average of a scalar test at the cohomological point. -/
def finiteAverageLine (F : LineValues n) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) : ℂ :=
  ∫ finite, standardGoodLineFiniteCuspWeight n cohomologicalPoint finite *
      F (atFinite (standardGoodLineFiniteCoordinates finite).block, functional)
    ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)

theorem tensorAverage_eq_finiteAverageLine (data : InducingData n)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (values : cuspidalTensorValues data.cusp (HomogeneousPoly n)) :
    tensorAverage data functional values =
      finiteAverageLine (fun p => p.2 (values.val p.1)) functional := by
  unfold tensorAverage goodLineFiniteVectorIntegral finiteAverageLine
  simp only [cuspidalTensorFunctional_realize]

theorem cohomologicalExponent_re (large : 3 < n) :
    3 < ((n : ℂ) / 2 + 3 + cohomologicalPoint).re := by
  have degree_large : (3 : ℝ) < n := by exact_mod_cast large
  norm_num [cohomologicalPoint, Complex.add_re, Complex.div_re]
  linarith

/-- **Fubini for finite averages of dominated continuous families.** -/
theorem integral_tensorAverage_eq (large : 3 < n) (data : InducingData n)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (X : ℝ × ℝ → cuspidalTensorValues data.cusp (HomogeneousPoly n))
    (finite : ∀ u, X u ∈ cuspidalTensorFiniteLevel data.cusp (HomogeneousPoly n))
    (continuous : ∀ h, Continuous fun u => functional ((X u).val h))
    (g : ℝ × ℝ → ℝ) (integrable : Integrable g ((volume : Measure ℝ).prod volume))
    (bound : ∀ u h, ‖functional ((X u).val h)‖ ≤ g u) :
    Integrable (fun u => tensorAverage data functional (X u))
        ((volume : Measure ℝ).prod volume) ∧
      ∫ u, tensorAverage data functional (X u) ∂((volume : Measure ℝ).prod volume) =
        finiteAverageLine (fun p => ∫ u, p.2 ((X u).val p.1) ∂((volume : Measure ℝ).prod volume))
          functional := by
  set e : ℂ := (n : ℂ) / 2 + 3 + cohomologicalPoint
  set G : ℝ × ℝ → FiniteAwayThree × FiniteAwayThree → ℂ := fun u f =>
    standardGoodLineFiniteCuspWeight n cohomologicalPoint f *
      functional ((X u).val (atFinite (standardGoodLineFiniteCoordinates f).block))
  have spherical (u : ℝ × ℝ) :=
    cuspidalTensorFunctional_spherical data.cusp functional (X u) (finite u)
  have padic (u : ℝ × ℝ) : G u = goodLineFinitePadicIntegrand data.cusp
      (cuspidalTensorFunctional data.cusp functional (X u)) e := by
    funext f
    rw [← goodLineFinitePadicIntegrand_eq n data.cusp cohomologicalPoint _ (spherical u) f,
      cuspidalTensorFunctional_realize]
  have average (u : ℝ × ℝ) : tensorAverage data functional (X u) =
      ∫ f, G u f ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := by
    rw [tensorAverage_eq_finiteAverageLine]
    rfl
  have measurable : StronglyMeasurable (Function.uncurry G) := by
    refine stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
      (fun f => continuous_const.mul (continuous _)) (fun u => ?_)
    rw [padic u]
    exact (goodLineFinitePadicIntegrand_continuous _ _ (spherical u) e).stronglyMeasurable
  have dominating : Integrable (fun z : (ℝ × ℝ) × (FiniteAwayThree × FiniteAwayThree) =>
      g z.1 * goodLinePositiveWeight e z.2)
      (((volume : Measure ℝ).prod volume).prod
        (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) :=
    integrable.mul_prod (goodLinePositiveWeight_integrable e (cohomologicalExponent_re large))
  have joint : Integrable (Function.uncurry G)
      (((volume : Measure ℝ).prod volume).prod
        (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) := by
    refine dominating.mono' measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    change ‖G z.1 z.2‖ ≤ _
    rw [padic z.1]
    change ‖normPower (GeneralLinearGroup.det
        (atFinite (standardGoodLineFinitePadicCoordinates z.2).block)) e *
      data.cusp.realize (cuspidalTensorFunctional data.cusp functional (X z.1))
        (atFinite (standardGoodLineFinitePadicCoordinates z.2).block)‖ ≤ _
    rw [norm_mul, cuspidalTensorFunctional_realize, mul_comm (g z.1)]
    exact mul_le_mul_of_nonneg_left (bound _ _) (norm_nonneg _)
  refine ⟨joint.integral_prod_left.congr (Filter.Eventually.of_forall fun u => (average u).symm),
    ?_⟩
  calc ∫ u, tensorAverage data functional (X u) ∂((volume : Measure ℝ).prod volume) =
      ∫ u, ∫ f, G u f ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)
        ∂((volume : Measure ℝ).prod volume) :=
        integral_congr_ae (Filter.Eventually.of_forall average)
    _ = ∫ f, ∫ u, G u f ∂((volume : Measure ℝ).prod volume)
        ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := integral_integral_swap joint
    _ = _ := by
      unfold finiteAverageLine
      congr 1
      funext f
      exact integral_const_mul _ _

/-! ### Domination of the transferred integrand -/

/-- **The transferred integrand is dominated by an integrable function of `u`.** -/
theorem lineTransferIntegrand_dominated (large : 5 ≤ n) (N : BinaryPointCocycle n)
    (x : Fin 3 → LineGroup) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    ∃ g : ℝ × ℝ → ℝ, Integrable g ((volume : Measure ℝ).prod volume) ∧
      ∀ u h, ‖functional (lineTransferIntegrand N.value x u h)‖ ≤ g u := by
  obtain ⟨C, -, hC⟩ := lineTransferIntegrand_bound N x functional
  refine ⟨fun u => C * kernelBase (lineInput (x 0) u) ^ (-(((n : ℝ) + 3) / 4)),
    ((lineInput_measurePreserving (x 0)).integrable_comp_of_integrable
      (kernelBase_decay_integrable large)).const_mul _, fun u h => ?_⟩
  refine (hC u h).trans (le_of_eq ?_)
  rw [cornerScale_gsVertex (goodLineForm_lineMatrix u (x 0)), gsVertex_lineMatrix_corner,
    ← abs_of_pos (inv_pos.mpr (gsRadius_pos _)), gsRadius_inv_rpow, mul_comm]
  congr 2
  ring

/-! ### The canonical binary cocycle as a pointwise binary cocycle -/

/-- Regularity of pointwise binary values: scalar tests are continuous in the matrix and bounded
on compact sets, uniformly in the adelic argument. -/
structure BinaryValuesRegular
    (N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)) : Prop where
  continuous : ∀ (h : BinaryAdelicGL) (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ),
    Continuous (fun A => functional (N A h))
  bounded : ∀ (K : Set BinaryRealGL), IsCompact K →
    ∀ functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ,
      ∃ C : ℝ, ∀ A ∈ K, ∀ h, ‖functional (N A h)‖ ≤ C

/-- The binary cocycle of the canonical relative cocycle as a pointwise binary cocycle. -/
def canonicalPointCocycle (data : InducingData n) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly n))
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep n data.cusp data.chi))
    (regular : RealPlaneLevelMixedRegular n data.cusp data.chi basis relative)
    (binaryRegular :
      BinaryValuesRegular (canonicalBinaryValues data trivial basis relative regular)) :
    BinaryPointCocycle n where
  value := canonicalBinaryValues data trivial basis relative regular
  cocycle A C := (congrArg Subtype.val ((groupCohomology.mem_cocycles₁_iff _).mp
    (realPlaneLevelBinaryCocycle n data.cusp data.chi trivial basis relative regular).property
      A C)).trans (add_comm _ _)
  continuous := binaryRegular.continuous
  bounded := binaryRegular.bounded

/-! ### The integrated canonical averages -/

/-- **The integrated canonical average of a radical simplex is a finite average of the real
transfer at the radical pair.** -/
theorem integral_radicalCanonicalAverage (large : 5 ≤ n) (data : InducingData n)
    (trivial : data.chi = trivialCharacter) (basis : Module.Basis index ℂ (HomogeneousPoly n))
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep n data.cusp data.chi))
    (regular : RealPlaneLevelMixedRegular n data.cusp data.chi basis relative)
    (binaryRegular :
      BinaryValuesRegular (canonicalBinaryValues data trivial basis relative regular))
    (r₁ r₂ : RadicalLattice) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    ∫ u, tensorAverage data functional
        (radicalCanonicalTerm data trivial basis relative regular u r₁ r₂)
        ∂((volume : Measure ℝ).prod volume) =
      finiteAverageLine (lineTransferCochain
        (canonicalBinaryValues data trivial basis relative regular) (latticePoint r₁)
          (latticePoint r₂)) functional := by
  set N := canonicalPointCocycle data trivial basis relative regular binaryRegular
  set x : Fin 3 → LineGroup := ![1, latticePoint r₁, latticePoint r₁ * latticePoint r₂]
  obtain ⟨g, hg, bound⟩ := lineTransferIntegrand_dominated large N x functional
  have result := (integral_tensorAverage_eq (by omega) data functional
    (fun u => radicalCanonicalTerm data trivial basis relative regular u r₁ r₂)
    (fun u => radicalCanonicalTerm_finiteLevel data trivial basis relative regular u r₁ r₂)
    (fun h => by
      simp only [radicalCanonicalTerm_val]
      exact lineTransferIntegrand_continuous N x h functional)
    g hg (fun u h => by
      rw [radicalCanonicalTerm_val]
      exact bound u h)).2
  rw [result]
  simp only [radicalCanonicalTerm_val]
  rfl

theorem leviPoint_conj_mul (γ : GeneralLinearGroup (Fin 2) ℤ) (r : RadicalLattice) :
    leviPoint γ * ((leviPoint γ)⁻¹ * latticePoint r * leviPoint γ) =
      latticePoint r * leviPoint γ := by
  group

/-- **The integrated canonical average of one radical generator is a finite average of the
mixed radical edge of the real transfer.** Also exports integrability. -/
theorem integral_canonicalProjectedTerm (large : 5 ≤ n) (data : InducingData n)
    (trivial : data.chi = trivialCharacter) (basis : Module.Basis index ℂ (HomogeneousPoly n))
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep n data.cusp data.chi))
    (regular : RealPlaneLevelMixedRegular n data.cusp data.chi basis relative)
    (binaryRegular :
      BinaryValuesRegular (canonicalBinaryValues data trivial basis relative regular))
    (γ : GeneralLinearGroup (Fin 2) ℤ) (r : RadicalLattice)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    Integrable (fun u => tensorAverage data functional
        (canonicalProjectedTerm data trivial basis relative regular u γ r))
        ((volume : Measure ℝ).prod volume) ∧
      ∫ u, tensorAverage data functional
          (canonicalProjectedTerm data trivial basis relative regular u γ r)
          ∂((volume : Measure ℝ).prod volume) =
        finiteAverageLine (radicalEdge (lineTransferCochain
          (canonicalBinaryValues data trivial basis relative regular)) (integralLevi γ)
            (latticeVector r)) functional := by
  set NB := canonicalBinaryValues data trivial basis relative regular
  set N := canonicalPointCocycle data trivial basis relative regular binaryRegular
  set x₁ : Fin 3 → LineGroup := ![1, leviPoint γ, latticePoint r * leviPoint γ]
  set x₂ : Fin 3 → LineGroup := ![1, latticePoint r, latticePoint r * leviPoint γ]
  obtain ⟨g₁, hg₁, bound₁⟩ := lineTransferIntegrand_dominated large N x₁ functional
  obtain ⟨g₂, hg₂, bound₂⟩ := lineTransferIntegrand_dominated large N x₂ functional
  have result := integral_tensorAverage_eq (by omega) data functional
    (fun u => canonicalProjectedTerm data trivial basis relative regular u γ r)
    (fun u => canonicalProjectedTerm_finiteLevel data trivial basis relative regular u γ r)
    (fun h => by
      simp only [canonicalProjectedTerm_val, map_sub]
      exact (lineTransferIntegrand_continuous N x₁ h functional).sub
        (lineTransferIntegrand_continuous N x₂ h functional))
    (g₁ + g₂) (hg₁.add hg₂) (fun u h => by
      rw [canonicalProjectedTerm_val, map_sub]
      exact (norm_sub_le _ _).trans (add_le_add (bound₁ u h) (bound₂ u h)))
  refine ⟨result.1, result.2.trans ?_⟩
  congr 1
  funext p
  have first : lineTransferCochain NB (leviPoint γ)
      ((leviPoint γ)⁻¹ * latticePoint r * leviPoint γ) = lineTransfer NB x₁ := by
    change lineTransfer NB ![1, leviPoint γ,
      leviPoint γ * ((leviPoint γ)⁻¹ * latticePoint r * leviPoint γ)] = _
    rw [leviPoint_conj_mul]
  have second : lineTransferCochain NB (latticePoint r) (leviPoint γ) = lineTransfer NB x₂ := rfl
  change _ = (lineTransferCochain NB (leviPoint γ)
      ((leviPoint γ)⁻¹ * latticePoint r * leviPoint γ) -
    lineTransferCochain NB (latticePoint r) (leviPoint γ)) p
  rw [first, second]
  change _ = (∫ u, p.2 (lineTransferIntegrand NB x₁ u p.1) ∂((volume : Measure ℝ).prod volume)) -
    ∫ u, p.2 (lineTransferIntegrand NB x₂ u p.1) ∂((volume : Measure ℝ).prod volume)
  have integrable₁ : Integrable (fun u => p.2 (lineTransferIntegrand NB x₁ u p.1))
      ((volume : Measure ℝ).prod volume) := lineTransferIntegrand_integrable large N x₁ p.1 p.2
  have integrable₂ : Integrable (fun u => p.2 (lineTransferIntegrand NB x₂ u p.1))
      ((volume : Measure ℝ).prod volume) := lineTransferIntegrand_integrable large N x₂ p.1 p.2
  rw [← integral_sub integrable₁ integrable₂]
  simp only [canonicalProjectedTerm_val, map_sub]
  rfl

/-- **The integrated canonical projected average is a sum of finite averages of mixed radical
edges of the real transfer**, one for each radical generator, tested through the lower radical
lattice contributions. -/
theorem integral_canonicalProjectedAverage (large : 5 ≤ n) (data : InducingData n)
    (trivial : data.chi = trivialCharacter) (basis : Module.Basis index ℂ (HomogeneousPoly n))
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep n data.cusp data.chi))
    (regular : RealPlaneLevelMixedRegular n data.cusp data.chi basis relative)
    (binaryRegular :
      BinaryValuesRegular (canonicalBinaryValues data trivial basis relative regular))
    (γ : GeneralLinearGroup (Fin 2) ℤ) (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ) :
    ∫ u, canonicalProjectedAverage data trivial basis relative regular γ functional u
        ∂((volume : Measure ℝ).prod volume) =
      finiteAverageLine (radicalEdge (lineTransferCochain
          (canonicalBinaryValues data trivial basis relative regular)) (integralLevi γ)
            (latticeVector radicalLatticeFirst))
          (functional.comp (lowerRadicalLatticeContribution n 0)) +
        finiteAverageLine (radicalEdge (lineTransferCochain
          (canonicalBinaryValues data trivial basis relative regular)) (integralLevi γ)
            (latticeVector radicalLatticeSecond))
          (functional.comp (lowerRadicalLatticeContribution n 1)) := by
  obtain ⟨i₀, e₀⟩ := integral_canonicalProjectedTerm large data trivial basis relative regular
    binaryRegular γ radicalLatticeFirst (functional.comp (lowerRadicalLatticeContribution n 0))
  obtain ⟨i₁, e₁⟩ := integral_canonicalProjectedTerm large data trivial basis relative regular
    binaryRegular γ radicalLatticeSecond (functional.comp (lowerRadicalLatticeContribution n 1))
  unfold canonicalProjectedAverage
  rw [integral_add i₀ i₁, e₀, e₁]

/-- The integrated canonical projected average as a sum over the two radical generators. -/
theorem integral_canonicalProjectedAverage_sum (large : 5 ≤ n) (data : InducingData n)
    (trivial : data.chi = trivialCharacter) (basis : Module.Basis index ℂ (HomogeneousPoly n))
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep n data.cusp data.chi))
    (regular : RealPlaneLevelMixedRegular n data.cusp data.chi basis relative)
    (binaryRegular :
      BinaryValuesRegular (canonicalBinaryValues data trivial basis relative regular))
    (γ : GeneralLinearGroup (Fin 2) ℤ) (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ) :
    ∫ u, canonicalProjectedAverage data trivial basis relative regular γ functional u
        ∂((volume : Measure ℝ).prod volume) =
      ∑ i : Fin 2, finiteAverageLine (radicalEdge (lineTransferCochain
          (canonicalBinaryValues data trivial basis relative regular)) (integralLevi γ)
            (latticeVector (![radicalLatticeFirst, radicalLatticeSecond] i)))
          (functional.comp (lowerRadicalLatticeContribution n i)) := by
  rw [Fin.sum_univ_two]
  exact integral_canonicalProjectedAverage large data trivial basis relative regular
    binaryRegular γ functional

end TernaryPeriodPolynomials.AnalyticClasses
