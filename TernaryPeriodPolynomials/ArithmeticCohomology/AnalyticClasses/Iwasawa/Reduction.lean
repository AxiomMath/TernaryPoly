module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Iwasawa.EdgeIntegrability

@[expose] public section


/-!
# Reduction of the good-line mixed coordinate to the source on Iwasawa simplices

The integrated Iwasawa prism scalars `I_ℓ(1, y)` are linear in `ℓ`, so they are the scalar tests of
one coefficient vector `f(y)`. By the Levi and radical equivariance of the prism, the prism part of the
integrated mixed finite family is the mixed coordinate of the two-coboundary of `f` restricted to the
good-line stabilizer. Hence

`∫ (mixed finite family) = ∫ (finite average of the projected part) + ℓ(mixed coordinate of δ f)`,

and only the source on the Gram–Schmidt (plane-parabolic) simplices remains in the integral.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

/-- The prism edge averages are linear in the test functional. -/
theorem prismEdgeAverage_sum (large : 3 < n) (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (functionals : ι → HomogeneousPoly n →ₗ[ℂ] ℂ) (x y : RealGL3) (u : ℝ × ℝ) :
    prismEdgeAverage data source cocycle (∑ i ∈ s, c i • functionals i) x y u =
      ∑ i ∈ s, c i * prismEdgeAverage data source cocycle (functionals i) x y u := by
  unfold prismEdgeAverage
  apply finiteAverage_combination large data.cusp _ s c
    (fun i => cuspidalTensorFunctional data.cusp (functionals i) (goodLineIwasawaPrism data source cocycle u ![x, y]))
    (fun i => goodLineIwasawaPrism_spherical data source cocycle u ![x, y] _)
  intro A
  simp only [cuspidalTensorFunctional_realize]
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, smul_eq_mul]

theorem prismEdgeIntegral_sum (large : 3 < n) (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (functionals : ι → HomogeneousPoly n →ₗ[ℂ] ℂ) (x y : RealGL3)
    (integrable : ∀ i ∈ s, Integrable (prismEdgeAverage data source cocycle (functionals i) x y)
      ((volume : Measure ℝ).prod volume)) :
    prismEdgeIntegral data source cocycle (∑ i ∈ s, c i • functionals i) x y =
      ∑ i ∈ s, c i * prismEdgeIntegral data source cocycle (functionals i) x y := by
  unfold prismEdgeIntegral
  simp_rw [prismEdgeAverage_sum large data source cocycle s c functionals x y]
  rw [integral_finsetSum _ (fun i hi => (integrable i hi).const_mul (c i))]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_const_mul _ _

/-- The coefficient vector dual to the integrated prism scalars at `(1, y)`. -/
def prismDualVector (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (y : RealGL3) : HomogeneousPoly n :=
  let _ : FiniteDimensional ℂ (HomogeneousPoly n) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 3) ℂ n)
  let basis := Module.finBasis ℂ (HomogeneousPoly n)
  ∑ i, prismEdgeIntegral data source cocycle (basis.coord i) 1 y • basis i

/-- **The integrated prism scalars at `(1, y)` are the tests of one coefficient vector.** -/
theorem functional_prismDualVector (large : 3 < n) (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (y : RealGL3)
    (integrable : ∀ functional : HomogeneousPoly n →ₗ[ℂ] ℂ,
      Integrable (prismEdgeAverage data source cocycle functional 1 y) ((volume : Measure ℝ).prod volume))
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    functional (prismDualVector data source cocycle y) = prismEdgeIntegral data source cocycle functional 1 y := by
  let _ : FiniteDimensional ℂ (HomogeneousPoly n) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 3) ℂ n)
  let basis := Module.finBasis ℂ (HomogeneousPoly n)
  have decomposition : functional = ∑ i, functional (basis i) • basis.coord i := by
    apply basis.ext
    intro j
    simp
  change functional (∑ i, prismEdgeIntegral data source cocycle (basis.coord i) 1 y • basis i) = _
  conv_rhs => rw [decomposition]
  rw [prismEdgeIntegral_sum large data source cocycle Finset.univ _ _ 1 y (fun i _ => integrable _), map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, smul_eq_mul, mul_comm]

end TernaryPeriodPolynomials.AnalyticClasses

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

/-- The integrated Iwasawa prism cochain on the good-line stabilizer. -/
def prismStabilizerCochain (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) :
    flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine) → goodLineCoefficientRep n :=
  fun g => prismDualVector data source cocycle (GeneralLinearGroup.map (algebraMap ℚ ℝ) g.val)

theorem goodLineLevi_radical_commute (γ : GeneralLinearGroup (Fin 2) ℤ) (r : RadicalLattice) :
    goodLineLeviSection γ * goodLineRadicalInclusion (lowerLeviLatticeInput γ r) =
      goodLineRadicalInclusion r * goodLineLeviSection γ := by
  apply Subtype.ext
  exact (lowerLeviLatticeInput_conjugation γ r).symm

theorem edgeRadical_mul_edgeLevi (γ : GeneralLinearGroup (Fin 2) ℤ) (r : RadicalLattice) :
    edgeRadical r * edgeLevi γ = edgeLevi γ * edgeRadical (lowerLeviLatticeInput γ r) := by
  rw [edgeRadical, edgeLevi, edgeRadical, ← map_mul, ← map_mul, lowerLeviLatticeInput_conjugation]

/-- **The prism combination of one radical generator is a coboundary coordinate.** -/
theorem integral_prismCombination_eq (large : 5 ≤ n) (data : InducingData n)
    (trivial : data.chi = trivialCharacter) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (γ : GeneralLinearGroup (Fin 2) ℤ) (r : RadicalLattice) :
    ∫ u, prismCombination data source cocycle functional γ r u ∂((volume : Measure ℝ).prod volume) =
      (functional.comp (goodLineCoefficientPolynomial n))
        (twoBoundaryCycle (goodLineCoefficientRep n) (prismStabilizerCochain data source cocycle)
          (goodLineLeviSection γ, goodLineRadicalInclusion (lowerLeviLatticeInput γ r)) -
        twoBoundaryCycle (goodLineCoefficientRep n) (prismStabilizerCochain data source cocycle)
          (goodLineRadicalInclusion r, goodLineLeviSection γ)) := by
  have three : 3 < n := by omega
  set ℓ := functional.comp (goodLineCoefficientPolynomial n) with hℓ
  have dualLevi (ℓ' : HomogeneousPoly n →ₗ[ℂ] ℂ) :
      ℓ' (prismDualVector data source cocycle (edgeLevi γ)) =
        prismEdgeIntegral data source cocycle ℓ' 1 (edgeLevi γ) :=
    functional_prismDualVector three data source cocycle (edgeLevi γ)
      (fun ℓ'' => prismEdgeAverage_one_integrable large data trivial source cocycle ℓ'' _
        (fun u => corner_levi u γ)) ℓ'
  have dualRadical (s : RadicalLattice) (ℓ' : HomogeneousPoly n →ₗ[ℂ] ℂ) :
      ℓ' (prismDualVector data source cocycle (edgeRadical s)) =
        prismEdgeIntegral data source cocycle ℓ' 1 (edgeRadical s) :=
    functional_prismDualVector three data source cocycle (edgeRadical s)
      (fun ℓ'' => prismEdgeAverage_one_integrable large data trivial source cocycle ℓ'' _
        (fun u => corner_radical u s)) ℓ'
  have leviEdge : prismEdgeIntegral data source cocycle functional (edgeLevi γ) (edgeRadical r * edgeLevi γ) =
      prismEdgeIntegral data source cocycle
        (functional.comp (realCoefficientComponent n data.chi (edgeLevi γ))) 1
        (edgeRadical (lowerLeviLatticeInput γ r)) := by
    rw [edgeRadical_mul_edgeLevi, ← prismEdgeIntegral_levi, mul_one]
  have radicalEdge : prismEdgeIntegral data source cocycle functional (edgeRadical r)
      (edgeRadical r * edgeLevi γ) =
      prismEdgeIntegral data source cocycle
        (functional.comp (realCoefficientComponent n data.chi (edgeRadical r))) 1 (edgeLevi γ) := by
    have := prismEdgeIntegral_radical data source cocycle functional r 1 (edgeLevi γ)
    rwa [mul_one] at this
  have termρ (g : flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
      (y : RealGL3) (hy : GeneralLinearGroup.map (algebraMap ℚ ℝ) g.val = y) (v : goodLineCoefficientRep n) :
      ℓ ((goodLineCoefficientRep n).ρ g v) =
        (functional.comp (realCoefficientComponent n data.chi y)) v := by
    rw [hℓ, ← hy, trivial]; rfl
  have termF (g : flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine)) :
      ℓ (prismStabilizerCochain data source cocycle g) =
        functional (prismDualVector data source cocycle (GeneralLinearGroup.map (algebraMap ℚ ℝ) g.val)) := rfl
  have termG (ℓ' : HomogeneousPoly n →ₗ[ℂ] ℂ)
      (g : flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine)) :
      ℓ' (prismStabilizerCochain data source cocycle g) =
        ℓ' (prismDualVector data source cocycle (GeneralLinearGroup.map (algebraMap ℚ ℝ) g.val)) := rfl
  rw [integral_prismCombination large data trivial source cocycle functional γ r, leviEdge, radicalEdge,
    map_sub, twoBoundaryCycle_apply, twoBoundaryCycle_apply, goodLineLevi_radical_commute,
    map_add, map_sub, map_add, map_sub,
    termρ (goodLineLeviSection γ) (edgeLevi γ) rfl, termρ (goodLineRadicalInclusion r) (edgeRadical r) rfl,
    termF, termF, termF, termG, termG]
  have eR (s : RadicalLattice) : GeneralLinearGroup.map (algebraMap ℚ ℝ) (goodLineRadicalInclusion s).val =
      edgeRadical s := rfl
  have eL : GeneralLinearGroup.map (algebraMap ℚ ℝ) (goodLineLeviSection γ).val = edgeLevi γ := rfl
  simp only [eR, eL, dualLevi, dualRadical]
  ring

/-- The mixed coordinate as the sum of its two lattice contributions. -/
theorem goodLineMixedCoordinate_eq_contributions (γ : GeneralLinearGroup (Fin 2) ℤ)
    (F : (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine) ×
      flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine)) → goodLineCoefficientRep n) :
    goodLineMixedCoordinate n γ F =
      lowerRadicalLatticeContribution n 0 (goodLineCoefficientPolynomial n
          (F (goodLineLeviSection γ, goodLineRadicalInclusion (lowerLeviLatticeInput γ radicalLatticeFirst)) -
            F (goodLineRadicalInclusion radicalLatticeFirst, goodLineLeviSection γ))) +
        lowerRadicalLatticeContribution n 1 (goodLineCoefficientPolynomial n
          (F (goodLineLeviSection γ, goodLineRadicalInclusion (lowerLeviLatticeInput γ radicalLatticeSecond)) -
            F (goodLineRadicalInclusion radicalLatticeSecond, goodLineLeviSection γ))) := by
  let pair : Fin 2 → HomogeneousPoly n := fun c => goodLineCoefficientPolynomial n
    (F (goodLineLeviSection γ, goodLineRadicalInclusion (lowerLeviLatticeInput γ (radicalLatticeGenerator c))) -
      F (goodLineRadicalInclusion (radicalLatticeGenerator c), goodLineLeviSection γ))
  calc goodLineMixedCoordinate n γ F =
      lowerRadicalCoordinate n (fun c => (lowerRadicalAverageEquiv n c).symm (pair c)) := rfl
    _ = lowerRadicalLatticeContribution n 0 (pair 0) + lowerRadicalLatticeContribution n 1 (pair 1) :=
      lowerRadicalCoordinate_averages n pair
    _ = _ := rfl

/-- **Reduction of the integrated good-line mixed finite family to the Iwasawa-projected part.**
At `s = -3/2` the integral of the mixed finite family equals the integral of the finite average of the
source on the Gram–Schmidt (plane-parabolic) simplices plus the good-line mixed coordinate of the
two-coboundary of the integrated prism cochain on the good-line stabilizer. -/
theorem integral_mixedFiniteFamily_iwasawa (large : 9 ≤ n) (data : InducingData n)
    (trivial : data.chi = trivialCharacter) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (γ : GeneralLinearGroup (Fin 2) ℤ)
    (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ) :
    ∫ u, mixedFiniteFamily data source cocycle γ functional cohomologicalPoint u
        ∂((volume : Measure ℝ).prod volume) =
      ∫ u, projectedAverage data source cocycle γ functional u ∂((volume : Measure ℝ).prod volume) +
        functional (goodLineMixedCoordinate n γ (fun pair =>
          twoBoundaryCycle (goodLineCoefficientRep n) (prismStabilizerCochain data source cocycle) pair)) := by
  have three : 3 < n := by omega
  have five : 5 ≤ n := by omega
  set ℓ0 := functional.comp (lowerRadicalLatticeContribution n 0)
  set ℓ1 := functional.comp (lowerRadicalLatticeContribution n 1)
  have hdec := mixedFiniteFamily_decomposition three data source cocycle γ functional
  have iM := mixedFiniteFamily_endpoint_integrable five data source cocycle γ functional
  have i0 := prismCombination_integrable five data trivial source cocycle ℓ0 γ radicalLatticeFirst
  have i1 := prismCombination_integrable five data trivial source cocycle ℓ1 γ radicalLatticeSecond
  have iP : Integrable (projectedAverage data source cocycle γ functional) ((volume : Measure ℝ).prod volume) := by
    refine ((iM.sub i0).sub i1).congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [Pi.sub_apply, hdec u]
    ring
  have split : (fun u => mixedFiniteFamily data source cocycle γ functional cohomologicalPoint u) =
      fun u => (projectedAverage data source cocycle γ functional u +
        prismCombination data source cocycle ℓ0 γ radicalLatticeFirst u) +
        prismCombination data source cocycle ℓ1 γ radicalLatticeSecond u := funext hdec
  have hsum1 := integral_add (iP.add i0) i1
  have hsum2 := integral_add iP i0
  simp only [Pi.add_apply] at hsum1 hsum2
  rw [split, hsum1, hsum2,
    integral_prismCombination_eq five data trivial source cocycle ℓ0 γ radicalLatticeFirst,
    integral_prismCombination_eq five data trivial source cocycle ℓ1 γ radicalLatticeSecond,
    goodLineMixedCoordinate_eq_contributions, map_add]
  simp only [ℓ0, ℓ1, LinearMap.comp_apply]
  ring

end TernaryPeriodPolynomials.AnalyticClasses
