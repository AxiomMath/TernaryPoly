module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Iwasawa.Reduction

@[expose] public section


/-!
# Transfer of an equivariant edge cochain to the good-line stabilizer

An earlier stage transferred one specific one-cochain (the Gram–Schmidt prism) along the standard good-line
argument and showed that its integrated mixed combination is a coboundary coordinate on the
good-line stabilizer. Here the same argument is carried out for an arbitrary edge cochain `E` of
real vertices with values in the cuspidal tensor values, assuming only

* finite level of its values,
* equivariance under the conjugated integral Levi elements `planeLevi B 1` (`E(L y₀, L y₁)` is the
  real-plane action of `L` on `E(y₀, y₁)`),
* absolute integrability of the transported edge averages along every pair of stabilizer elements.

Radical equivariance is automatic: the radical lattice acts on the good-line argument by
translation. The conclusion: the integral of the four-edge combination of one radical generator is
the mixed-coordinate entry of the two-coboundary of the dual stabilizer cochain.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

/-- An edge cochain of real vertices. -/
abbrev EdgeCochain (data : InducingData n) :=
  (Fin 2 → RealGL3) → cuspidalTensorValues data.cusp (HomogeneousPoly n)

/-- The edge moved by the good-line argument and transported back. -/
def edgeTransported (data : InducingData n) (E : EdgeCochain data) (u : ℝ × ℝ)
    (x y : RealGL3) : cuspidalTensorValues data.cusp (HomogeneousPoly n) :=
  cuspidalTensorMap data.cusp
    (realCoefficientComponent n data.chi (standardGoodLineRealArgument u)⁻¹)
    (E ![standardGoodLineRealArgument u * x, standardGoodLineRealArgument u * y])

/-- The finite good-line average of a scalar test of a transported edge. -/
def edgeAverage (data : InducingData n) (E : EdgeCochain data)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (x y : RealGL3) (u : ℝ × ℝ) : ℂ :=
  goodLineFiniteVectorIntegral n data.cusp cohomologicalPoint
    (cuspidalTensorFunctional data.cusp functional (edgeTransported data E u x y))

/-- The integrated edge scalar. -/
def edgeIntegral (data : InducingData n) (E : EdgeCochain data)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (x y : RealGL3) : ℂ :=
  ∫ u, edgeAverage data E functional x y u ∂((volume : Measure ℝ).prod volume)

/-- Finite level of an edge cochain. -/
def EdgeFinite (data : InducingData n) (E : EdgeCochain data) : Prop :=
  ∀ V, E V ∈ cuspidalTensorFiniteLevel data.cusp (HomogeneousPoly n)

/-- The basic good-line vertices `1` and the radical lattice elements. -/
def IsBasicVertex (x : RealGL3) : Prop := x = 1 ∨ ∃ s : RadicalLattice, x = edgeRadical s

/-- Equivariance under the conjugated integral Levi elements, on moved basic vertices. -/
def EdgeLeviEquivariant (data : InducingData n) (E : EdgeCochain data) : Prop :=
  ∀ (γ : GeneralLinearGroup (Fin 2) ℤ) (w : ℝ × ℝ) (x y : RealGL3),
    IsBasicVertex x → IsBasicVertex y →
    E ![goodLineConjugateRealLevi γ * (standardGoodLineRealArgument w * x),
        goodLineConjugateRealLevi γ * (standardGoodLineRealArgument w * y)] =
      cuspidalTensorMap data.cusp
        (realCoefficientComponent n data.chi (goodLineConjugateRealLevi γ))
        (cuspidalTensorTranslation data.cusp
          (atInfinity (realLeviMatrix (conjugateLeviInteger γ)))
          (E ![standardGoodLineRealArgument w * x, standardGoodLineRealArgument w * y]))

theorem edgeTransported_finiteLevel (data : InducingData n) (E : EdgeCochain data)
    (finite : EdgeFinite data E) (u : ℝ × ℝ) (x y : RealGL3) :
    edgeTransported data E u x y ∈ cuspidalTensorFiniteLevel data.cusp (HomogeneousPoly n) :=
  cuspidalTensorMap_finiteLevel _ _ _ (finite _)

theorem edgeTransported_spherical (data : InducingData n) (E : EdgeCochain data)
    (finite : EdgeFinite data E) (u : ℝ × ℝ) (x y : RealGL3)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    (cuspidalTensorFunctional data.cusp functional (edgeTransported data E u x y)).val ∈
      cuspSphericalValues data.cusp :=
  cuspidalTensorFunctional_spherical data.cusp functional _
    (edgeTransported_finiteLevel data E finite u x y)

theorem edge_pair (M x y : RealGL3) :
    (![M * x, M * y] : Fin 2 → RealGL3) = ![M * x, M * y] := rfl

/-- **Levi transport of an equivariant edge.** -/
theorem edgeTransported_levi (data : InducingData n) (E : EdgeCochain data)
    (levi : EdgeLeviEquivariant data E) (u : ℝ × ℝ) (γ : GeneralLinearGroup (Fin 2) ℤ)
    (x y : RealGL3) (hx : IsBasicVertex x) (hy : IsBasicVertex y) :
    edgeTransported data E u (edgeLevi γ * x) (edgeLevi γ * y) =
      cuspidalTensorMap data.cusp (realCoefficientComponent n data.chi (edgeLevi γ))
        (cuspidalTensorTranslation data.cusp (atInfinity (realLeviMatrix (conjugateLeviInteger γ)))
          (edgeTransported data E (goodLineLeviRealInput γ u) x y)) := by
  set M := standardGoodLineRealArgument u with hM
  set M' := standardGoodLineRealArgument (goodLineLeviRealInput γ u) with hM'
  set L := goodLineConjugateRealLevi γ with hL
  have transport : M * edgeLevi γ = L * M' := standardGoodLineRealArgument_levi u γ
  have hinv : M⁻¹ * L = edgeLevi γ * M'⁻¹ := by
    have : L = M * edgeLevi γ * M'⁻¹ := by rw [transport, mul_inv_cancel_right]
    rw [this]
    simp only [mul_assoc, inv_mul_cancel_left]
  apply Subtype.ext
  funext A
  unfold edgeTransported
  rw [cuspidalTensorMap_val_apply, ← hM, ← mul_assoc, ← mul_assoc, transport, mul_assoc, mul_assoc,
    levi γ _ x y hx hy]
  change realCoefficientComponent n data.chi M⁻¹
      (realCoefficientComponent n data.chi L
        ((E ![M' * x, M' * y]).val (A * atInfinity (realLeviMatrix (conjugateLeviInteger γ))))) =
    realCoefficientComponent n data.chi (edgeLevi γ)
      (realCoefficientComponent n data.chi M'⁻¹
        ((E ![M' * x, M' * y]).val (A * atInfinity (realLeviMatrix (conjugateLeviInteger γ)))))
  rw [← Module.End.mul_apply, ← map_mul, hinv, map_mul, Module.End.mul_apply]

/-- **Radical transport of an edge.** -/
theorem edgeTransported_radical (data : InducingData n) (E : EdgeCochain data) (u : ℝ × ℝ)
    (r : RadicalLattice) (x y : RealGL3) :
    edgeTransported data E u (edgeRadical r * x) (edgeRadical r * y) =
      cuspidalTensorMap data.cusp (realCoefficientComponent n data.chi (edgeRadical r))
        (edgeTransported data E (goodLineRadicalRealShift r u) x y) := by
  have transport := standardGoodLineRealArgument_radical u r
  have hinv : (standardGoodLineRealArgument u)⁻¹ =
      edgeRadical r * (standardGoodLineRealArgument (goodLineRadicalRealShift r u))⁻¹ := by
    rw [← transport, _root_.mul_inv_rev, mul_inv_cancel_left]
  apply Subtype.ext
  funext A
  unfold edgeTransported
  rw [cuspidalTensorMap_val_apply, cuspidalTensorMap_val_apply, cuspidalTensorMap_val_apply,
    ← mul_assoc, ← mul_assoc, transport, hinv, map_mul, Module.End.mul_apply]

theorem edgeAverage_levi (data : InducingData n) (E : EdgeCochain data)
    (finite : EdgeFinite data E)
    (levi : EdgeLeviEquivariant data E) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (γ : GeneralLinearGroup (Fin 2) ℤ) (x y : RealGL3) (hx : IsBasicVertex x)
    (hy : IsBasicVertex y) (u : ℝ × ℝ) :
    edgeAverage data E functional (edgeLevi γ * x) (edgeLevi γ * y) u =
      edgeAverage data E (functional.comp (realCoefficientComponent n data.chi (edgeLevi γ))) x y
        (goodLineLeviRealInput γ u) := by
  unfold edgeAverage
  rw [edgeTransported_levi data E levi u γ x y hx hy, cuspidalTensorFunctional_map,
    cuspidalTensorFunctional_translation]
  exact goodLineFiniteVectorIntegral_realTranslate n data.cusp cohomologicalPoint
    (conjugateLeviInteger γ) _ (edgeTransported_spherical data E finite _ x y _)

theorem edgeAverage_radical (data : InducingData n) (E : EdgeCochain data)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (r : RadicalLattice) (x y : RealGL3)
    (u : ℝ × ℝ) :
    edgeAverage data E functional (edgeRadical r * x) (edgeRadical r * y) u =
      edgeAverage data E (functional.comp (realCoefficientComponent n data.chi (edgeRadical r))) x y
        (goodLineRadicalRealShift r u) := by
  unfold edgeAverage
  rw [edgeTransported_radical, cuspidalTensorFunctional_map]

theorem edgeIntegral_levi (data : InducingData n) (E : EdgeCochain data)
    (finite : EdgeFinite data E)
    (levi : EdgeLeviEquivariant data E) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (γ : GeneralLinearGroup (Fin 2) ℤ) (x y : RealGL3) (hx : IsBasicVertex x)
    (hy : IsBasicVertex y) :
    edgeIntegral data E functional (edgeLevi γ * x) (edgeLevi γ * y) =
      edgeIntegral data E (functional.comp (realCoefficientComponent n data.chi (edgeLevi γ)))
        x y := by
  unfold edgeIntegral
  simp_rw [edgeAverage_levi data E finite levi functional γ x y hx hy]
  exact integral_goodLineLeviRealInput (fun u => edgeAverage data E _ x y u) γ

theorem edgeIntegral_radical (data : InducingData n) (E : EdgeCochain data)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (r : RadicalLattice) (x y : RealGL3) :
    edgeIntegral data E functional (edgeRadical r * x) (edgeRadical r * y) =
      edgeIntegral data E (functional.comp (realCoefficientComponent n data.chi (edgeRadical r)))
        x y := by
  unfold edgeIntegral
  simp_rw [edgeAverage_radical, goodLineRadicalRealShift_eq_add]
  exact integral_add_right_eq_self (fun u => edgeAverage data E _ x y u) _

theorem edgeAverage_sum (large : 3 < n) (data : InducingData n) (E : EdgeCochain data)
    (finite : EdgeFinite data E) {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (functionals : ι → HomogeneousPoly n →ₗ[ℂ] ℂ) (x y : RealGL3) (u : ℝ × ℝ) :
    edgeAverage data E (∑ i ∈ s, c i • functionals i) x y u =
      ∑ i ∈ s, c i * edgeAverage data E (functionals i) x y u := by
  unfold edgeAverage
  apply finiteAverage_combination large data.cusp _ s c
    (fun i => cuspidalTensorFunctional data.cusp (functionals i) (edgeTransported data E u x y))
    (fun i => edgeTransported_spherical data E finite u x y _)
  intro A
  simp only [cuspidalTensorFunctional_realize]
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, smul_eq_mul]

theorem edgeIntegral_sum (large : 3 < n) (data : InducingData n) (E : EdgeCochain data)
    (finite : EdgeFinite data E) {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (functionals : ι → HomogeneousPoly n →ₗ[ℂ] ℂ) (x y : RealGL3)
    (integrable : ∀ i ∈ s, Integrable (edgeAverage data E (functionals i) x y)
      ((volume : Measure ℝ).prod volume)) :
    edgeIntegral data E (∑ i ∈ s, c i • functionals i) x y =
      ∑ i ∈ s, c i * edgeIntegral data E (functionals i) x y := by
  unfold edgeIntegral
  simp_rw [edgeAverage_sum large data E finite s c functionals x y]
  rw [integral_finsetSum _ (fun i hi => (integrable i hi).const_mul (c i))]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_const_mul _ _

/-- The coefficient vector dual to the integrated edge scalars at `(1, y)`. -/
def edgeDualVector (data : InducingData n) (E : EdgeCochain data) (y : RealGL3) :
    HomogeneousPoly n :=
  let _ : FiniteDimensional ℂ (HomogeneousPoly n) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 3) ℂ n)
  let basis := Module.finBasis ℂ (HomogeneousPoly n)
  ∑ i, edgeIntegral data E (basis.coord i) 1 y • basis i

theorem functional_edgeDualVector (large : 3 < n) (data : InducingData n) (E : EdgeCochain data)
    (finite : EdgeFinite data E) (y : RealGL3)
    (integrable : ∀ functional : HomogeneousPoly n →ₗ[ℂ] ℂ,
      Integrable (edgeAverage data E functional 1 y) ((volume : Measure ℝ).prod volume))
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    functional (edgeDualVector data E y) = edgeIntegral data E functional 1 y := by
  let _ : FiniteDimensional ℂ (HomogeneousPoly n) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 3) ℂ n)
  let basis := Module.finBasis ℂ (HomogeneousPoly n)
  have decomposition : functional = ∑ i, functional (basis i) • basis.coord i := by
    apply basis.ext
    intro j
    simp
  change functional (∑ i, edgeIntegral data E (basis.coord i) 1 y • basis i) = _
  conv_rhs => rw [decomposition]
  rw [edgeIntegral_sum large data E finite Finset.univ _ _ 1 y (fun i _ => integrable _), map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, smul_eq_mul, mul_comm]

/-- The integrated edge cochain on the good-line stabilizer. -/
def edgeStabilizerCochain (data : InducingData n) (E : EdgeCochain data) :
    flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine) → goodLineCoefficientRep n :=
  fun g => edgeDualVector data E (GeneralLinearGroup.map (algebraMap ℚ ℝ) g.val)

/-- The four transported edges of one radical generator. -/
def edgeCombination (data : InducingData n) (E : EdgeCochain data)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (γ : GeneralLinearGroup (Fin 2) ℤ) (r : RadicalLattice)
    (u : ℝ × ℝ) : ℂ :=
  edgeAverage data E functional (edgeLevi γ) (edgeRadical r * edgeLevi γ) u -
    edgeAverage data E functional (edgeRadical r) (edgeRadical r * edgeLevi γ) u +
    edgeAverage data E functional 1 (edgeLevi γ) u -
    edgeAverage data E functional 1 (edgeRadical r) u

/-- Integrability of the transported edges of the four-edge combinations. -/
def EdgeIntegrable (data : InducingData n) (E : EdgeCochain data) : Prop :=
  ∀ (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (γ : GeneralLinearGroup (Fin 2) ℤ)
    (r : RadicalLattice),
    Integrable (edgeAverage data E functional (edgeLevi γ) (edgeRadical r * edgeLevi γ))
        ((volume : Measure ℝ).prod volume) ∧
      Integrable (edgeAverage data E functional (edgeRadical r) (edgeRadical r * edgeLevi γ))
        ((volume : Measure ℝ).prod volume) ∧
      Integrable (edgeAverage data E functional 1 (edgeLevi γ))
        ((volume : Measure ℝ).prod volume) ∧
      Integrable (edgeAverage data E functional 1 (edgeRadical r))
        ((volume : Measure ℝ).prod volume)

theorem edgeLevi_eq (γ : GeneralLinearGroup (Fin 2) ℤ) :
    GeneralLinearGroup.map (algebraMap ℚ ℝ) (goodLineLeviSection γ).val = edgeLevi γ := rfl

theorem edgeRadical_eq (r : RadicalLattice) :
    GeneralLinearGroup.map (algebraMap ℚ ℝ) (goodLineRadicalInclusion r).val = edgeRadical r := rfl

theorem edgeRadicalLevi_eq (γ : GeneralLinearGroup (Fin 2) ℤ) (r : RadicalLattice) :
    GeneralLinearGroup.map (algebraMap ℚ ℝ)
        (goodLineRadicalInclusion r * goodLineLeviSection γ).val = edgeRadical r * edgeLevi γ := by
  rw [Subgroup.coe_mul, map_mul]
  rfl

theorem edgeOne_eq :
    GeneralLinearGroup.map (algebraMap ℚ ℝ)
      (1 : flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine)).val = 1 := by
  rw [OneMemClass.coe_one, map_one]

/-- **The integrated four-edge combination is a coboundary coordinate.** -/
theorem integral_edgeCombination_eq (large : 5 ≤ n) (data : InducingData n)
    (trivial : data.chi = trivialCharacter) (E : EdgeCochain data) (finite : EdgeFinite data E)
    (levi : EdgeLeviEquivariant data E) (integrable : EdgeIntegrable data E)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (γ : GeneralLinearGroup (Fin 2) ℤ)
    (r : RadicalLattice) :
    ∫ u, edgeCombination data E functional γ r u ∂((volume : Measure ℝ).prod volume) =
      (functional.comp (goodLineCoefficientPolynomial n))
        (twoBoundaryCycle (goodLineCoefficientRep n) (edgeStabilizerCochain data E)
          (goodLineLeviSection γ, goodLineRadicalInclusion (lowerLeviLatticeInput γ r)) -
        twoBoundaryCycle (goodLineCoefficientRep n) (edgeStabilizerCochain data E)
          (goodLineRadicalInclusion r, goodLineLeviSection γ)) := by
  have three : 3 < n := by omega
  obtain ⟨i1, i2, i3, i4⟩ := integrable functional γ r
  have split : ∫ u, edgeCombination data E functional γ r u ∂((volume : Measure ℝ).prod volume) =
      edgeIntegral data E functional (edgeLevi γ) (edgeRadical r * edgeLevi γ) -
        edgeIntegral data E functional (edgeRadical r) (edgeRadical r * edgeLevi γ) +
        edgeIntegral data E functional 1 (edgeLevi γ) -
        edgeIntegral data E functional 1 (edgeRadical r) := by
    unfold edgeCombination edgeIntegral
    have h1 := integral_sub ((i1.sub i2).add i3) i4
    have h2 := integral_add (i1.sub i2) i3
    have h3 := integral_sub i1 i2
    simp only [Pi.sub_apply, Pi.add_apply] at h1 h2 h3
    rw [h1, h2, h3]
  set ℓ := functional.comp (goodLineCoefficientPolynomial n) with hℓ
  have dualLevi (ℓ' : HomogeneousPoly n →ₗ[ℂ] ℂ) :
      ℓ' (edgeDualVector data E (edgeLevi γ)) = edgeIntegral data E ℓ' 1 (edgeLevi γ) :=
    functional_edgeDualVector three data E finite (edgeLevi γ)
      (fun ℓ'' => (integrable ℓ'' γ r).2.2.1) ℓ'
  have dualRadical (s : RadicalLattice) (ℓ' : HomogeneousPoly n →ₗ[ℂ] ℂ) :
      ℓ' (edgeDualVector data E (edgeRadical s)) = edgeIntegral data E ℓ' 1 (edgeRadical s) :=
    functional_edgeDualVector three data E finite (edgeRadical s)
      (fun ℓ'' => (integrable ℓ'' γ s).2.2.2) ℓ'
  have leviEdge : edgeIntegral data E functional (edgeLevi γ) (edgeRadical r * edgeLevi γ) =
      edgeIntegral data E (functional.comp (realCoefficientComponent n data.chi (edgeLevi γ))) 1
        (edgeRadical (lowerLeviLatticeInput γ r)) := by
    rw [edgeRadical_mul_edgeLevi, ← edgeIntegral_levi data E finite levi _ γ 1 _ (Or.inl rfl)
      (Or.inr ⟨_, rfl⟩), mul_one]
  have radicalEdge : edgeIntegral data E functional (edgeRadical r) (edgeRadical r * edgeLevi γ) =
      edgeIntegral data E (functional.comp (realCoefficientComponent n data.chi (edgeRadical r))) 1
        (edgeLevi γ) := by
    have := edgeIntegral_radical data E functional r 1 (edgeLevi γ)
    rwa [mul_one] at this
  have termρ (g : flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
      (y : RealGL3) (hy : GeneralLinearGroup.map (algebraMap ℚ ℝ) g.val = y)
      (v : goodLineCoefficientRep n) :
      ℓ ((goodLineCoefficientRep n).ρ g v) =
        (functional.comp (realCoefficientComponent n data.chi y)) v := by
    rw [hℓ, ← hy, trivial]; rfl
  have termF (g : flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine)) :
      ℓ (edgeStabilizerCochain data E g) =
        functional (edgeDualVector data E (GeneralLinearGroup.map (algebraMap ℚ ℝ) g.val)) := rfl
  have termG (ℓ' : HomogeneousPoly n →ₗ[ℂ] ℂ)
      (g : flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine)) :
      ℓ' (edgeStabilizerCochain data E g) =
        ℓ' (edgeDualVector data E (GeneralLinearGroup.map (algebraMap ℚ ℝ) g.val)) := rfl
  rw [split, leviEdge, radicalEdge, map_sub, twoBoundaryCycle_apply, twoBoundaryCycle_apply,
    goodLineLevi_radical_commute, map_add, map_sub, map_add, map_sub,
    termρ (goodLineLeviSection γ) (edgeLevi γ) rfl,
    termρ (goodLineRadicalInclusion r) (edgeRadical r) rfl,
    termF, termF, termF, termG, termG]
  simp only [edgeRadical_eq, edgeLevi_eq, dualLevi, dualRadical]
  ring

end TernaryPeriodPolynomials.AnalyticClasses
