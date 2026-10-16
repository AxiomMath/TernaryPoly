module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.FixedRealizationLimit
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Cusp.HilbertAction
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section


/-!
# Realization commutes with Bochner integrals of principal-level fixed smooth vectors

Original work by Claude Sonnet 5.5.

Let `v : X → data.cusp.smooth` be a family of smooth vectors, all fixed by the principal congruence
subgroup, whose Hilbert-space values are Bochner integrable over a finite measure space, whose
realizations are uniformly bounded and measurable in the family parameter, and let `W` be a smooth
vector with `W = ∫ v` in the Hilbert space. Then `realize W B = ∫ realize (v x) B` for every binary
adele `B` (`realize_integral_of_fixed`).

The proof is by the rotation modes. For a fixed level the isotypic components of the rotation group
are finite dimensional, so the `n`-th mode of the realization at `B` is a continuous linear
functional of the Hilbert vector (`exists_mode_functional`, by Hahn-Banach from
`FiniteRotationTypes.scalar_mode_continuous`). Hence the `n`-th Fourier coefficient of the orbit of the
realization of `W` is the integral of those of the `v x`. The orbit of `B ↦ ∫ realize (v x) B` is
continuous and its Fourier coefficients are the same integrals (Fubini), and
`RotationBanach.eq_zero_of_coefficients` identifies the two functions.
-/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationCircle (Parameter rotation)
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence

namespace HCReal

/-- The `index`-th rotation mode of the realization at `test` is a continuous linear functional of
the Hilbert vector, on the vectors fixed by the principal congruence subgroup. -/
theorem exists_mode_functional {degree : ℕ} (data : InducingData degree) (test : BinaryAdelicGL)
    (index : ℤ) :
    ∃ functional : data.cusp.H →L[ℂ] ℂ, ∀ vector : data.cusp.smooth,
      vector.val ∈ BinaryLevel.fixedSubspace data.cusp BinaryLevel.finiteCongruence →
        functional vector.val =
          data.cusp.realize (RotationFourier.smoothMode data.cusp index vector) test := by
  have _finiteTypes : FiniteDimensional ℂ
      (FiniteRotationTypes.fixedMode data.cusp BinaryLevel.finiteCongruence index) :=
    EndpointAdmissibility.all_finiteDimensional data index
  have continuity : Continuous (fun value : SobolevSeminorms.fixedSmooth data.cusp
      BinaryLevel.finiteCongruence => data.cusp.realize
        (RotationFourier.smoothMode data.cusp index value.val) test) :=
    FiniteRotationTypes.scalar_mode_continuous data.cusp BinaryLevel.finiteCongruence
      BinaryLevel.finiteCongruence_isOpen BinaryLevel.finiteCongruence_isCompact index
      (fun value => value) (continuous_subtype_val.comp continuous_subtype_val) test
  let evaluation : ↥(SobolevSeminorms.fixedSmooth data.cusp BinaryLevel.finiteCongruence) →L[ℂ] ℂ :=
    ⟨(LinearMap.proj test).comp (data.cusp.realize.comp
      ((RotationFourier.smoothMode data.cusp index).comp
        (SobolevSeminorms.fixedSmooth data.cusp BinaryLevel.finiteCongruence).subtype)),
      continuity⟩
  obtain ⟨first, firstAgreement, -⟩ := exists_extension_norm_eq
    (SobolevSeminorms.fixedSmooth data.cusp BinaryLevel.finiteCongruence) evaluation
  obtain ⟨second, secondAgreement, -⟩ := exists_extension_norm_eq data.cusp.smooth first
  refine ⟨second, fun vector fixed => ?_⟩
  have step := firstAgreement ⟨vector, fixed⟩
  rw [secondAgreement vector]
  exact step

/-- The Fourier coefficient of the integral over a finite measure space is the integral of the
Fourier coefficients (Fubini), for a uniformly bounded family of continuous functions on the circle
which is measurable in the family parameter. -/
theorem fourierCoeff_integral_swap {X : Type*} [MeasurableSpace X] (measure : Measure X)
    [IsFiniteMeasure measure] (function : X → Parameter → ℂ) (bound : ℝ)
    (bounded : ∀ point parameter, ‖function point parameter‖ ≤ bound)
    (measurableInPoint : ∀ parameter, Measurable (fun point => function point parameter))
    (continuousInParameter : ∀ point, Continuous (function point)) (index : ℤ) :
    fourierCoeff (fun parameter => ∫ point, function point parameter ∂measure) index =
      ∫ point, fourierCoeff (function point) index ∂measure := by
  have jointMeasurable : Measurable (Function.uncurry
      (fun (parameter : Parameter) (point : X) => function point parameter)) :=
    measurable_uncurry_of_continuous_of_measurable continuousInParameter measurableInPoint
  have weightMeasurable : Measurable (fun pair : Parameter × X =>
      (fourier (-index) : C(Parameter, ℂ)) pair.1) :=
    (fourier (-index) : C(Parameter, ℂ)).continuous.measurable.comp measurable_fst
  have productMeasurable : Measurable (Function.uncurry
      (fun (parameter : Parameter) (point : X) =>
        (fourier (-index) : C(Parameter, ℂ)) parameter • function point parameter)) :=
    weightMeasurable.smul jointMeasurable
  have productIntegrable : Integrable (Function.uncurry
      (fun (parameter : Parameter) (point : X) =>
        (fourier (-index) : C(Parameter, ℂ)) parameter • function point parameter))
      (AddCircle.haarAddCircle.prod measure) := by
    refine Integrable.mono' (integrable_const bound) productMeasurable.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun pair => ?_))
    change ‖(fourier (-index) : C(Parameter, ℂ)) pair.1 • function pair.2 pair.1‖ ≤ bound
    rw [norm_smul, RotationCircle.fourier_norm_one, one_mul]
    exact bounded _ _
  calc fourierCoeff (fun parameter => ∫ point, function point parameter ∂measure) index
      = ∫ parameter : Parameter, ∫ point, (fourier (-index) : C(Parameter, ℂ)) parameter •
          function point parameter ∂measure ∂AddCircle.haarAddCircle := by
        unfold fourierCoeff
        refine integral_congr_ae (Filter.Eventually.of_forall (fun parameter => ?_))
        exact (integral_smul _ _).symm
    _ = ∫ point, ∫ parameter : Parameter, (fourier (-index) : C(Parameter, ℂ)) parameter •
          function point parameter ∂AddCircle.haarAddCircle ∂measure :=
        integral_integral_swap productIntegrable
    _ = ∫ point, fourierCoeff (function point) index ∂measure := rfl

/-- The scalar function `B ↦ ∫ realize (v x) B` of a bounded measurable family of smooth vectors,
as an element of the space of bounded functions with continuous rotation orbits. -/
theorem exists_orbit_element {degree : ℕ} (data : InducingData degree) {X : Type*}
    [MeasurableSpace X] (measure : Measure X) [IsFiniteMeasure measure]
    (family : X → data.cusp.smooth) (bound : ℝ)
    (bounded : ∀ point test, ‖data.cusp.realize (family point) test‖ ≤ bound)
    (measurableFamily : ∀ test, Measurable (fun point => data.cusp.realize (family point) test)) :
    ∃ element : RotationBanach.orbitSpace, ∀ test : BinaryAdelicGL,
      element.val test = ∫ point, data.cusp.realize (family point) test ∂measure := by
  have scalarBounded : ∀ test : BinaryAdelicGL,
      ‖∫ point, data.cusp.realize (family point) test ∂measure‖ ≤ ∫ _ : X, bound ∂measure :=
    fun test => norm_integral_le_of_norm_le (integrable_const bound)
      (Filter.Eventually.of_forall (fun point => bounded point test))
  refine ⟨⟨⟨fun test => ∫ point, data.cusp.realize (family point) test ∂measure,
    memℓp_infty ⟨∫ _ : X, bound ∂measure, ?_⟩⟩, ?_⟩, fun test => rfl⟩
  · rintro _ ⟨test, rfl⟩
    exact scalarBounded test
  · intro test
    show Continuous (fun parameter : Parameter => ∫ point, data.cusp.realize (family point)
      (test * atInfinity (rotation parameter)) ∂measure)
    apply continuous_of_dominated (bound := fun _ => bound)
    · intro parameter
      exact (measurableFamily (test * atInfinity (rotation parameter))).aestronglyMeasurable
    · intro parameter
      exact Filter.Eventually.of_forall (fun point => bounded point _)
    · exact integrable_const bound
    · exact Filter.Eventually.of_forall (fun point =>
        RotationRealization.scalarOrbit_continuous data.cusp test (family point))

theorem realization_apply (data : CuspidalRepresentation) (vector : data.smooth)
    (test : BinaryAdelicGL) :
    (RotationBanach.realization data vector).val test = data.realize vector test := rfl

/-- The Hilbert-space integral of principal-level fixed vectors is principal-level fixed. -/
theorem integral_fixed {degree : ℕ} (data : InducingData degree) {X : Type*}
    [MeasurableSpace X] (measure : Measure X) (family : X → data.cusp.smooth)
    (fixed : ∀ point, ∀ unit : BinaryLevel.finiteCongruence,
      data.cusp.π (atFinite unit.val) (family point).val = (family point).val)
    (total : data.cusp.smooth) (totalEquation : total.val = ∫ point, (family point).val ∂measure)
    (unit : BinaryLevel.finiteCongruence) :
    data.cusp.π (atFinite unit.val) total.val = total.val := by
  have commute : (∫ point, data.cusp.π (atFinite unit.val) (family point).val ∂measure) =
      data.cusp.π (atFinite unit.val) (∫ point, (family point).val ∂measure) :=
    (CuspHilbertAction.isometry data.cusp (atFinite unit.val)).integral_comp_comm
      (fun point => (family point).val)
  rw [totalEquation, ← commute]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun point => fixed point unit))

/-- **Realization commutes with the Bochner integral.** A smooth vector which is the Hilbert-space
integral of a bounded measurable family of principal-level fixed smooth vectors over a finite
measure space realizes the integral of the realizations. -/
theorem realize_integral_of_fixed {degree : ℕ} (data : InducingData degree) {X : Type*}
    [MeasurableSpace X] (measure : Measure X) [IsFiniteMeasure measure]
    (family : X → data.cusp.smooth)
    (fixed : ∀ point, ∀ unit : BinaryLevel.finiteCongruence,
      data.cusp.π (atFinite unit.val) (family point).val = (family point).val)
    (hilbertIntegrable : Integrable (fun point => (family point).val) measure)
    (total : data.cusp.smooth)
    (totalEquation : total.val = ∫ point, (family point).val ∂measure)
    (bound : ℝ) (bounded : ∀ point test, ‖data.cusp.realize (family point) test‖ ≤ bound)
    (measurableFamily : ∀ test, Measurable (fun point => data.cusp.realize (family point) test))
    (binary : BinaryAdelicGL) :
    data.cusp.realize total binary = ∫ point, data.cusp.realize (family point) binary ∂measure := by
  obtain ⟨element, elementApply⟩ :=
    exists_orbit_element data measure family bound bounded measurableFamily
  have totalFixed : total.val ∈
      BinaryLevel.fixedSubspace data.cusp BinaryLevel.finiteCongruence :=
    fun unit => integral_fixed data measure family fixed total totalEquation unit
  have coefficients : ∀ (test : BinaryAdelicGL) (index : ℤ),
      RotationBanach.coefficient test index
        (RotationBanach.realization data.cusp total - element) = 0 := by
    intro test index
    rw [map_sub, sub_eq_zero]
    obtain ⟨functional, functionalAgreement⟩ := exists_mode_functional data test index
    have leftSide : RotationBanach.coefficient test index
        (RotationBanach.realization data.cusp total) =
        ∫ point, RotationBanach.coefficient test index
          (RotationBanach.realization data.cusp (family point)) ∂measure := by
      rw [RotationBanach.coefficient_realization, ← functionalAgreement total totalFixed,
        totalEquation, ← functional.integral_comp_comm hilbertIntegrable]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun point => ?_))
      show functional (family point).val = RotationBanach.coefficient test index
        (RotationBanach.realization data.cusp (family point))
      rw [RotationBanach.coefficient_realization]
      exact functionalAgreement (family point) (fun unit => fixed point unit)
    have rightSide : RotationBanach.coefficient test index element =
        ∫ point, RotationBanach.coefficient test index
          (RotationBanach.realization data.cusp (family point)) ∂measure := by
      have swap := fourierCoeff_integral_swap measure
        (fun point parameter => data.cusp.realize (family point)
          (test * atInfinity (rotation parameter)))
        bound (fun point parameter => bounded point _) (fun parameter => measurableFamily _)
        (fun point => RotationRealization.scalarOrbit_continuous data.cusp test (family point))
        index
      have orbitEquation : (fun parameter : Parameter =>
          element.val (test * atInfinity (rotation parameter))) =
          fun parameter => ∫ point, data.cusp.realize (family point)
            (test * atInfinity (rotation parameter)) ∂measure :=
        funext (fun parameter => elementApply _)
      rw [RotationBanach.coefficient_apply, orbitEquation, swap]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun point => ?_))
      show fourierCoeff (fun parameter => data.cusp.realize (family point)
        (test * atInfinity (rotation parameter))) index = RotationBanach.coefficient test index
          (RotationBanach.realization data.cusp (family point))
      rw [RotationBanach.coefficient_apply]
      simp only [realization_apply]
    rw [leftSide, rightSide]
  have equality : RotationBanach.realization data.cusp total = element :=
    sub_eq_zero.mp (RotationBanach.eq_zero_of_coefficients _ coefficients)
  have atBinary : data.cusp.realize total binary = element.val binary :=
    congrArg (fun value : RotationBanach.orbitSpace => value.val binary) equality
  rw [atBinary]
  exact elementApply binary

end HCReal

end TernaryPeriodPolynomials.EdgeConvergence
