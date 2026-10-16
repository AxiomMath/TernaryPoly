module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.HolomorphicStandardValue
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.PolynomialNaturality
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.PolynomialFamilies
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Standard.Relation
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.RealTranslations
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Endpoint.SourceStandard

@[expose] public section


/-!
# The standard operator at the edge `n = 3`: interface and totality of `Related`

For `4 ≤ n`, Sol's `EndpointStandardValue.sectionStandard` is the standard integral itself; it needs
`4 ≤ n` only to know that `cohomologicalPoint = -3/2` lies in the half plane of absolute Hilbert
convergence `-n/2 < Re s`. That hypothesis is used in exactly three places downstream:

* `EndpointStandardInduction.integral_induced` : the value is an induced LINE section;
* `EndpointStandardValue.sectionStandard_right_real` : right real equivariance (an integral
  identity `∫ f(w⁻¹ u g h) = (∫ f(w⁻¹ u ·))(g h)`);
* `EndpointSourceStandard.sectionFamily_hasSmoothCuspLift` : joint smoothness of vertex families in
  the Hilbert globalization of the line value.

For every `n` the holomorphic-continuation operator
`HolomorphicStandardValue.sectionStandard data holomorphic` exists, is linear, and (by
`StandardValue.standardValue_realizes`) realizes the standard continuation of the unique flat
extension of each section. So the only missing ingredients for `n = 3` are those three properties of
that operator, collected in `EdgeStandardOperator`; `related_total_of_edgeStandardOperator` then
shows `StandardRelation.Related data c line` for every plane source cocycle `c`, by copying
`EndpointPolynomialStandard` / `EndpointSourceStandard` with the operator in place of
`EndpointStandardValue.sectionStandard data large holomorphic`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous Matrix
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence.EdgeStandard

/-- The holomorphic-continuation standard operator on plane sections at the cohomological point. -/
abbrev edgeStd {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) :
    SectionSpace.inducedSections data .plane cohomologicalPoint →ₗ[ℂ]
      StandardValue.radicalLevelFunctions :=
  HolomorphicStandardValue.sectionStandard data holomorphic

theorem atInfinity_one : atInfinity (1 : RealGL3) = 1 := by
  apply InducedContinuity.adelic_ext
  · simp only [InducedContinuity.realGroup_atInfinity, map_one]
  · simp only [InducedContinuity.finiteGroup_atInfinity, map_one]

/-- The three properties of `HolomorphicStandardValue.sectionStandard` that Sol proves from the
absolute-convergence half plane (`4 ≤ n`), and that are all `related_total` needs beyond it
(the remaining conditions in `IsInduced data .line s₀` are derived, see `EdgeStandardOperator.induced`):

* `smooth_real` : for each plane section `f` and adelic `g`, `x ↦ (S f)(g x)` is smooth on
  `GL₃(ℝ)`;
* `right_real` : `S (R(h) f) = R(h) (S f)` for every real `h`, with `R(h) f = f(· h)`;
* `smooth_lift` : for every smooth-cusp-lift family `x ↦ f_x` of plane sections (any arity, in
  particular `0` for a single section and `3` for the vertices of a source cocycle),
  `x ↦ S f_x` is a smooth-cusp-lift family of line sections. -/
structure EdgeStandardOperator {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) : Prop where
  smooth_real : ∀ (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
      (argument : AdelicGL),
    Smooth (fun x : Fin 1 → RealGL3 =>
      (edgeStd data holomorphic sectionValue).val (argument * atInfinity (x 0)))
  right_real : ∀ (real : RealGL3)
      (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint),
    (edgeStd data holomorphic
        (RealTranslations.sectionRightReal data .plane cohomologicalPoint real sectionValue)).val =
      fun argument => (edgeStd data holomorphic sectionValue).val (argument * atInfinity real)
  smooth_lift : ∀ {arity : ℕ} (function : (Fin arity → RealGL3) → AdelicGL → ℂ)
      (induced : ∀ vertices, IsInduced data .plane cohomologicalPoint (function vertices)),
    HasSmoothCuspLift data .plane cohomologicalPoint function →
    HasSmoothCuspLift data .line cohomologicalPoint (fun vertices =>
      (edgeStd data holomorphic ⟨function vertices, induced vertices⟩).val)

namespace EdgeStandardOperator

variable {degree : ℕ} {data : InducingData degree} {holomorphic : PlaneEisensteinHolomorphic data}

/-- The value of an induced plane section is an induced line section at the cohomological point.
Radical and finite-level invariance and the `GL₁` equivariance hold for every `n`
(`StandardValue.standardValue_invariant`, `HolomorphicStandardValue.flatStandard_rankOne`); the
cusp-constituent condition and the lift for `k = 0` come from `smooth_lift` for the constant family. -/
theorem induced (edge : EdgeStandardOperator data holomorphic)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint) :
    IsInduced data .line cohomologicalPoint (edgeStd data holomorphic sectionValue).val := by
  obtain ⟨radicalInvariant, finiteInvariant⟩ := (edgeStd data holomorphic sectionValue).property
  have plane : IsInduced data .plane cohomologicalPoint sectionValue.val := sectionValue.property
  have lift : HasSmoothCuspLift data .line cohomologicalPoint
      (fun (_ : Fin 0 → RealGL3) => (edgeStd data holomorphic sectionValue).val) :=
    edge.smooth_lift (arity := 0) (fun _ => sectionValue.val) (fun _ => plane) plane.2.2.1
  refine ⟨edge.smooth_real sectionValue, finiteInvariant, lift, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro first second argument
    exact radicalInvariant first second argument
  · intro unit argument
    have rankOne := HolomorphicStandardValue.flatStandard_rankOne data holomorphic
      (SectionSpace.linearFlatExtension data holomorphic sectionValue) unit argument
    have exponent : 2 * inductionExponent .line cohomologicalPoint = 2 := by
      norm_num [inductionExponent, cohomologicalPoint]
    rw [exponent]
    exact rankOne
  · intro argument
    obtain ⟨vectors, _, realizes⟩ := lift argument
    refine LinearMap.mem_range.mpr ⟨vectors (fun _ => 1), ?_⟩
    funext binary
    have key := realizes (fun _ => (1 : RealGL3)) binary
    rw [key, atInfinity_one, mul_one]
    rfl

/-- The section-level standard operator `S₃ : inducedSections plane s₀ →ₗ inducedSections line s₀`. -/
def operator (edge : EdgeStandardOperator data holomorphic) :
    SectionSpace.inducedSections data .plane cohomologicalPoint →ₗ[ℂ]
      SectionSpace.inducedSections data .line cohomologicalPoint :=
  (((Submodule.subtype StandardValue.radicalLevelFunctions).comp (edgeStd data holomorphic)).codRestrict
    (SectionSpace.inducedSections data .line cohomologicalPoint) edge.induced)

theorem operator_apply (edge : EdgeStandardOperator data holomorphic)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint) :
    (edge.operator sectionValue).val = (edgeStd data holomorphic sectionValue).val := rfl

end EdgeStandardOperator

/-- For `4 ≤ n` Sol's integral operator satisfies the interface (so the interface is not vacuous and
`related_total_of_edgeStandardOperator` recovers `EndpointSourceStandard.related_total`). -/
theorem edgeStandardOperator_of_large {degree : ℕ} (data : InducingData degree)
    (large : 4 ≤ degree) (holomorphic : PlaneEisensteinHolomorphic data) :
    EdgeStandardOperator data holomorphic where
  smooth_real sectionValue argument := by
    have induced : IsInduced data .line cohomologicalPoint
        (EndpointStandardValue.sectionStandard data large holomorphic sectionValue).val :=
      (EndpointStandardValue.sectionStandard data large holomorphic sectionValue).property
    exact induced.1 argument
  right_real real sectionValue := by
    have equality := EndpointStandardValue.sectionStandard_right_real data large holomorphic
      sectionValue real
    exact congrArg Subtype.val equality
  smooth_lift {arity} function induced lift :=
    EndpointSourceStandard.sectionFamily_hasSmoothCuspLift data large holomorphic function
      induced lift

/-! ### Polynomial-valued sections -/

variable {degree : ℕ} (data : InducingData degree)
  (holomorphic : PlaneEisensteinHolomorphic data)

/-- Coefficientwise standard value on polynomial-valued plane sections. -/
def edgePolynomialValue :
    PolynomialEisenstein.polynomialSections data →ₗ[ℂ] (AdelicGL → HomogeneousPoly degree) where
  toFun sectionValue argument := FlatExtensions.assemblePolynomial degree
    (fun monomial =>
      (edgeStd data holomorphic
        (PolynomialEisenstein.coefficientSection data monomial sectionValue)).val argument)
  map_add' first second := by
    funext argument
    apply Subtype.ext
    apply MvPolynomial.ext
    intro monomial
    simp only [Submodule.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      FlatExtensions.assemblePolynomial_coeff, map_add, Submodule.coe_add, Pi.add_apply]
    split_ifs <;> simp
  map_smul' scalar sectionValue := by
    funext argument
    apply Subtype.ext
    apply MvPolynomial.ext
    intro monomial
    simp only [Submodule.coe_smul, MvPolynomial.coeff_smul,
      FlatExtensions.assemblePolynomial_coeff, map_smul, Submodule.coe_smul,
      Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp

theorem edgePolynomialValue_coeff
    (sectionValue : PolynomialEisenstein.polynomialSections data)
    (monomial : Fin 3 →₀ ℕ) (argument : AdelicGL) :
    (edgePolynomialValue data holomorphic sectionValue argument).val.coeff monomial =
      (edgeStd data holomorphic
        (PolynomialEisenstein.coefficientSection data monomial sectionValue)).val argument := by
  change (FlatExtensions.assemblePolynomial degree _).val.coeff monomial = _
  rw [FlatExtensions.assemblePolynomial_coeff]
  split_ifs with homogeneous
  · rfl
  · have zeroCoefficient :
        PolynomialEisenstein.coefficientSection data monomial sectionValue = 0 := by
      apply Subtype.ext
      funext argument
      exact (sectionValue.val argument).property.coeff_eq_zero homogeneous
    rw [zeroCoefficient, map_zero]
    rfl

theorem edgePolynomialValue_tensor (polynomial : HomogeneousPoly degree)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (argument : AdelicGL) :
    edgePolynomialValue data holomorphic
        (PolynomialNaturality.tensorSection data polynomial sectionValue) argument =
      (edgeStd data holomorphic sectionValue).val argument • polynomial := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  rw [edgePolynomialValue_coeff, PolynomialNaturality.coefficient_tensor, map_smul]
  simp [mul_comm]

theorem edgePolynomialValue_sum_basis
    (sectionValue : PolynomialEisenstein.polynomialSections data) (argument : AdelicGL) :
    (∑ monomial ∈ FlatExtensions.degreeMonomials degree,
      (edgeStd data holomorphic
        (PolynomialEisenstein.coefficientSection data monomial sectionValue)).val argument •
          PolynomialNaturality.basisVector degree monomial) =
        edgePolynomialValue data holomorphic sectionValue argument := by
  have equality := congrArg (fun value =>
    edgePolynomialValue data holomorphic value argument)
    (PolynomialNaturality.section_sum_basis data sectionValue)
  simpa only [map_sum, Finset.sum_apply, edgePolynomialValue_tensor] using equality

theorem edgePolynomialValue_coefficientMap
    (operator : Module.End ℂ (HomogeneousPoly degree))
    (sectionValue : PolynomialEisenstein.polynomialSections data) (argument : AdelicGL) :
    edgePolynomialValue data holomorphic
        (PolynomialNaturality.coefficientMap data operator sectionValue) argument =
      operator (edgePolynomialValue data holomorphic sectionValue argument) := by
  have equality := congrArg operator
    (edgePolynomialValue_sum_basis data holomorphic sectionValue argument)
  simpa only [PolynomialNaturality.coefficientMap, map_sum, Finset.sum_apply,
    edgePolynomialValue_tensor, map_smul] using equality

theorem edgePolynomialValue_source_closed
    (source : SourceSpace.sourceCocycles data .plane)
    (vertices : Fin 4 → RealGL3) (argument : AdelicGL) :
    edgePolynomialValue data holomorphic
        (PolynomialEisenstein.sourceSection data source ![vertices 1, vertices 2, vertices 3])
          argument -
      edgePolynomialValue data holomorphic
        (PolynomialEisenstein.sourceSection data source ![vertices 0, vertices 2, vertices 3])
          argument +
      edgePolynomialValue data holomorphic
        (PolynomialEisenstein.sourceSection data source ![vertices 0, vertices 1, vertices 3])
          argument -
      edgePolynomialValue data holomorphic
        (PolynomialEisenstein.sourceSection data source ![vertices 0, vertices 1, vertices 2])
          argument = 0 := by
  have closed := congrArg (edgePolynomialValue data holomorphic)
    (PolynomialEisenstein.sourceSection_closed data source vertices)
  change edgePolynomialValue data holomorphic
      (PolynomialEisenstein.sourceSection data source ![vertices 1, vertices 2, vertices 3] -
          PolynomialEisenstein.sourceSection data source ![vertices 0, vertices 2, vertices 3] +
        PolynomialEisenstein.sourceSection data source ![vertices 0, vertices 1, vertices 3] -
          PolynomialEisenstein.sourceSection data source ![vertices 0, vertices 1, vertices 2]) =
      edgePolynomialValue data holomorphic 0 at closed
  rw [LinearMap.map_sub (edgePolynomialValue data holomorphic)
      (PolynomialEisenstein.sourceSection data source ![vertices 1, vertices 2, vertices 3] -
          PolynomialEisenstein.sourceSection data source ![vertices 0, vertices 2, vertices 3] +
        PolynomialEisenstein.sourceSection data source ![vertices 0, vertices 1, vertices 3])
      (PolynomialEisenstein.sourceSection data source ![vertices 0, vertices 1, vertices 2]),
    LinearMap.map_add (edgePolynomialValue data holomorphic)
      (PolynomialEisenstein.sourceSection data source ![vertices 1, vertices 2, vertices 3] -
        PolynomialEisenstein.sourceSection data source ![vertices 0, vertices 2, vertices 3])
      (PolynomialEisenstein.sourceSection data source ![vertices 0, vertices 1, vertices 3]),
    LinearMap.map_sub (edgePolynomialValue data holomorphic)
      (PolynomialEisenstein.sourceSection data source ![vertices 1, vertices 2, vertices 3])
      (PolynomialEisenstein.sourceSection data source ![vertices 0, vertices 2, vertices 3]),
    LinearMap.map_zero (edgePolynomialValue data holomorphic)] at closed
  simpa only [map_sub, map_add, map_zero, Pi.sub_apply, Pi.add_apply, Pi.zero_apply] using
    congrFun closed argument

theorem edgePolynomialValue_induced (edge : EdgeStandardOperator data holomorphic)
    (sectionValue : PolynomialEisenstein.polynomialSections data) (monomial : Fin 3 →₀ ℕ) :
    IsInduced data .line cohomologicalPoint (fun argument =>
      (edgePolynomialValue data holomorphic sectionValue argument).val.coeff monomial) := by
  simp only [edgePolynomialValue_coeff]
  exact edge.induced (PolynomialEisenstein.coefficientSection data monomial sectionValue)

theorem edgePolynomialValue_right_real (edge : EdgeStandardOperator data holomorphic)
    (sectionValue : PolynomialEisenstein.polynomialSections data)
    (real : RealGL3) (argument : AdelicGL) :
    edgePolynomialValue data holomorphic (PolynomialNaturality.rightReal data real sectionValue)
        argument =
      edgePolynomialValue data holomorphic sectionValue (argument * atInfinity real) := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  rw [edgePolynomialValue_coeff, edgePolynomialValue_coeff,
    PolynomialNaturality.coefficient_rightReal]
  exact congrFun (edge.right_real real
    (PolynomialEisenstein.coefficientSection data monomial sectionValue)) argument

/-- The vertex-indexed standard values of a plane source cocycle. -/
def edgeSourceValue (source : SourceSpace.sourceCocycles data .plane) :
    (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree :=
  fun vertices => edgePolynomialValue data holomorphic
    (PolynomialEisenstein.sourceSection data source vertices)

theorem edgeSourceValue_real_covariant (edge : EdgeStandardOperator data holomorphic)
    (source : SourceSpace.sourceCocycles data .plane)
    (real : RealGL3) (vertices : Fin 3 → RealGL3) (argument : AdelicGL) :
    edgeSourceValue data holomorphic source (fun index => real * vertices index) argument =
      realCoefficientComponent degree data.chi real
        (edgeSourceValue data holomorphic source vertices (argument * atInfinity real)) := by
  unfold edgeSourceValue
  rw [PolynomialNaturality.sourceSection_transformed, edgePolynomialValue_coefficientMap,
    edgePolynomialValue_right_real data holomorphic edge]

theorem edgeSourceValue_closed (source : SourceSpace.sourceCocycles data .plane)
    (vertices : Fin 4 → RealGL3) (argument : AdelicGL) :
    edgeSourceValue data holomorphic source ![vertices 1, vertices 2, vertices 3] argument -
      edgeSourceValue data holomorphic source ![vertices 0, vertices 2, vertices 3] argument +
      edgeSourceValue data holomorphic source ![vertices 0, vertices 1, vertices 3] argument -
      edgeSourceValue data holomorphic source ![vertices 0, vertices 1, vertices 2] argument = 0 :=
  edgePolynomialValue_source_closed data holomorphic source vertices argument

/-- Chosen standard continuation of the coefficient families (as in `PolynomialFamilies`, but with
the regular standard family supplied by the holomorphy hypothesis instead of `4 ≤ n`). -/
def edgePolynomialContinuation (sectionValue : PolynomialEisenstein.polynomialSections data) :
    ℂ → AdelicGL → HomogeneousPoly degree :=
  fun parameter argument => FlatExtensions.assemblePolynomial degree (fun monomial =>
    StandardValue.chosenContinuation data
      (HolomorphicStandardValue.regularFamily data holomorphic
        (SectionSpace.linearFlatExtension data holomorphic
          (PolynomialEisenstein.coefficientSection data monomial sectionValue)))
      parameter argument)

theorem edgePolynomialContinuation_continues
    (sectionValue : PolynomialEisenstein.polynomialSections data) (monomial : Fin 3 →₀ ℕ) :
    IsStandardContinuation
      (fun parameter argument => (PolynomialFamilies.polynomialFlatExtension data holomorphic sectionValue
          parameter argument).val.coeff monomial)
      (fun parameter argument => (edgePolynomialContinuation data holomorphic sectionValue parameter argument).val.coeff monomial) := by
  change IsStandardContinuation
    (fun parameter argument => (FlatExtensions.assemblePolynomial degree _).val.coeff monomial)
    (fun parameter argument => (FlatExtensions.assemblePolynomial degree _).val.coeff monomial)
  by_cases homogeneous : Finsupp.degree monomial = degree
  · simp only [FlatExtensions.assemblePolynomial_coeff, ite_eq_left homogeneous]
    exact (StandardValue.chosenContinuation_spec data
      (HolomorphicStandardValue.regularFamily data holomorphic
        (SectionSpace.linearFlatExtension data holomorphic
          (PolynomialEisenstein.coefficientSection data monomial sectionValue)))).1
  · simpa only [FlatExtensions.assemblePolynomial_coeff, ite_eq_right homogeneous] using
      FlatExtensions.standardContinuation_zero

theorem edgePolynomialContinuation_regular
    (sectionValue : PolynomialEisenstein.polynomialSections data)
    (argument : AdelicGL) (monomial : Fin 3 →₀ ℕ) :
    AnalyticAt ℂ (fun parameter => (edgePolynomialContinuation data holomorphic sectionValue parameter argument).val.coeff monomial)
      cohomologicalPoint := by
  change AnalyticAt ℂ (fun parameter => (FlatExtensions.assemblePolynomial degree _).val.coeff monomial) cohomologicalPoint
  by_cases homogeneous : Finsupp.degree monomial = degree
  · simpa only [FlatExtensions.assemblePolynomial_coeff, ite_eq_left homogeneous] using
      (StandardValue.chosenContinuation_spec data
        (HolomorphicStandardValue.regularFamily data holomorphic
          (SectionSpace.linearFlatExtension data holomorphic
            (PolynomialEisenstein.coefficientSection data monomial sectionValue)))).2 argument
  · simpa only [FlatExtensions.assemblePolynomial_coeff, ite_eq_right homogeneous] using
      (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) cohomologicalPoint)

theorem edgePolynomialContinuation_endpoint
    (sectionValue : PolynomialEisenstein.polynomialSections data) :
    edgePolynomialContinuation data holomorphic sectionValue cohomologicalPoint =
      edgePolynomialValue data holomorphic sectionValue := rfl

/-- The vertex-indexed continuation of a plane source cocycle. -/
def edgeSourceContinuation (source : SourceSpace.sourceCocycles data .plane) :
    ℂ → (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree :=
  fun parameter vertices => edgePolynomialContinuation data holomorphic
    (PolynomialEisenstein.sourceSection data source vertices) parameter

theorem edgeSourceContinuation_endpoint (source : SourceSpace.sourceCocycles data .plane) :
    edgeSourceContinuation data holomorphic source cohomologicalPoint =
      edgeSourceValue data holomorphic source := rfl

/-! ### The standard value of a source cocycle is a source cocycle -/

theorem edgeSourceValue_isSource (edge : EdgeStandardOperator data holomorphic)
    (source : SourceSpace.sourceCocycles data .plane) :
    IsSourceCocycle data .line (edgeSourceValue data holomorphic source) := by
  refine ⟨?_, ?_, edgeSourceValue_real_covariant data holomorphic edge source,
    edgeSourceValue_closed data holomorphic source⟩
  · intro vertices monomial
    exact edgePolynomialValue_induced data holomorphic edge
      (PolynomialEisenstein.sourceSection data source vertices) monomial
  · intro monomial
    have lift := edge.smooth_lift
      (fun vertices argument => (source.val vertices argument).val.coeff monomial)
      (fun vertices => source.property.1 vertices monomial) (source.property.2.1 monomial)
    simp only [edgeSourceValue, edgePolynomialValue_coeff]
    exact lift

/-- The plane-to-line standard operator on source cocycles built from the interface. -/
def edgeSourceCocycle (edge : EdgeStandardOperator data holomorphic)
    (source : SourceSpace.sourceCocycles data .plane) :
    SourceSpace.sourceCocycles data .line :=
  ⟨edgeSourceValue data holomorphic source, edgeSourceValue_isSource data holomorphic edge source⟩

def edgeSourceStandard (edge : EdgeStandardOperator data holomorphic) :
    SourceSpace.sourceCocycles data .plane →ₗ[ℂ] SourceSpace.sourceCocycles data .line where
  toFun := edgeSourceCocycle data holomorphic edge
  map_add' first second := by
    apply Subtype.ext
    funext vertices argument
    change edgePolynomialValue data holomorphic
      (PolynomialEisenstein.sourceSection data first vertices +
        PolynomialEisenstein.sourceSection data second vertices) argument = _
    rw [map_add]
    rfl
  map_smul' scalar source := by
    apply Subtype.ext
    funext vertices argument
    change edgePolynomialValue data holomorphic
      (scalar • PolynomialEisenstein.sourceSection data source vertices) argument = _
    rw [map_smul]
    rfl

theorem edgeSourceStandard_related (edge : EdgeStandardOperator data holomorphic)
    (source : SourceSpace.sourceCocycles data .plane) :
    StandardRelation.Related data source (edgeSourceStandard data holomorphic edge source) := by
  refine ⟨PolynomialFamilies.sourceFlatExtension data holomorphic source,
    edgeSourceContinuation data holomorphic source, ?_,
    PolynomialFamilies.sourceFlatExtension_endpoint data holomorphic source, ?_, ?_, rfl⟩
  · intro vertices monomial
    exact PolynomialFamilies.polynomialFlatExtension_flat data holomorphic
      (PolynomialEisenstein.sourceSection data source vertices) monomial
  · intro vertices monomial
    exact edgePolynomialContinuation_continues data holomorphic
      (PolynomialEisenstein.sourceSection data source vertices) monomial
  · intro vertices argument monomial
    exact edgePolynomialContinuation_regular data holomorphic
      (PolynomialEisenstein.sourceSection data source vertices) argument monomial

/-- Totality of the standard relation on plane source cocycles, given the edge standard operator.
This is the `existsIntegral` input of `GraphReduction.standard_graph_of_eisenstein` for `n = 3`. -/
theorem related_total_of_edgeStandardOperator (edge : EdgeStandardOperator data holomorphic) :
    ∀ plane : SourceSpace.sourceCocycles data .plane,
      ∃ line, StandardRelation.Related data plane line := by
  intro plane
  exact ⟨edgeSourceStandard data holomorphic edge plane,
    edgeSourceStandard_related data holomorphic edge plane⟩

theorem planeClass_surjective_of_edgeStandardOperator (edge : EdgeStandardOperator data holomorphic) :
    Function.Surjective (StandardRelation.planeClass data) :=
  StandardRelation.planeClass_surjective data
    (related_total_of_edgeStandardOperator data holomorphic edge)

end TernaryPeriodPolynomials.EdgeConvergence.EdgeStandard
