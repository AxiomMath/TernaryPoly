module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.FiniteEntries.T0Entry
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.StandardOperatorLinear

@[expose] public section


/-!
# The printed intertwiner `eq:intertwiner` is the uniqueness map `T₀` of `line_constant_term_comparison`

Formalized by Claude Sonnet 5.5.

The printed operator is `(Tφ)(g) = ∫_{𝔸²} φ(w₀⁻¹ u(s,t) g) ds dt` with `w₀ = [[0,0,1],[1,0,0],[0,1,0]]` (`weyl`),
`u(s,t) = [[1,s,t],[0,1,0],[0,0,1]]` (`lineUnipotent`) and the Haar measure `radicalMeasure` of `𝔸²` (Lebesgue at infinity,
`vol(ℤ_p) = 1`).  In the library this is `standardIntegrand` and `sourceStandard`, the standard operator on plane source cocycles.

Question of R7 s4.4: are the premises of `Statements.FacePairing.standard_eq_T` (`RealizesStandardConv`, `4 ≤ n`, the graph property)
discharged for the actual printed operator?  Answer, proved here:

* the operator `sourceStandard` is the printed integral itself, coefficientwise, absolutely convergent at the cohomological point
  `s₀ = -3/2` for `n ≥ 4` (`sourceStandard_coeff_integral`, `printed_integrable`; no continuation is used there);
* `T₀_eq_printed` (= `ConsumersStd.T₀_sourceClass_eq_std`, premises discharged: `4 ≤ n`, `planeEisensteinConvergent`, the uniqueness
  clause `(line_constant_term_comparison n hn).choose_spec.2`): `T₀ [plane] = [sourceStandard plane]`;
* `printed_respects_classes`: the printed operator is well defined on classes of plane sources (this is not needed to define
  `sourceStandard` but it is what makes it a map on the boundary summand: the common value is `T₀` of the class);
* `realizes_eq_T0`: every linear map of the boundary summands with `RealizesStandardConv` is `T₀` on the plane summand;
  `RealizesStandardConv` is satisfied by the actual printed operator on classes, `ConsumersStd.standardFromT0Std` (= `T₀`
  restricted), `standardFromT0Std_realizesStandardConv`.

What is NOT claimed: that `T₀` is intrinsic to the Eisenstein series of forms (that is the classical-form comparison, R7 s4.5); and
the Haar measure normalization is the library's `radicalMeasure` (Lebesgue × `vol(ℤ_p)=1`), as in the paper.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.SourceConstruction

noncomputable section

namespace TernaryPeriodPolynomials.Argument.PrintedIntertwiner

variable {n : ℕ} (D : CohomologicalCuspData n) (hn : 4 ≤ n)

theorem sourceStandard_coeff_integral (plane : SourceSpace.sourceCocycles D.inducingData .plane)
    (vertices : Fin 3 → RealGL3) (g : AdelicGL) (m : Fin 3 →₀ ℕ) :
    ((ConvergentEisenstein.EndpointSourceStandard.sourceStandard D.inducingData hn (planeEisensteinConvergent hn D.inducingData) plane).val
        vertices g).val.coeff m =
      ∫ u : Adeles × Adeles, ((plane.val vertices (weyl⁻¹ * lineUnipotent u.1 u.2 * g)).val.coeff m)
        ∂radicalMeasure := by
  change (ConvergentEisenstein.EndpointPolynomialStandard.polynomialValue D.inducingData hn (planeEisensteinConvergent hn D.inducingData)
    (PolynomialEisenstein.sourceSection D.inducingData plane vertices) g).val.coeff m = _
  rw [ConvergentEisenstein.EndpointPolynomialStandard.polynomialValue_coeff, ConvergentEisenstein.EndpointStandardValue.sectionStandard_eq_integral]
  rfl

include hn in
/-- **The printed integral converges absolutely** (degree `n ≥ 4`, at the cohomological point). -/
theorem printed_integrable (plane : SourceSpace.sourceCocycles D.inducingData .plane)
    (vertices : Fin 3 → RealGL3) (g : AdelicGL) (m : Fin 3 →₀ ℕ) :
    MeasureTheory.Integrable (fun u : Adeles × Adeles =>
      (plane.val vertices (weyl⁻¹ * lineUnipotent u.1 u.2 * g)).val.coeff m) radicalMeasure := by
  let sec := PolynomialEisenstein.coefficientSection D.inducingData m
    (PolynomialEisenstein.sourceSection D.inducingData plane vertices)
  have h := CompactScalarConvergence.standard_endpoint_integrable D.inducingData
    (ConvergentEisenstein.SectionSpace.linearFlatExtension D.inducingData (planeEisensteinConvergent hn D.inducingData) sec).val
    (ConvergentEisenstein.SectionSpace.linearFlatExtension D.inducingData (planeEisensteinConvergent hn D.inducingData) sec).property hn g
  have e : standardIntegrand (ConvergentEisenstein.SectionSpace.linearFlatExtension D.inducingData
      (planeEisensteinConvergent hn D.inducingData) sec).val cohomologicalPoint g =
      fun u : Adeles × Adeles => sec.val (weyl⁻¹ * lineUnipotent u.1 u.2 * g) := by
    funext u
    simp only [standardIntegrand, ConvergentEisenstein.SectionSpace.linearFlatExtension_endpoint]
  rw [e] at h
  exact h

open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.ConsumersStd in
/-- **`T₀` is the printed intertwiner on classes.** For the uniqueness map `T₀ = (line_constant_term_comparison n hn).choose` and every plane source
cocycle, `T₀ [plane] = [sourceStandard plane]` in the line stratum, where `sourceStandard plane` is the printed integral. -/
theorem T0_eq_printed (plane : SourceSpace.sourceCocycles D.inducingData .plane) :
    (TernaryPeriodPolynomials.line_constant_term_comparison n hn).choose (SourceSpace.sourceClass D.inducingData .plane plane) =
      SourceSpace.sourceClass D.inducingData .line
        (ConvergentEisenstein.EndpointSourceStandard.sourceStandard D.inducingData hn
          (planeEisensteinConvergent hn D.inducingData) plane) :=
  T₀_sourceClass_eq_std D hn (planeEisensteinConvergent hn D.inducingData)
    (TernaryPeriodPolynomials.line_constant_term_comparison n hn).choose
    (TernaryPeriodPolynomials.line_constant_term_comparison n hn).choose_spec.2 plane

/-- **The printed intertwiner descends to classes**: plane sources with the same class have standard line sources with the same
class (their common value is `T₀` of the class). -/
theorem printed_respects_classes (plane plane' : SourceSpace.sourceCocycles D.inducingData .plane)
    (h : SourceSpace.sourceClass D.inducingData .plane plane = SourceSpace.sourceClass D.inducingData .plane plane') :
    SourceSpace.sourceClass D.inducingData .line
        (ConvergentEisenstein.EndpointSourceStandard.sourceStandard D.inducingData hn
          (planeEisensteinConvergent hn D.inducingData) plane) =
      SourceSpace.sourceClass D.inducingData .line
        (ConvergentEisenstein.EndpointSourceStandard.sourceStandard D.inducingData hn
          (planeEisensteinConvergent hn D.inducingData) plane') := by
  rw [← T0_eq_printed D hn plane, ← T0_eq_printed D hn plane', h]

/-- **Any linear standard operator with `RealizesStandardConv` is `T₀` on the plane summand** (so the printed operator, defined on
classes by its integral, is `T₀` restricted). -/
theorem realizes_eq_T0 (standard : boundarySummand D.inducingData .plane →ₗ[ℂ] boundarySummand D.inducingData .line)
    (hstd : RealizesStandardConv D.inducingData standard) (x : boundarySummand D.inducingData .plane) :
    (standard x).val = (TernaryPeriodPolynomials.line_constant_term_comparison n hn).choose x.val := by
  obtain ⟨plane, hplane⟩ := SourceQuotient.sourceToSummand_surjective D.inducingData .plane x
  subst hplane
  have h1 := ConvergentEisenstein.StandardConv.realizesStandardConv_apply_eq_sourceStandard D.inducingData hn
    (planeEisensteinConvergent hn D.inducingData) standard hstd plane
  have h2 := T0_eq_printed D hn plane
  have e1 := ConvergentEisenstein.ConsumersStd.sourceToSummand_val_std D.inducingData .line
    (ConvergentEisenstein.EndpointSourceStandard.sourceStandard D.inducingData hn
      (planeEisensteinConvergent hn D.inducingData) plane)
  have e2 := ConvergentEisenstein.ConsumersStd.sourceToSummand_val_std D.inducingData .plane plane
  exact ((congrArg Subtype.val h1).trans e1).trans (h2.symm.trans (congrArg _ e2.symm))

/-- **The printed intertwiner `eq:intertwiner` is the uniqueness map `T₀` of `line_constant_term_comparison`.**

For `n ≥ 4` and every paper datum `D`, with `T₀ = (line_constant_term_comparison n hn).choose` and `sourceStandard` the standard operator on plane
source cocycles:
1. (the printed integral) the monomial coefficients of `sourceStandard plane` at `(vertices, g)` are the absolutely convergent
   integrals `∫_{𝔸²} φ(w₀⁻¹ u(s,t) g) ds dt` of the coefficients of the plane section `φ = plane vertices`, at the cohomological
   point `s₀ = -3/2` (the integral converges there since `n ≥ 4`);
2. (identification) `T₀ [plane] = [sourceStandard plane]` in the line stratum;
3. (descent) the printed operator is well defined on classes, and
4. every linear map `standard` of the boundary summands with `RealizesStandardConv` (the continuation of the standard family) equals
   `T₀` on the plane summand.

All premises are discharged for the actual objects: `4 ≤ n` is the hypothesis; the plane Eisenstein hypothesis is
`planeEisensteinConvergent` (absolute convergence); the uniqueness clause of `T₀` is `(line_constant_term_comparison n hn).choose_spec.2`;
`RealizesStandardConv` is a hypothesis only in 4, and is satisfied by `standardFromT0Std` (`ConsumersStd`). -/
theorem printed_intertwiner_eq_T0 :
    (∀ (plane : SourceSpace.sourceCocycles D.inducingData .plane) (vertices : Fin 3 → RealGL3) (g : AdelicGL)
        (m : Fin 3 →₀ ℕ),
      MeasureTheory.Integrable (fun u : Adeles × Adeles =>
        (plane.val vertices (weyl⁻¹ * lineUnipotent u.1 u.2 * g)).val.coeff m) radicalMeasure ∧
      ((ConvergentEisenstein.EndpointSourceStandard.sourceStandard D.inducingData hn
          (planeEisensteinConvergent hn D.inducingData) plane).val vertices g).val.coeff m =
        ∫ u : Adeles × Adeles, ((plane.val vertices (weyl⁻¹ * lineUnipotent u.1 u.2 * g)).val.coeff m)
          ∂radicalMeasure) ∧
    (∀ plane : SourceSpace.sourceCocycles D.inducingData .plane,
      (TernaryPeriodPolynomials.line_constant_term_comparison n hn).choose (SourceSpace.sourceClass D.inducingData .plane plane) =
        SourceSpace.sourceClass D.inducingData .line
          (ConvergentEisenstein.EndpointSourceStandard.sourceStandard D.inducingData hn
            (planeEisensteinConvergent hn D.inducingData) plane)) ∧
    (∀ plane plane' : SourceSpace.sourceCocycles D.inducingData .plane,
      SourceSpace.sourceClass D.inducingData .plane plane = SourceSpace.sourceClass D.inducingData .plane plane' →
      SourceSpace.sourceClass D.inducingData .line
          (ConvergentEisenstein.EndpointSourceStandard.sourceStandard D.inducingData hn
            (planeEisensteinConvergent hn D.inducingData) plane) =
        SourceSpace.sourceClass D.inducingData .line
          (ConvergentEisenstein.EndpointSourceStandard.sourceStandard D.inducingData hn
            (planeEisensteinConvergent hn D.inducingData) plane')) ∧
    (∀ (standard : boundarySummand D.inducingData .plane →ₗ[ℂ] boundarySummand D.inducingData .line),
      RealizesStandardConv D.inducingData standard → ∀ x : boundarySummand D.inducingData .plane,
        (standard x).val = (TernaryPeriodPolynomials.line_constant_term_comparison n hn).choose x.val) :=
  ⟨fun plane vertices g m => ⟨printed_integrable D hn plane vertices g m,
      sourceStandard_coeff_integral D hn plane vertices g m⟩,
    T0_eq_printed D hn, printed_respects_classes D hn, realizes_eq_T0 D hn⟩

end TernaryPeriodPolynomials.Argument.PrintedIntertwiner
