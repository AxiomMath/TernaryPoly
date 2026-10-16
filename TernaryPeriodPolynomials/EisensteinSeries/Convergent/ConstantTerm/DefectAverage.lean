module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.ConstantTerm.Averaging
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.StandardConstantTermComparison
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.DefectAverage

@[expose] public section


/-!
# Vanishing averages of the defect (convergent)

The real averages of the defect over the unipotent radical vanish: the plane and line constant terms of the convergent Eisenstein series.

Re-port of `TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm.DefectAverage` (from the Sol reference implementation, ported by AxiomCode) with `PlaneEisensteinHolomorphic` replaced by the continuation-free
`PlaneEisensteinConvergent`; declarations that do not depend on the continuation hypothesis are
not copied (the original ones are used).  Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.ConstantTerm

open TernaryPeriodPolynomials
open TernaryPeriodPolynomials.EisensteinGraph
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm
open TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm.DefectAverage


open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous MeasureTheory
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers
  (realPlaneUnitMeasure planeDomainMeasure planeDomainMeasure_eq
    planeDomain_integral_real_projection radical_periodic_integral_rational_scaling
    scalar_plane_constant_term atInfinity_planeUnipotent planeUnipotent_continuous
    lineUnipotent_continuous map_planeUnipotent map_lineUnipotent atInfinity_atFinite_commute
    atFinite_left_conjugate finiteGroup_atInfinity integral_principal_finite_conjugate
    planeUnipotent_three_reduction planeUnipotent_adelic_factor)
variable {n : ℕ}
namespace DefectAverage
/-- The scalar Eisenstein series attached to the `m`-th coefficient of the section of `c`
at the vertex tuple `y`. -/
def eisensteinCoefficient (D : InducingData n) (hol : PlaneEisensteinConvergent D)
    (c : SourceSpace.sourceCocycles D .plane) (y : Fin 3 → RealGL3) (m : Fin 3 →₀ ℕ) :
    AdelicGL → ℂ :=
  (SectionSpace.sectionEisensteinValue D hol
    (PolynomialEisenstein.coefficientSection D m (PolynomialEisenstein.sourceSection D c y))).val

theorem eisensteinValue_coeff (D : InducingData n) (hol : PlaneEisensteinConvergent D)
    (c : SourceSpace.sourceCocycles D .plane) (y : Fin 3 → RealGL3) (m : Fin 3 →₀ ℕ)
    (g : AdelicGL) :
    (eisensteinValue D hol c y g).val.coeff m = eisensteinCoefficient D hol c y m g :=
  PolynomialNaturality.polynomialValue_coeff D hol (PolynomialEisenstein.sourceSection D c y) m g

theorem eisensteinCoefficient_continuous (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinConvergent D) (c : SourceSpace.sourceCocycles D .plane)
    (y : Fin 3 → RealGL3) (m : Fin 3 →₀ ℕ) :
    Continuous (eisensteinCoefficient D hol c y m) :=
  sectionEisensteinValue_continuous D hol large _

theorem eisensteinCoefficient_rational (D : InducingData n) (hol : PlaneEisensteinConvergent D)
    (c : SourceSpace.sourceCocycles D .plane) (y : Fin 3 → RealGL3) (m : Fin 3 →₀ ℕ)
    (element : RationalGL3) (x : AdelicGL) :
    eisensteinCoefficient D hol c y m (rationalGroup element * x) =
      eisensteinCoefficient D hol c y m x :=
  (SectionSpace.sectionEisensteinValue D hol
    (PolynomialEisenstein.coefficientSection D m
      (PolynomialEisenstein.sourceSection D c y))).property.1 element x

theorem eisensteinCoefficient_finite (D : InducingData n) (hol : PlaneEisensteinConvergent D)
    (c : SourceSpace.sourceCocycles D .plane) (y : Fin 3 → RealGL3) (m : Fin 3 →₀ ℕ)
    (level : finiteLevel) (x : AdelicGL) :
    eisensteinCoefficient D hol c y m (x * atFinite level.val) =
      eisensteinCoefficient D hol c y m x :=
  (SectionSpace.sectionEisensteinValue D hol
    (PolynomialEisenstein.coefficientSection D m
      (PolynomialEisenstein.sourceSection D c y))).property.2 level x

/-- The constant term of the plane Eisenstein series of a section along the plane radical is
the section itself. -/
theorem sectionEisenstein_plane_constant_term (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinConvergent D)
    (s : SectionSpace.inducedSections D .plane cohomologicalPoint) (g : AdelicGL) :
    (∫ point : Adeles × Adeles, (SectionSpace.sectionEisensteinValue D hol s).val
        (planeUnipotent point.1 point.2 * g) ∂planeDomainMeasure) = s.val g := by
  have halfPlane : -(n : ℝ) / 2 < cohomologicalPoint.re := by
    have fourReal : (4 : ℝ) ≤ n := by exact_mod_cast large
    norm_num [cohomologicalPoint]
    linarith
  have flat := (SectionSpace.linearFlatExtension D hol s).property
  have hsum : ∀ x, (SectionSpace.sectionEisensteinValue D hol s).val x =
      ∑' flag : Flags .plane, eisensteinSummand
        (SectionSpace.linearFlatExtension D hol s).val cohomologicalPoint x flag := by
    intro x
    rw [EndpointEisensteinCocycle.sectionEisensteinValue_eq_sum D hol large s x]
    simp only [eisensteinSummand, SectionSpace.linearFlatExtension_endpoint]
  have constantTerm := (scalar_plane_constant_term (inducingData := D)
    (family := (SectionSpace.linearFlatExtension D hol s).val) flat cohomologicalPoint
    halfPlane g).2
  calc (∫ point : Adeles × Adeles, (SectionSpace.sectionEisensteinValue D hol s).val
        (planeUnipotent point.1 point.2 * g) ∂planeDomainMeasure)
      = ∫ point : Adeles × Adeles, ∑' flag : Flags .plane, eisensteinSummand
          (SectionSpace.linearFlatExtension D hol s).val cohomologicalPoint
          (planeUnipotent point.1 point.2 * g) flag ∂planeDomainMeasure :=
        integral_congr_ae (ae_of_all _ fun point => hsum _)
    _ = (SectionSpace.linearFlatExtension D hol s).val cohomologicalPoint g := constantTerm
    _ = s.val g := by rw [SectionSpace.linearFlatExtension_endpoint]

theorem eisensteinCoefficient_plane_constant_term (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinConvergent D) (c : SourceSpace.sourceCocycles D .plane)
    (y : Fin 3 → RealGL3) (m : Fin 3 →₀ ℕ) (g : AdelicGL) :
    (∫ point : Adeles × Adeles, eisensteinCoefficient D hol c y m
        (planeUnipotent point.1 point.2 * g) ∂planeDomainMeasure) =
      (c.val y g).val.coeff m :=
  sectionEisenstein_plane_constant_term large D hol
    (PolynomialEisenstein.coefficientSection D m (PolynomialEisenstein.sourceSection D c y)) g

/-- The constant term of the Eisenstein coefficient along the line radical is the corresponding
coefficient of the standard continuation `J c`. -/
theorem sourceStandard_coeff_eq_integral (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinConvergent D) (c : SourceSpace.sourceCocycles D .plane)
    (y : Fin 3 → RealGL3) (m : Fin 3 →₀ ℕ) (g : AdelicGL) :
    ((EndpointSourceStandard.sourceStandard D large hol c).val y g).val.coeff m =
      ∫ point : Adeles × Adeles, eisensteinCoefficient D hol c y m
        (lineUnipotent point.1 point.2 * g) ∂planeDomainMeasure := by
  rw [StandardConstantTermComparison.sourceStandard_coeff_constantTerm large D hol c y g m,
    planeDomainMeasure_eq]
  refine integral_congr_ae (ae_of_all _ fun point => ?_)
  exact PolynomialNaturality.polynomialValue_coeff D hol
    (PolynomialEisenstein.sourceSection D c y) m _

/-- Real average of the Eisenstein coefficient along the plane radical: it is the coefficient
of `c`. -/
theorem eisensteinCoefficient_plane_real_average (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinConvergent D) (c : SourceSpace.sourceCocycles D .plane)
    (y : Fin 3 → RealGL3) (m : Fin 3 →₀ ℕ) (integral : GL3 IntegralAdeles) (g : AdelicGL)
    (finite_eq : finiteGroup g = Matrix.GeneralLinearGroup.map integralEmbedding integral) :
    (∫ r : ℝ × ℝ, eisensteinCoefficient D hol c y m
        (atInfinity (planeUnipotent (3 * r.1) (3 * r.2)) * g) ∂realPlaneUnitMeasure) =
      (c.val y g).val.coeff m :=
  (plane_real_average_eq_adelic (F := eisensteinCoefficient D hol c y m)
    (eisensteinCoefficient_continuous large D hol c y m)
    (eisensteinCoefficient_rational D hol c y m) (eisensteinCoefficient_finite D hol c y m)
    integral g finite_eq).trans (eisensteinCoefficient_plane_constant_term large D hol c y m g)

/-- Real average of the Eisenstein coefficient along the line radical: it is the coefficient of
`J c`. -/
theorem eisensteinCoefficient_line_real_average (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinConvergent D) (c : SourceSpace.sourceCocycles D .plane)
    (y : Fin 3 → RealGL3) (m : Fin 3 →₀ ℕ) (integral : GL3 IntegralAdeles) (g : AdelicGL)
    (finite_eq : finiteGroup g = Matrix.GeneralLinearGroup.map integralEmbedding integral) :
    (∫ r : ℝ × ℝ, eisensteinCoefficient D hol c y m
        (atInfinity (lineUnipotent (3 * r.1) (3 * r.2)) * g) ∂realPlaneUnitMeasure) =
      ((EndpointSourceStandard.sourceStandard D large hol c).val y g).val.coeff m :=
  (line_real_average_eq_adelic (F := eisensteinCoefficient D hol c y m)
    (eisensteinCoefficient_continuous large D hol c y m)
    (eisensteinCoefficient_rational D hol c y m) (eisensteinCoefficient_finite D hol c y m)
    integral g finite_eq).trans (sourceStandard_coeff_eq_integral large D hol c y m g).symm

theorem source_line_path_invariant (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinConvergent D) (c : SourceSpace.sourceCocycles D .plane)
    (y : Fin 3 → RealGL3) (m : Fin 3 →₀ ℕ) (a b : ℝ) (g : AdelicGL) :
    ((EndpointSourceStandard.sourceStandard D large hol c).val y
          (atInfinity (lineUnipotent a b) * g)).val.coeff m =
      ((EndpointSourceStandard.sourceStandard D large hol c).val y g).val.coeff m := by
  rw [atInfinity_lineUnipotent_eq]
  exact isInduced_line_unipotent
    ((EndpointSourceStandard.sourceStandard D large hol c).property.1 y m) (a, 0) (b, 0) g

theorem sideSource_plane (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinConvergent D) (c : SourceSpace.sourceCocycles D .plane) :
    sideSource large D hol c .plane = c := rfl

theorem sideSource_line (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinConvergent D) (c : SourceSpace.sourceCocycles D .plane) :
    sideSource large D hol c .line = EndpointSourceStandard.sourceStandard D large hol c := rfl

theorem defectFamily_three (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinConvergent D) (c : SourceSpace.sourceCocycles D .plane)
    (side : Side) (q : RationalGL3) (r : ℝ × ℝ) (y : Fin 3 → RationalGL3) :
    defectFamily large D hol c side q 3 r y =
      defectValue large D hol c side (GlobalEisensteinCocycle.realVertices y)
        (atInfinity (sideUnipotent side (3 * r.1) (3 * r.2)) * rationalGroup q⁻¹) :=
  rfl

theorem defectValue_coeff (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinConvergent D) (c : SourceSpace.sourceCocycles D .plane)
    (side : Side) (y : Fin 3 → RealGL3) (m : Fin 3 →₀ ℕ) (g : AdelicGL) :
    (defectValue large D hol c side y g).val.coeff m =
      (eisensteinValue D hol c y g).val.coeff m -
        ((sideSource large D hol c side).val y g).val.coeff m := by
  unfold defectValue
  rw [Submodule.coe_sub, MvPolynomial.coeff_sub]

end DefectAverage
open DefectAverage
/-- Plane stratum: for a rational flag whose inverse has integral finite part, the real torus
average of the defect translation family vanishes under every linear functional. -/
theorem defectFamily_plane_average_zero (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinConvergent D) (c : SourceSpace.sourceCocycles D .plane)
    (q : RationalGL3) (integral : GL3 IntegralAdeles)
    (hq : finiteGroup (rationalGroup q⁻¹) =
      Matrix.GeneralLinearGroup.map integralEmbedding integral)
    (y : Fin 3 → RationalGL3) (μ : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    (∫ r : ℝ × ℝ, μ (defectFamily large D hol c .plane q 3 r y) ∂realPlaneUnitMeasure) = 0 := by
  refine average_zero_of_coefficients μ
    (fun r => defectFamily large D hol c .plane q 3 r y)
    (fun m r => DefectAverage.eisensteinCoefficient D hol c (GlobalEisensteinCocycle.realVertices y) m
      (atInfinity (planeUnipotent (3 * r.1) (3 * r.2)) * rationalGroup q⁻¹))
    (fun m => (c.val (GlobalEisensteinCocycle.realVertices y) (rationalGroup q⁻¹)).val.coeff m)
    ?_ ?_ ?_
  · intro r m
    show (defectFamily large D hol c .plane q 3 r y).val.coeff m =
      DefectAverage.eisensteinCoefficient D hol c (GlobalEisensteinCocycle.realVertices y) m
        (atInfinity (planeUnipotent (3 * r.1) (3 * r.2)) * rationalGroup q⁻¹) -
      (c.val (GlobalEisensteinCocycle.realVertices y) (rationalGroup q⁻¹)).val.coeff m
    rw [DefectAverage.defectFamily_three, DefectAverage.defectValue_coeff, sideUnipotent_plane, DefectAverage.eisensteinValue_coeff,
      DefectAverage.sideSource_plane, source_plane_path_invariant]
  · intro m
    exact integrable_realPlaneUnit_of_continuous
      ((DefectAverage.eisensteinCoefficient_continuous large D hol c _ m).comp
        (continuous_planePath (rationalGroup q⁻¹)))
  · intro m
    exact DefectAverage.eisensteinCoefficient_plane_real_average large D hol c _ m integral _ hq

/-- Line stratum: the same vanishing, with `J c` in place of `c`. -/
theorem defectFamily_line_average_zero (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinConvergent D) (c : SourceSpace.sourceCocycles D .plane)
    (q : RationalGL3) (integral : GL3 IntegralAdeles)
    (hq : finiteGroup (rationalGroup q⁻¹) =
      Matrix.GeneralLinearGroup.map integralEmbedding integral)
    (y : Fin 3 → RationalGL3) (μ : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    (∫ r : ℝ × ℝ, μ (defectFamily large D hol c .line q 3 r y) ∂realPlaneUnitMeasure) = 0 := by
  refine average_zero_of_coefficients μ
    (fun r => defectFamily large D hol c .line q 3 r y)
    (fun m r => DefectAverage.eisensteinCoefficient D hol c (GlobalEisensteinCocycle.realVertices y) m
      (atInfinity (lineUnipotent (3 * r.1) (3 * r.2)) * rationalGroup q⁻¹))
    (fun m => ((EndpointSourceStandard.sourceStandard D large hol c).val
        (GlobalEisensteinCocycle.realVertices y) (rationalGroup q⁻¹)).val.coeff m)
    ?_ ?_ ?_
  · intro r m
    show (defectFamily large D hol c .line q 3 r y).val.coeff m =
      DefectAverage.eisensteinCoefficient D hol c (GlobalEisensteinCocycle.realVertices y) m
        (atInfinity (lineUnipotent (3 * r.1) (3 * r.2)) * rationalGroup q⁻¹) -
      ((EndpointSourceStandard.sourceStandard D large hol c).val
          (GlobalEisensteinCocycle.realVertices y) (rationalGroup q⁻¹)).val.coeff m
    rw [DefectAverage.defectFamily_three, DefectAverage.defectValue_coeff, sideUnipotent_line, DefectAverage.eisensteinValue_coeff,
      DefectAverage.sideSource_line, DefectAverage.source_line_path_invariant]
  · intro m
    exact integrable_realPlaneUnit_of_continuous
      ((DefectAverage.eisensteinCoefficient_continuous large D hol c _ m).comp
        (continuous_linePath (rationalGroup q⁻¹)))
  · intro m
    exact DefectAverage.eisensteinCoefficient_line_real_average large D hol c _ m integral _ hq

/-- Plane stratum at an integral flag representative `g`, over the closed unit square. -/
theorem defectFamily_plane_average_zero_Icc (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinConvergent D) (c : SourceSpace.sourceCocycles D .plane)
    (g : IntegralGL3) (y : Fin 3 → RationalGL3) (μ : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    (∫ r in Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
      μ (defectFamily large D hol c .plane
        (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) g) 3 r y)) = 0 := by
  rw [← realPlaneUnitMeasure_eq_Icc]
  exact defectFamily_plane_average_zero large D hol c _ _
    (finiteGroup_rationalGroup_integral_inv g) y μ

/-- Line stratum at an integral flag representative `g`, over the closed unit square. -/
theorem defectFamily_line_average_zero_Icc (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinConvergent D) (c : SourceSpace.sourceCocycles D .plane)
    (g : IntegralGL3) (y : Fin 3 → RationalGL3) (μ : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    (∫ r in Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
      μ (defectFamily large D hol c .line
        (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) g) 3 r y)) = 0 := by
  rw [← realPlaneUnitMeasure_eq_Icc]
  exact defectFamily_line_average_zero large D hol c _ _
    (finiteGroup_rationalGroup_integral_inv g) y μ

/-- Both strata at an integral flag representative `g`, over the closed unit square. -/
theorem defectFamily_average_zero_Icc (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinConvergent D) (c : SourceSpace.sourceCocycles D .plane)
    (side : Side) (g : IntegralGL3) (y : Fin 3 → RationalGL3)
    (μ : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    (∫ r in Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
      μ (defectFamily large D hol c side
        (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) g) 3 r y)) = 0 := by
  cases side
  · exact defectFamily_plane_average_zero_Icc large D hol c g y μ
  · exact defectFamily_line_average_zero_Icc large D hol c g y μ



end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.ConstantTerm
