module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.ConstantTerm.Basic
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.Averaging

@[expose] public section


/-!
# Averages of the defect (convergent)

Basic identities for the defect family and continuity of the Eisenstein coefficients.

Re-port of `TernaryPeriodPolynomials.Argument.EisensteinGraph.ConstantTerm.Averaging` (from the Sol reference implementation, ported by AxiomCode) with `PlaneEisensteinHolomorphic` replaced by the continuation-free
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


open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
section GridAverage
variable {V : Type} [AddCommGroup V] [Module ℂ V]
end GridAverage
section Defect
variable {n : ℕ} (large : 4 ≤ n) (D : InducingData n) (hol : PlaneEisensteinConvergent D)
  (c : SourceSpace.sourceCocycles D .plane)
theorem defectValue_plane (y : Fin 3 → RealGL3) (g : AdelicGL) :
    defectValue large D hol c .plane y g = eisensteinValue D hol c y g - c.val y g := rfl

theorem defectValue_line (y : Fin 3 → RealGL3) (g : AdelicGL) :
    defectValue large D hol c .line y g = eisensteinValue D hol c y g -
      (EndpointSourceStandard.sourceStandard D large hol c).val y g := rfl

theorem defectFamily_eq (side : Side) (q : RationalGL3) (K : ℕ) (r : ℝ × ℝ)
    (y : Fin 3 → RationalGL3) :
    defectFamily large D hol c side q K r y =
      eisensteinValue D hol c (GlobalEisensteinCocycle.realVertices y)
          (atInfinity (sideUnipotent side ((K : ℝ) * r.1) ((K : ℝ) * r.2)) *
            rationalGroup q⁻¹) -
        (sideSource large D hol c side).val (GlobalEisensteinCocycle.realVertices y)
          (atInfinity (sideUnipotent side ((K : ℝ) * r.1) ((K : ℝ) * r.2)) *
            rationalGroup q⁻¹) := rfl

end Defect
theorem sectionEisensteinValue_continuous {n : ℕ} (D : InducingData n)
    (hol : PlaneEisensteinConvergent D) (large : 4 ≤ n)
    (s : SectionSpace.inducedSections D .plane cohomologicalPoint) :
    Continuous (SectionSpace.sectionEisensteinValue D hol s).val := by
  set fam := SectionSpace.linearFlatExtension D hol s
  obtain ⟨bound, -, bounded⟩ :=
    CompactScalarRealization.flat_uniform_binary_bound D fam.val fam.property
  have halfPlane : -(n : ℝ) / 2 < cohomologicalPoint.re := by
    have : (4 : ℝ) ≤ n := by exact_mod_cast large
    norm_num [cohomologicalPoint]; linarith
  rw [continuous_iff_continuousAt]
  intro g
  have h := NormalConvergence.continuousAt_halfPlane D fam.val fam.property bound
    (fun k hk b => bounded cohomologicalPoint k hk b) cohomologicalPoint g halfPlane
  have hc : ContinuousAt (fun x : AdelicGL => (cohomologicalPoint, x)) g :=
    (continuous_const.prodMk continuous_id).continuousAt
  refine (h.comp hc).congr ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  simp only [Function.comp]
  rw [EndpointEisensteinCocycle.sectionEisensteinValue_eq_sum D hol large s x]
  simp only [eisensteinSummand, fam, SectionSpace.linearFlatExtension_endpoint]



end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.ConstantTerm
