module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.ConstantTerm.Averaging
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.DefectRegularity

@[expose] public section


/-!
# Regularity of the defect (convergent)

Cocycle property and continuity of the defect translation family.

Re-port of `TernaryPeriodPolynomials.Argument.EisensteinGraph.ConstantTerm.DefectRegularity` (from the Sol reference implementation, ported by AxiomCode) with `PlaneEisensteinHolomorphic` replaced by the continuation-free
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
variable {n : ℕ}
/-- The Eisenstein value at real vertices satisfies the four-term cocycle relation, at every
adelic argument. -/
theorem eisensteinValue_fourTerm (D : InducingData n) (hol : PlaneEisensteinConvergent D)
    (c : SourceSpace.sourceCocycles D .plane) (x : Fin 4 → RationalGL3) (g : AdelicGL) :
    eisensteinValue D hol c (GlobalEisensteinCocycle.realVertices ![x 1, x 2, x 3]) g -
      eisensteinValue D hol c (GlobalEisensteinCocycle.realVertices ![x 0, x 2, x 3]) g +
      eisensteinValue D hol c (GlobalEisensteinCocycle.realVertices ![x 0, x 1, x 3]) g -
      eisensteinValue D hol c (GlobalEisensteinCocycle.realVertices ![x 0, x 1, x 2]) g = 0 := by
  have h := PolynomialEisenstein.polynomialValue_source_closed D hol c
    (GlobalEisensteinCocycle.realVertexTuple x) g
  rw [← realVertices_face123, ← realVertices_face023, ← realVertices_face013,
    ← realVertices_face012] at h
  exact h

/-- **Cocycle law.** For every translation parameter `r` the defect family is a homogeneous
2-cocycle on rational vertex tuples. -/
theorem defectFamily_isCocycle₂ (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinConvergent D) (c : SourceSpace.sourceCocycles D .plane) (side : Side)
    (q : RationalGL3) (K : ℕ) (r : ℝ × ℝ) :
    IsCocycle₂ (defectFamily large D hol c side q K r) := by
  intro x
  simp only [defectFamily_eq]
  exact four_term_sub _ _ _ _ _ _ _ _ (eisensteinValue_fourTerm D hol c x _)
    (sourceCocycle_fourTerm (sideSource large D hol c side) x _)

/-- Continuity of each monomial coefficient of the defect family in the parameter. -/
theorem defectFamily_coeff_continuous (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinConvergent D) (c : SourceSpace.sourceCocycles D .plane) (side : Side)
    (q : RationalGL3) (K : ℕ) (y : Fin 3 → RationalGL3) (m : Fin 3 →₀ ℕ) :
    Continuous (fun r : ℝ × ℝ =>
      (defectFamily large D hol c side q K r y).val.coeff m) := by
  have hg := defectArgument_continuous side q K
  have e : (fun r : ℝ × ℝ => (defectFamily large D hol c side q K r y).val.coeff m) =
      fun r : ℝ × ℝ =>
        (SectionSpace.sectionEisensteinValue D hol
          (PolynomialEisenstein.coefficientSection D m
            (PolynomialEisenstein.sourceSection D c
              (GlobalEisensteinCocycle.realVertices y)))).val
          (atInfinity (sideUnipotent side ((K : ℝ) * r.1) ((K : ℝ) * r.2)) *
            rationalGroup q⁻¹) -
        ((sideSource large D hol c side).val
          (GlobalEisensteinCocycle.realVertices y)
          (atInfinity (sideUnipotent side ((K : ℝ) * r.1) ((K : ℝ) * r.2)) *
            rationalGroup q⁻¹)).val.coeff m := by
    funext r
    rw [defectFamily_eq, Submodule.coe_sub, MvPolynomial.coeff_sub]
    congr 1
    exact PolynomialNaturality.polynomialValue_coeff D hol
      (PolynomialEisenstein.sourceSection D c (GlobalEisensteinCocycle.realVertices y)) m _
  rw [e]
  exact ((sectionEisensteinValue_continuous D hol large _).comp hg).sub
    ((StandardConstruction.InducedContinuity.induced_continuous D side cohomologicalPoint _
      ((sourceCocycle_isSource (sideSource large D hol c side)).1
        (GlobalEisensteinCocycle.realVertices y) m)).comp hg)

/-- **Continuity.** Every linear functional of the defect family is continuous in the
translation parameter, at every rational vertex tuple. -/
theorem defectFamily_functional_continuous (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinConvergent D) (c : SourceSpace.sourceCocycles D .plane) (side : Side)
    (q : RationalGL3) (K : ℕ) (y : Fin 3 → RationalGL3)
    (μ : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    Continuous (fun r : ℝ × ℝ => μ (defectFamily large D hol c side q K r y)) := by
  obtain ⟨weight, hweight⟩ := FlagExactness.homogeneous_functional_eq_sum n μ
  simp_rw [hweight]
  exact continuous_finsetSum _ (fun s _ =>
    (defectFamily_coeff_continuous large D hol c side q K y s.val).mul continuous_const)

/-- Both regularity properties of the defect translation family. -/
theorem defectFamily_regularity (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinConvergent D) (c : SourceSpace.sourceCocycles D .plane) (side : Side)
    (q : RationalGL3) (K : ℕ) :
    (∀ r : ℝ × ℝ, IsCocycle₂ (defectFamily large D hol c side q K r)) ∧
      ∀ (y : Fin 3 → RationalGL3) (μ : HomogeneousPoly n →ₗ[ℂ] ℂ),
        Continuous (fun r : ℝ × ℝ => μ (defectFamily large D hol c side q K r y)) :=
  ⟨defectFamily_isCocycle₂ large D hol c side q K,
    defectFamily_functional_continuous large D hol c side q K⟩



end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.ConstantTerm
