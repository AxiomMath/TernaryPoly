module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.ConstantTerm.Averaging
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.ConstantTerm.RestrictionAssembly

@[expose] public section


/-!
# The defect at flags (convergent)

The defect family at the origin and stabilizer equivariance of the defect cochain.

Re-port of `TernaryPeriodPolynomials.Argument.EisensteinGraph.ConstantTerm.FlagDefect` (from the Sol reference implementation, ported by AxiomCode) with `PlaneEisensteinHolomorphic` replaced by the continuation-free
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


open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
variable {n : ℕ}
theorem defectFamily_zero_eq (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinConvergent D) (c : SourceSpace.sourceCocycles D .plane) (side : Side)
    (q : RationalGL3) (K : ℕ) (y : Fin 3 → RationalGL3) :
    defectFamily large D hol c side q K 0 y =
      (defectCochain large D hol c side).val y (QuotientGroup.mk q) := by
  have h1 : sideUnipotent side ((K : ℝ) * (0 : ℝ × ℝ).1) ((K : ℝ) * (0 : ℝ × ℝ).2) = 1 := by
    simp only [Prod.fst_zero, Prod.snd_zero, mul_zero]
    exact sideUnipotent_zero side
  have e1 : (restrictionCocycle n D.chi side
      (EndpointEisensteinCocycle.globalCocycle D hol large c)).val.val y (QuotientGroup.mk q) =
        eisensteinValue D hol c (GlobalEisensteinCocycle.realVertices y) (rationalGroup q⁻¹) := by
    change (EndpointEisensteinCocycle.globalCocycle D hol large c).val.val y = _
    rw [EndpointEisensteinCocycle.globalCocycle_realizes,
      GlobalEisensteinCocycle.evaluatedSourceValue_eq_anchor D hol c y q]
    rfl
  have e2 : (SourceSpace.evaluatedSource D side (sideSource large D hol c side)).val.val y
      (QuotientGroup.mk q) =
        (sideSource large D hol c side).val (GlobalEisensteinCocycle.realVertices y)
          (rationalGroup q⁻¹) :=
    SourceSpace.evaluatedSource_realizes D side (sideSource large D hol c side) y q
  have hD : (defectCochain large D hol c side).val y (QuotientGroup.mk q) =
      (restrictionCocycle n D.chi side
        (EndpointEisensteinCocycle.globalCocycle D hol large c)).val.val y (QuotientGroup.mk q) -
      (SourceSpace.evaluatedSource D side (sideSource large D hol c side)).val.val y
        (QuotientGroup.mk q) := rfl
  rw [hD, e1, e2]
  unfold defectFamily
  rw [h1, LineInductionLaws.atInfinity_one, one_mul]
  rfl

/-- The flag component of the defect cochain is equivariant for the stabilizer of the flag in the
arithmetic level. -/
theorem defectCochain_stabilizer_equivariant (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinConvergent D) (c : SourceSpace.sourceCocycles D .plane) (side : Side)
    (q : RationalGL3) :
    Equivariant (rationalLevel ⊓ MulAction.stabilizer RationalGL3 (QuotientGroup.mk q : Flags side))
      (rationalCoefficientComponent n D.chi)
      (fun y => (defectCochain large D hol c side).val y (QuotientGroup.mk q)) := by
  intro γ hγ x
  obtain ⟨hγL, hγS⟩ := Subgroup.mem_inf.mp hγ
  have h := (defectCochain large D hol c side).property ⟨γ, hγL⟩ x
  have h' := congrFun h (QuotientGroup.mk q)
  change _ = rationalCoefficientComponent n D.chi γ
    ((defectCochain large D hol c side).val x (γ⁻¹ • (QuotientGroup.mk q : Flags side))) at h'
  have hs : γ⁻¹ • (QuotientGroup.mk q : Flags side) = QuotientGroup.mk q := by
    rw [inv_smul_eq_iff]
    exact (MulAction.mem_stabilizer_iff.mp hγS).symm
  rw [hs] at h'
  exact h'



end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.ConstantTerm
