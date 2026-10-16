module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Top.BoundaryComparisonEvaluation
public import TernaryPeriodPolynomials.GroupCohomology.Homology.NormalAction

@[expose] public section


/-!
# Equivariance of the canonical evaluation of `Hom`-cohomology

For a chain complex `D` of representations of a normal subgroup `H ≤ G` with a compatible `G`-action
(`GActC`), the evaluation `H^n(Hom_H(D, W)) → Hom_H(H_n(D), W)` of the library intertwines the
conjugation action `hcohAct` on cohomology with `ρ_W(g) ∘ - ∘ ρ(g)⁻¹`, in the form: the value on
the class of a cycle `z` is `ρ_W(g)` applied to the original cocycle at `ρ(g)⁻¹ z`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GroupHomology

open CategoryTheory TernaryPoly TernaryPoly.OrdinaryTopBoundaryComparison
  TernaryPoly.EquivariantSingularSmall

variable {G : Type} [Group G] {H : Subgroup G} [H.Normal]

/-- The evaluation of a conjugated cohomology class on the class of a cycle. -/
theorem homologyEvaluation_hcohAct {D : ChainComplex (Rep.{0} ℚ ↥H) ℕ} {W : Rep.{0} ℚ ↥H}
    (A : GActC D) (B : GAct H W) (g : G) (n : ℕ) (x : (homCochains D W).cycles n)
    (z : D.cycles n) :
    (homologyEvaluation D W n
        (hcohAct A B g n ((homCochains D W).homologyπ n x))).hom (D.homologyπ n z) =
      B.ρ g ((cocycleValue D W n x).hom ((A.act n).ρ g⁻¹ (D.iCycles n z))) := by
  have hn : hcohAct A B g n ((homCochains D W).homologyπ n x) =
      (homCochains D W).homologyπ n (HomologicalComplex.cyclesMap (hcAct A B g) n x) :=
    (congrArg (fun m => m x) (HomologicalComplex.homologyπ_naturality (hcAct A B g) n))
  rw [hn, homologyEvaluation_apply]
  have hi : (homCochains D W).iCycles n (HomologicalComplex.cyclesMap (hcAct A B g) n x) =
      (hcAct A B g).f n ((homCochains D W).iCycles n x) :=
    congrArg (fun m => m x) (HomologicalComplex.cyclesMap_i (hcAct A B g) n)
  change ((homCochains D W).iCycles n (HomologicalComplex.cyclesMap (hcAct A B g) n x)).hom
    (D.iCycles n z) = _
  rw [hi]
  rfl

end TernaryPeriodPolynomials.Argument.GroupHomology
