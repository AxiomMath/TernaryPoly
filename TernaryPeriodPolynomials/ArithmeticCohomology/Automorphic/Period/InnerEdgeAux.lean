module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.ParabolicBounds

@[expose] public section


/-!
# Sol's parabolic classes are parabolic for `Γ₁'(3)`

Sol's `binaryParabolicH1 degree` consists of the classes of `H¹(Γ₁'(3), Sym^{degree+1})` whose
restriction to every rational cusp stabilizer `binaryCuspLevel frame` vanishes.  Workstream D's
`parabolicH1 (levelRep (degree + 1) 0) (upper 1) (lower 1)` only asks for the restrictions to the two
generator subgroups `⟨upper 1⟩` and `⟨lower 1⟩`.  Since `upper 1` fixes the cusp `∞` and `lower 1`
fixes the cusp `0`, the first space is contained in the second
(`mem_parabolicH1_of_mem_binaryParabolicH1`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators LowDegreeParabolic
open TernaryPeriodPolynomials.LevelThree.GammaOneThree
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds
open TernaryPeriodPolynomials.LevelThree.TwoGenerator

namespace TernaryPeriodPolynomials.Automorphic.Period.InnerEdgeAux

/-- **Sol's parabolic classes are D's parabolic classes.**  A class of `H¹(Γ₁'(3), Sym^{degree+1})`
restricting to zero at every rational cusp stabilizer restricts to zero at `⟨upper 1⟩` and
`⟨lower 1⟩`, the two generator subgroups defining `parabolicH1`. -/
theorem mem_parabolicH1_of_mem_binaryParabolicH1 (degree : ℕ)
    (x : CrossedH1 (binaryArithmeticRepresentation degree)) (hx : x ∈ binaryParabolicH1 degree) :
    x ∈ parabolicH1 (levelRep (degree + 1) 0) (upper 1) (lower 1) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hx' : (crossedBoundaries (binaryArithmeticRepresentation degree)).mkQ z ∈
      binaryParabolicH1 degree := hx
  refine ⟨z, ⟨?_, ?_⟩, rfl⟩
  · obtain ⟨p, hp⟩ := parabolic_generator_primitive z hx' 1 (upper 1) upper_cusp
    exact ⟨p, hp.symm⟩
  · have membership : lower 1 ∈ binaryCuspLevel oppositeFrame := by
      rw [← inv_inv (lower 1), lower_inv]
      exact (binaryCuspLevel oppositeFrame).inv_mem lower_cusp
    obtain ⟨p, hp⟩ := parabolic_generator_primitive z hx' oppositeFrame (lower 1) membership
    exact ⟨p, hp.symm⟩

end TernaryPeriodPolynomials.Automorphic.Period.InnerEdgeAux
