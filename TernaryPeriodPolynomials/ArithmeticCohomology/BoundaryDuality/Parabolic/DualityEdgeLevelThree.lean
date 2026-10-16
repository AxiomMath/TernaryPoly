module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityLevelThree
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Bad.LineBound
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneBound
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.LocalUniqueness

@[expose] public section


/-!
# The edge classes at the level-three cusps are parabolic

The parabolic classes of `H¹(Γ₁'(3), ρ)` of `ParabolicDualityLevelThree` (crossed homomorphisms whose
values at `T` and at `L` are coboundaries) are exactly the parabolic classes
`TwoGenerator.parabolicH1 ρ T L` (`parabolicCrossedH1_eq`).  Hence the results that the Hochschild–Serre edge images of the local joint generalized eigenclasses are
parabolic apply verbatim:

* bad line, trivial character: `jointEdgeMap_mem_parabolicCrossedH1`, in
  `CrossedH1 (binaryArithmeticRepresentation n)` (coefficients `(m, e) = (n + 1, 0)`);
* good plane, trivial character: `goodPlaneEdge_mem_parabolicCrossedH1`, in
  `CrossedH1 (levelRep (n + 1) (-1))` (coefficients `(m, e) = (n + 1, -1)`).

For odd `n` the classical pairing `binaryPairing (n + 1)` pairs the two coefficient systems
(`twistedPairing_badLine_goodPlane`), and parabolic duality gives left nondegeneracy in the bad-line
variable (`badLine_left_nondegenerate`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree

open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.LevelThree
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators

section Comparison

variable {V : Type} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ binaryArithmeticLevel V)

/-- The parabolic crossed homomorphisms of `ParabolicDuality` are those. -/
theorem parabolicCrossed_eq :
    parabolicCrossed ρ = TwoGenerator.parabolicCocycles ρ (upper 1) (lower 1) := by
  ext x
  rw [mem_parabolicCrossed_iff]
  constructor
  · rintro ⟨⟨u, hu⟩, ⟨w, hw⟩⟩
    exact ⟨(TwoGenerator.mem_moved ρ).2 ⟨u, hu.symm⟩, (TwoGenerator.mem_moved ρ).2 ⟨w, hw.symm⟩⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨u, hu⟩ := (TwoGenerator.mem_moved ρ).1 h1
    obtain ⟨w, hw⟩ := (TwoGenerator.mem_moved ρ).1 h2
    exact ⟨⟨u, hu.symm⟩, ⟨w, hw.symm⟩⟩

/-- **The parabolic classes of `ParabolicDuality` are the parabolic classes.** -/
theorem parabolicCrossedH1_eq :
    parabolicCrossedH1 ρ = TwoGenerator.parabolicH1 ρ (upper 1) (lower 1) := by
  show (parabolicCrossed ρ).map (crossedBoundaries ρ).mkQ =
    (TwoGenerator.parabolicCocycles ρ (upper 1) (lower 1)).map (crossedBoundaries ρ).mkQ
  rw [parabolicCrossed_eq]

end Comparison

section Edges

/-- **Bad line, trivial character.**  The edge image of a local joint generalized eigenclass is a
parabolic class of `H¹(Γ₁'(3), Sym^{n+1})`. -/
theorem jointEdgeMap_mem_parabolicCrossedH1 (n : ℕ) (hn : 3 ≤ n) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp LocalUniqueness.two) - 1‖ ≤ 3 / 4)
    (y : localJoint n trivialCharacter c .line false) :
    BadLineBound.jointEdgeMap n (by omega) c hc y ∈
      parabolicCrossedH1 (binaryArithmeticRepresentation n) := by
  have h := BadLineBound.jointEdgeMap_mem_parabolic n hn c hc y
  rw [parabolicCrossedH1_eq]
  exact h

/-- **Good plane, trivial character.**  The edge image of a local joint generalized eigenclass is a
parabolic class of `H¹(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)`. -/
theorem goodPlaneEdge_mem_parabolicCrossedH1 (n : ℕ) (hn : 1 ≤ n) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp LocalUniqueness.two) - 1‖ ≤ 3 / 4)
    {x : CuspH2 n trivialCharacter .plane true}
    (hx : x ∈ localJoint n trivialCharacter c .plane true) :
    GoodPlaneEdge3.goodPlaneEdge (by omega : 0 < n) x ∈
      parabolicCrossedH1 (ParabolicBounds.levelRep (n + 1) (-1)) := by
  have h := GoodPlaneJoint.map_localJoint_le n (by omega) c
    (Submodule.mem_map_of_mem (f := GoodPlaneEdge3.goodPlaneEdge (by omega : 0 < n)) hx)
  have h' := GoodPlaneBound.levelJoint_le_parabolic n hn c hc h
  rw [parabolicCrossedH1_eq]
  exact h'

end Edges

section Pairings

/-- **Coefficient pairing at the bad line / good plane**: for odd `n`, `binaryPairing (n + 1)` pairs
`Sym^{n+1}` with `Sym^{n+1} ⊗ det⁻¹` (`(m, e, e') = (n + 1, 0, -1)`, `e + e' - m = -(n + 2)` odd). -/
theorem twistedPairing_badLine_goodPlane {n : ℕ} (hodd : Odd n) :
    TwistedPairing (ParabolicBounds.levelRep (n + 1) 0) (ParabolicBounds.levelRep (n + 1) (-1))
      (BinaryPairing.binaryPairing (n + 1)) :=
  twistedPairing_levelRep (n + 1) 0 (-1) (by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨-(k : ℤ) - 2, by omega⟩)

/-- **Left nondegeneracy in the bad-line variable.** -/
theorem badLine_left_nondegenerate {n : ℕ} (hodd : Odd n)
    (cl : parabolicCrossedH1 (ParabolicBounds.levelRep (n + 1) 0))
    (h : ∀ cl' : parabolicCrossedH1 (ParabolicBounds.levelRep (n + 1) (-1)),
      parabolicPairing (twistedPairing_badLine_goodPlane hodd) cl cl' = 0) : cl = 0 :=
  parabolicPairing_left_nondegenerate (twistedPairing_badLine_goodPlane hodd) cl h

end Pairings

end TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree
