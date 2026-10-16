module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.BridgeBad
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.BridgeBadOddPairing

@[expose] public section


/-!
# The level-three bridge at the bad line, odd degree

For odd `n` the bad line `L₀` (trivial character) is a genuine case, because `-I ∉ Γ₁'(3)`.  The
`Γ₁'(3)`-modules of the parabolic duality are `M = Sym^{n+1}` (`levelRep (n+1) 0`) for the bad-line
coordinate and `M' = Sym^{n+1} ⊗ det⁻¹` (`levelRep (n+1) (-1)`) for the rotated dual coordinate (the
rotation twist `n + 2` is odd, congruent to `-1` modulo `2`), paired by `binaryPairing (n+1)`
(`twistedPairing_badLine_goodPlane`).  The line coordinate and its crossed cocycle `badX` are those of
the even case; the plane crossed cocycle is `badXOdd'`; the Kostant constant is `c = -(n+1)!/3`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains (levelStabilizer)

attribute [local instance] TernaryPeriodPolynomials.SphericalDetection.Helpers.complexEndRationalAlgebra

namespace TernaryPeriodPolynomials.BoundaryDuality.Kostant

open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly (latL0)
open TernaryPeriodPolynomials.BoundaryDuality.L2Matrices (L₀)
open TernaryPeriodPolynomials.BoundaryDuality.FiberCochains
  (cochainRep leviCocycle leviCocycle_mul)
open TernaryPeriodPolynomials.BoundaryDuality.FiberFormula (FiberHyp)
open TernaryPeriodPolynomials.BoundaryDuality.FiberL1 (dualRep)
open TernaryPeriodPolynomials.BoundaryDuality.FiberParabolicL0 (LevelThreeBridge)
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives (dualityData)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)

section Bridge

variable {n : ℕ} {Λe : Subgroup RationalGL3}
  {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
  {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}

/-- **The plane crossed cocycle of the odd-degree bridge**: `γ ↦ Ψ(A'(k_γ⁻¹))`, a crossed cocycle of
`Γ₁'(3)` with values in `Sym^{n+1} ⊗ det⁻¹`. -/
def badXOdd' (hodd : Odd n)
    (hF : FiberHyp (rationalCoefficientComponent n trivialCharacter)
      (dualRep (dualityData n trivialCharacter)) (dualityData n trivialCharacter).B
      (levelStabilizer L₀) Λe latL0.sub ζ η ω ωU θU) :
    crossedCocycles (levelRep (n + 1) (-1)) :=
  ⟨fun γ => PsiBad n
      (leviCocycle (dualRep (dualityData n trivialCharacter)) θU (badLevi γ)⁻¹), by
    intro a b
    have e1 : leviCocycle (dualRep (dualityData n trivialCharacter)) θU (badLevi (a * b))⁻¹ =
        leviCocycle (dualRep (dualityData n trivialCharacter)) θU (badLevi a)⁻¹ +
          cochainRep (dualRep (dualityData n trivialCharacter)) (badLevi a)
            (leviCocycle (dualRep (dualityData n trivialCharacter)) θU (badLevi b)⁻¹) := by
      rw [map_mul, _root_.mul_inv_rev]
      exact leviCocycle_mul (dualRep (dualityData n trivialCharacter)) θU
        (badLevi b)⁻¹ (badLevi a)⁻¹
    show PsiBad n (leviCocycle (dualRep (dualityData n trivialCharacter)) θU
        (badLevi (a * b))⁻¹) =
      PsiBad n (leviCocycle (dualRep (dualityData n trivialCharacter)) θU (badLevi a)⁻¹) +
        levelRep (n + 1) (-1) a (PsiBad n
          (leviCocycle (dualRep (dualityData n trivialCharacter)) θU (badLevi b)⁻¹))
    rw [e1, map_add, PsiBad_levi_odd n hodd (uCocycle_leviCocycle_bad hF b).2 a]⟩

/-- **The level-three bridge at the bad line for odd `n`** (trivial character):
`M = Sym^{n+1}`, `M' = Sym^{n+1} ⊗ det⁻¹`, and the Kostant constant `c = -(n+1)!/3`. -/
def levelThreeBridgeBadOdd (hodd : Odd n)
    (hF : FiberHyp (rationalCoefficientComponent n trivialCharacter)
      (dualRep (dualityData n trivialCharacter)) (dualityData n trivialCharacter).B
      (levelStabilizer L₀) Λe latL0.sub ζ η ω ωU θU) :
    LevelThreeBridge (dualityData n trivialCharacter) ωU θU (levelRep (n + 1) 0)
      (levelRep (n + 1) (-1)) (BinaryPairing.binaryPairing (n + 1))
      (badX hodd.pos hF) (badXOdd' hodd hF) (-((n + 1).factorial : ℂ) / 3) where
  levi := badLevi
  Φ := PhiBad n hodd.pos
  Ψ := PsiBad n
  levi_T := badLevi_T
  levi_L := badLevi_L
  pairing := fun _ _ hf hg => kostantBad_eq_binaryPairing_odd n hodd.pos hodd hf hg
  alpha := fun _ => rfl
  beta := fun _ => rfl
  equivΦ := fun γ _ hf => PhiBad_levi n hodd.pos hf γ
  equivΨ := fun γ _ hg => PsiBad_levi_odd n hodd hg γ

end Bridge

end TernaryPeriodPolynomials.BoundaryDuality.Kostant

end
