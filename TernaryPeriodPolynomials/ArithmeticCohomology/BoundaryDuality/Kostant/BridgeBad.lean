module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.BridgeBadLevi

@[expose] public section


/-!
# The level-three bridge at the bad line

At the bad line `L₀` of the level, for the trivial character and even `n`, the `Γ₁'(3)`-modules of
the parabolic duality are both `Sym^{n+1}` (`binaryArithmeticRepresentation n`, determinant twist
`0`, paired by the invariant pairing `binaryPairing (n+1)`).  The coordinates are the bad-line
coordinate `PhiBad` (the explicit binary coordinate of the radical cohomology) and the rotated dual
coordinate `PsiBad`; the Levi cocycles `γ ↦ Φ(A(k_γ⁻¹))` and `γ ↦ Ψ(A'(k_γ⁻¹))` are crossed
cocycles of `Γ₁'(3)` (`badX`, `badX'`) because the coordinates are equivariant on the
`U`-equivariant one-cocycles (`PhiBad_levi`, `PsiBad_levi`) and the Levi cocycles are such cocycles
(`uCocycle_leviCocycle_bad`).  The Kostant pairing is `(n+1)!/3` times the binary pairing of the
coordinates (`kostantBad_eq_binaryPairing`).  These data form the level-three bridge
`levelThreeBridgeBad`, with the Levi embedding `badLevi` sending the generators `upper 1`, `lower 1`
to `T = I + E₁₂`, `L = I + 3E₂₁`.

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

section Bridge

variable {n : ℕ} {Λe : Subgroup RationalGL3}
  {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
  {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}

/-- **The line crossed cocycle of the bridge**: `γ ↦ Φ(A(k_γ⁻¹))`, a crossed cocycle of
`Γ₁'(3)` with values in `Sym^{n+1}`. -/
def badX (positive : 0 < n)
    (hF : FiberHyp (rationalCoefficientComponent n trivialCharacter)
      (dualRep (dualityData n trivialCharacter)) (dualityData n trivialCharacter).B
      (levelStabilizer L₀) Λe latL0.sub ζ η ω ωU θU) :
    crossedCocycles (binaryArithmeticRepresentation n) :=
  ⟨fun γ => PhiBad n positive
      (leviCocycle (rationalCoefficientComponent n trivialCharacter) ωU (badLevi γ)⁻¹), by
    intro a b
    have e1 : leviCocycle (rationalCoefficientComponent n trivialCharacter) ωU
        (badLevi (a * b))⁻¹ =
        leviCocycle (rationalCoefficientComponent n trivialCharacter) ωU (badLevi a)⁻¹ +
          cochainRep (rationalCoefficientComponent n trivialCharacter) (badLevi a)
            (leviCocycle (rationalCoefficientComponent n trivialCharacter) ωU (badLevi b)⁻¹) := by
      rw [map_mul, _root_.mul_inv_rev]
      exact leviCocycle_mul (rationalCoefficientComponent n trivialCharacter) ωU
        (badLevi b)⁻¹ (badLevi a)⁻¹
    show PhiBad n positive (leviCocycle (rationalCoefficientComponent n trivialCharacter) ωU
        (badLevi (a * b))⁻¹) =
      PhiBad n positive (leviCocycle (rationalCoefficientComponent n trivialCharacter) ωU
        (badLevi a)⁻¹) +
        binaryArithmeticRepresentation n a (PhiBad n positive
          (leviCocycle (rationalCoefficientComponent n trivialCharacter) ωU (badLevi b)⁻¹))
    rw [e1, map_add, PhiBad_levi n positive (uCocycle_leviCocycle_bad hF b).1 a]⟩

/-- **The plane crossed cocycle of the bridge**: `γ ↦ Ψ(A'(k_γ⁻¹))`. -/
def badX' (heven : Even n)
    (hF : FiberHyp (rationalCoefficientComponent n trivialCharacter)
      (dualRep (dualityData n trivialCharacter)) (dualityData n trivialCharacter).B
      (levelStabilizer L₀) Λe latL0.sub ζ η ω ωU θU) :
    crossedCocycles (binaryArithmeticRepresentation n) :=
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
        binaryArithmeticRepresentation n a (PsiBad n
          (leviCocycle (dualRep (dualityData n trivialCharacter)) θU (badLevi b)⁻¹))
    rw [e1, map_add, PsiBad_levi n heven (uCocycle_leviCocycle_bad hF b).2 a]⟩

/-- **The level-three bridge at the bad line**, for the trivial character and even `n`:
`M = M' = Sym^{n+1}` with the invariant pairing, and the Kostant constant `c = (n+1)!/3`. -/
def levelThreeBridgeBad (positive : 0 < n) (heven : Even n)
    (hF : FiberHyp (rationalCoefficientComponent n trivialCharacter)
      (dualRep (dualityData n trivialCharacter)) (dualityData n trivialCharacter).B
      (levelStabilizer L₀) Λe latL0.sub ζ η ω ωU θU) :
    LevelThreeBridge (dualityData n trivialCharacter) ωU θU (binaryArithmeticRepresentation n)
      (binaryArithmeticRepresentation n) (BinaryPairing.binaryPairing (n + 1))
      (badX positive hF) (badX' heven hF) (((n + 1).factorial : ℂ) / 3) where
  levi := badLevi
  Φ := PhiBad n positive
  Ψ := PsiBad n
  levi_T := badLevi_T
  levi_L := badLevi_L
  pairing := fun _ _ hf hg => kostantBad_eq_binaryPairing n positive heven hf hg
  alpha := fun _ => rfl
  beta := fun _ => rfl
  equivΦ := fun γ _ hf => PhiBad_levi n positive hf γ
  equivΨ := fun γ _ hg => PsiBad_levi n heven hg γ

end Bridge

end TernaryPeriodPolynomials.BoundaryDuality.Kostant

end
