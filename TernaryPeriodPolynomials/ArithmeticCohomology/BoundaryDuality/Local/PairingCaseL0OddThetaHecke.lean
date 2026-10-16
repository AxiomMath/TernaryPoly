module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL0OddPairing
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL0OddHeckeTransfer
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL0OddCompat
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL0Odd

@[expose] public section


/-!
# The transport commutes with the Hecke operators `T_p` of `Γ₁'(3)`

The transport `thetaH1 : [e] ↦ [γ ↦ - E (e (α γ))]` of `H¹(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)`
(`LocalPairingCaseL0OddPairing`) commutes with the Hecke operator `T_p = levelHecke (n+1) (-1) p`
(`thetaHeckeCommute`), for odd `n`.

This is the instance of the generic commutation `LocalPairingCaseL0OddHeckeTransfer.transportH1_hecke`
for the coset system `Γ₁'(3) α_j` of `T_p`: the involution `tilde h = δ (h⁻¹)ᵀ δ⁻¹` of `GL₂(ℚ)`
extending `α` (`tilde_levelEmbed`) permutes the cosets up to the central element `z = ε_p p⁻¹` and
elements of `Γ₁'(3)` (`LocalPairingCaseL0OddTilde.exists_coset_data`), and the comparison map `E`
is compatible with the coset representatives (`LocalPairingCaseL0OddCompat.compat_at_coset`): the
scalar `det(α_j)^{n+3} = p^{n+3}` by which the twists `n + 2` and `-1` differ at the representatives
is exactly the scalar by which the central element `z` acts.

Consequently the standard adjointness `AdjointLevelThreePairing.BadGoodHeckeAdjoint` implies the
adjointness `BadGoodHeckeAdjointOdd` in the coordinates of the reference good plane
(`badGoodHeckeAdjointOdd_of_adjoint`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Odd

open TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0OddTilde
  (invTG map_invTG tilde tilde_apply zUnit zUnit_comm piEquiv exists_coset_data)
open TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0OddIntertwine
  (planeE)
open TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0OddCompat
  (compat_at_coset)
open TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0OddHeckeTransfer
  (transportH1_hecke)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.IdentBad
  (alpha kap_alpha planeComparison)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneFrame (del integralEmbed_kap)
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeH1
  (rationalRho level_compat levelHecke)
open TernaryPeriodPolynomials.LevelThree.LevelThreeCosets
  (heckeRep levelEmbed levelEmbed_apply levelEmbed_injective levelCosets)
open TernaryPeriodPolynomials.Spectral.LevelOneCosets (integralEmbed)
open TernaryPeriodPolynomials.BoundaryDuality.Kostant (invT)
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace (traceDataL2)
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives (dualityData)
open TernaryPeriodPolynomials.BoundaryDuality.CuspFullness (LocalNondegenerate)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)

variable {n : ℕ}

/-- **The involution `tilde` of `GL₂(ℚ)` extends `α`**: `tilde (ι g) = ι (α g)` for `g ∈ Γ₁'(3)`. -/
theorem tilde_levelEmbed (g : binaryArithmeticLevel) :
    tilde (levelEmbed g) = levelEmbed (alpha g) := by
  have h1 := integralEmbed_kap (alpha g)
  rw [kap_alpha] at h1
  have h2 : integralEmbed (invT g.1) = invTG (integralEmbed g.1) :=
    map_invTG (Int.castRingHom ℚ) g.1
  have h3 : del * invTG (integralEmbed g.1) * del⁻¹ = integralEmbed (alpha g).val := by
    rw [← h2, h1]
    group
  rw [levelEmbed_apply, levelEmbed_apply, tilde_apply]
  exact h3

/-- The comparison map of `LocalPairingCaseL0OddIntertwine` is `IdentBad.planeComparison`. -/
theorem planeE_eq_planeComparison (n : ℕ) : planeE n = planeComparison n := rfl

/-- The compatibility of the negated comparison map at the coset representatives. -/
theorem compat_planeNeg (hodd : Odd n) (p : Nat.Primes) (hp3 : p.val ≠ 3)
    (γ : Option (Fin p.val) → binaryArithmeticLevel)
    (hA : ∀ j, tilde (heckeRep p j) = zUnit p * levelEmbed (γ j) * heckeRep p (piEquiv p hp3 j))
    (j : Option (Fin p.val)) (v : Binary.HomogeneousPoly (n + 1)) :
    rationalRho (n + 1) (-1) (heckeRep p j)⁻¹ (planeNeg n (levelRep (n + 1) (-1) (γ j) v)) =
      planeNeg n (rationalRho (n + 1) (-1) (heckeRep p (piEquiv p hp3 j))⁻¹ v) := by
  have h := compat_at_coset hodd p hp3 γ hA j v
  rw [planeNeg_apply, planeNeg_apply, map_neg, level_compat (n + 1) (-1) (γ j)]
  exact congrArg Neg.neg h

/-- **The transport commutes with the Hecke operators `T_p` of `H¹(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)`.** -/
theorem thetaHeckeCommute (hodd : Odd n) : ThetaHeckeCommute hodd := by
  intro p hp3 y
  obtain ⟨γ, hA⟩ := exists_coset_data p hp3
  exact transportH1_hecke (levelCosets p hp3) (rationalRho (n + 1) (-1)) (levelRep (n + 1) (-1))
    (level_compat (n + 1) (-1)) levelEmbed_injective alphaHom tilde tilde_levelEmbed (planeNeg n)
    (planeNeg_intertwines hodd) (zUnit p) (zUnit_comm p) (piEquiv p hp3) γ hA
    (fun j v => compat_planeNeg hodd p hp3 γ hA j v) y

/-- **The adjointness in the coordinates of the reference good plane** from the standard
adjointness `BadGoodHeckeAdjoint` of the Lefschetz pairing. -/
theorem badGoodHeckeAdjointOdd_of_adjoint (hodd : Odd n)
    (hadj : AdjointLevelThree.BadGoodHeckeAdjoint hodd) : BadGoodHeckeAdjointOdd hodd :=
  badGoodHeckeAdjointOdd_of_commute hodd (thetaHeckeCommute hodd) hadj

/-- **Local nondegeneracy at the bad line `L₀`, trivial character, odd degree**, from the standard
level-three adjointness `AdjointLevelThreePairing.BadGoodHeckeAdjoint` of the Lefschetz pairing of
the bad-line and good-plane Levi cohomology: the only hypothesis besides `3 ≤ n` and a nonzero
associate pair. -/
theorem localNondegenerate_L0_odd_of_standardAdjoint (hn : 3 ≤ n) (hodd : Odd n)
    (D : InducingData n) (hχ : D.chi = trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hne : associatePair D ≠ ⊥)
    (hadj : AdjointLevelThree.BadGoodHeckeAdjoint hodd) :
    LocalNondegenerate traceDataL2 D (dualityData n D.chi) hecke hhecke 0
      (TernaryPeriodPolynomials.BoundaryDuality.CuspDualL2.good 0) :=
  localNondegenerate_L0_odd hn hodd D hχ hecke hhecke hne
    (badGoodHeckeAdjointOdd_of_adjoint hodd hadj)

/-- **The bad-line case of odd degree** (`ParityCases.BadLineOddInput`) from the standard level-three
adjointness `AdjointLevelThreePairing.BadGoodHeckeAdjoint` of the Lefschetz pairing. -/
theorem badLineOddInput_of_standardAdjoint (hn : 3 ≤ n)
    (hadj : ∀ hodd : Odd n, AdjointLevelThree.BadGoodHeckeAdjoint hodd) :
    ParityCases.BadLineOddInput n :=
  badLineOddInput hn fun hodd => badGoodHeckeAdjointOdd_of_adjoint hodd (hadj hodd)

end TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Odd

end
