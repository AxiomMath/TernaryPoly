module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.L3ClassBridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.L3Final
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.L3Kappa
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.AdjointLevelThreePairing
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityEdgeLevelThree

@[expose] public section


/-!
# Hecke adjointness of the level-three parabolic cup pairings

* `badGoodHeckeAdjoint`: for odd `n` the cup pairing `badGoodPairing` of the parabolic classes of
  `H¹(Γ₁'(3), Sym^{n+1})` and `H¹(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)` is Hecke adjoint with the constant
  `κ_p = p⁻¹` (`AdjointLevelThree.BadGoodHeckeAdjoint`).
* `evenPairing_hecke_adjoint`: for even `n` the parabolic cup pairing of `H¹(Γ₁'(3), Sym^{n+1})`
  with itself satisfies `⟨T_p x, y⟩ = ε_p ⟨x, T_p y⟩`, `ε_p ≡ p (mod 3)` the sign.

Both are specializations of `AdjL3.coreAdjoint` (the adjointness at the level of `Γ₁(3)` for every
coefficient system `Sym^m ⊗ det^e`, `Sym^m ⊗ det^{e'}`) through the class-level glue of `AdjL3ClassBridge`,
with the constant `kappaGen`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.AdjL3

open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree
open TernaryPeriodPolynomials.BoundaryDuality.AdjointLevelThree
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)

/-- **Hecke adjointness of the bad-line / good-plane Lefschetz pairing** (`n` odd), with
`κ_p = p⁻¹`: the hypothesis `BadGoodHeckeAdjoint` consumed by the local nondegeneracy at the
bad line. -/
theorem badGoodHeckeAdjoint {n : ℕ} (hodd : Odd n) : BadGoodHeckeAdjoint hodd := by
  intro p hp3
  have hodd' : Odd ((0 : ℤ) + (-1) - ((n + 1 : ℕ) : ℤ)) := by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨-(k : ℤ) - 2, by omega⟩
  have h := isHeckeAdjoint_of_core' (n + 1) 0 (-1) hodd' p hp3 (kappaGen (n + 1) 0 (-1) p)
    (coreAdjoint (n + 1) 0 (-1) p hp3)
  rw [kappaGen_odd n hodd p] at h
  exact h

/-- **Hecke adjointness of the parabolic cup pairing of `H¹(Γ₁'(3), Sym^{n+1})` with itself**
(`n` even): `⟨T_p x, y⟩ = ε_p ⟨x, T_p y⟩`. -/
theorem evenPairing_hecke_adjoint {n : ℕ} (heven : Even n) (p : Nat.Primes) (hp3 : p.val ≠ 3) :
    HeckeAdjointLevi.IsHeckeAdjoint
      (parabolicPairing (twistedPairing_binaryArithmeticRepresentation n heven))
      (parabolicHecke (n + 1) 0 p hp3) (parabolicHecke (n + 1) 0 p hp3)
      (((AdjL3Cosets.eps p : ℤ) : ℂ)) := by
  have hodd' : Odd ((0 : ℤ) + 0 - ((n + 1 : ℕ) : ℤ)) := by
    obtain ⟨k, hk⟩ := heven
    exact ⟨-(k : ℤ) - 1, by omega⟩
  have h := isHeckeAdjoint_of_core' (n + 1) 0 0 hodd' p hp3 (kappaGen (n + 1) 0 0 p)
    (coreAdjoint (n + 1) 0 0 p hp3)
  rw [kappaGen_even n heven p] at h
  exact h

end TernaryPeriodPolynomials.BoundaryDuality.AdjL3
