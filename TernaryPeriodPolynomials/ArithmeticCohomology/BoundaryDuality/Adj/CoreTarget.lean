module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.CoreAdjoint
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.AdjointLevelOneEigen

@[expose] public section


/-!
# Hecke adjointness of the parabolic cup pairing of `GL₂(ℤ)`, for all primes

For `m` even and `e + e' - m` odd, the parabolic cup pairing of `H¹(GL₂(ℤ), Sym^m ⊗ det^e)` with
`H¹(GL₂(ℤ), Sym^m ⊗ det^{e'})` is Hecke adjoint with the scalar `κ_p = p^{e' - e}` for the
Hecke operators `T_p` of `GL₂(ℤ) diag(p, 1) GL₂(ℤ)` restricted to the parabolic classes, for every
prime `p` (`parabolicPairingHeckeAdjoint`); in particular for the pairs `(n + 1, 0, -1)` and
`(n + 1, -1, 0)` with `n` odd.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.AdjCore

open TernaryPeriodPolynomials.BoundaryDuality.AdjointLevelOne

/-- **Hecke adjointness of the parabolic cup pairing of `GL₂(ℤ)`** with the scalar
`κ_p = p^{e' - e}`, for every prime `p`. -/
theorem parabolicPairingHeckeAdjoint (m : ℕ) (e e' : ℤ) (hm : Even m)
    (hodd : Odd (e + e' - (m : ℤ))) : ParabolicPairingHeckeAdjoint m e e' hm hodd := by
  intro p c c'
  exact parabolicPairing_arithmeticHecke m e e' hm hodd p c c'
    (arithmeticHecke_mem_parabolicH1 m e p c.2) (arithmeticHecke_mem_parabolicH1 m e' p c'.2)

/-- Hecke adjointness for the untwisted good line against the identity plane:
`(m, e, e') = (n + 1, 0, -1)` with `n` odd. -/
theorem parabolicPairingHeckeAdjoint_trivial {n : ℕ} (hodd : Odd n) :
    ParabolicHeckeAdjoint (n + 1) 0 (-1)
      (ParabolicDuality.LevelOne.parabolicPairing
        (ParabolicDuality.LevelOne.twistedPairing_goodLine_trivial hodd))
      (heckeScalar 0 (-1)) :=
  parabolicPairingHeckeAdjoint (n + 1) 0 (-1) hodd.add_one (by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨-(k : ℤ) - 2, by omega⟩)

/-- Hecke adjointness for the odd-twisted good line against the odd-twisted identity plane:
`(m, e, e') = (n + 1, -1, 0)` with `n` odd. -/
theorem parabolicPairingHeckeAdjoint_odd {n : ℕ} (hodd : Odd n) :
    ParabolicHeckeAdjoint (n + 1) (-1) 0
      (ParabolicDuality.LevelOne.parabolicPairing
        (ParabolicDuality.LevelOne.twistedPairing_goodLine_odd hodd))
      (heckeScalar (-1) 0) :=
  parabolicPairingHeckeAdjoint (n + 1) (-1) 0 hodd.add_one (by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨-(k : ℤ) - 2, by omega⟩)

end TernaryPeriodPolynomials.BoundaryDuality.AdjCore
