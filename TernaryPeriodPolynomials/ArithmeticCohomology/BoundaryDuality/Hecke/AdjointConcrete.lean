module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Hecke.AdjointLevi
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Level.OneHeckeH1
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.HeckeH1
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneLocalOp
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Identity.PlaneLocalOp
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.PALocalOp

@[expose] public section


/-!
# Hecke adjointness of the Levi pairings, and the dual eigenvalue at each plane edge

The Levi quotient of the stabilizer of a good line is `GL₂(ℤ)` (level one) and that of the bad line
is `Γ₁'(3)`; the stabilizers of the identity plane and of the good plane have Levi quotients
`GL₂(ℤ)` and `Γ₁'(3)` with the dual coefficient twist. The cup product on `H¹` of a Levi group with
coefficients `Sym^d ⊗ det^τ` and `Sym^d ⊗ det^τ'` is a bilinear pairing `π` into `ℂ` after the
parabolic trace. The Hecke operator `T_p` of `Γ diag(p, 1) Γ` is carried by `g ↦ g⁻¹` to the same
double coset up to a central scalar, so the pairing is adjoint to itself up to a scalar `κ_p`:

  `π (T_p x, y) = κ_p · π (x, T_p y)`.

The scalar `κ_p` is determined by the weights, and by the affine edge formulas it must equal the
ratio `s' / s` of the coefficients `s`, `s'` of `T_p E` in the two edge formulas (`p^{τ' - τ}` for the
pairs occurring here). The statements below record the adjointness as a hypothesis on the pairing, for
the level-one operators (any twists, covering the untwisted good line against the identity plane and
the sign-twisted good line against the twisted identity plane) and for the level-three operators
(bad line against good plane), and combine it with the edge formulas of each plane cusp to give the
eigenfunctional relation `π x (E'(localOp w)) = e · π x (E' w)` for an eigen-edge `x`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointConcrete

open TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointLevi
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction (CuspH2 localOp)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeH1 (levelHecke badLevelHecke)

/-- **Level-one Hecke adjointness.** The pairing `π` of `H¹(GL₂(ℤ), Sym^d ⊗ det^τ)` with
`H¹(GL₂(ℤ), Sym^d ⊗ det^τ')` satisfies `π (T_p x, y) = κ_p π (x, T_p y)` for all primes `p`. -/
def LevelOneHeckeAdjoint (d : ℕ) (τ τ' : ℤ)
    (π : groupCohomology.H1 (arithmeticBinaryRep d τ) →ₗ[ℂ]
      groupCohomology.H1 (arithmeticBinaryRep d τ') →ₗ[ℂ] ℂ) (κ : Nat.Primes → ℂ) : Prop :=
  ∀ p : Nat.Primes, IsHeckeAdjoint π (LevelOneHeckeH1.arithmeticHecke d τ p)
    (LevelOneHeckeH1.arithmeticHecke d τ' p) (κ p)

/-- **Level-three Hecke adjointness.** The pairing `π` of `H¹(Γ₁'(3), Sym^{n+1})` (the bad-line
Levi) with `H¹(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)` (the good-plane Levi) satisfies
`π (T_p x, y) = κ_p π (x, T_p y)` for all primes `p ≠ 3`. -/
def LevelThreeHeckeAdjoint (n : ℕ)
    (π : CrossedH1 (binaryArithmeticRepresentation n) →ₗ[ℂ]
      CrossedH1 (levelRep (n + 1) (-1)) →ₗ[ℂ] ℂ) (κ : Nat.Primes → ℂ) : Prop :=
  ∀ (p : Nat.Primes) (hp3 : p.val ≠ 3), IsHeckeAdjoint π (badLevelHecke p hp3 n)
    (levelHecke (n + 1) (-1) p hp3) (κ p)

/-- **Good-plane dual eigenvalue.** If `x` is an eigen-edge of the bad line (`a x + s T_p x = c x`)
and the level-three pairing is `κ_p`-adjoint, then `π x (E_good-plane (T_p y))` is the dual
eigenvalue times `π x (E_good-plane y)`, with the edge formula
`E(T_p y) = E y + p^{-(n+2)} T_p E y`. -/
theorem goodPlane_pairing_eigen (n : ℕ) (hn : 0 < n) (p : Nat.Primes) (hp3 : p.val ≠ 3)
    (π : CrossedH1 (binaryArithmeticRepresentation n) →ₗ[ℂ]
      CrossedH1 (levelRep (n + 1) (-1)) →ₗ[ℂ] ℂ) (κ : Nat.Primes → ℂ)
    (hadj : LevelThreeHeckeAdjoint n π κ) (hκ : κ p ≠ 0)
    {x : CrossedH1 (binaryArithmeticRepresentation n)} (a s c : ℂ) (hs : s ≠ 0)
    (hx : a • x + s • badLevelHecke p hp3 n x = c • x)
    (η : CuspH2 n trivialCharacter .plane true) :
    π x (LevelThree.GoodPlaneEdge3.goodPlaneEdge hn
        (localOp n trivialCharacter (TpExistence.tp p) (TpExistence.tp_awayThree p hp3)
          .plane true η)) =
      dualEigenvalue a s 1 (((p.val : ℂ) ^ (n + 2))⁻¹) (κ p) c *
        π x (LevelThree.GoodPlaneEdge3.goodPlaneEdge hn η) :=
  pairing_eigen_of_edge π (badLevelHecke p hp3 n) (levelHecke (n + 1) (-1) p hp3) (κ p)
    (hadj p hp3) (LevelThree.GoodPlaneEdge3.goodPlaneEdge hn)
    (localOp n trivialCharacter (TpExistence.tp p) (TpExistence.tp_awayThree p hp3) .plane true)
    a s 1 (((p.val : ℂ) ^ (n + 2))⁻¹) c hs hκ
    (fun w => by
      rw [one_smul]
      exact LevelThree.GoodPlaneLocalOp.goodPlaneEdge_localOp_tp p hp3 n hn w)
    hx η

/-- **Identity-plane dual eigenvalue.** With the edge formula
`E(T_p y) = E y + p^{-(n+2)} T_p E y` into `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)` and a `κ_p`-adjoint
pairing against `H¹(GL₂(ℤ), Sym^{n+1})`. -/
theorem identityPlane_pairing_eigen (n : ℕ) (hn : 0 < n) (hodd : Odd n) (p : Nat.Primes)
    (hp3 : p.val ≠ 3)
    (π : groupCohomology.H1 (arithmeticBinaryRep (n + 1) 0) →ₗ[ℂ]
      groupCohomology.H1 (arithmeticBinaryRep (n + 1) (-1)) →ₗ[ℂ] ℂ) (κ : Nat.Primes → ℂ)
    (hadj : LevelOneHeckeAdjoint (n + 1) 0 (-1) π κ) (hκ : κ p ≠ 0)
    {x : groupCohomology.H1 (arithmeticBinaryRep (n + 1) 0)} (a s c : ℂ) (hs : s ≠ 0)
    (hx : a • x + s • LevelOneHeckeH1.arithmeticHecke (n + 1) 0 p x = c • x)
    (η : CuspH2 n trivialCharacter .plane false) :
    π x (IdentityPlaneHecke.edgeH2 n hn hodd
        (localOp n trivialCharacter (TpExistence.tp p) (TpExistence.tp_awayThree p hp3)
          .plane false η)) =
      dualEigenvalue a s 1 (((p.val : ℂ) ^ (n + 2))⁻¹) (κ p) c *
        π x (IdentityPlaneHecke.edgeH2 n hn hodd η) :=
  pairing_eigen_of_edge π (LevelOneHeckeH1.arithmeticHecke (n + 1) 0 p)
    (LevelOneHeckeH1.arithmeticHecke (n + 1) (-1) p) (κ p) (hadj p)
    (IdentityPlaneHecke.edgeH2 n hn hodd)
    (localOp n trivialCharacter (TpExistence.tp p) (TpExistence.tp_awayThree p hp3) .plane false)
    a s 1 (((p.val : ℂ) ^ (n + 2))⁻¹) c hs hκ
    (fun w => by
      rw [one_smul]
      exact IdentityPlaneLocalOp.edgeH2_localOp_tp p n hn hodd hp3 w)
    hx η

/-- **Twisted identity-plane dual eigenvalue** (odd conductor-3 character `χ`). The edge formula is
`E(T_p y) = sgn_p E y + p^{-(n+1)} T_p E y` into `H¹(GL₂(ℤ), Sym^{n+1})`, against a `κ_p`-adjoint
pairing with `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)`, where the sign-twisted good line lives. -/
theorem twistedIdentityPlane_pairing_eigen (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (hn : 0 < n) (hodd : Odd n) (p : Nat.Primes)
    (hp3 : p.val ≠ 3)
    (π : groupCohomology.H1 (arithmeticBinaryRep (n + 1) (-1)) →ₗ[ℂ]
      groupCohomology.H1 (arithmeticBinaryRep (n + 1) 0) →ₗ[ℂ] ℂ) (κ : Nat.Primes → ℂ)
    (hadj : LevelOneHeckeAdjoint (n + 1) (-1) 0 π κ) (hκ : κ p ≠ 0)
    {x : groupCohomology.H1 (arithmeticBinaryRep (n + 1) (-1))} (a s c : ℂ) (hs : s ≠ 0)
    (hx : a • x + s • LevelOneHeckeH1.arithmeticHecke (n + 1) (-1) p x = c • x)
    (η : CuspH2 n χ .plane false) :
    π x (Twisted.edgeH2T n χ hχ hn hodd
        (localOp n χ (TpExistence.tp p) (TpExistence.tp_awayThree p hp3) .plane false η)) =
      dualEigenvalue a s ((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ) (((p.val : ℂ) ^ (n + 1))⁻¹)
        (κ p) c * π x (Twisted.edgeH2T n χ hχ hn hodd η) :=
  pairing_eigen_of_edge π (LevelOneHeckeH1.arithmeticHecke (n + 1) (-1) p)
    (LevelOneHeckeH1.arithmeticHecke (n + 1) 0 p) (κ p) (hadj p)
    (Twisted.edgeH2T n χ hχ hn hodd)
    (localOp n χ (TpExistence.tp p) (TpExistence.tp_awayThree p hp3) .plane false)
    a s ((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ) (((p.val : ℂ) ^ (n + 1))⁻¹) c hs hκ
    (fun w => Twisted.edgeH2T_localOp_tp n χ hχ p hn hodd hp3 w) hx η

end TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointConcrete
