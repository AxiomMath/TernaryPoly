module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.L3Core

@[expose] public section


/-!
# The values of the cup pairing against the Hecke cocycles

For a pair `D = (x̂, ŷ)` of parabolic crossed homomorphisms of `Γ₁'(3)` normalized to vanish at
`L` (`Data`), this file computes, in terms of local terms of cup primitives on the stabilizer `H`
of the base coset,

* `lhs_value`: the cup formula of `(T x, y)`;
* `rhs_value`: the cup formula of `(x, T y)`;

as sums over the four cusp elements `T^p`, `r_∞ T r_∞⁻¹`, `L`, `r_∞ L^p r_∞⁻¹` of `H`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.AdjL3

open Matrix
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators
open TernaryPeriodPolynomials.Spectral.HeckeH1
open TernaryPeriodPolynomials.LevelThree.LevelThreeCosets
open TernaryPeriodPolynomials.LevelThree.GammaOneThree
open TernaryPeriodPolynomials.BoundaryDuality.AdjL3Cosets
open TernaryPeriodPolynomials.BoundaryDuality.AdjCore
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeH1 (rationalRho
  level_compat core_compat crossedHeckeFun_mem)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep coreRep)
open GeneralEisenstein
open TripleModel LinearDuality CocycleBridge EpsilonSplit

/-- The pairing of binary forms of degree `m`. -/
abbrev Bm (m : ℕ) : Binary.HomogeneousPoly m →ₗ[ℂ] Binary.HomogeneousPoly m →ₗ[ℂ] ℂ :=
  BinaryPairing.binaryPairing m

/-- **A pair of parabolic crossed homomorphisms of `Γ₁'(3)`, normalized to vanish at `L`.** -/
structure Data (m : ℕ) (e e' : ℤ) where
  /-- The crossed homomorphism for `Sym^m ⊗ det^e`. -/
  x : binaryArithmeticLevel → Binary.HomogeneousPoly m
  /-- The crossed homomorphism for `Sym^m ⊗ det^{e'}`. -/
  y : binaryArithmeticLevel → Binary.HomogeneousPoly m
  hx : IsCocycle (levelRep m e) x
  hy : IsCocycle (levelRep m e') y
  hxT : CobAt (levelRep m e) x (upper 1)
  hyT : CobAt (levelRep m e') y (upper 1)
  hxL : x (lower 1) = 0
  hyL : y (lower 1) = 0

section Invariance

variable (m : ℕ) (e e' : ℤ)

/-- The pairing of binary forms is invariant under `Γ₁(3)`. -/
theorem hinvK (k : core) (v w : Binary.HomogeneousPoly m) :
    Bm m (coreRep m e k v) (coreRep m e' k w) = Bm m v w :=
  BinaryPairing.binaryPairing_homogeneousAction_of_det_eq_one m e e'
    (binaryIntegralComplex (k : binaryArithmeticLevel).val)
    (Units.ext (ParabolicDuality.LevelThree.complex_det_core k)) v w

end Invariance

section Values

variable {m : ℕ} {e e' : ℤ} (D : Data m e e') (p : Nat.Primes) (hp3 : p.val ≠ 3)

/-- The base cocycle of `x`. -/
def xBase : HK p hp3 → Binary.HomogeneousPoly m :=
  baseCocycle (S := SK p hp3) (j₀ := J0 p) (A := Rep.of (coreRep m e)) (rationalRho m e)
    (restr D.x)

/-- The base cocycle of `y`. -/
def yBase : HK p hp3 → Binary.HomogeneousPoly m :=
  baseCocycle (S := SK p hp3) (j₀ := J0 p) (A := Rep.of (coreRep m e')) (rationalRho m e')
    (restr D.y)

/-- The Hecke cocycle `T x` of `Γ₁(3)`. -/
def hX : core → Binary.HomogeneousPoly m :=
  heckeFun (SK p hp3) (Rep.of (coreRep m e)) (rationalRho m e) (restr D.x)

/-- The Hecke cocycle `T y` of `Γ₁(3)`. -/
def hY : core → Binary.HomogeneousPoly m :=
  heckeFun (SK p hp3) (Rep.of (coreRep m e')) (rationalRho m e') (restr D.y)

theorem isCocycle_hX : IsCocycle (coreRep m e) (hX D p hp3) := by
  have := crossedHeckeFun_mem (SK p hp3) (rationalRho m e) (coreRep m e) (core_compat m e)
    coreEmbed_injective ⟨restr D.x, isCocycle_restr m e D.hx⟩
  exact this

theorem isCocycle_hY : IsCocycle (coreRep m e') (hY D p hp3) := by
  have := crossedHeckeFun_mem (SK p hp3) (rationalRho m e') (coreRep m e') (core_compat m e')
    coreEmbed_injective ⟨restr D.y, isCocycle_restr m e' D.hy⟩
  exact this

/-- **The adjointness statement at the level of `Γ₁(3)`** (proved in `AdjL3Final`): for every pair of
normalized parabolic crossed homomorphisms and every pair of primitive triples, the cup formula of
`(T x, y)` is `κ` times the cup formula of `(x, T y)`. -/
def CoreAdjoint (m : ℕ) (e e' : ℤ) (p : Nat.Primes) (hp3 : p.val ≠ 3) (κ : ℂ) : Prop :=
  ∀ (D : Data m e e')
    {v : Binary.HomogeneousPoly m × Binary.HomogeneousPoly m × Binary.HomogeneousPoly m}
    (_ : IsPrimitive (coreRep m e) coreT coreL⁻¹ (hX D p hp3) v)
    {w : Binary.HomogeneousPoly m × Binary.HomogeneousPoly m × Binary.HomogeneousPoly m}
    (_ : IsPrimitive (coreRep m e) coreT coreL⁻¹ (restr D.x) w)
    (_ : CobAt (coreRep m e') (hY D p hp3) coreL),
    cupFormula (Bm m) (coreRep m e') coreT coreL⁻¹ (hX D p hp3) (restr D.y) v =
      κ * cupFormula (Bm m) (coreRep m e') coreT coreL⁻¹ (restr D.x) (hY D p hp3) w

end Values

end TernaryPeriodPolynomials.BoundaryDuality.AdjL3
