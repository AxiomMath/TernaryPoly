module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.L3Fricke
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.L3CosetsPairing
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.L3Hecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.L3Para

@[expose] public section


/-!
# The Fricke element acting on the coefficients `Sym^m ⊗ det^e`

With `g' = gP ∈ GL₂(ℚ)` (`g'² = (ε/p) · 1`), `F = ρ_e(g')⁻¹`, `F' = ρ_{e'}(g')` and `Ω` the
conjugation by `g'` on the stabilizer `H` of the base coset, the hypotheses of the transport lemmas
of `AdjL3Transport` hold with the constant `κΩ = frickeKappa p m e e'`
(`AdjL3Cosets.pairing_fricke`):

  `F (ρ(Ω a) v) = ρ(a) (F v)`, `F' (ρ'(Ω a) w) = ρ'(a) (F' w)`,
  `⟨F v, ρ'(a) F' w⟩ = κΩ ⟨v, ρ'(Ω a) w⟩`     (`fricke_hF`, `fricke_hF'`, `fricke_hcomp`).

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
  level_compat core_compat)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep coreRep)
open GeneralEisenstein
open TripleModel LinearDuality CocycleBridge EpsilonSplit

variable (m : ℕ) (e e' : ℤ) (p : Nat.Primes) (hp3 : p.val ≠ 3)

/-- The restriction of the representation `Sym^m ⊗ det^e` of `Γ₁(3)` to the stabilizer `H`. -/
abbrev ρH : Representation ℂ (HK p hp3) (Binary.HomogeneousPoly m) :=
  (coreRep m e).comp (HK p hp3).subtype

theorem ρH_apply (a : HK p hp3) (v : Binary.HomogeneousPoly m) :
    ρH m e p hp3 a v = rationalRho m e (coreEmbed (a : core)) v := by
  change coreRep m e (a : core) v = _
  rw [core_compat m e (a : core)]

theorem embed_Ω' (a : HK p hp3) :
    coreEmbed ((Ω p hp3 a : HK p hp3) : core) =
      (gP p hp3)⁻¹ * coreEmbed (a : core) * gP p hp3 := by
  rw [embed_Ω, conj_gP_eq]

/-- `F (ρ(Ω a) v) = ρ(a) (F v)` for `F = ρ_e(g')⁻¹`. -/
theorem fricke_hF (a : HK p hp3) (v : Binary.HomogeneousPoly m) :
    rationalRho m e (gP p hp3)⁻¹ (ρH m e p hp3 (Ω p hp3 a) v) =
      ρH m e p hp3 a (rationalRho m e (gP p hp3)⁻¹ v) := by
  rw [ρH_apply, ρH_apply, embed_Ω, ← rep_mul_apply (rationalRho m e),
    ← rep_mul_apply (rationalRho m e)]
  have key : (gP p hp3)⁻¹ * (gP p hp3 * coreEmbed (a : core) * (gP p hp3)⁻¹) =
      coreEmbed (a : core) * (gP p hp3)⁻¹ := by group
  rw [key]

/-- `F' (ρ'(Ω a) w) = ρ'(a) (F' w)` for `F' = ρ_{e'}(g')`. -/
theorem fricke_hF' (a : HK p hp3) (w : Binary.HomogeneousPoly m) :
    rationalRho m e' (gP p hp3) (ρH m e' p hp3 (Ω p hp3 a) w) =
      ρH m e' p hp3 a (rationalRho m e' (gP p hp3) w) := by
  rw [ρH_apply, ρH_apply, embed_Ω', ← rep_mul_apply (rationalRho m e'),
    ← rep_mul_apply (rationalRho m e')]
  have key : gP p hp3 * ((gP p hp3)⁻¹ * coreEmbed (a : core) * gP p hp3) =
      coreEmbed (a : core) * gP p hp3 := by group
  rw [key]

include hp3 in
/-- **The pairing against the Fricke element.** -/
theorem fricke_hcomp (a : HK p hp3) (v w : Binary.HomogeneousPoly m) :
    BinaryPairing.binaryPairing m (rationalRho m e (gP p hp3)⁻¹ v)
        (ρH m e' p hp3 a (rationalRho m e' (gP p hp3) w)) =
      frickeKappa p m e e' *
        BinaryPairing.binaryPairing m v (ρH m e' p hp3 (Ω p hp3 a) w) := by
  have h1 : ρH m e' p hp3 a (rationalRho m e' (gP p hp3) w) =
      rationalRho m e' (gP p hp3) (ρH m e' p hp3 (Ω p hp3 a) w) :=
    (fricke_hF' m e' p hp3 a w).symm
  rw [h1]
  exact pairing_fricke p hp3 m e e' v _

end TernaryPeriodPolynomials.BoundaryDuality.AdjL3
