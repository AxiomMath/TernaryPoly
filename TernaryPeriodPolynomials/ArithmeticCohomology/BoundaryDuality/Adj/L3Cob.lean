module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.L3Value

@[expose] public section


/-!
# Coboundary values of parabolic crossed homomorphisms at the cusp elements of `H`

A parabolic crossed homomorphism `z` of `Γ₁'(3)` takes coboundary values at every conjugate of every
power of `T` and `L`.  For the four cusp elements `T^p`, `r_∞ T r_∞⁻¹`, `L`, `r_∞ L^p r_∞⁻¹` of the
stabilizer `H` of the base coset this gives coboundary values of `z` at the element itself and at
its transition `δ(h, j₀) = s Ω(h) s⁻¹` (`Para.four`); `baseCocycle_cobAt` turns the latter into a
coboundary value of the base cocycle.

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

section Para

variable {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ binaryArithmeticLevel V}
  {z : binaryArithmeticLevel → V}

theorem cob_upper (hz : IsCocycle ρ z) (hT : CobAt ρ z (upper 1)) (k : binaryArithmeticLevel)
    (n : ℤ) : CobAt ρ z (k * upper n * k⁻¹) := by
  rw [upper_zpow n]
  exact (hT.zpow hz n).conj hz k

theorem cob_lower (hz : IsCocycle ρ z) (hL : CobAt ρ z (lower 1)) (k : binaryArithmeticLevel)
    (n : ℤ) : CobAt ρ z (k * lower n * k⁻¹) := by
  rw [lower_zpow n]
  exact (hL.zpow hz n).conj hz k

variable (p : Nat.Primes) (hp3 : p.val ≠ 3)

/-- The transition `δ(h, j₀)` of an element of `H` at the base coset. -/
def deltaE (h : HK p hp3) : binaryArithmeticLevel :=
  sF p hp3 * ((Ω p hp3 h : HK p hp3) : binaryArithmeticLevel) * sInv p hp3

theorem deltaE_eq (h : HK p hp3) :
    (((SK p hp3).delta (h : core) (J0 p) : core) : binaryArithmeticLevel) = deltaE p hp3 h :=
  delta_eq p hp3 h

theorem deltaE_TpK : deltaE p hp3 (TpK p hp3) = upper 1 := by
  rw [deltaE, Ω_TpK_val, sF_eq_inv]
  group

theorem deltaE_LK : deltaE p hp3 (LK p hp3) = lower (p.val : ℤ) := by
  rw [deltaE, Ω_LK_val, sF_eq_inv]
  group

theorem deltaE_tK2 :
    (eps p = -1 ∧ deltaE p hp3 (tK2 p hp3) = sF p hp3 * upper (p.val : ℤ) * (sF p hp3)⁻¹) ∨
      (eps p = 1 ∧ deltaE p hp3 (tK2 p hp3) = sF p hp3 * upper (-(p.val : ℤ)) * (sF p hp3)⁻¹) := by
  rcases Ω_tK2 p hp3 with ⟨he, h⟩ | ⟨he, h⟩
  · left
    refine ⟨he, ?_⟩
    rw [deltaE, h, TpK_val, sInv_eq_inv]
  · right
    refine ⟨he, ?_⟩
    rw [deltaE, h, Subgroup.coe_inv, Subgroup.coe_inv, TpK_val, sInv_eq_inv]
    have : upper (-(p.val : ℤ)) = (upper (p.val : ℤ))⁻¹ := by
      rw [upper_zpow (-(p.val : ℤ)), upper_zpow (p.val : ℤ), _root_.zpow_neg]
    rw [this]

theorem deltaE_tL2 :
    (eps p = -1 ∧ deltaE p hp3 (tL2 p hp3) = sF p hp3 * lower 1 * (sF p hp3)⁻¹) ∨
      (eps p = 1 ∧ deltaE p hp3 (tL2 p hp3) = sF p hp3 * lower (-1) * (sF p hp3)⁻¹) := by
  rcases Ω_tL2 p hp3 with ⟨he, h⟩ | ⟨he, h⟩
  · left
    refine ⟨he, ?_⟩
    rw [deltaE, h, LK_val, sInv_eq_inv]
  · right
    refine ⟨he, ?_⟩
    rw [deltaE, h, Subgroup.coe_inv, Subgroup.coe_inv, LK_val, sInv_eq_inv]
    have : lower (-1 : ℤ) = (lower 1)⁻¹ := by
      rw [lower_zpow (-1), lower_zpow 1, _root_.zpow_neg_one, zpow_one]
    rw [this]

/-- The cusp elements and their transitions carry coboundary values of a parabolic cocycle. -/
theorem Para.four (hz : IsCocycle ρ z) (hT : CobAt ρ z (upper 1)) (hL : CobAt ρ z (lower 1)) :
    CobAt ρ z (TpK p hp3).1.1 ∧ CobAt ρ z (tK2 p hp3).1.1 ∧ CobAt ρ z (LK p hp3).1.1 ∧
      CobAt ρ z (tL2 p hp3).1.1 ∧ CobAt ρ z (deltaE p hp3 (TpK p hp3)) ∧
      CobAt ρ z (deltaE p hp3 (tK2 p hp3)) ∧ CobAt ρ z (deltaE p hp3 (LK p hp3)) ∧
      CobAt ρ z (deltaE p hp3 (tL2 p hp3)) := by
  have hU : ∀ k n, CobAt ρ z (k * upper n * k⁻¹) := fun k n => cob_upper hz hT k n
  have hLo : ∀ k n, CobAt ρ z (k * lower n * k⁻¹) := fun k n => cob_lower hz hL k n
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := hU 1 (p.val : ℤ)
    rw [one_mul, inv_one, mul_one] at this
    rw [show (TpK p hp3).1.1 = upper (p.val : ℤ) from TpK_val p hp3]
    exact this
  · rw [show (tK2 p hp3).1.1 = _ from tK2_val p hp3]
    have := hU (sInv p hp3) (if eps p = 1 then -1 else 1)
    rw [sInv_eq_inv, inv_inv] at this
    rw [sInv_eq_inv]
    exact this
  · have := hLo 1 1
    rw [one_mul, inv_one, mul_one] at this
    rw [show (LK p hp3).1.1 = lower 1 from LK_val p hp3]
    exact this
  · rw [show (tL2 p hp3).1.1 = _ from tL2_val p hp3]
    have := hLo (sInv p hp3) (if eps p = 1 then -(p.val : ℤ) else (p.val : ℤ))
    rw [sInv_eq_inv, inv_inv] at this
    rw [sInv_eq_inv]
    exact this
  · rw [deltaE_TpK]; exact hT
  · rcases deltaE_tK2 p hp3 with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h]
    · exact hU _ _
    · exact hU _ _
  · rw [deltaE_LK]
    have := hLo 1 (p.val : ℤ)
    rw [one_mul, inv_one, mul_one] at this
    exact this
  · rcases deltaE_tL2 p hp3 with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h]
    · exact hLo _ _
    · exact hLo _ _

end Para

section BaseCob

variable {m : ℕ} (e : ℤ) (p : Nat.Primes) (hp3 : p.val ≠ 3)

/-- **A coboundary value at the transition gives a coboundary value of the base cocycle.** -/
theorem baseCocycle_cobAt {z : binaryArithmeticLevel → Binary.HomogeneousPoly m} (h : HK p hp3)
    {u : Binary.HomogeneousPoly m}
    (hu : z (deltaE p hp3 h) = (levelRep m e (deltaE p hp3 h) - 1) u) :
    baseCocycle (S := SK p hp3) (j₀ := J0 p) (A := Rep.of (coreRep m e)) (rationalRho m e)
        (restr z) h =
      (ρH m e p hp3 h - 1) (rationalRho m e (heckeRep p (J0 p))⁻¹ u) := by
  have e1 := embed_delta_stab (S := SK p hp3) (j₀ := J0 p) h.2
  have e2 : levelEmbed (deltaE p hp3 h) =
      heckeRep p (J0 p) * coreEmbed (h : core) * (heckeRep p (J0 p))⁻¹ := by
    rw [← deltaE_eq]
    exact e1
  unfold baseCocycle
  change rationalRho m e (heckeRep p (J0 p))⁻¹
    (z (((SK p hp3).delta (h : core) (J0 p) : core) : binaryArithmeticLevel)) = _
  rw [deltaE_eq, hu]
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, ρH_apply]
  rw [show levelRep m e (deltaE p hp3 h) u = rationalRho m e (levelEmbed (deltaE p hp3 h)) u from
    by rw [level_compat m e], e2, ← rep_mul_apply (rationalRho m e),
    ← rep_mul_apply (rationalRho m e)]
  have key : (heckeRep p (J0 p))⁻¹ * (heckeRep p (J0 p) * coreEmbed (h : core) *
      (heckeRep p (J0 p))⁻¹) = coreEmbed (h : core) * (heckeRep p (J0 p))⁻¹ := by group
  rw [key]

end BaseCob

end TernaryPeriodPolynomials.BoundaryDuality.AdjL3
