module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.L3Rep
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.L3Orbit

@[expose] public section


/-!
# The Fricke relations between the base cocycles of a crossed homomorphism of `Γ₁'(3)`

Let `x̂` be a crossed homomorphism of `Γ₁'(3)` for `Sym^m ⊗ det^e`, `x = x̂|_{Γ₁(3)}` its
restriction and `x' = baseCocycle x` the crossed homomorphism
`h ↦ ρ(α₀)⁻¹ x(δ(h, j₀))` of the stabilizer `H`.  Conjugation by the Fricke element
`g' = α₀⁻¹ s` relates `x'` and `x|_H`:

  `x' (Ω h) = ρ(g') x(h) - (ρ(Ω h) - 1) ρ(α₀)⁻¹ x̂(s)`        (`baseCocycle_Ω`).

Consequently (`relation_left`)  `F (x' (Ω h)) + (ρ h u - u) = x h`  with `F = ρ(g')⁻¹` and
`u = F ρ(α₀)⁻¹ x̂(s)`, and (`relation_right`)  `F' (x (Ω h)) = x' h + (ρ' h u' - u')` with
`F' = ρ'(g')` and `u' = ρ'(α₀)⁻¹ x̂(s)`.

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
open TripleModel LinearDuality CocycleBridge EpsilonSplit
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeH1 (rationalRho
  level_compat core_compat)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep coreRep)
open GeneralEisenstein

variable (m : ℕ) (e e' : ℤ) (p : Nat.Primes) (hp3 : p.val ≠ 3)

/-- The restriction of a function on `Γ₁'(3)` to `Γ₁(3)`. -/
def restr {V : Type} (x : binaryArithmeticLevel → V) : core → V := fun k => x k.1

theorem isCocycle_restr {x : binaryArithmeticLevel → Binary.HomogeneousPoly m}
    (hx : IsCocycle (levelRep m e) x) : IsCocycle (coreRep m e) (restr x) :=
  fun a b => hx a.1 b.1

theorem levelRep_apply (g : binaryArithmeticLevel) (v : Binary.HomogeneousPoly m) :
    levelRep m e g v = rationalRho m e (levelEmbed g) v := by
  rw [level_compat m e g]

theorem coreRep_apply (k : core) (v : Binary.HomogeneousPoly m) :
    coreRep m e k v = rationalRho m e (coreEmbed k) v := by
  rw [core_compat m e k]

theorem rho_alpha_inv_sF (v : Binary.HomogeneousPoly m) :
    rationalRho m e (heckeRep p (J0 p))⁻¹ (rationalRho m e (levelEmbed (sF p hp3)) v) =
      rationalRho m e (gP p hp3) v := by
  rw [← rep_mul_gP p hp3, ← rep_mul_apply (rationalRho m e), inv_mul_cancel_left]

theorem rho_alpha_inv_conj (h : HK p hp3) (v : Binary.HomogeneousPoly m) :
    rationalRho m e (heckeRep p (J0 p))⁻¹
        (rationalRho m e (levelEmbed (sF p hp3 * h.1.1 * (sF p hp3)⁻¹)) v) =
      rationalRho m e (coreEmbed ((Ω p hp3 h : HK p hp3) : core))
        (rationalRho m e (heckeRep p (J0 p))⁻¹ v) := by
  have hd : (((SK p hp3).delta ((Ω p hp3 h : HK p hp3) : core) (J0 p) : core) :
      binaryArithmeticLevel) = sF p hp3 * h.1.1 * (sF p hp3)⁻¹ := by
    rw [delta_eq, Ω_Ω, sInv_eq_inv]
  have e1 := embed_delta_stab (S := SK p hp3) (j₀ := J0 p) (Ω p hp3 h).2
  have e2 : levelEmbed (sF p hp3 * h.1.1 * (sF p hp3)⁻¹) =
      heckeRep p (J0 p) * coreEmbed ((Ω p hp3 h : HK p hp3) : core) * (heckeRep p (J0 p))⁻¹ := by
    rw [← hd]
    exact e1
  rw [e2, ← rep_mul_apply (rationalRho m e), ← rep_mul_apply (rationalRho m e)]
  have key : (heckeRep p (J0 p))⁻¹ * (heckeRep p (J0 p) * coreEmbed ((Ω p hp3 h : HK p hp3) : core) *
      (heckeRep p (J0 p))⁻¹) = coreEmbed ((Ω p hp3 h : HK p hp3) : core) * (heckeRep p (J0 p))⁻¹ := by
    group
  rw [key]

/-- **The Fricke relation for the base cocycle.** -/
theorem baseCocycle_Ω {x : binaryArithmeticLevel → Binary.HomogeneousPoly m}
    (hx : IsCocycle (levelRep m e) x) (h : HK p hp3) :
    baseCocycle (S := SK p hp3) (j₀ := J0 p) (A := Rep.of (coreRep m e)) (rationalRho m e)
        (restr x) (Ω p hp3 h) =
      rationalRho m e (gP p hp3) (x h.1.1) -
        (rationalRho m e (coreEmbed ((Ω p hp3 h : HK p hp3) : core)) - 1)
          (rationalRho m e (heckeRep p (J0 p))⁻¹ (x (sF p hp3))) := by
  have hd : (((SK p hp3).delta ((Ω p hp3 h : HK p hp3) : core) (J0 p) : core) :
      binaryArithmeticLevel) = sF p hp3 * h.1.1 * (sF p hp3)⁻¹ := by
    rw [delta_eq, Ω_Ω, sInv_eq_inv]
  unfold baseCocycle
  change rationalRho m e (heckeRep p (J0 p))⁻¹
    (x (((SK p hp3).delta ((Ω p hp3 h : HK p hp3) : core) (J0 p) : core) :
      binaryArithmeticLevel)) = _
  rw [hd, cocycle_conj hx (sF p hp3) h.1.1]
  simp only [map_add, map_sub, LinearMap.sub_apply, Module.End.one_apply, levelRep_apply]
  rw [rho_alpha_inv_sF, rho_alpha_inv_conj]
  abel

/-- The correction vector of the Fricke relation: `u = ρ(g')⁻¹ ρ(α₀)⁻¹ x̂(s)`. -/
def fricke_u {V : Type} [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin 2) ℚ) V)
    (x : binaryArithmeticLevel → V) : V :=
  σ (gP p hp3)⁻¹ (σ (heckeRep p (J0 p))⁻¹ (x (sF p hp3)))

/-- **First relation:** `F (x' (Ω h)) + (ρ h u - u) = x h`. -/
theorem relation_left {x : binaryArithmeticLevel → Binary.HomogeneousPoly m}
    (hx : IsCocycle (levelRep m e) x) (h : HK p hp3) :
    rationalRho m e (gP p hp3)⁻¹
        (baseCocycle (S := SK p hp3) (j₀ := J0 p) (A := Rep.of (coreRep m e)) (rationalRho m e)
          (restr x) (Ω p hp3 h)) +
      (ρH m e p hp3 h (fricke_u p hp3 (rationalRho m e) x) - fricke_u p hp3 (rationalRho m e) x) =
    x h.1.1 := by
  rw [baseCocycle_Ω m e p hp3 hx h]
  have hF := fricke_hF m e p hp3 h (rationalRho m e (heckeRep p (J0 p))⁻¹ (x (sF p hp3)))
  rw [ρH_apply] at hF
  have e1 : rationalRho m e (gP p hp3)⁻¹ (rationalRho m e (gP p hp3) (x h.1.1)) = x h.1.1 := by
    rw [← rep_mul_apply, inv_mul_cancel, map_one]; rfl
  simp only [map_sub, LinearMap.sub_apply, Module.End.one_apply, e1, hF, fricke_u, ρH_apply]
  abel

/-- **Second relation:** `F' (y (Ω h)) = y' h + (ρ' h u' - u')`. -/
theorem relation_right {y : binaryArithmeticLevel → Binary.HomogeneousPoly m}
    (hy : IsCocycle (levelRep m e') y) (h : HK p hp3) :
    rationalRho m e' (gP p hp3) (y (Ω p hp3 h).1.1) =
      baseCocycle (S := SK p hp3) (j₀ := J0 p) (A := Rep.of (coreRep m e')) (rationalRho m e')
          (restr y) h +
        (ρH m e' p hp3 h (rationalRho m e' (heckeRep p (J0 p))⁻¹ (y (sF p hp3))) -
          rationalRho m e' (heckeRep p (J0 p))⁻¹ (y (sF p hp3))) := by
  have := baseCocycle_Ω m e' p hp3 hy (Ω p hp3 h)
  rw [Ω_Ω] at this
  rw [this]
  simp only [ρH_apply, LinearMap.sub_apply, Module.End.one_apply]
  abel

end TernaryPeriodPolynomials.BoundaryDuality.AdjL3
