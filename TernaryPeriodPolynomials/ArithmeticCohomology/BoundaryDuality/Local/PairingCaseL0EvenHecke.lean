module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL0EvenHeckeAbs
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL0EvenIntertwine
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL0EvenPairing
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.BinaryCentralCoefficient

@[expose] public section


/-!
# The Hecke compatibility of the plane transport

The transport `planeTransportH1` of `H¹(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)` to `H¹(Γ₁'(3), Sym^{n+1})` along
the cusp-exchanging involution `α` and the coefficient comparison `E` intertwines the Hecke
operators up to the sign and the factor `p`:

  `T_p^{(0)} ∘ Θ = (ε_p / p) · Θ ∘ T_p^{(-1)}`        (`levelHecke_planeTransport`),

where `ε_p = ±1`, `ε_p ≡ p mod 3`.  This is the abstract statement `hecke_transportH1` for the
data

* `ι(α γ) = alHom ι(γ)`, `alHom x = δ x^{-T} δ⁻¹` (`levelEmbed_alpha`);
* `alHom α_j = (ε_p / p) · ι(u_j) α_{τ j}` (`alHom_heckeRep_exists`);
* `E Sym^{n+1}⊗det⁻¹(ι(u_j) α_{τ j}) = (ε_p / p) Sym^{n+1}(α_j) E` (`planeComparison_rep`), from
  `E (Sym^{n+1} ⊗ det⁻¹)(alHom x) = (Sym^{n+1} ⊗ det^{n+2})(x) E` (`planeComparison_alHom_det`) and
  the action of the central scalar `ε_p / p`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Even

open TernaryPeriodPolynomials.BoundaryDuality.Kostant (invT)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.IdentBad
  (alpha kap_alpha planeComparison planeComparison_intertwines)
open TernaryPeriodPolynomials.Spectral.LevelOneCosets
  (integralEmbed integralEmbed_val)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneFrame
  (del integralEmbed_kap)
open TernaryPeriodPolynomials.LevelThree.LevelThreeCosets
  (heckeRep signP signP_mul_self levelEmbed levelEmbed_apply levelEmbed_injective levelCosets
    levelCosets_rep)
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeH1
  (rationalRho level_compat levelHecke)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)

variable {n : ℕ}

/-! ### The cusp-exchanging involution as a conjugation -/

theorem integralEmbed_invT (γ : GL (Fin 2) ℤ) :
    integralEmbed (invT γ) = invTQ (integralEmbed γ) := by
  apply Units.ext
  rw [integralEmbed_val, invTQ_val, ← map_inv, integralEmbed_val]
  exact Matrix.transpose_map

/-- **`ι ∘ α = alHom ∘ ι`**. -/
theorem levelEmbed_alpha (g : binaryArithmeticLevel) :
    levelEmbed (alpha g) = alHom (levelEmbed g) := by
  have h := integralEmbed_kap (alpha g)
  rw [kap_alpha, integralEmbed_invT] at h
  rw [levelEmbed_apply, alHom_apply, levelEmbed_apply, h]
  group

/-! ### The action of the central scalar -/

/-- The scalar `ε_p / p` as a complex number. -/
def zC (p : Nat.Primes) : ℂ := (((signP p : ℤ) : ℂ)) / (p.val : ℂ)

theorem sigma_zP (m : ℕ) (e : ℤ) (p : Nat.Primes) (w : Binary.HomogeneousPoly m) :
    rationalRho m e (zP p) w = (((zC p) ^ 2) ^ e * (zC p)⁻¹ ^ m) • w := by
  change Binary.homogeneousAction m e
    (GeneralLinearGroup.map (algebraMap ℚ ℂ) (GeneralLinearGroup.scalar (Fin 2) (zUnit p))) w = _
  rw [GeneralLinearGroup.map_scalar,
    EisensteinGraph.StandardConstruction.BinaryCentralCoefficient.homogeneousAction_scalar]
  congr 2
  · simp [zC, zUnit]
  · simp [zC, zUnit]

theorem zC_ne_zero (p : Nat.Primes) : zC p ≠ 0 := by
  have hq : (p.val : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hε : ((signP p : ℤ) : ℂ) ≠ 0 := by
    have := signP_mul_self p
    intro h
    have h' : (((signP p : ℤ) : ℤ) : ℂ) * (((signP p : ℤ) : ℤ) : ℂ) = 1 := by exact_mod_cast this
    rw [h] at h'
    simp at h'
  exact div_ne_zero hε hq

theorem signC_sq (p : Nat.Primes) : ((signP p : ℤ) : ℂ) * ((signP p : ℤ) : ℂ) = 1 := by
  exact_mod_cast signP_mul_self p

/-- **The scalar identity**: `ε_p / p` times the scalar by which `ε_p / p` acts on
`Sym^{n+1} ⊗ det⁻¹` is `p^{n+2}` for even `n`. -/
theorem zC_mul_c0 (heven : Even n) (p : Nat.Primes) :
    zC p * (((zC p) ^ 2) ^ (-1 : ℤ) * (zC p)⁻¹ ^ (n + 1)) = (p.val : ℂ) ^ (n + 2) := by
  have hε := signC_sq p
  obtain ⟨k, hk⟩ := heven
  have hpow : ((signP p : ℤ) : ℂ) ^ (n + 2) = 1 := by
    have : n + 2 = 2 * (k + 1) := by omega
    rw [this, pow_mul, sq, hε, one_pow]
  have aux : ∀ a : ℂ, a ≠ 0 → a * ((a ^ 2)⁻¹ * a⁻¹ ^ (n + 1)) = a⁻¹ ^ (n + 2) := by
    intro a ha
    have hab : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
    rw [← inv_pow]
    linear_combination (a⁻¹ ^ (n + 2)) * hab
  rw [_root_.zpow_neg_one, aux _ (zC_ne_zero p), zC, inv_div, div_pow, hpow, div_one]

/-- **The comparison of a Hecke representative with the transported one.** -/
theorem planeComparison_rep (heven : Even n) (p : Nat.Primes) (j k : Option (Fin p.val))
    (u : binaryArithmeticLevel)
    (h : alHom (heckeRep p j) = zP p * (levelEmbed u * heckeRep p k))
    (v : Binary.HomogeneousPoly (n + 1)) :
    planeComparison n (rationalRho (n + 1) (-1) (levelEmbed u * heckeRep p k) v) =
      zC p • rationalRho (n + 1) 0 (heckeRep p j) (planeComparison n v) := by
  have h1 := planeComparison_alHom_det n (heckeRep p j) v
  have h2 : rationalRho (n + 1) (-1) (alHom (heckeRep p j)) v =
      (((zC p) ^ 2) ^ (-1 : ℤ) * (zC p)⁻¹ ^ (n + 1)) •
        rationalRho (n + 1) (-1) (levelEmbed u * heckeRep p k) v := by
    rw [h, map_mul, Module.End.mul_apply, sigma_zP]
  rw [h2, map_smul, AdjointLevelThree.det_heckeRep p j] at h1
  have ht : (((n + 1 : ℕ) : ℤ) - (-1)) = ((n + 2 : ℕ) : ℤ) := by push_cast; ring
  rw [ht, zpow_natCast] at h1
  have hc0 : (((zC p) ^ 2) ^ (-1 : ℤ) * (zC p)⁻¹ ^ (n + 1)) ≠ 0 := by
    have := zC_ne_zero p
    simp [this]
  have h3 : zC p * (((zC p) ^ 2) ^ (-1 : ℤ) * (zC p)⁻¹ ^ (n + 1)) = (p.val : ℂ) ^ (n + 2) :=
    zC_mul_c0 heven p
  have h6 : planeComparison n (rationalRho (n + 1) (-1) (levelEmbed u * heckeRep p k) v) =
      (((zC p) ^ 2) ^ (-1 : ℤ) * (zC p)⁻¹ ^ (n + 1))⁻¹ •
        ((((zC p) ^ 2) ^ (-1 : ℤ) * (zC p)⁻¹ ^ (n + 1)) •
          planeComparison n (rationalRho (n + 1) (-1) (levelEmbed u * heckeRep p k) v)) := by
    rw [inv_smul_smul₀ hc0]
  rw [h6, h1, smul_smul, ← h3]
  congr 1
  rw [mul_comm (zC p), ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]

/-- **The Hecke operators and the plane transport**: `T_p^{(0)} ∘ Θ = (ε_p / p) · Θ ∘ T_p^{(-1)}`
on `H¹(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)`, for even `n`. -/
theorem levelHecke_planeTransport (heven : Even n) (p : Nat.Primes) (hp3 : p.val ≠ 3)
    (y : CrossedH1 (levelRep (n + 1) (-1))) :
    levelHecke (n + 1) 0 p hp3 (planeTransportH1 heven y) =
      zC p • planeTransportH1 heven (levelHecke (n + 1) (-1) p hp3 y) := by
  choose τ u hτ using fun j => alHom_heckeRep_exists p hp3 j
  exact hecke_transportH1 (levelCosets p hp3) levelEmbed_injective (rationalRho (n + 1) (-1))
    (rationalRho (n + 1) 0) (levelRep (n + 1) (-1)) (binaryArithmeticRepresentation n)
    (level_compat (n + 1) (-1)) (level_compat (n + 1) 0) alpha alpha_mul (planeComparison n)
    (planeComparison_intertwines n heven) alHom levelEmbed_alpha alHom_alHom (zP p)
    (zP_central p) τ u hτ (zC p)
    (fun j v => planeComparison_rep heven p j (τ j) (u j) (hτ j) v) y

/-! ### The adjointness of the even pairing from the plain adjointness -/

open TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointLevi (IsHeckeAdjoint)
open TernaryPeriodPolynomials.BoundaryDuality.AdjointLevelThree
  (parabolicHecke parabolicHecke_coe levelThreeKappa)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree
  (parabolicCrossedH1 parabolicPairing twistedPairing_binaryArithmeticRepresentation)

/-- **The plain Hecke adjointness (E1)** of the cup pairing of `H¹_par(Γ₁'(3), Sym^{n+1})` with
itself: `⟨T_p x, y⟩ = ε_p ⟨x, T_p y⟩`, `ε_p = ±1 ≡ p mod 3`, for all primes `p ≠ 3`. -/
def PlainEvenHeckeAdjoint (heven : Even n) : Prop :=
  ∀ (p : Nat.Primes) (hp3 : p.val ≠ 3),
    IsHeckeAdjoint (parabolicPairing (twistedPairing_binaryArithmeticRepresentation n heven))
      (parabolicHecke (n + 1) 0 p hp3) (parabolicHecke (n + 1) 0 p hp3) ((signP p : ℤ) : ℂ)

/-- **The parabolic Hecke operator and the plane transport** (the parabolic form of
`levelHecke_planeTransport`). -/
theorem parabolicHecke_planeTransportPar (heven : Even n) (p : Nat.Primes) (hp3 : p.val ≠ 3)
    (y : parabolicCrossedH1 (levelRep (n + 1) (-1))) :
    parabolicHecke (n + 1) 0 p hp3 (planeTransportPar heven y) =
      zC p • planeTransportPar heven (parabolicHecke (n + 1) (-1) p hp3 y) := by
  apply Subtype.ext
  exact levelHecke_planeTransport heven p hp3 y.1

/-- **`BadGoodHeckeAdjointEven` from the plain adjointness**: with `E1` (`ε_p`-adjointness of the
plain pairing) and `E2` (`levelHecke_planeTransport`, the factor `ε_p / p`), the pairing
`badGoodPairingEven` is `p⁻¹`-adjoint. -/
theorem badGoodHeckeAdjointEven_of_plain (heven : Even n) (h : PlainEvenHeckeAdjoint heven) :
    BadGoodHeckeAdjointEven heven := by
  intro p hp3 x y
  have hε := signC_sq p
  have hq : (p.val : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have e1 := h p hp3 x (planeTransportPar heven y)
  have e2 := parabolicHecke_planeTransportPar heven p hp3 y
  have e3 := congrArg
    (fun z => parabolicPairing (twistedPairing_binaryArithmeticRepresentation n heven) x z) e2
  simp only [map_smul, smul_eq_mul] at e3
  have e4 := congrArg (fun t => ((signP p : ℤ) : ℂ) * t) e3
  refine e1.trans (e4.trans ?_)
  change ((signP p : ℤ) : ℂ) * (zC p * parabolicPairing
    (twistedPairing_binaryArithmeticRepresentation n heven) x
      (planeTransportPar heven (parabolicHecke (n + 1) (-1) p hp3 y))) =
    levelThreeKappa p * parabolicPairing (twistedPairing_binaryArithmeticRepresentation n heven) x
      (planeTransportPar heven (parabolicHecke (n + 1) (-1) p hp3 y))
  rw [levelThreeKappa, zC]
  field_simp
  linear_combination (parabolicPairing (twistedPairing_binaryArithmeticRepresentation n heven) x
    (planeTransportPar heven (parabolicHecke (n + 1) (-1) p hp3 y))) * hε

end TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Even

end
