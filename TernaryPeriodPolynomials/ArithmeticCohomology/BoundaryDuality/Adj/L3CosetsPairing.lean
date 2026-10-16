module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.L3CosetsExtra
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.BinaryPairing
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.HeckeH1
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.Action

@[expose] public section


/-!
# The pairing of binary forms against the Fricke element `g'`

For `g' = gP = α₀⁻¹ s ∈ GL₂(ℚ)` (`g'² = (ε/p) · 1`, `det g' = -ε/p`) and the representation
`rationalRho m e` of `GL₂(ℚ)` on `Sym^m ⊗ det^e`, the pairing of binary forms satisfies

  `⟨σ_e(g'⁻¹) v, σ_{e'}(g') w⟩ = κ ⟨v, w⟩`,
  `κ = frickeKappa p m e e' = (-(p ε))^(e + e' - m) · (p ε)^(m - 2 e')`

(`pairing_fricke`).  This is the hypothesis `hW` of the generic Fricke lemma.  In modulus,
`κ = p^(e - e')`; the sign is `(-1)^(m - e - e') ε^(e' - e)`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.AdjL3Cosets

open Matrix GeneralEisenstein
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeH1 (rationalRho)
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers

variable (p : Nat.Primes) (hp3 : p.val ≠ 3)

/-- **The Fricke scalar** `κ = (-(p ε))^(e + e' - m) · (p ε)^(m - 2 e')`. -/
def frickeKappa (m : ℕ) (e e' : ℤ) : ℂ :=
  (-((p.val : ℂ) * ((eps p : ℤ) : ℂ))) ^ (e + e' - (m : ℤ)) *
    (((p.val : ℂ) * ((eps p : ℤ) : ℂ))) ^ ((m : ℤ) - 2 * e')

theorem frickeKappa_ne_zero (m : ℕ) (e e' : ℤ) : frickeKappa p m e e' ≠ 0 := by
  have he : ((eps p : ℤ) : ℂ) ≠ 0 := by
    intro h
    have h2 : ((eps p : ℤ) : ℂ) * ((eps p : ℤ) : ℂ) = 1 := by exact_mod_cast eps_mul_self p
    rw [h, zero_mul] at h2
    exact zero_ne_one h2
  have hp : (p.val : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hpe : (p.val : ℂ) * ((eps p : ℤ) : ℂ) ≠ 0 := mul_ne_zero hp he
  exact mul_ne_zero (zpow_ne_zero _ (neg_ne_zero.mpr hpe)) (zpow_ne_zero _ hpe)

theorem eps_ne_zero_C : ((eps p : ℤ) : ℂ) ≠ 0 := by
  intro h
  have h2 : ((eps p : ℤ) : ℂ) * ((eps p : ℤ) : ℂ) = 1 := by exact_mod_cast eps_mul_self p
  rw [h, zero_mul] at h2
  exact zero_ne_one h2

theorem prime_ne_zero_C : (p.val : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero

/-- Arithmetic of the Fricke scalar. -/
theorem kappa_arith (m : ℕ) (e e' : ℤ) :
    (-(((eps p : ℤ) : ℂ) / (p.val : ℂ)))⁻¹ ^ (e + e' - (m : ℤ)) *
        ((((eps p : ℤ) : ℂ) / (p.val : ℂ)) ^ (2 * e') *
          ((((eps p : ℤ) : ℂ) / (p.val : ℂ))⁻¹) ^ m) = frickeKappa p m e e' := by
  have he : ((eps p : ℤ) : ℂ) * ((eps p : ℤ) : ℂ) = 1 := by exact_mod_cast eps_mul_self p
  have hp := prime_ne_zero_C p
  have hE := eps_ne_zero_C p
  have hpe : (p.val : ℂ) * ((eps p : ℤ) : ℂ) ≠ 0 := mul_ne_zero hp hE
  have h1 : (-(((eps p : ℤ) : ℂ) / (p.val : ℂ)))⁻¹ = -((p.val : ℂ) * ((eps p : ℤ) : ℂ)) := by
    field_simp
    linear_combination he
  have h2 : (((eps p : ℤ) : ℂ) / (p.val : ℂ)) = ((p.val : ℂ) * ((eps p : ℤ) : ℂ))⁻¹ := by
    symm
    apply inv_eq_of_mul_eq_one_right
    calc ((p.val : ℂ) * ((eps p : ℤ) : ℂ)) * (((eps p : ℤ) : ℂ) / (p.val : ℂ))
        = (((eps p : ℤ) : ℂ) * ((eps p : ℤ) : ℂ)) * ((p.val : ℂ) / (p.val : ℂ)) := by ring
      _ = 1 := by rw [he, div_self hp, one_mul]
  rw [frickeKappa, h1, h2, inv_inv]
  congr 1
  rw [_root_.inv_zpow', ← zpow_natCast, ← zpow_add₀ hpe]
  congr 1
  ring

include hp3 in
/-- **The pairing of binary forms against the Fricke element.** -/
theorem pairing_fricke (m : ℕ) (e e' : ℤ) (v w : Binary.HomogeneousPoly m) :
    BinaryPairing.binaryPairing m (rationalRho m e (gP p hp3)⁻¹ v) (rationalRho m e' (gP p hp3) w) =
      frickeKappa p m e e' * BinaryPairing.binaryPairing m v w := by
  have hp := prime_ne_zero_C p
  have hE := eps_ne_zero_C p
  have hzne : ((eps p : ℤ) : ℂ) / (p.val : ℂ) ≠ 0 := div_ne_zero hE hp
  set g := gP p hp3 with hg
  set G : GL (Fin 2) ℂ := Matrix.GeneralLinearGroup.map (algebraMap ℚ ℂ) g with hG
  have hGG : G * G = GeneralLinearGroup.scalar (Fin 2)
      (Units.mk0 (((eps p : ℤ) : ℂ) / (p.val : ℂ)) hzne) := by
    rw [hG, ← map_mul, hg, gP_mul_gP p hp3, GeneralLinearGroup.map_scalar]
    congr 1
    apply Units.ext
    simp
  have hdet : ((GeneralLinearGroup.det G : ℂˣ) : ℂ) = -((eps p : ℤ) : ℂ) / (p.val : ℂ) := by
    have h := val_det_gP p hp3
    rw [hG, GeneralLinearGroup.val_det_apply]
    change ((algebraMap ℚ ℂ).mapMatrix (g : Matrix (Fin 2) (Fin 2) ℚ)).det = _
    rw [← RingHom.map_det, ← GeneralLinearGroup.val_det_apply, hg, h]
    simp
  have h1 : rationalRho m e g⁻¹ v = Binary.homogeneousAction m e G⁻¹ v := by
    show Binary.homogeneousAction m e (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℂ) g⁻¹) v = _
    rw [map_inv]
  have h2 : rationalRho m e' g w = Binary.homogeneousAction m e' G w := rfl
  rw [h1, h2]
  have hsc : Binary.homogeneousAction m e' (G * G) w =
      (((((eps p : ℤ) : ℂ) / (p.val : ℂ)) ^ (2 * e') *
        ((((eps p : ℤ) : ℂ) / (p.val : ℂ))⁻¹) ^ m) • w) := by
    rw [hGG, binary_homogeneous_action_scalar]
    rfl
  have hback : Binary.homogeneousAction m e' G⁻¹ (Binary.homogeneousAction m e' (G * G) w) =
      Binary.homogeneousAction m e' G w := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_left]
  have key := BinaryPairing.binaryPairing_homogeneousAction m e e' G⁻¹ v
    (Binary.homogeneousAction m e' (G * G) w)
  rw [hback] at key
  rw [key, hsc, map_smul, smul_eq_mul]
  have hdet' : ((GeneralLinearGroup.det G⁻¹ : ℂˣ) : ℂ) =
      (-(((eps p : ℤ) : ℂ) / (p.val : ℂ)))⁻¹ := by
    rw [map_inv, Units.val_inv_eq_inv_val, hdet, neg_div]
  rw [hdet', ← kappa_arith p m e e']
  ring

end TernaryPeriodPolynomials.BoundaryDuality.AdjL3Cosets
