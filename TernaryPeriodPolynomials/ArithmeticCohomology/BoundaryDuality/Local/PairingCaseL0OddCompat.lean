module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL0OddTilde
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL0OddIntertwine

@[expose] public section


/-!
# Compatibility of the comparison map with the Hecke cosets

Let `σ = rationalRho (n + 1) (-1)`, `E = planeE n` and `tilde h = δ (h⁻¹)ᵀ δ⁻¹`.

* `tilde_tilde`, `tilde_zUnit`: `tilde` is an involution and inverts the central element `z`;
* `planeE_rho_integral`: for odd `n`, `E` intertwines `σ(ι g)` and `σ(tilde ι g)` for `g ∈ GL₂(ℤ)`;
* `compat_at_coset`: on a Hecke coset `tilde α_j = z · γ_j · α_{π j}`,
  `σ(α_j)⁻¹ E σ(γ_j) = E σ(α_{π j})⁻¹`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein Matrix

namespace TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0OddCompat

open TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0OddTilde
  (invTG invTG_val invTG_mul invTG_one map_invTG tilde tilde_apply zUnit zUnit_val zUnit_comm
    piEquiv)
open TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0OddIntertwine
  (cQ planeE tw planeE_rho_tilde invTG_del_inv)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneFrame (del del_val del_inv_val)
open TernaryPeriodPolynomials.LevelThree.LevelThreeCosets
  (heckeRep heckeRep_val N N_det signP signP_mul_self levelEmbed levelEmbed_apply)
open TernaryPeriodPolynomials.LevelThree.LevelThreeHeckeH1 (rationalRho)
open TernaryPeriodPolynomials.Spectral.LevelOneCosets (integralEmbed)
open TernaryPeriodPolynomials.BoundaryDuality.Kostant (homogeneousAction_zpow_twist)
open TernaryPeriodPolynomials.SphericalDetection.Helpers (binary_homogeneousAction_scalar)
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
  (binaryArithmeticLevel)

variable {n : ℕ}

section Involution

theorem invTG_invTG {R : Type*} [CommRing R] (h : GL (Fin 2) R) : invTG (invTG h) = h :=
  Units.ext (Matrix.transpose_transpose h.val)

theorem invTG_del : invTG (del : GL (Fin 2) ℚ) = del⁻¹ := by
  have h := congrArg invTG invTG_del_inv
  rw [invTG_invTG] at h
  exact h.symm

/-- `tilde` is an involution. -/
theorem tilde_tilde (h : GL (Fin 2) ℚ) : tilde (tilde h) = h := by
  change del * invTG (del * invTG h * del⁻¹) * del⁻¹ = h
  rw [invTG_mul, invTG_mul, invTG_invTG, invTG_del, invTG_del_inv]
  group

theorem invTG_zUnit (p : Nat.Primes) : invTG (zUnit p) = (zUnit p)⁻¹ := by
  apply Units.ext
  rw [invTG_val]
  change ((((signP p : ℤ) : ℚ) * (p.val : ℚ)) • (1 : Matrix (Fin 2) (Fin 2) ℚ)).transpose =
    (((signP p : ℤ) : ℚ) * (p.val : ℚ)) • (1 : Matrix (Fin 2) (Fin 2) ℚ)
  rw [Matrix.transpose_smul, Matrix.transpose_one]

/-- `tilde` inverts the central element `z`. -/
theorem tilde_zUnit (p : Nat.Primes) : tilde (zUnit p) = (zUnit p)⁻¹ := by
  change del * invTG (zUnit p) * del⁻¹ = _
  rw [invTG_zUnit]
  have c : Commute (zUnit p) del := zUnit_comm p del
  have hc : del * (zUnit p)⁻¹ = (zUnit p)⁻¹ * del := c.inv_left.symm.eq
  rw [mul_inv_eq_iff_eq_mul, hc]

end Involution

section Determinants

theorem det_invTG (h : GL (Fin 2) ℚ) :
    GeneralLinearGroup.det (invTG h) = (GeneralLinearGroup.det h)⁻¹ := by
  rw [← map_inv]
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_det_apply, invTG_val,
    Matrix.det_transpose]

theorem det_tilde (h : GL (Fin 2) ℚ) :
    GeneralLinearGroup.det (tilde h) = (GeneralLinearGroup.det h)⁻¹ := by
  rw [tilde_apply, map_mul, map_mul, det_invTG, map_inv, mul_comm, inv_mul_cancel_left]

theorem det_cQ (h : GL (Fin 2) ℚ) :
    ((GeneralLinearGroup.det (cQ h) : ℂˣ) : ℂ) =
      algebraMap ℚ ℂ ((GeneralLinearGroup.det h : ℚˣ) : ℚ) := by
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_det_apply]
  have h' := RingHom.map_det (algebraMap ℚ ℂ) h.val
  rw [RingHom.mapMatrix_apply] at h'
  exact h'.symm

theorem det_integralEmbed (g : GL (Fin 2) ℤ) :
    (((GeneralLinearGroup.det (integralEmbed g) : ℚˣ)) : ℚ) = 1 ∨
      (((GeneralLinearGroup.det (integralEmbed g) : ℚˣ)) : ℚ) = -1 := by
  have h' := RingHom.map_det (Int.castRingHom ℚ) g.val
  rw [RingHom.mapMatrix_apply] at h'
  have e : (((GeneralLinearGroup.det (integralEmbed g) : ℚˣ)) : ℚ) =
      ((GeneralLinearGroup.det g : ℤˣ) : ℤ) := by
    rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_det_apply]
    exact h'.symm.trans (by simp)
  rcases Int.units_eq_one_or (GeneralLinearGroup.det g) with h1 | h1
  · left
    rw [e, h1]
    simp
  · right
    rw [e, h1]
    simp

theorem det_tilde_integralEmbed_pow (hodd : Odd n) (g : GL (Fin 2) ℤ) :
    ((GeneralLinearGroup.det (cQ (tilde (integralEmbed g))) : ℂˣ) : ℂ) ^ (n + 3) = 1 := by
  rw [det_cQ, det_tilde, Units.val_inv_eq_inv_val, map_inv₀]
  have hev : Even (n + 3) := by
    rcases hodd with ⟨k, hk⟩
    exact ⟨k + 2, by omega⟩
  rcases det_integralEmbed g with h1 | h1
  · rw [h1]
    simp
  · rw [h1]
    simp [hev.neg_pow]

theorem det_heckeRep (p : Nat.Primes) (j : Option (Fin p.val)) :
    (((GeneralLinearGroup.det (heckeRep p j) : ℚˣ)) : ℚ) = (p.val : ℚ) := by
  rw [GeneralLinearGroup.val_det_apply, heckeRep_val]
  have h := RingHom.map_det (Int.castRingHom ℚ) (N p j)
  rw [RingHom.mapMatrix_apply] at h
  rw [← h, N_det]
  simp

end Determinants

section Action

/-- The twisted action differs from the untwisted one by a power of the determinant. -/
theorem act_tw (M : GL (Fin 2) ℂ) (w : Binary.HomogeneousPoly (n + 1)) :
    Binary.homogeneousAction (n + 1) (tw n) M w =
      (((GeneralLinearGroup.det M : ℂˣ) : ℂ) ^ (n + 3)) •
        Binary.homogeneousAction (n + 1) (-1) M w := by
  rw [homogeneousAction_zpow_twist (n + 1) (tw n) M, homogeneousAction_zpow_twist (n + 1) (-1) M,
    LinearMap.smul_apply, LinearMap.smul_apply, smul_smul]
  congr 1
  rw [← zpow_natCast, ← zpow_add₀ (Units.ne_zero _)]
  congr 1
  simp only [tw]
  push_cast
  ring

theorem planeE_rho_integral (hodd : Odd n) (g : GL (Fin 2) ℤ)
    (v : Binary.HomogeneousPoly (n + 1)) :
    planeE n (rationalRho (n + 1) (-1) (integralEmbed g) v) =
      rationalRho (n + 1) (-1) (tilde (integralEmbed g)) (planeE n v) := by
  change planeE n (Binary.homogeneousAction (n + 1) (-1) (cQ (integralEmbed g)) v) =
    Binary.homogeneousAction (n + 1) (-1) (cQ (tilde (integralEmbed g))) (planeE n v)
  rw [planeE_rho_tilde, act_tw, det_tilde_integralEmbed_pow hodd, one_smul]

/-- The matrix `z` acts on `Sym^{n+1}` with the twist `-1` by the scalar `p^{n+3}`. -/
theorem rho_zUnit (hodd : Odd n) (p : Nat.Primes) (w : Binary.HomogeneousPoly (n + 1)) :
    rationalRho (n + 1) (-1) (zUnit p) w = ((p.val : ℂ) ^ (n + 3)) • w := by
  have hp : (p.val : ℚ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hq : (((signP p : ℤ) : ℚ) / (p.val : ℚ)) ≠ 0 := by
    have hs : ((signP p : ℤ) : ℚ) ≠ 0 := by
      have h1 : ((signP p : ℤ) : ℚ) * ((signP p : ℤ) : ℚ) = 1 := by
        exact_mod_cast signP_mul_self p
      intro h0
      rw [h0] at h1
      simp at h1
    exact div_ne_zero hs hp
  have hz : cQ (zUnit p) = GeneralLinearGroup.scalar (Fin 2)
      (Units.mk0 (algebraMap ℚ ℂ (((signP p : ℤ) : ℚ) / (p.val : ℚ)))
        ((map_ne_zero (algebraMap ℚ ℂ)).mpr hq)) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [zUnit_val, GeneralLinearGroup.map_apply]
  change Binary.homogeneousAction (n + 1) (-1) (cQ (zUnit p)) w = _
  rw [hz, binary_homogeneousAction_scalar]
  congr 1
  have hs : ((signP p : ℤ) : ℂ) * ((signP p : ℤ) : ℂ) = 1 := by
    exact_mod_cast signP_mul_self p
  have hpc : (p.val : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hev : Even (n + 3) := by
    rcases hodd with ⟨k, hk⟩
    exact ⟨k + 2, by omega⟩
  obtain ⟨k, hk⟩ := hev
  have hε : ((signP p : ℤ) : ℂ) ^ (k + k) = 1 := by
    rw [← two_mul, pow_mul, sq, hs, one_pow]
  have hinv : ((Units.mk0 (algebraMap ℚ ℂ (((signP p : ℤ) : ℚ) / (p.val : ℚ)))
      ((map_ne_zero (algebraMap ℚ ℂ)).mpr hq) : ℂˣ) : ℂ)⁻¹ = (p.val : ℂ) * ((signP p : ℤ) : ℂ) := by
    rw [Units.val_mk0]
    simp only [map_div₀, map_intCast, map_natCast]
    have hs0 : ((signP p : ℤ) : ℂ) ≠ 0 := by
      intro h0
      rw [h0] at hs
      simp at hs
    field_simp
    linear_combination (-1 : ℂ) * hs
  rw [hinv]
  show ((p.val : ℂ) * ((signP p : ℤ) : ℂ)) ^ (n + 3) = (p.val : ℂ) ^ (n + 3)
  rw [mul_pow, hk, hε, mul_one]

end Action

section Coset

/-- The determinant of the inverse of `tilde r` is that of `r`. -/
theorem det_inv_tilde (r : GL (Fin 2) ℚ) :
    GeneralLinearGroup.det (tilde r)⁻¹ = GeneralLinearGroup.det r := by
  rw [map_inv, det_tilde, inv_inv]

theorem rho_heckeRep_inv_tilde (p : Nat.Primes) (k : Option (Fin p.val))
    (v : Binary.HomogeneousPoly (n + 1)) :
    planeE n (rationalRho (n + 1) (-1) (heckeRep p k)⁻¹ v) =
      ((p.val : ℂ) ^ (n + 3)) • rationalRho (n + 1) (-1) (tilde (heckeRep p k))⁻¹ (planeE n v) := by
  change planeE n (Binary.homogeneousAction (n + 1) (-1) (cQ (heckeRep p k)⁻¹) v) =
    ((p.val : ℂ) ^ (n + 3)) • Binary.homogeneousAction (n + 1) (-1) (cQ (tilde (heckeRep p k))⁻¹)
      (planeE n v)
  rw [planeE_rho_tilde, map_inv tilde (heckeRep p k), act_tw, det_cQ, det_inv_tilde,
    det_heckeRep, map_natCast]

/-- **Compatibility on a Hecke coset**: if `tilde α_j = z γ_j α_{π j}` then
`σ(α_j)⁻¹ E σ(γ_j) = E σ(α_{π j})⁻¹`. -/
theorem compat_at_coset (hodd : Odd n) (p : Nat.Primes) (hp3 : p.val ≠ 3)
    (γ : Option (Fin p.val) → binaryArithmeticLevel)
    (hA : ∀ j, tilde (heckeRep p j) =
      zUnit p * levelEmbed (γ j) * heckeRep p (piEquiv p hp3 j))
    (j : Option (Fin p.val)) (v : Binary.HomogeneousPoly (n + 1)) :
    rationalRho (n + 1) (-1) (heckeRep p j)⁻¹
        (planeE n (rationalRho (n + 1) (-1) (levelEmbed (γ j)) v)) =
      planeE n (rationalRho (n + 1) (-1) (heckeRep p (piEquiv p hp3 j))⁻¹ v) := by
  have hrj : heckeRep p j = (zUnit p)⁻¹ * tilde (levelEmbed (γ j)) *
      tilde (heckeRep p (piEquiv p hp3 j)) := by
    have h := congrArg tilde (hA j)
    rw [tilde_tilde, map_mul, map_mul, tilde_zUnit] at h
    exact h
  have hT : tilde (levelEmbed (γ j)) =
      zUnit p * heckeRep p j * (tilde (heckeRep p (piEquiv p hp3 j)))⁻¹ := by
    calc tilde (levelEmbed (γ j))
        = zUnit p * ((zUnit p)⁻¹ * tilde (levelEmbed (γ j)) *
          tilde (heckeRep p (piEquiv p hp3 j))) * (tilde (heckeRep p (piEquiv p hp3 j)))⁻¹ := by
          group
      _ = _ := by rw [← hrj]
  have hprod : (heckeRep p j)⁻¹ * tilde (levelEmbed (γ j)) =
      zUnit p * (tilde (heckeRep p (piEquiv p hp3 j)))⁻¹ := by
    rw [hT, zUnit_comm p (heckeRep p j)]
    group
  have e3 : planeE n (rationalRho (n + 1) (-1) (levelEmbed (γ j)) v) =
      rationalRho (n + 1) (-1) (tilde (levelEmbed (γ j))) (planeE n v) :=
    planeE_rho_integral hodd (γ j).val v
  rw [e3, ← Module.End.mul_apply, ← map_mul, hprod, rho_heckeRep_inv_tilde p, map_mul,
    Module.End.mul_apply, rho_zUnit hodd]

end Coset

end TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0OddCompat

end
