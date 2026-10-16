module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.L3CosetsCore

@[expose] public section


/-!
# Further identities for the level-three Hecke adjointness

* `upper_pow`, `lower_pow`: the natural powers `T^n = upper n`, `L^n = lower n`.
* `levelNext_lower_p`: `L^p` acts trivially on all `p + 1` Hecke cosets; `levelNext_lower_iff`:
  `L` fixes a coset iff it is the base coset; `levelDelta_lower_p_none`: the transition of `L^p`
  at `∞` is `L`.
* `gP_mul_gP`, `val_det_gP`: `g'² = (ε/p) · 1` is a scalar and `det g' = -ε/p`.
* `levelDelta_fricke`: the transition of `fricke h` at the base coset is `s h s⁻¹`.
* the reflection `diag(-1, 1)`: conjugation of `upper n`, `lower n`; it fixes the base coset and
  `∞` (`levelNext_reflection_base`, `levelNext_reflection_none`), and `s⁻¹ ·reflection` carries the
  base coset to `∞`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.AdjL3Cosets

open Matrix
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators
open TernaryPeriodPolynomials.Spectral.HeckeH1
open TernaryPeriodPolynomials.Spectral.LevelOneCosets (integralEmbed integralEmbed_val)
open TernaryPeriodPolynomials.LevelThree.LevelThreeCosets

variable (p : Nat.Primes) (hp3 : p.val ≠ 3)

theorem upper_pow (n : ℕ) : upper 1 ^ n = upper (n : ℤ) := by
  rw [upper_zpow (n : ℤ), zpow_natCast]

theorem lower_pow (n : ℕ) : lower 1 ^ n = lower (n : ℤ) := by
  rw [lower_zpow (n : ℤ), zpow_natCast]

section Lower

/-- **`L^p` acts trivially on all Hecke cosets.** -/
theorem levelNext_lower_p (j : Option (Fin p.val)) :
    levelNext p hp3 (lower (p.val : ℤ)) j = j := by
  cases j with
  | none => exact (levelNext_lower_none_iff p hp3 _).mpr (dvd_refl _)
  | some i =>
    have h3 : (3 : ZMod 3) = 0 := by decide
    refine levelNext_eq_of_mul p hp3 _
      (matLevel (1 + 3 * (p.val : ℤ) * i.val) (-(3 * (i.val : ℤ) ^ 2)) (3 * (p.val : ℤ) ^ 2)
        (1 - 3 * (p.val : ℤ) * i.val) 1 (by norm_num) (by ring)
        (by
          push_cast
          rw [h3, zero_mul])
        (by
          push_cast
          rw [h3, zero_mul, zero_mul, sub_zero])) _ _ ?_
    rw [matLevel_val, N_some, lower_val, Matrix.mul_fin_two, Matrix.mul_fin_two]
    exact mat2_eq (by ring) (by ring) (by ring) (by ring)

/-- The transition of `L^p` at `∞` is `L`. -/
theorem levelDelta_lower_p_none : levelDelta p hp3 (lower (p.val : ℤ)) none = lower 1 := by
  refine levelDelta_eq_of_mul p hp3 _ (lower 1) _ none ?_
  rw [N_none, lower_val, lower_val, Matrix.mul_fin_two, Matrix.mul_fin_two]
  exact mat2_eq (by ring) (by ring) (by ring) (by ring)

/-- **`L` fixes a coset iff it is the base coset.** -/
theorem levelNext_lower_iff (j : Option (Fin p.val)) :
    levelNext p hp3 (lower 1) j = j ↔ j = baseIdx p := by
  constructor
  · intro hn
    cases j with
    | none =>
      exfalso
      have hd := (levelNext_lower_none_iff p hp3 1).mp hn
      have h2 := p.property.two_le
      have := Int.le_of_dvd one_pos hd
      omega
    | some i =>
      have spec := levelDelta_spec p hp3 (lower 1) (some i)
      rw [hn, N_some, lower_val_one] at spec
      have e00 : (levelDelta p hp3 (lower 1) (some i)).val.val 0 0 = 1 + 3 * (i.val : ℤ) := by
        have := congrFun (congrFun spec 0) 0
        simp [Matrix.mul_apply, Fin.sum_univ_two] at this
        linarith
      have e01 : (levelDelta p hp3 (lower 1) (some i)).val.val 0 0 * (i.val : ℤ) +
          (levelDelta p hp3 (lower 1) (some i)).val.val 0 1 * (p.val : ℤ) = (i.val : ℤ) := by
        have := congrFun (congrFun spec 0) 1
        simp [Matrix.mul_apply, Fin.sum_univ_two] at this
        linarith
      have hd : (p.val : ℤ) ∣ 3 * ((i.val : ℤ) * i.val) :=
        ⟨-(levelDelta p hp3 (lower 1) (some i)).val.val 0 1, by
          linear_combination e01 - (i.val : ℤ) * e00⟩
      have hpz : Prime (p.val : ℤ) := Nat.prime_iff_prime_int.mp p.property
      have hi : (p.val : ℤ) ∣ (i.val : ℤ) := by
        rcases hpz.dvd_or_dvd hd with h3 | hii
        · exfalso
          have h3' : p.val ∣ 3 := by exact_mod_cast h3
          exact hp3 ((Nat.prime_dvd_prime_iff_eq p.property Nat.prime_three).mp h3')
        · rcases hpz.dvd_or_dvd hii with h | h <;> exact h
      have hlt : |(i.val : ℤ)| < p.val := by
        rw [abs_lt]
        have := i.isLt
        constructor <;> omega
      have hz := Int.eq_zero_of_abs_lt_dvd hi hlt
      have hz' : i.val = 0 := by omega
      exact congrArg some (Fin.ext hz')
  · rintro rfl
    have h := levelNext_lower_base p hp3 1
    rwa [show (lower 1 : binaryArithmeticLevel) = lower 1 from rfl] at h

end Lower

section Gp

theorem eps_ne_zero_Q : ((eps p : ℤ) : ℚ) ≠ 0 := by
  intro h
  have h2 : ((eps p : ℤ) : ℚ) * ((eps p : ℤ) : ℚ) = 1 := by exact_mod_cast eps_mul_self p
  rw [h, zero_mul] at h2
  exact zero_ne_one h2

theorem prime_ne_zero_Q : (p.val : ℚ) ≠ 0 := by exact_mod_cast p.property.ne_zero

/-- The matrix of a scalar element of `GL₂(ℚ)`. -/
theorem scalar_val_Q (u : ℚˣ) :
    ((GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      Matrix.diagonal (fun _ => (u : ℚ)) := rfl

theorem gPinv_mul_gPinv :
    gPinv p hp3 * gPinv p hp3 = GeneralLinearGroup.scalar (Fin 2)
      (Units.mk0 ((p.val : ℚ) * ((eps p : ℤ) : ℚ))
        (mul_ne_zero (prime_ne_zero_Q p) (eps_ne_zero_Q p))) := by
  apply Units.ext
  rw [gPinv_sq_val, scalar_val_Q]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- **`g'² = (ε/p) · 1`** in `GL₂(ℚ)`. -/
theorem gP_mul_gP :
    gP p hp3 * gP p hp3 = GeneralLinearGroup.scalar (Fin 2)
      (Units.mk0 (((eps p : ℤ) : ℚ) / (p.val : ℚ))
        (div_ne_zero (eps_ne_zero_Q p) (prime_ne_zero_Q p))) := by
  have he : ((eps p : ℤ) : ℚ) * ((eps p : ℤ) : ℚ) = 1 := by exact_mod_cast eps_mul_self p
  have hp := prime_ne_zero_Q p
  have h1 : gP p hp3 * gP p hp3 = (gPinv p hp3 * gPinv p hp3)⁻¹ := by
    rw [_root_.mul_inv_rev]
    rfl
  rw [h1, gPinv_mul_gPinv, ← map_inv]
  congr 1
  apply Units.ext
  rw [Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0]
  have hpe : (p.val : ℚ) * ((eps p : ℤ) : ℚ) ≠ 0 := mul_ne_zero hp (eps_ne_zero_Q p)
  field_simp
  linear_combination (-1 : ℚ) * he

/-- **`det g' = -ε/p`.** -/
theorem val_det_gP : ((GeneralLinearGroup.det (gP p hp3) : ℚˣ) : ℚ) =
    -((eps p : ℤ) : ℚ) / (p.val : ℚ) := by
  have he : ((eps p : ℤ) : ℚ) * ((eps p : ℤ) : ℚ) = 1 := by exact_mod_cast eps_mul_self p
  have hp := prime_ne_zero_Q p
  have h1 : ((GeneralLinearGroup.det (gPinv p hp3) : ℚˣ) : ℚ) =
      -((p.val : ℚ) * ((eps p : ℤ) : ℚ)) := by
    have hd : (gInvInt p).det = -((p.val : ℤ) * eps p) := by
      rw [gInvInt, Matrix.det_fin_two_of]
      linear_combination ((p.val : ℤ) ^ 2) * eps_mul_self p
    rw [GeneralLinearGroup.val_det_apply, gPinv_val]
    change ((Int.castRingHom ℚ).mapMatrix (gInvInt p)).det = _
    rw [← RingHom.map_det, hd]
    simp
  rw [gP, map_inv, Units.val_inv_eq_inv_val, h1]
  have hpe : (p.val : ℚ) * ((eps p : ℤ) : ℚ) ≠ 0 := mul_ne_zero hp (eps_ne_zero_Q p)
  field_simp
  linear_combination he

/-- **The transition of the Fricke image at the base coset**: `δ(fricke h, 0) = s h s⁻¹`. -/
theorem levelDelta_fricke (h : stabH p hp3) :
    levelDelta p hp3 (fricke p hp3 h).1 (baseIdx p) = sF p hp3 * h.1 * sInv p hp3 := by
  apply levelEmbed_injective
  have e := (levelCosets p hp3).delta_spec (fricke p hp3 h).1 (baseIdx p)
  have hn : (levelCosets p hp3).next (fricke p hp3 h).1 (baseIdx p) = baseIdx p :=
    (fricke p hp3 h).2
  rw [hn] at e
  change levelEmbed (levelDelta p hp3 (fricke p hp3 h).1 (baseIdx p)) =
    heckeRep p (baseIdx p) * levelEmbed (fricke p hp3 h).1 * (heckeRep p (baseIdx p))⁻¹ at e
  rw [e, levelEmbed_fricke, map_mul, map_mul, sInv_eq_inv, map_inv,
    ← rep_mul_gP p hp3]
  group

end Gp

section Reflection

theorem reflection_val :
    (((reflection).val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) = !![-1, 0; 0, 1] := rfl

theorem reflection_conj_upper_n (n : ℤ) : reflection * upper n * reflection = upper (-n) := by
  apply Subtype.ext
  apply Units.ext
  change (((reflection).val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) *
      (((upper n).val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) *
      (((reflection).val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) =
    (((upper (-n)).val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)
  rw [reflection_val, upper_val, upper_val, Matrix.mul_fin_two, Matrix.mul_fin_two]
  exact mat2_eq (by ring) (by ring) (by ring) (by ring)

theorem reflection_conj_lower_n (n : ℤ) : reflection * lower n * reflection = lower (-n) := by
  apply Subtype.ext
  apply Units.ext
  change (((reflection).val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) *
      (((lower n).val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) *
      (((reflection).val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) =
    (((lower (-n)).val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)
  rw [reflection_val, lower_val, lower_val, Matrix.mul_fin_two, Matrix.mul_fin_two]
  exact mat2_eq (by ring) (by ring) (by ring) (by ring)

theorem reflection_N_base :
    (((reflection).val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) * N p (baseIdx p) =
      N p (baseIdx p) * (((reflection).val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) := by
  rw [reflection_val, N_baseIdx, Matrix.mul_fin_two, Matrix.mul_fin_two]
  exact mat2_eq (by ring) (by ring) (by ring) (by ring)

theorem reflection_N_none :
    (((reflection).val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) * N p none =
      N p none * (((reflection).val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) := by
  rw [reflection_val, N_none, Matrix.mul_fin_two, Matrix.mul_fin_two]
  exact mat2_eq (by ring) (by ring) (by ring) (by ring)

/-- The reflection fixes the base coset, with transition itself. -/
theorem levelNext_reflection_base : levelNext p hp3 reflection (baseIdx p) = baseIdx p :=
  levelNext_eq_of_mul p hp3 _ reflection _ _ (reflection_N_base p)

theorem levelDelta_reflection_base : levelDelta p hp3 reflection (baseIdx p) = reflection :=
  levelDelta_eq_of_mul p hp3 _ reflection _ _ (reflection_N_base p)

/-- The reflection fixes the coset `∞`, with transition itself. -/
theorem levelNext_reflection_none : levelNext p hp3 reflection none = none :=
  levelNext_eq_of_mul p hp3 _ reflection _ _ (reflection_N_none p)

theorem levelDelta_reflection_none : levelDelta p hp3 reflection none = reflection :=
  levelDelta_eq_of_mul p hp3 _ reflection _ _ (reflection_N_none p)

theorem sF_reflection_mul_N :
    (((sF p hp3 * reflection).val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) * N p none =
      N p (baseIdx p) * (((sInv p hp3 * reflection).val : GL (Fin 2) ℤ) :
        Matrix (Fin 2) (Fin 2) ℤ) := by
  change ((sF p hp3).val.val * (reflection).val.val) * N p none =
    N p (baseIdx p) * ((sInv p hp3).val.val * (reflection).val.val)
  rw [Matrix.mul_assoc, reflection_N_none p, ← Matrix.mul_assoc, sF_mul_N p hp3,
    Matrix.mul_assoc]

/-- **`s⁻¹ ·reflection` (determinant `+ε`) carries the base coset to `∞`**, with transition
`s ·reflection`. -/
theorem levelNext_sInv_reflection :
    levelNext p hp3 (sInv p hp3 * reflection) (baseIdx p) = none :=
  levelNext_eq_of_mul p hp3 _ (sF p hp3 * reflection) _ _ (sF_reflection_mul_N p hp3)

theorem levelDelta_sInv_reflection :
    levelDelta p hp3 (sInv p hp3 * reflection) (baseIdx p) = sF p hp3 * reflection :=
  levelDelta_eq_of_mul p hp3 _ _ _ _ (sF_reflection_mul_N p hp3)

end Reflection

end TernaryPeriodPolynomials.BoundaryDuality.AdjL3Cosets
