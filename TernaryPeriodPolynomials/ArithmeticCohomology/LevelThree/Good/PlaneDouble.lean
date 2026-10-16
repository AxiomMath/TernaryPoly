module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Identity.PlaneLocalOp
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneFrame
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneCosetData
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Cosets

@[expose] public section


/-!
# The good-plane coset representatives lie in the double coset of `diag(p, 1, 1)`

Let `g = F · diag(1, 3, 1)` be the rational frame of the good plane (`GoodPlaneFrame.gF`) and let
`σ₀`, `s_{j,r}` be the explicit local coset representatives at the good plane
(`GoodPlaneCosetData.sExpl`). We show that every `g s g⁻¹` lies in `Γ diag(p, 1, 1) Γ`, with
explicit factorizations `a · diag(p, 1, 1) · b` with `a, b` in the level (`rationalLevel`). Write
`ε = ±1 ≡ p (mod 3)`, `E = εp ≡ 1 (mod 3)` and `β = (1 - E) / 3`. Then:

* `g s_{i,r} g⁻¹ = [[p, r, -i], [0, 1, 0], [0, 0, 1]] = a · diag(p, 1, 1)` with `a` unipotent;
* `g σ₀ g⁻¹ = diag(1, E, 1) = [[1, -β, 0], [3, E, 0], [0, 0, 1]] · diag(p, 1, 1) ·
  [[ε, βε, 0], [-3, E, 0], [0, 0, 1]]`;
* `g s_{∞,r} g⁻¹ = [[ε, 0, 0], [0, 1, 0], [0, 3r, E]] = [[ε, 0, -εβ], [0, 1, 0], [3, 3r, E]] ·
  diag(p, 1, 1) · [[ε, 0, βε], [0, 1, 0], [-3, 0, E]]`.

This is the analogue of `IdentityPlaneLocalOp.sExpl_double` for the good plane.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.LevelThree.GoodPlaneDouble

open TernaryPeriodPolynomials.Spectral
open IdentityPlaneCosets (icast epsP epsP_mod epsU_val)
open IdentityPlaneLocalOp (lvl lvl_val betaP three_betaP zmod_one zmod_three
  zmod_neg_three)
open TernaryPeriodPolynomials.LevelThree.LevelThreeCosets (signP signP_cast)
open TernaryPeriodPolynomials.HeckeEigen.Satake (gP gP_val)

variable (p : Nat.Primes)

/-! ### The sign relation -/

/-- `p · ε = E`, where `ε = ±1 ≡ p (mod 3)` and `E = εp = ±p ≡ 1 (mod 3)`. -/
theorem sign_mul_eps (hp3 : p.val ≠ 3) :
    (p.val : ℤ) * ((signP p : ℤˣ) : ℤ) = epsP p := by
  have hc := signP_cast p hp3
  have hc' : ((((signP p : ℤˣ) : ℤ) - (p.val : ℤ) : ℤ) : ZMod 3) = 0 := by
    rw [Int.cast_sub, hc, Int.cast_natCast, sub_self]
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp hc'
  have hd' : (3 : ℤ) ∣ ((signP p : ℤˣ) : ℤ) - (p.val : ℤ) := by exact_mod_cast hd
  clear hd hc' hc
  have hs : ((signP p : ℤˣ) : ℤ) = 1 ∨ ((signP p : ℤˣ) : ℤ) = -1 := by
    rcases Int.units_eq_one_or (signP p) with h | h
    · left; simp [h]
    · right; simp [h]
  unfold epsP
  rcases hs with h | h <;> rw [h] at hd' ⊢ <;> split_ifs <;> omega

theorem sign_mul_eps_rat (hp3 : p.val ≠ 3) :
    (p.val : ℚ) * (((signP p : ℤˣ) : ℤ) : ℚ) = (epsP p : ℚ) := by
  exact_mod_cast sign_mul_eps p hp3

/-! ### The three families -/

/-- `g s_{i,r} g⁻¹ = a · diag(p, 1, 1)` for the representatives with finite index. -/
theorem good_some_some (k r : Fin p.val) :
    ∃ a b : rationalLevel,
      GoodPlaneFrame.gF * GoodPlaneCosetData.sExpl p (some (some k, r)) * GoodPlaneFrame.gF⁻¹
        = a.val * gP p.property * b.val := by
  let Ma : Matrix (Fin 3) (Fin 3) ℤ := !![1, (r.val : ℤ), -(k.val : ℤ); 0, 1, 0; 0, 0, 1]
  have hda : IsUnit Ma.det := by
    have : Ma.det = 1 := by simp [Ma, Matrix.det_fin_three]
    rw [this]; exact isUnit_one
  have hra : ∀ j, ((Ma 2 j : ℤ) : ZMod 3) = if j = 2 then 1 else 0 := by
    intro j; fin_cases j <;> simp [Ma]
  refine ⟨lvl Ma hda hra, 1, ?_⟩
  apply Units.ext
  simp only [Units.val_mul]
  rw [lvl_val, gP_val, GoodPlaneCosetData.sExpl, PlaneCoordinates.P_val, GoodPlaneFrame.gF_val,
    GoodPlaneFrame.gF_inv_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ma, Matrix.mul_apply, Fin.sum_univ_three, GoodPlaneCosetData.BG_val,
      GoodPlaneCosetData.Bmat, GoodPlaneCosetData.wint, icast]
  ring1

/-- `g σ₀ g⁻¹ = diag(1, E, 1) = a · diag(p, 1, 1) · b`. -/
theorem good_none (hp3 : p.val ≠ 3) :
    ∃ a b : rationalLevel,
      GoodPlaneFrame.gF * GoodPlaneCosetData.sExpl p none * GoodPlaneFrame.gF⁻¹
        = a.val * gP p.property * b.val := by
  have R1q := sign_mul_eps_rat p hp3
  have R2 := three_betaP p hp3
  have R2q : 3 * (betaP p : ℚ) = 1 - (epsP p : ℚ) := by exact_mod_cast R2
  let Ma : Matrix (Fin 3) (Fin 3) ℤ := !![1, -betaP p, 0; 3, epsP p, 0; 0, 0, 1]
  let Mb : Matrix (Fin 3) (Fin 3) ℤ :=
    !![((signP p : ℤˣ) : ℤ), betaP p * ((signP p : ℤˣ) : ℤ), 0; -3, epsP p, 0; 0, 0, 1]
  have hda : IsUnit Ma.det := by
    have : Ma.det = 1 := by
      simp only [Ma, Matrix.det_fin_three]
      simp
      linear_combination R2
    rw [this]; exact isUnit_one
  have hdb : IsUnit Mb.det := by
    have : Mb.det = ((signP p : ℤˣ) : ℤ) := by
      simp only [Mb, Matrix.det_fin_three]
      simp
      linear_combination ((signP p : ℤˣ) : ℤ) * R2
    rw [this]; exact Units.isUnit (signP p)
  have hra : ∀ j, ((Ma 2 j : ℤ) : ZMod 3) = if j = 2 then 1 else 0 := by
    intro j; fin_cases j <;> simp [Ma]
  have hrb : ∀ j, ((Mb 2 j : ℤ) : ZMod 3) = if j = 2 then 1 else 0 := by
    intro j; fin_cases j <;> simp [Mb]
  refine ⟨lvl Ma hda hra, lvl Mb hdb hrb, ?_⟩
  apply Units.ext
  simp only [Units.val_mul]
  rw [lvl_val, lvl_val, gP_val, GoodPlaneCosetData.sExpl, PlaneCoordinates.P_val,
    GoodPlaneFrame.gF_val, GoodPlaneFrame.gF_inv_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ma, Mb, Matrix.mul_apply, Fin.sum_univ_three, epsU_val] <;>
    first
    | linear_combination -R1q - R2q
    | linear_combination R1q + R2q
    | linear_combination -(betaP p : ℚ) * R1q
    | linear_combination (betaP p : ℚ) * R1q
    | linear_combination -3 * R1q
    | linear_combination 3 * R1q
    | linear_combination -(epsP p : ℚ) * R2q - 3 * (betaP p : ℚ) * R1q

/-- `g s_{∞,r} g⁻¹ = a · diag(p, 1, 1) · b`. -/
theorem good_some_none (hp3 : p.val ≠ 3) (r : Fin p.val) :
    ∃ a b : rationalLevel,
      GoodPlaneFrame.gF * GoodPlaneCosetData.sExpl p (some (none, r)) * GoodPlaneFrame.gF⁻¹
        = a.val * gP p.property * b.val := by
  have R1q := sign_mul_eps_rat p hp3
  have R2 := three_betaP p hp3
  have hmod := epsP_mod p hp3
  have R2q : 3 * (betaP p : ℚ) = 1 - (epsP p : ℚ) := by exact_mod_cast R2
  let Ma : Matrix (Fin 3) (Fin 3) ℤ :=
    !![((signP p : ℤˣ) : ℤ), 0, -(betaP p * ((signP p : ℤˣ) : ℤ)); 0, 1, 0;
      3, 3 * (r.val : ℤ), epsP p]
  let Mb : Matrix (Fin 3) (Fin 3) ℤ :=
    !![((signP p : ℤˣ) : ℤ), 0, betaP p * ((signP p : ℤˣ) : ℤ); 0, 1, 0; -3, 0, epsP p]
  have hda : IsUnit Ma.det := by
    have : Ma.det = ((signP p : ℤˣ) : ℤ) := by
      simp only [Ma, Matrix.det_fin_three]
      simp
      linear_combination ((signP p : ℤˣ) : ℤ) * R2
    rw [this]; exact Units.isUnit (signP p)
  have hdb : IsUnit Mb.det := by
    have : Mb.det = ((signP p : ℤˣ) : ℤ) := by
      simp only [Mb, Matrix.det_fin_three]
      simp
      linear_combination ((signP p : ℤˣ) : ℤ) * R2
    rw [this]; exact Units.isUnit (signP p)
  have hra : ∀ j, ((Ma 2 j : ℤ) : ZMod 3) = if j = 2 then 1 else 0 := by
    intro j; fin_cases j
    · exact zmod_three
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr ⟨(r.val : ℤ), rfl⟩
    · simpa [Ma] using zmod_one hmod
  have hrb : ∀ j, ((Mb 2 j : ℤ) : ZMod 3) = if j = 2 then 1 else 0 := by
    intro j; fin_cases j
    · exact zmod_neg_three
    · simp [Mb]
    · simpa [Mb] using zmod_one hmod
  refine ⟨lvl Ma hda hra, lvl Mb hdb hrb, ?_⟩
  apply Units.ext
  simp only [Units.val_mul]
  rw [lvl_val, lvl_val, gP_val, GoodPlaneCosetData.sExpl, PlaneCoordinates.P_val,
    GoodPlaneFrame.gF_val, GoodPlaneFrame.gF_inv_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ma, Mb, Matrix.mul_apply, Fin.sum_univ_three, GoodPlaneCosetData.BG_val,
      GoodPlaneCosetData.Bmat, GoodPlaneCosetData.wint, icast] <;>
    first
    | linear_combination -(((signP p : ℤˣ) : ℤ) : ℚ) * R1q - (((signP p : ℤˣ) : ℤ) : ℚ) * R2q
    | linear_combination (((signP p : ℤˣ) : ℤ) : ℚ) * R1q + (((signP p : ℤˣ) : ℤ) : ℚ) * R2q
    | linear_combination -(betaP p : ℚ) * (((signP p : ℤˣ) : ℤ) : ℚ) * R1q
    | linear_combination (betaP p : ℚ) * (((signP p : ℤˣ) : ℤ) : ℚ) * R1q
    | linear_combination -3 * R1q
    | linear_combination 3 * R1q
    | linear_combination (1 - 3 * (betaP p : ℚ)) * R1q - (epsP p : ℚ) * R2q

/-- **Every explicit good-plane representative, conjugated by the good-plane frame, lies in
`Γ diag(p, 1, 1) Γ`.** -/
theorem sExpl_double (hp3 : p.val ≠ 3) (i : GoodPlaneCosetData.SIdx p) :
    ∃ a b : GeneralEisenstein.rationalLevel,
      GoodPlaneFrame.gF * GoodPlaneCosetData.sExpl p i * GoodPlaneFrame.gF⁻¹
        = a.val * TernaryPeriodPolynomials.HeckeEigen.Satake.gP p.property * b.val := by
  rcases i with _ | ⟨_ | k, r⟩
  · exact good_none p hp3
  · exact good_some_none p hp3 r
  · exact good_some_some p k r

end TernaryPeriodPolynomials.LevelThree.GoodPlaneDouble
