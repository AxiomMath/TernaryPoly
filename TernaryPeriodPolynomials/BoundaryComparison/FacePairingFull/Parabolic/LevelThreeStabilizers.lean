module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Parabolic.CuspTransport
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityLevelThree

@[expose] public section


/-!
# The cusp stabilizers `∞` and `0` of `Γ₁'(3)`

In `Γ = binaryArithmeticLevel` (`GL₂(ℤ)` matrices with second row `≡ (0,1) mod 3`) the stabilizer of
the cusp `∞` (`binaryCuspLevel 1`) consists of the matrices `T^k` and `ε T^k`
(`T = upper 1`, `ε = reflection = diag(-1, 1)`), and that of the cusp `0` (`binaryCuspLevel swapQ`) of
`L^k` and `ε L^k` (`L = lower 1`). Hence a crossed cocycle trivial on `T` (resp. `L`) is trivial on
the whole cusp stabilizer (`vanishes_cusp_one`, `vanishes_cusp_swap`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein Homogeneous Matrix
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators
open TernaryPeriodPolynomials.LevelThree.GammaOneThree
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree
  (swapQ swapQ_inv)

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Parabolic

/-- The integral entries of an element of `Γ`. -/
abbrev ent (γ : binaryArithmeticLevel) (i j : Fin 2) : ℤ := γ.val.val i j

theorem ent_det (γ : binaryArithmeticLevel) :
    ent γ 0 0 * ent γ 1 1 - ent γ 0 1 * ent γ 1 0 = ((γ.val.det : ℤˣ) : ℤ) := by
  rw [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]

theorem ent_unit (γ : binaryArithmeticLevel) :
    ent γ 0 0 * ent γ 1 1 - ent γ 0 1 * ent γ 1 0 = 1 ∨
      ent γ 0 0 * ent γ 1 1 - ent γ 0 1 * ent γ 1 0 = -1 := by
  rw [ent_det]
  exact Int.isUnit_iff.mp (Units.isUnit _)

theorem ent_row (γ : binaryArithmeticLevel) :
    ((ent γ 1 0 : ℤ) : ZMod 3) = 0 ∧ ((ent γ 1 1 : ℤ) : ZMod 3) = 1 := by
  have h := (mem_binaryArithmeticLevel_iff γ.val).mp γ.property
  exact ⟨by simpa using h 0, by simpa using h 1⟩

theorem refl_mul_upper : reflection * upper 1 = (upper 1)⁻¹ * reflection := by
  have inv : (upper 1)⁻¹ = upper (-1) := by rw [upper_zpow (-1), _root_.zpow_neg_one]
  rw [inv]
  calc reflection * upper 1 = reflection * upper 1 * reflection * reflection := by
        rw [mul_assoc _ reflection reflection, reflection_mul_self, mul_one]
    _ = upper (-1) * reflection := by rw [reflection_conj_upper]

theorem refl_mul_lower : reflection * lower 1 = (lower 1)⁻¹ * reflection := by
  rw [lower_inv]
  calc reflection * lower 1 = reflection * lower 1 * reflection * reflection := by
        rw [mul_assoc _ reflection reflection, reflection_mul_self, mul_one]
    _ = lower (-1) * reflection := by rw [reflection_conj_lower]

/-- Units of `ℤ` with `d ≡ 1 mod 3` and `a * d = ±1`: `d = 1` and `a = ±1`. -/
theorem unit_entries (a d : ℤ) (hd : ((d : ℤ) : ZMod 3) = 1) (h : a * d = 1 ∨ a * d = -1) :
    d = 1 ∧ (a = 1 ∨ a = -1) := by
  have hdu : IsUnit d := by
    rcases h with h | h
    · exact isUnit_iff_exists_inv.mpr ⟨a, by rw [mul_comm]; exact h⟩
    · exact isUnit_iff_exists_inv.mpr ⟨-a, by linarith⟩
  have hd' : d = 1 ∨ d = -1 := Int.isUnit_iff.mp hdu
  have hd1 : d = 1 := by
    rcases hd' with rfl | rfl
    · rfl
    · exfalso
      revert hd
      decide
  subst hd1
  refine ⟨rfl, ?_⟩
  rcases h with h | h
  · left; linarith
  · right; linarith

theorem cusp_one_form (γ : binaryArithmeticLevel) (h : γ ∈ binaryCuspLevel 1) :
    ∃ k : ℤ, γ = upper k ∨ γ = reflection * upper k := by
  rw [mem_binaryCuspLevel_iff] at h
  have hc : ent γ 1 0 = 0 := by
    have h' : ((γ.val.val.map (Int.castRingHom ℚ)) 1 0 : ℚ) = 0 := by simpa using h
    simpa using h'
  have hdet := ent_unit γ
  rw [hc] at hdet
  simp only [mul_zero, sub_zero] at hdet
  obtain ⟨hd, ha⟩ := unit_entries (ent γ 0 0) (ent γ 1 1) (ent_row γ).2 hdet
  rcases ha with ha | ha
  · refine ⟨ent γ 0 1, Or.inl ?_⟩
    apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upper] <;> assumption
  · refine ⟨-(ent γ 0 1), Or.inr ?_⟩
    apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [reflection, upper, Matrix.mul_apply, Fin.sum_univ_two]
      <;> assumption

theorem cusp_swap_form (γ : binaryArithmeticLevel) (h : γ ∈ binaryCuspLevel swapQ) :
    ∃ k : ℤ, γ = lower k ∨ γ = reflection * lower k := by
  rw [mem_binaryCuspLevel_iff, swapQ_inv] at h
  have hb : ent γ 0 1 = 0 := by
    have h' : ((γ.val.val.map (Int.castRingHom ℚ)) 0 1 : ℚ) = 0 := by
      change (swapQ.val * ((γ.val.val.map (Int.castRingHom ℚ))) * swapQ.val) 1 0 = 0 at h
      simpa [swapQ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] using h
    simpa using h'
  have hdet := ent_unit γ
  rw [hb] at hdet
  simp only [zero_mul, sub_zero] at hdet
  obtain ⟨hd, ha⟩ := unit_entries (ent γ 0 0) (ent γ 1 1) (ent_row γ).2 hdet
  have hc3 : (3 : ℤ) ∣ ent γ 1 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (ent γ 1 0) 3).mp (ent_row γ).1
    exact_mod_cast this
  obtain ⟨k, hk⟩ := hc3
  rcases ha with ha | ha
  · refine ⟨k, Or.inl ?_⟩
    apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lower] <;> assumption
  · refine ⟨k, Or.inr ?_⟩
    apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [reflection, lower, Matrix.mul_apply, Fin.sum_univ_two]
      <;> assumption

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ binaryArithmeticLevel V)

/-- A crossed cocycle trivial on `T` is trivial on the stabilizer of the cusp `∞`. -/
theorem vanishes_cusp_one (x : crossedCocycles ρ)
    (hT : ∃ u, x.val (upper 1) = ρ (upper 1) u - u) :
    ∃ w, ∀ γ ∈ binaryCuspLevel 1, x.val γ = ρ γ w - w := by
  obtain ⟨u, hu⟩ := hT
  obtain ⟨w, hpow, hrefl⟩ := cusp_group_trivial ρ x (upper 1) reflection reflection_mul_self
    refl_mul_upper u hu
  refine ⟨w, fun γ hγ => ?_⟩
  obtain ⟨k, hk | hk⟩ := cusp_one_form γ hγ
  · rw [hk, upper_zpow]; exact hpow k
  · rw [hk, upper_zpow]; exact hrefl k

/-- A crossed cocycle trivial on `L` is trivial on the stabilizer of the cusp `0`. -/
theorem vanishes_cusp_swap (x : crossedCocycles ρ)
    (hL : ∃ u, x.val (lower 1) = ρ (lower 1) u - u) :
    ∃ w, ∀ γ ∈ binaryCuspLevel swapQ, x.val γ = ρ γ w - w := by
  obtain ⟨u, hu⟩ := hL
  obtain ⟨w, hpow, hrefl⟩ := cusp_group_trivial ρ x (lower 1) reflection reflection_mul_self
    refl_mul_lower u hu
  refine ⟨w, fun γ hγ => ?_⟩
  obtain ⟨k, hk | hk⟩ := cusp_swap_form γ hγ
  · rw [hk, lower_zpow]; exact hpow k
  · rw [hk, lower_zpow]; exact hrefl k

end TernaryPeriodPolynomials.Argument.FacePairingFull.Parabolic
