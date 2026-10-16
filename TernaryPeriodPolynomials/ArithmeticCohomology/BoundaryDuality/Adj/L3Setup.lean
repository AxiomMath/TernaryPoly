module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.L3CosetsExtra
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.L3Orbit

@[expose] public section


/-!
# The Hecke cosets of `Γ₁(3)`: transversal, cusp transits and the Fricke involution

For a prime `p ≠ 3` let `S = coreCosets p hp3` be the `p + 1` right cosets of `Γ₁(3) = core` in
`Δ_p`, `j₀ = baseIdx p` the base coset and `H = AdjCore.stab S j₀` its stabilizer
(`Γ₁(3) ∩ Γ⁰(p)`).  This file builds, from the arithmetic of `AdjL3Cosets*`, the data that the
generic orbit lemmas of `AdjL3Orbit`/`AdjL3Hecke` need:

* the transversal `rK : Option (Fin p) → core` with `rK (some i) = T ^ i` and
  `rK none = rInfG` (`s⁻¹` if `ε_p = -1`, `s⁻¹ ε` if `ε_p = 1`; both of determinant one), see
  `rK_spec`;
* the transits of the cusp elements `T = coreT` and `L = coreL`: at `T` all transits are trivial
  except `T^p` at the last coset and `r_∞ T r_∞⁻¹` at the cusp coset (`transit_T_*`); `L` fixes
  only the base coset and `L^p` acts trivially (`next_L_iff`, `next_Lpow`);
* the Fricke involution `Ω : H →* H` (conjugation by `g' = α₀⁻¹ s`), its conjugation formula, and
  its action on the four cusp elements: `Ω (T^p) = (r_∞ T r_∞⁻¹)^σ`, `Ω L = (r_∞ L^p r_∞⁻¹)^σ`,
  with `σ = det s = -ε_p ∈ {±1}`.

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
open TernaryPeriodPolynomials.LevelThree.TwoGenerator
open TernaryPeriodPolynomials.BoundaryDuality.AdjL3Cosets

variable (p : Nat.Primes) (hp3 : p.val ≠ 3)

/-- `ε_p` is `1` or `-1`. -/
theorem eps_cases : eps p = 1 ∨ eps p = -1 := Int.eq_one_or_neg_one_of_mul_eq_one (eps_mul_self p)

/-- The coset data of `Γ₁(3)`. -/
abbrev SK : RightCosets coreEmbed := coreCosets p hp3

/-- The base coset. -/
abbrev J0 : Option (Fin p.val) := baseIdx p

/-- The stabilizer of the base coset in `Γ₁(3)`. -/
abbrev HK : Subgroup core := AdjCore.stab (SK p hp3) (J0 p)

theorem next_core (k : core) (j : Option (Fin p.val)) :
    (SK p hp3).next k j = levelNext p hp3 k.1 j := rfl

/-! ### The transversal -/

/-- The representative of the coset `∞`: an element of `Γ₁(3)` carrying the base coset to `∞`. -/
def rInfG : binaryArithmeticLevel :=
  if eps p = -1 then sInv p hp3 else sInv p hp3 * reflection

theorem rInfG_eq_of_neg (h : eps p = -1) : rInfG p hp3 = sInv p hp3 := by
  simp [rInfG, h]

theorem rInfG_eq_of_pos (h : eps p = 1) : rInfG p hp3 = sInv p hp3 * reflection := by
  have : ¬ (eps p = -1) := by rw [h]; decide
  simp [rInfG, this]

theorem det_reflection_val :
    (((reflection : binaryArithmeticLevel).val : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ).det =
      (-1 : ℤ) := by
  rw [reflection_val, Matrix.det_fin_two_of]
  norm_num

theorem rInfG_mem_core : rInfG p hp3 ∈ core := by
  rw [mem_core_iff]
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply]
  rcases eps_cases p with he | he
  · rw [rInfG_eq_of_pos p hp3 he]
    change (((sInv p hp3).val.val * reflection.val.val : Matrix (Fin 2) (Fin 2) ℤ)).det = _
    rw [Matrix.det_mul, det_sInv, det_reflection_val, he]
    simp
  · rw [rInfG_eq_of_neg p hp3 he, det_sInv, he]
    simp

/-- The transversal of the stabilizer `H` in `Γ₁(3)`: `T ^ i` for the coset `i` and `rInfG` for
the coset `∞`. -/
def rK : Option (Fin p.val) → core
  | some i => ⟨upper (i.val : ℤ), upper_mem_core _⟩
  | none => ⟨rInfG p hp3, rInfG_mem_core p hp3⟩

theorem rK_spec (j : Option (Fin p.val)) : (SK p hp3).next (rK p hp3 j) (J0 p) = j := by
  cases j with
  | none =>
    rcases eps_cases p with he | he
    · change levelNext p hp3 (rInfG p hp3) (baseIdx p) = none
      rw [rInfG_eq_of_pos p hp3 he]
      exact levelNext_sInv_reflection p hp3
    · change levelNext p hp3 (rInfG p hp3) (baseIdx p) = none
      rw [rInfG_eq_of_neg p hp3 he]
      exact levelNext_transv p hp3 none
  | some i => exact levelNext_transv p hp3 (some i)

theorem rK_base : rK p hp3 (J0 p) = 1 := by
  apply Subtype.ext
  change upper (((0 : ℕ)) : ℤ) = 1
  rw [Nat.cast_zero, upper_zero]

/-! ### Transits of the cusp elements -/

/-- The transition `r_j g r_{j g}⁻¹` of the transversal `rK`, an element of `H`. -/
abbrev tr (g : core) (j : Option (Fin p.val)) : HK p hp3 :=
  AdjCore.transit (S := SK p hp3) (j₀ := J0 p) (rK p hp3) (rK_spec p hp3) g j

theorem tr_val (g : core) (j : Option (Fin p.val)) :
    (tr p hp3 g j : binaryArithmeticLevel) =
      (rK p hp3 j).1 * g.1 * ((rK p hp3 (levelNext p hp3 g.1 j)).1)⁻¹ := rfl

theorem coreT_val : (coreT : binaryArithmeticLevel) = upper 1 := rfl

theorem coreL_val : (coreL : binaryArithmeticLevel) = lower 1 := rfl

theorem coreT_pow_val (n : ℕ) : ((coreT ^ n : core) : binaryArithmeticLevel) = upper (n : ℤ) := by
  rw [Subgroup.coe_pow, coreT_val, upper_pow]

theorem coreL_pow_val (n : ℕ) : ((coreL ^ n : core) : binaryArithmeticLevel) = lower (n : ℤ) := by
  rw [Subgroup.coe_pow, coreL_val, lower_pow]

theorem tr_T_some (b : Fin p.val) (hb : b.val + 1 < p.val) : tr p hp3 coreT (some b) = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  rw [tr_val, coreT_val, levelNext_upper_some p hp3 b hb]
  change upper (b.val : ℤ) * upper 1 * (upper (((b.val + 1 : ℕ)) : ℤ))⁻¹ = 1
  rw [upper_mul, Nat.cast_add, Nat.cast_one]
  exact mul_inv_cancel _

theorem tr_T_last_val :
    (tr p hp3 coreT (some (lastIdx p)) : binaryArithmeticLevel) = upper (p.val : ℤ) := by
  have hp := p.property.pos
  have hc : (((lastIdx p).val : ℕ) : ℤ) = (p.val : ℤ) - 1 := by
    show (((p.val - 1 : ℕ)) : ℤ) = _
    omega
  rw [tr_val, coreT_val, levelNext_upper_last p hp3]
  change upper (((lastIdx p).val : ℕ) : ℤ) * upper 1 * (upper (((0 : ℕ)) : ℤ))⁻¹ = _
  rw [upper_mul, hc, Nat.cast_zero, upper_zero, inv_one, mul_one, sub_add_cancel]

theorem tr_T_none_val :
    (tr p hp3 coreT none : binaryArithmeticLevel) =
      rInfG p hp3 * upper 1 * (rInfG p hp3)⁻¹ := by
  rw [tr_val, coreT_val, levelNext_upper_none p hp3]
  rfl

theorem tr_L_base_val : (tr p hp3 coreL (J0 p) : binaryArithmeticLevel) = lower 1 := by
  rw [tr_val, coreL_val, levelNext_lower_base p hp3 1, rK_base]
  simp

theorem tr_Lpow_none_val :
    (tr p hp3 (coreL ^ p.val) none : binaryArithmeticLevel) =
      rInfG p hp3 * lower (p.val : ℤ) * (rInfG p hp3)⁻¹ := by
  rw [tr_val, coreL_pow_val, (levelNext_lower_none_iff p hp3 _).mpr (dvd_refl _)]
  rfl

theorem next_T_last : (SK p hp3).next coreT (some (lastIdx p)) = J0 p :=
  levelNext_upper_last p hp3

theorem next_T_none : (SK p hp3).next coreT none = none :=
  levelNext_upper_none p hp3

theorem next_L_iff (j : Option (Fin p.val)) : (SK p hp3).next coreL j = j ↔ j = J0 p :=
  levelNext_lower_iff p hp3 j

theorem next_Lpow (j : Option (Fin p.val)) : (SK p hp3).next (coreL ^ p.val) j = j := by
  have := levelNext_lower_p p hp3 j
  rw [next_core, coreL_pow_val, this]

theorem rK_some_pow (n : ℕ) (hn : n < p.val) : rK p hp3 (some ⟨n, hn⟩) = coreT ^ n := by
  apply Subtype.ext
  rw [coreT_pow_val]
  rfl

end TernaryPeriodPolynomials.BoundaryDuality.AdjL3
