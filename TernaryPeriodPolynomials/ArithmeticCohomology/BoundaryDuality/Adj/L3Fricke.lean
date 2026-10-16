module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.L3Setup

@[expose] public section


/-!
# The Fricke involution of `Γ₁(3) ∩ Γ⁰(p)` on the cusp elements

`Ω : H →* H` is the conjugation of the stabilizer `H = Γ₁(3) ∩ Γ⁰(p)` of the base coset by the
Fricke element `g' = α₀⁻¹ s ∈ GL₂(ℚ)` (`AdjL3Cosets.frickeCore`, transported to
`AdjCore.stab (coreCosets p hp3) (baseIdx p)`).  The four cusp elements of `H` are

* `TpK = r_{p-1} T r_0⁻¹ = T ^ p`, `tK2 = r_∞ T r_∞⁻¹`   (over the cusp `∞`),
* `LK = r_0 L r_0⁻¹ = L`, `tL2 = r_∞ L ^ p r_∞⁻¹`          (over the cusp `0`).

`Ω` exchanges them: `Ω TpK = tK2 ^ σ`, `Ω tK2 = TpK ^ σ`, `Ω LK = tL2 ^ σ`, `Ω tL2 = LK ^ σ`
with `σ = 1` if `ε_p = -1` and `σ = -1` if `ε_p = 1`.  The transition of an element of `H` at the
base coset is `δ(h, j₀) = s Ω(h) s⁻¹` (`delta_eq`).

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

variable (p : Nat.Primes) (hp3 : p.val ≠ 3)

/-- The stabilizer of `AdjCore.stab (coreCosets ..)` as a subgroup of `Γ₁(3) ∩ Γ⁰(p)`. -/
def toStabCore (h : HK p hp3) : stabCore p hp3 :=
  ⟨h.1.1, Subgroup.mem_inf.mpr ⟨h.1.2, h.2⟩⟩

/-- Back from `Γ₁(3) ∩ Γ⁰(p)` to the stabilizer in `core`. -/
def ofStabCore (h : stabCore p hp3) : HK p hp3 :=
  ⟨⟨h.1, (Subgroup.mem_inf.mp h.2).1⟩, (Subgroup.mem_inf.mp h.2).2⟩

theorem ofStabCore_toStabCore (h : HK p hp3) : ofStabCore p hp3 (toStabCore p hp3 h) = h := rfl

theorem toStabCore_ofStabCore (h : stabCore p hp3) : toStabCore p hp3 (ofStabCore p hp3 h) = h :=
  rfl

theorem toStabCore_mul (h k : HK p hp3) :
    toStabCore p hp3 (h * k) = toStabCore p hp3 h * toStabCore p hp3 k := rfl

theorem ofStabCore_mul (h k : stabCore p hp3) :
    ofStabCore p hp3 (h * k) = ofStabCore p hp3 h * ofStabCore p hp3 k := rfl

/-- **The Fricke involution `Ω` of the stabilizer `H` of the base coset in `Γ₁(3)`.** -/
def Ω : HK p hp3 →* HK p hp3 :=
  MonoidHom.mk' (fun h => ofStabCore p hp3 (frickeCore p hp3 (toStabCore p hp3 h))) (by
    intro h k
    rw [toStabCore_mul, map_mul, ofStabCore_mul])

theorem Ω_val (h : HK p hp3) :
    ((Ω p hp3 h : HK p hp3) : binaryArithmeticLevel) = (frickeCore p hp3 (toStabCore p hp3 h)).1 :=
  rfl

theorem Ω_Ω (h : HK p hp3) : Ω p hp3 (Ω p hp3 h) = h := by
  change ofStabCore p hp3 (frickeCore p hp3 (toStabCore p hp3
    (ofStabCore p hp3 (frickeCore p hp3 (toStabCore p hp3 h))))) = h
  rw [toStabCore_ofStabCore, frickeCore_frickeCore]
  rfl

/-- **The conjugation formula** `α_{Ωh} = g' α_h g'⁻¹` in `GL₂(ℚ)`. -/
theorem embed_Ω (h : HK p hp3) :
    coreEmbed ((Ω p hp3 h : HK p hp3) : core) =
      gP p hp3 * coreEmbed (h : core) * (gP p hp3)⁻¹ :=
  levelEmbed_frickeCore p hp3 (toStabCore p hp3 h)

/-- **The transition of an element of `H` at the base coset is a conjugate of its Fricke image**:
`δ(h, j₀) = s Ω(h) s⁻¹`. -/
theorem delta_eq (h : HK p hp3) :
    (((SK p hp3).delta (h : core) (J0 p) : core) : binaryArithmeticLevel) =
      sF p hp3 * ((Ω p hp3 h : HK p hp3) : binaryArithmeticLevel) * sInv p hp3 := by
  have e := levelDelta_fricke p hp3 ⟨((Ω p hp3 h : HK p hp3) : binaryArithmeticLevel), (Ω p hp3 h).2⟩
  have e2 : ((Ω p hp3 (Ω p hp3 h) : HK p hp3) : binaryArithmeticLevel) = h.1.1 := by
    rw [Ω_Ω]
  change levelDelta p hp3 (frickeElt p hp3 ⟨((Ω p hp3 h : HK p hp3) : binaryArithmeticLevel),
    (Ω p hp3 h).2⟩) (baseIdx p) = _ at e
  have e3 : frickeElt p hp3 ⟨((Ω p hp3 h : HK p hp3) : binaryArithmeticLevel), (Ω p hp3 h).2⟩ =
      h.1.1 := by
    have := e2
    rw [Ω_val] at this
    exact this
  rw [e3] at e
  exact e

/-! ### The four cusp elements -/

/-- `T ^ p`, the transit of `T` at the last coset. -/
abbrev TpK : HK p hp3 := tr p hp3 coreT (some (lastIdx p))

/-- The transit of `T` at `∞`. -/
abbrev tK2 : HK p hp3 := tr p hp3 coreT none

/-- `L`, the transit of `L` at the base coset. -/
abbrev LK : HK p hp3 := tr p hp3 coreL (J0 p)

/-- The transit of `L ^ p` at `∞`. -/
abbrev tL2 : HK p hp3 := tr p hp3 (coreL ^ p.val) none

theorem rInfG_upper_rInfG_inv :
    rInfG p hp3 * upper 1 * (rInfG p hp3)⁻¹ =
      sInv p hp3 * upper (if eps p = 1 then -1 else 1) * sF p hp3 := by
  rcases eps_cases p with he | he
  · rw [rInfG_eq_of_pos p hp3 he, ite_eq_left he, _root_.mul_inv_rev, reflection_inv, sF_eq_inv]
    have := reflection_conj_upper_n 1
    calc sInv p hp3 * reflection * upper 1 * (reflection * (sInv p hp3)⁻¹)
        = sInv p hp3 * (reflection * upper 1 * reflection) * (sInv p hp3)⁻¹ := by group
      _ = _ := by rw [this]
  · have : ¬ (eps p = 1) := by rw [he]; decide
    rw [rInfG_eq_of_neg p hp3 he, ite_eq_right this, sF_eq_inv]

theorem rInfG_lower_rInfG_inv :
    rInfG p hp3 * lower (p.val : ℤ) * (rInfG p hp3)⁻¹ =
      sInv p hp3 * lower (if eps p = 1 then -(p.val : ℤ) else (p.val : ℤ)) * sF p hp3 := by
  rcases eps_cases p with he | he
  · rw [rInfG_eq_of_pos p hp3 he, ite_eq_left he, _root_.mul_inv_rev, reflection_inv, sF_eq_inv]
    have := reflection_conj_lower_n (p.val : ℤ)
    calc sInv p hp3 * reflection * lower (p.val : ℤ) * (reflection * (sInv p hp3)⁻¹)
        = sInv p hp3 * (reflection * lower (p.val : ℤ) * reflection) * (sInv p hp3)⁻¹ := by group
      _ = _ := by rw [this]
  · have : ¬ (eps p = 1) := by rw [he]; decide
    rw [rInfG_eq_of_neg p hp3 he, ite_eq_right this, sF_eq_inv]

theorem TpK_val : (TpK p hp3 : binaryArithmeticLevel) = upper (p.val : ℤ) := tr_T_last_val p hp3

theorem tK2_val :
    (tK2 p hp3 : binaryArithmeticLevel) =
      sInv p hp3 * upper (if eps p = 1 then -1 else 1) * sF p hp3 := by
  rw [tr_T_none_val, rInfG_upper_rInfG_inv]

theorem LK_val : (LK p hp3 : binaryArithmeticLevel) = lower 1 := tr_L_base_val p hp3

theorem tL2_val :
    (tL2 p hp3 : binaryArithmeticLevel) =
      sInv p hp3 * lower (if eps p = 1 then -(p.val : ℤ) else (p.val : ℤ)) * sF p hp3 := by
  rw [tr_Lpow_none_val, rInfG_lower_rInfG_inv]

theorem Ω_TpK_val :
    ((Ω p hp3 (TpK p hp3) : HK p hp3) : binaryArithmeticLevel) =
      sInv p hp3 * upper 1 * sF p hp3 := by
  rw [Ω_val]
  have : toStabCore p hp3 (TpK p hp3) =
      ⟨upper (p.val : ℤ), upper_mem_stabCore p hp3⟩ := Subtype.ext (TpK_val p hp3)
  rw [this]
  exact frickeCore_upper p hp3

theorem Ω_LK_val :
    ((Ω p hp3 (LK p hp3) : HK p hp3) : binaryArithmeticLevel) =
      sInv p hp3 * lower (p.val : ℤ) * sF p hp3 := by
  rw [Ω_val]
  have : toStabCore p hp3 (LK p hp3) =
      ⟨lower 1, lower_mem_stabCore p hp3 1⟩ := Subtype.ext (LK_val p hp3)
  rw [this, frickeCore_lower]

/-- **`Ω` exchanges `T^p` and `r_∞ T r_∞⁻¹`** (up to inversion when `ε_p = 1`). -/
theorem Ω_TpK :
    (eps p = -1 ∧ Ω p hp3 (TpK p hp3) = tK2 p hp3) ∨
      (eps p = 1 ∧ Ω p hp3 (TpK p hp3) = (tK2 p hp3)⁻¹) := by
  rcases eps_cases p with he | he
  · right
    refine ⟨he, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rw [Ω_TpK_val, Subgroup.coe_inv, Subgroup.coe_inv, tK2_val, ite_eq_left he, sF_eq_inv]
    have : (upper (-1 : ℤ)) = (upper 1)⁻¹ := by rw [upper_zpow (-1), upper_zpow 1, _root_.zpow_neg_one, zpow_one]
    rw [this]
    group
  · left
    refine ⟨he, ?_⟩
    have : ¬ (eps p = 1) := by rw [he]; decide
    apply Subtype.ext
    apply Subtype.ext
    rw [Ω_TpK_val, tK2_val, ite_eq_right this]

theorem Ω_LK :
    (eps p = -1 ∧ Ω p hp3 (LK p hp3) = tL2 p hp3) ∨
      (eps p = 1 ∧ Ω p hp3 (LK p hp3) = (tL2 p hp3)⁻¹) := by
  rcases eps_cases p with he | he
  · right
    refine ⟨he, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rw [Ω_LK_val, Subgroup.coe_inv, Subgroup.coe_inv, tL2_val, ite_eq_left he, sF_eq_inv]
    have : (lower (-(p.val : ℤ))) = (lower (p.val : ℤ))⁻¹ := by
      rw [lower_zpow (-(p.val : ℤ)), lower_zpow (p.val : ℤ), _root_.zpow_neg]
    rw [this]
    group
  · left
    refine ⟨he, ?_⟩
    have : ¬ (eps p = 1) := by rw [he]; decide
    apply Subtype.ext
    apply Subtype.ext
    rw [Ω_LK_val, tL2_val, ite_eq_right this]

/-- `Ω` exchanges `r_∞ T r_∞⁻¹` and `T ^ p` (up to inversion when `ε_p = 1`). -/
theorem Ω_tK2 :
    (eps p = -1 ∧ Ω p hp3 (tK2 p hp3) = TpK p hp3) ∨
      (eps p = 1 ∧ Ω p hp3 (tK2 p hp3) = (TpK p hp3)⁻¹) := by
  rcases Ω_TpK p hp3 with ⟨he, h⟩ | ⟨he, h⟩
  · left
    refine ⟨he, ?_⟩
    rw [← h, Ω_Ω]
  · right
    refine ⟨he, ?_⟩
    have h2 := congrArg (Ω p hp3) h
    rw [Ω_Ω, map_inv] at h2
    rw [h2, inv_inv]

/-- `Ω` exchanges `r_∞ L ^ p r_∞⁻¹` and `L` (up to inversion when `ε_p = 1`). -/
theorem Ω_tL2 :
    (eps p = -1 ∧ Ω p hp3 (tL2 p hp3) = LK p hp3) ∨
      (eps p = 1 ∧ Ω p hp3 (tL2 p hp3) = (LK p hp3)⁻¹) := by
  rcases Ω_LK p hp3 with ⟨he, h⟩ | ⟨he, h⟩
  · left
    refine ⟨he, ?_⟩
    rw [← h, Ω_Ω]
  · right
    refine ⟨he, ?_⟩
    have h2 := congrArg (Ω p hp3) h
    rw [Ω_Ω, map_inv] at h2
    rw [h2, inv_inv]

end TernaryPeriodPolynomials.BoundaryDuality.AdjL3
