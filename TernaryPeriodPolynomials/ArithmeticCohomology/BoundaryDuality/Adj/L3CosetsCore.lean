module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.L3CosetsOrbits

@[expose] public section


/-!
# The determinant-one part of the stabilizer and the Fricke involution on it

The parabolic cup pairing of `Γ₁'(3)` is computed on the determinant-one subgroup
`core = Γ₁(3) = ⟨T, L⟩`, where the pairing of binary forms is invariant (on the determinant `-1`
elements of `Γ₁'(3)` it is odd).  Accordingly this file restricts the stabilizer
`stabH p hp3 = Γ₁'(3) ∩ Γ⁰(p)` of the base coset to `stabCore = Γ₁(3) ∩ Γ⁰(p)`:

* `stabCore` is the subgroup of elements of determinant one in `stabH`
  (`mem_stabCore_iff`); it contains `T^p`, `L`, `s⁻¹ T s` and `s⁻¹ L^p s` (the cusp generators);
* the Fricke conjugation preserves determinants (`det_frickeVal`), hence restricts to an involution
  `frickeCore : stabCore →* stabCore` with `levelEmbed (frickeCore h) = g' (levelEmbed h) g'⁻¹`
  (`levelEmbed_frickeCore`, `frickeCore_frickeCore`), exchanging `T^p ↔ s⁻¹ T s` and
  `L ↔ s⁻¹ L^p s`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.AdjL3Cosets

open Matrix
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators
open TernaryPeriodPolynomials.Spectral.HeckeH1
open TernaryPeriodPolynomials.LevelThree.LevelThreeCosets
open TernaryPeriodPolynomials.LevelThree.GammaOneThree (core coreT coreL)

variable (p : Nat.Primes) (hp3 : p.val ≠ 3)

theorem upper_mem_core (n : ℤ) : upper n ∈ core := by
  rw [upper_zpow]
  exact core.zpow_mem coreT.2 n

theorem lower_mem_core (n : ℤ) : lower n ∈ core := by
  rw [lower_zpow]
  exact core.zpow_mem coreL.2 n

/-- **The determinant-one part `Γ₁(3) ∩ Γ⁰(p)` of the stabilizer of the base coset.** -/
def stabCore : Subgroup binaryArithmeticLevel := core ⊓ stabH p hp3

theorem mem_stabCore_iff (h : binaryArithmeticLevel) :
    h ∈ stabCore p hp3 ↔ GeneralLinearGroup.det h.val = 1 ∧ (p.val : ℤ) ∣ h.val.val 0 1 := by
  rw [stabCore, Subgroup.mem_inf, mem_core_iff, mem_stabH_iff]

theorem stabCore_le_stabH : stabCore p hp3 ≤ stabH p hp3 := inf_le_right

theorem upper_mem_stabCore : upper (p.val : ℤ) ∈ stabCore p hp3 :=
  Subgroup.mem_inf.mpr ⟨upper_mem_core _, upper_mem_stabH p hp3⟩

theorem lower_mem_stabCore (n : ℤ) : lower n ∈ stabCore p hp3 :=
  Subgroup.mem_inf.mpr ⟨lower_mem_core _, lower_mem_stabH p hp3 n⟩

/-- The Fricke conjugation preserves the determinant. -/
theorem det_frickeVal (h : binaryArithmeticLevel) (hh : (p.val : ℤ) ∣ h.val.val 0 1) :
    GeneralLinearGroup.det (frickeVal p hp3 h hh).val = GeneralLinearGroup.det h.val := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_det_apply, frickeVal_val,
    Matrix.det_fin_two_of]
  exact frickeEntries_det p h hh

theorem det_frickeElt (h : stabH p hp3) :
    GeneralLinearGroup.det (frickeElt p hp3 h).val = GeneralLinearGroup.det h.1.val :=
  det_frickeVal p hp3 h.1 (dvd_of_mem_stabH p hp3 h.2)

theorem frickeElt_mem_core (h : stabH p hp3) (hc : h.1 ∈ core) : frickeElt p hp3 h ∈ core := by
  rw [mem_core_iff] at hc ⊢
  rw [det_frickeElt, hc]

/-- The Fricke conjugate of an element of the determinant-one stabilizer. -/
def frickeCoreElt (h : stabCore p hp3) : binaryArithmeticLevel :=
  frickeElt p hp3 ⟨h.1, stabCore_le_stabH p hp3 h.2⟩

theorem frickeCoreElt_mem (h : stabCore p hp3) : frickeCoreElt p hp3 h ∈ stabCore p hp3 :=
  Subgroup.mem_inf.mpr ⟨frickeElt_mem_core p hp3 _ (Subgroup.mem_inf.mp h.2).1,
    frickeElt_mem p hp3 _⟩

theorem levelEmbed_frickeCoreElt (h : stabCore p hp3) :
    levelEmbed (frickeCoreElt p hp3 h) = gP p hp3 * levelEmbed h.1 * (gP p hp3)⁻¹ :=
  levelEmbed_frickeElt p hp3 ⟨h.1, stabCore_le_stabH p hp3 h.2⟩

/-- **The Fricke involution of `Γ₁(3) ∩ Γ⁰(p)`.** -/
def frickeCore : stabCore p hp3 →* stabCore p hp3 :=
  MonoidHom.mk' (fun h => ⟨frickeCoreElt p hp3 h, frickeCoreElt_mem p hp3 h⟩) (by
    intro x y
    apply Subtype.ext
    apply levelEmbed_injective
    show levelEmbed (frickeCoreElt p hp3 (x * y)) =
      levelEmbed (frickeCoreElt p hp3 x * frickeCoreElt p hp3 y)
    rw [map_mul, levelEmbed_frickeCoreElt, levelEmbed_frickeCoreElt, levelEmbed_frickeCoreElt,
      Subgroup.coe_mul, map_mul]
    group)

theorem frickeCore_val (h : stabCore p hp3) :
    (frickeCore p hp3 h).1 = (fricke p hp3 ⟨h.1, stabCore_le_stabH p hp3 h.2⟩).1 := rfl

/-- **The conjugation property on the determinant-one part.** -/
theorem levelEmbed_frickeCore (h : stabCore p hp3) :
    levelEmbed (frickeCore p hp3 h).1 = gP p hp3 * levelEmbed h.1 * (gP p hp3)⁻¹ :=
  levelEmbed_fricke p hp3 ⟨h.1, stabCore_le_stabH p hp3 h.2⟩

/-- **The Fricke involution of the determinant-one part is an involution.** -/
theorem frickeCore_frickeCore (h : stabCore p hp3) :
    frickeCore p hp3 (frickeCore p hp3 h) = h := by
  apply Subtype.ext
  apply levelEmbed_injective
  rw [levelEmbed_frickeCore, levelEmbed_frickeCore]
  have hc := gP_sq_central p hp3 (levelEmbed h.1)
  calc gP p hp3 * (gP p hp3 * levelEmbed h.1 * (gP p hp3)⁻¹) * (gP p hp3)⁻¹
      = (gP p hp3 * gP p hp3 * levelEmbed h.1) * ((gP p hp3)⁻¹ * (gP p hp3)⁻¹) := by group
    _ = (levelEmbed h.1 * (gP p hp3 * gP p hp3)) * ((gP p hp3)⁻¹ * (gP p hp3)⁻¹) := by rw [hc]
    _ = levelEmbed h.1 := by group

/-- `s⁻¹ T s ∈ Γ₁(3) ∩ Γ⁰(p)`. -/
theorem sInv_upper_sF_mem : sInv p hp3 * upper 1 * sF p hp3 ∈ stabCore p hp3 := by
  rw [← fricke_upper]
  exact frickeCoreElt_mem p hp3 ⟨upper (p.val : ℤ), upper_mem_stabCore p hp3⟩

/-- `s⁻¹ L^p s ∈ Γ₁(3) ∩ Γ⁰(p)`. -/
theorem sInv_lower_sF_mem : sInv p hp3 * lower (p.val : ℤ) * sF p hp3 ∈ stabCore p hp3 := by
  rw [← fricke_lower]
  exact frickeCoreElt_mem p hp3 ⟨lower 1, lower_mem_stabCore p hp3 1⟩

/-- **The Fricke involution exchanges `T^p` and `s⁻¹ T s`** (determinant-one part). -/
theorem frickeCore_upper :
    (frickeCore p hp3 ⟨upper (p.val : ℤ), upper_mem_stabCore p hp3⟩).1 =
      sInv p hp3 * upper 1 * sF p hp3 := fricke_upper p hp3

theorem frickeCore_upper' :
    frickeCore p hp3 ⟨sInv p hp3 * upper 1 * sF p hp3, sInv_upper_sF_mem p hp3⟩ =
      ⟨upper (p.val : ℤ), upper_mem_stabCore p hp3⟩ := by
  have h := frickeCore_frickeCore p hp3 ⟨upper (p.val : ℤ), upper_mem_stabCore p hp3⟩
  have e : frickeCore p hp3 ⟨upper (p.val : ℤ), upper_mem_stabCore p hp3⟩ =
      ⟨sInv p hp3 * upper 1 * sF p hp3, sInv_upper_sF_mem p hp3⟩ :=
    Subtype.ext (frickeCore_upper p hp3)
  rw [e] at h
  exact h

/-- **The Fricke involution exchanges `L` and `s⁻¹ L^p s`** (determinant-one part). -/
theorem frickeCore_lower :
    frickeCore p hp3 ⟨lower 1, lower_mem_stabCore p hp3 1⟩ =
      ⟨sInv p hp3 * lower (p.val : ℤ) * sF p hp3, sInv_lower_sF_mem p hp3⟩ :=
  Subtype.ext (fricke_lower p hp3)

theorem frickeCore_lower' :
    frickeCore p hp3 ⟨sInv p hp3 * lower (p.val : ℤ) * sF p hp3, sInv_lower_sF_mem p hp3⟩ =
      ⟨lower 1, lower_mem_stabCore p hp3 1⟩ := by
  have h := frickeCore_frickeCore p hp3 ⟨lower 1, lower_mem_stabCore p hp3 1⟩
  rw [frickeCore_lower] at h
  exact h

end TernaryPeriodPolynomials.BoundaryDuality.AdjL3Cosets
