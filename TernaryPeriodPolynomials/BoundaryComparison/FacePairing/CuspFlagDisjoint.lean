module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.CuspOrbits
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeGoodCusps.Helpers

@[expose] public section


/-!
# Disjointness of the two plane cusp orbits under the rational level (M4 infrastructure)

`CuspOrbits.cuspFlag .plane true` and `CuspOrbits.cuspFlag .plane false` are, respectively, the
good and bad reference plane flags. `CuspOrbits.cuspFlag_good_iff` identifies `GoodFlag .plane` of
each with `good = true`. Since `GoodFlag` is invariant under the action of `rationalLevel`
(`AwayThreeHeckeGoodCusps.Helpers.good_flag_smul`, applied to level elements via
`CuspOrbits.level_matrix_of_rational_level`), the two reference flags cannot lie in the same
`rationalLevel`-orbit.

This is the ingredient needed to show that a Shapiro-realized plane class supported at one
representative line's dual flag automatically vanishes at the other representative line's dual
flag (`CuspSeparation.fixedPointH2_eq_zero_of_cuspRes` then transports that vanishing from the
plane cusp orbit to the actual dual-flag point), without using
`Separation.exists_cutoff_plane`.
-/

noncomputable section

open GeneralEisenstein
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.AwayThreeHeckeGoodCusps.Helpers

namespace TernaryPeriodPolynomials.Argument.FacePairing


/-- Goodness of a flag is invariant under the action of the rational level subgroup. -/
theorem goodFlag_smul_rationalLevel {side : Side} (γ : rationalLevel) (flag : Flags side) :
    GoodFlag side (γ.val • flag) ↔ GoodFlag side flag := by
  constructor
  · intro h
    have hinv : LevelMatrixAtThree (γ.val)⁻¹ :=
      level_matrix_of_rational_level (inv_mem γ.property)
    have := good_flag_smul hinv h
    rwa [inv_smul_smul] at this
  · exact good_flag_smul (level_matrix_of_rational_level γ.property)

/-- **The two plane cusp orbits are disjoint.** No element of the rational level carries the good
reference plane flag to the bad one. -/
theorem cuspFlag_plane_true_smul_ne_false (γ : rationalLevel) :
    γ.val • cuspFlag .plane true ≠ cuspFlag .plane false := by
  intro h
  have h1 : GoodFlag .plane (cuspFlag .plane true) := (cuspFlag_good_iff .plane true).mpr rfl
  have h2 : GoodFlag .plane (γ.val • cuspFlag .plane true) :=
    (goodFlag_smul_rationalLevel γ _).mpr h1
  rw [h] at h2
  exact absurd ((cuspFlag_good_iff .plane false).mp h2) (by decide)

/-- Symmetric form: no element of the rational level carries the bad reference plane flag to the
good one. -/
theorem cuspFlag_plane_false_smul_ne_true (γ : rationalLevel) :
    γ.val • cuspFlag .plane false ≠ cuspFlag .plane true := by
  intro h
  exact cuspFlag_plane_true_smul_ne_false γ⁻¹
    (by rw [Subgroup.coe_inv, ← h, inv_smul_smul])

/-- **Orbit-level disjointness.** The good and bad reference plane flags are never in the same
`rationalLevel`-orbit. -/
theorem not_exists_smul_cuspFlag_plane_eq (good₁ good₂ : Bool) (hne : good₁ ≠ good₂) :
    ¬ ∃ γ : rationalLevel, γ.val • cuspFlag .plane good₁ = cuspFlag .plane good₂ := by
  rintro ⟨γ, hγ⟩
  match good₁, good₂, hne with
  | true, true, hne => exact hne rfl
  | false, false, hne => exact hne rfl
  | true, false, _ => exact cuspFlag_plane_true_smul_ne_false γ hγ
  | false, true, _ => exact cuspFlag_plane_false_smul_ne_true γ hγ

end TernaryPeriodPolynomials.Argument.FacePairing
