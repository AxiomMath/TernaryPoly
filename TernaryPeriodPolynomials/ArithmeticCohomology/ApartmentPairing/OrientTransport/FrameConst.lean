module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.FrameFor

@[expose] public section


/-!
# A frame whose tube radius is constant on the chart box

`frame_for_const` is `Locality.frame_for` with the additional output that the tube radius `ρ'` is a constant `η > 0` on the closed
chart box `boxC ε R0`.  The radius is replaced by `min ρ' η`, where `η` is the minimum of `ρ'` on the (compact) box: the tube only
shrinks, and every property of the frame that is monotone in the tube (disjointness from the translated boxes, local finiteness,
the neighbourhood condition `D ∩ tube ⊆ box`, `ρ' < ‖π‖` on the lower cells) is preserved.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical Pointwise

namespace TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport

open TernaryPeriodPolynomials.Argument.Lemma33.Locality
open TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.IntegralGL3Congruence
  TernaryPeriodPolynomials.Argument.Lemma33.Retract
  TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree
  TernaryPeriodPolynomials.Argument.Lemma33.Retract.Cell0Geometry

theorem tube_min_subset (ρ' : Space → ℝ) (η : ℝ) :
    tube (fun S => min (ρ' S) η) ⊆ tube ρ' := fun _ (h : _ ≤ _) => (h.trans (min_le_left _ _) : _ ≤ ρ' _)

/-- **A frame with constant tube radius on the chart box.** -/
theorem frame_for_const (𝒞 : Finset (Graded 3)) :
    ∃ F : FrameOut,
      (∀ C ∈ 𝒞, ∀ g : principalSix, g • cellSet 3 C.1 ⊆ F.D) ∧
      (∀ C ∈ 𝒞, ∀ g : principalSix, g • C.1 ≠ T0 →
        cellSet 3 (g • C.1) ⊆ {S : Space | F.ρ' S < ‖piR3 S‖}) ∧
      (∀ D ∈ (incQ T0).support, cellSet 2 D ⊆ {S : Space | F.ρ' S < ‖piR3 S‖}) ∧
      ∃ η : ℝ, 0 < η ∧ ∀ S ∈ boxC F.ε F.R0, F.ρ' S = η := by
  obtain ⟨F, h1, h2, h3⟩ := frame_for 𝒞
  have hne : (boxC F.ε F.R0).Nonempty :=
    ⟨p0, boxO_subset_boxC _ _ (p0_mem_boxO F.hε (F.hδ.trans F.hδR))⟩
  obtain ⟨S0, hS0, hmin⟩ := (isCompact_boxC F.ε F.R0).exists_isMinOn hne F.hρc.continuousOn
  set η := F.ρ' S0 with hη
  have hηpos : 0 < η := F.hρpos S0
  have hle : ∀ S ∈ boxC F.ε F.R0, η ≤ F.ρ' S := fun S hS => hmin hS
  let F' : FrameOut :=
    { F with
      ρ' := fun S => min (F.ρ' S) η
      hρc := F.hρc.min continuous_const
      hρpos := fun S => lt_min (F.hρpos S) hηpos
      hρε := fun S => lt_of_le_of_lt (min_le_left _ _) (F.hρε S)
      hone := fun g hg => (F.hone g hg).mono_right (tube_min_subset F.ρ' η)
      hfin := fun K hK => (F.hfin K hK).subset (fun g hg =>
        hg.mono (Set.inter_subset_inter_right _ (tube_min_subset F.ρ' η)))
      hDz := fun S hS hSt => F.hDz S hS (tube_min_subset F.ρ' η hSt) }
  refine ⟨F', h1, ?_, ?_, η, hηpos, ?_⟩
  · intro C hC g hg S hS
    exact lt_of_le_of_lt (min_le_left _ _) (show F.ρ' S < ‖piR3 S‖ from h2 C hC g hg hS)
  · intro D hD S hS
    exact lt_of_le_of_lt (min_le_left _ _) (show F.ρ' S < ‖piR3 S‖ from h3 D hD hS)
  · intro S hS
    exact min_eq_right (hle S hS)

end TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport
