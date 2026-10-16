module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.BridgeFrame
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.SpaceCover

@[expose] public section


/-!
# Lemma 3.3, G3: the flat points over the support lie in the chart box

`FrameOut.flat_over`: a flat point of the symmetric space whose image in the base lies in the image of the
neighbourhood `D` of the retract or of the closed slab lies in the chart box.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical Pointwise

namespace TernaryPeriodPolynomials.Argument.Lemma33.Locality

open CategoryTheory TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.IntegralGL3Congruence
  TernaryPeriodPolynomials.Argument.Lemma33.Retract SphereOddDegree
  TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree

section FlatOver

variable {B : TopCat.{0}} (p : SpaceTop ⟶ B) (hp : IsQuotientCoveringMap p principalSix) (F : FrameOut)

include hp

/-- A flat point whose image lies over the neighbourhood of the retract or the slab lies in the chart box. -/
theorem FrameOut.flat_over (K : Set B) (hK : K ⊆ F.D1 p ∪ F.Qs p) (S : Space) (hS : S ∈ flat)
    (hSK : p S ∈ K) : S ∈ F.Tt := by
  have hτ : S ∈ tube F.ρ' := by
    change ‖piR3 S‖ ≤ F.ρ' S
    have : piR3 S = 0 := hS
    rw [this, norm_zero]
    exact (F.hρpos S).le
  rcases hK hSK with ⟨d, hd, hdS⟩ | ⟨q, hq, hqS⟩
  · obtain ⟨g, hg⟩ := (cover_eq_iff p hp d S).mp hdS
    have hSD : S ∈ F.D := by
      have := F.hDg g⁻¹ d hd
      rw [← hg, inv_smul_smul] at this
      exact this
    exact F.hDz S hSD hτ
  · obtain ⟨g, hg⟩ := (cover_eq_iff p hp q S).mp hqS
    by_cases hg1 : g = 1
    · subst hg1
      rw [one_smul] at hg
      have hq2 : S ∈ boxC F.ε F.δ := hg ▸ hq
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_ball, dist_zero_right, coordHomeo_fst]
        have : piR3 S = 0 := hS
        rw [this, norm_zero]; exact F.hε
      · rw [Metric.mem_ball, dist_zero_right]
        have := hq2.2
        rw [Metric.mem_closedBall, dist_zero_right] at this
        exact lt_of_le_of_lt this F.hδR
    · exfalso
      have hq' : q ∈ boxC F.ε F.R0 := F.boxC_slab_sub hq
      have hmem : S ∈ g⁻¹ • boxC F.ε F.R0 :=
        Set.mem_smul_set_iff_inv_smul_mem.mpr (by rw [inv_inv, hg]; exact hq')
      exact Set.disjoint_left.mp (F.hone g⁻¹ (inv_ne_one.mpr hg1)) hmem hτ

end FlatOver

end TernaryPeriodPolynomials.Argument.Lemma33.Locality
