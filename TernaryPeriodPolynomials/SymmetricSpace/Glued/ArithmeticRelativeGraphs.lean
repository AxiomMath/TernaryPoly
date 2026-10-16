module

public import TernaryPeriodPolynomials.SymmetricSpace.Glued.ArithmeticDual

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceGluedArithmetic
open Matrix SymmetricSpacePositive SymmetricSpaceFlagCoordinates SymmetricSpaceRationalGluing
open SymmetricSpaceRationalAction SymmetricSpaceCornerSeparation

/-- Equality of actual arithmetic chart points is the literal full relative transition graph. -/
theorem integral_chart_eq_iff_graph (a b : RationalGL) (g : IntegralGL) (p q : Corner) :
    integralAction g (chart a p)=chart b q ↔ (p,q)∈fullGraph (realRational (relative a b g)) := by
  rw [integralAction_chart,chart_eq_iff]
  have hm : changeMatrix (integralRational g*a) b=realRational (relative a b g) := by
    simp only [changeMatrix,relative,mul_assoc]
  change (∃ hp : p∈domain (changeMatrix (integralRational g*a) b),
    (transition (changeMatrix (integralRational g*a) b) ⟨p,hp⟩).val=q) ↔ _
  rw [hm]
  rfl

/-- A compact pair of corners has one bound for both roots and all actual shear coordinates. -/
theorem compact_corner_bound (K L : Set Corner) (hK : IsCompact K) (hL : IsCompact L) :
    ∃ M : ℝ,1≤M ∧ ∀ p∈K∪L,(∀ i,|p.1 i|≤M) ∧ p.2.1.val≤M ∧ p.2.2.val≤M := by
  have hc : Continuous (fun p : Corner => max ‖p.1‖ (max p.2.1.val p.2.2.val)) :=
    continuous_fst.norm.max
      ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).max
        (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)))
  obtain ⟨B,hB⟩ := (hK.union hL).bddAbove_image hc.continuousOn
  refine ⟨max 1 B,le_max_left _ _,?_⟩
  intro p hp
  have hb : max ‖p.1‖ (max p.2.1.val p.2.2.val)≤max 1 B :=
    (hB ⟨p,hp,rfl⟩).trans (le_max_right _ _)
  refine ⟨fun i => (norm_le_pi_norm p.1 i).trans ((le_max_left _ _).trans hb),?_,?_⟩
  · exact (le_max_left _ _).trans ((le_max_right _ _).trans hb)
  · exact (le_max_right _ _).trans ((le_max_right _ _).trans hb)

end TernaryPoly.SymmetricSpaceGluedArithmetic
