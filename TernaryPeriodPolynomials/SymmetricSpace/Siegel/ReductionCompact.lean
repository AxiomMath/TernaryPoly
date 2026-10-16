module

public import TernaryPeriodPolynomials.SymmetricSpace.Flag.CoordinatesCorner
public import Mathlib.Topology.Order.Compact

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceSiegelReduction
open SymmetricSpacePositive SymmetricSpaceFlagCoordinates

/-- The closed simple-root quadrant box, allowing the two boundary parameters to vanish. -/
def cornerBox (U T : ℝ) : Set Corner :=
  {p | (∀ i, |p.1 i|≤U) ∧ p.2.1.val≤T ∧ p.2.2.val≤T}

theorem isCompact_halfLine_segment (T : ℝ) :
    IsCompact {t : HalfLine | t.val≤T} := by
  rw [Subtype.isCompact_iff]
  have he : (Subtype.val '' {t : HalfLine | t.val≤T} : Set ℝ)=Set.Icc 0 T := by
    ext r
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨t.property,ht⟩
    · intro hr
      exact ⟨⟨r,hr.1⟩,hr.2,rfl⟩
  rw [he]
  exact isCompact_Icc

/-- Compactness is for the actual finite product of closed bounded real intervals. -/
theorem isCompact_cornerBox (U T : ℝ) : IsCompact (cornerBox U T) := by
  have hu : IsCompact {v : Vec3 | ∀ i, |v i|≤U} := by
    have hi : IsCompact {v : Vec3 | ∀ i, v i∈Set.Icc (-U) U} :=
      isCompact_pi_infinite (fun _ : Fin 3 => (isCompact_Icc : IsCompact (Set.Icc (-U) U)))
    convert hi using 1
    ext v
    simp only [Set.mem_ofPred_eq,Set.mem_Icc,abs_le]

  exact hu.prod ((isCompact_halfLine_segment T).prod (isCompact_halfLine_segment T))

/-- The positive points of the box correspond exactly to actual root coordinates with these bounds. -/
theorem cornerEmbedding_mem_box (U T : ℝ) (S : Space) :
    cornerEmbedding S∈cornerBox U T ↔
      (∀ i, |(rootHomeomorph S).1 i|≤U) ∧
        (rootHomeomorph S).2.1.val≤T ∧ (rootHomeomorph S).2.2.val≤T := Iff.rfl

end TernaryPoly.SymmetricSpaceSiegelReduction
