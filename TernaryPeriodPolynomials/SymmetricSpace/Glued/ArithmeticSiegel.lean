module

public import TernaryPeriodPolynomials.SymmetricSpace.Glued.ArithmeticLowerLeft
public import TernaryPeriodPolynomials.SymmetricSpace.Glued.ArithmeticLineFinite

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceGluedArithmetic
open Matrix SymmetricSpacePositive SymmetricSpaceFlagCoordinates SymmetricSpaceRationalGluing
open SymmetricSpaceRationalAction SymmetricSpaceCornerSeparation

/-- Swapping the two actual chart endpoints inverts their arithmetic transporter. -/
theorem integral_chart_eq_inv (a b : RationalGL) (g : IntegralGL) (p q : Corner)
    (he : integralAction g (chart a p)=chart b q) :
    integralAction g⁻¹ (chart b q)=chart a p := by
  change g⁻¹ • chart b q=chart a p
  change g • chart a p=chart b q at he
  rw [←he,inv_smul_smul]

/-- Nonzero inverse lower-left entries have finite compact-chart transporters as well. -/
theorem compact_inverse_lowerLeft_chart_transporters (a b : RationalGL) (K L : Set Corner)
    (hK : IsCompact K) (hL : IsCompact L) :
    {g : IntegralGL | (realRational (relative a b g))⁻¹.val 2 0≠0 ∧
      ∃ p∈K,∃ q∈L,integralAction g (chart a p)=chart b q}.Finite := by
  refine Set.Finite.of_injOn (f := fun g : IntegralGL => g⁻¹) ?_ inv_injective.injOn
    (compact_lowerLeft_chart_transporters b a L K hL hK)
  rintro g ⟨hne,p,hp,q,hq,he⟩
  have hinv : (realRational (relative a b g))⁻¹=realRational (relative b a g⁻¹) := by
    rw [←map_inv,relative_inv]
  exact ⟨by rwa [←hinv],q,hq,p,hp,integral_chart_eq_inv a b g p q he⟩

/-- Actual integral transporters between arbitrary compact rational chart pieces are finite,
including all zero-root boundary strata. -/
theorem compact_chart_transporters (a b : RationalGL) (K L : Set Corner)
    (hK : IsCompact K) (hL : IsCompact L) :
    {g : IntegralGL | ∃ p∈K,∃ q∈L,integralAction g (chart a p)=chart b q}.Finite := by
  have hf := ((compact_plane_chart_transporters a b K L hK hL).union
    (compact_line_chart_transporters a b K L hK hL)).union
    ((compact_lowerLeft_chart_transporters a b K L hK hL).union
      (compact_inverse_lowerLeft_chart_transporters a b K L hK hL))
  apply hf.subset
  intro g hg
  by_cases h : (realRational (relative a b g)).val 2 0=0
  · by_cases hi : (realRational (relative a b g))⁻¹.val 2 0=0
    · rcases two_lowerLeft_zero_parabolic _ h hi with hp|hl
      · exact Or.inl (Or.inl ⟨hp,hg⟩)
      · exact Or.inl (Or.inr ⟨hl,hg⟩)
    · exact Or.inr (Or.inr ⟨hi,hg⟩)
  · exact Or.inr (Or.inl ⟨h,hg⟩)

end TernaryPoly.SymmetricSpaceGluedArithmetic
