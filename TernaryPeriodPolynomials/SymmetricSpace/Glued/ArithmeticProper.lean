module

public import TernaryPeriodPolynomials.SymmetricSpace.Glued.ArithmeticSiegel
public import TernaryPeriodPolynomials.SymmetricSpace.CompactChartCover

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceGluedArithmetic
open SymmetricSpaceRationalGluing

/-- The literal actual integral action has finite transporters between all compact subsets
of the rational corner gluing. -/
theorem compact_transporter_finite (C D : Set Glued) (hC : IsCompact C) (hD : IsCompact D) :
    {g : IntegralGL | ((g • ·) '' C ∩ D).Nonempty}.Finite :=
  SymmetricSpaceCompactChartCover.finite_compact_transporters
    compact_chart_transporters C D hC hD

/-- An equivalent pointwise form of actual compact transporter finiteness. -/
theorem compact_transporter_finite_pointwise (C D : Set Glued)
    (hC : IsCompact C) (hD : IsCompact D) :
    {g : IntegralGL | ∃ x∈C,integralAction g x∈D}.Finite := by
  refine (compact_transporter_finite C D hC hD).subset ?_
  rintro g ⟨x,hx,hd⟩
  exact ⟨g • x,⟨x,hx,rfl⟩,hd⟩

end TernaryPoly.SymmetricSpaceGluedArithmetic
