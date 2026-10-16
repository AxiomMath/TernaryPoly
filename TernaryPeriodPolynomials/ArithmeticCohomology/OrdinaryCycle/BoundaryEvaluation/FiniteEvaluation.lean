module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.FiniteCone
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullOrdinaryCoordinates

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryActualEvaluation
open CategoryTheory HomologicalComplex Representation SymmetricSpaceBoundaryFull
open ReferenceCoefficientMatrices OrdinaryParabolicGroups

section Induction
variable {G : Type} [Group G] (S : Subgroup G) (W : Rep.{0} ℚ G)

/-- Exact induced zero-bar evaluation, including the inverse ambient coefficient action. -/
theorem inducedZero_cochain (b : (inducedBarComplex S).X 0 ⟶ W) (g : G) :
    b.hom (inducedZero S g) = W.ρ g⁻¹ (b.hom (inducedZero S 1)) := by
  have h := Rep.hom_comm_apply b g⁻¹ (inducedZero S 1)
  change b.hom (Representation.ind S.subtype ((Rep.barResolution ℚ S).complex.X 0).ρ
    g⁻¹ (IndV.mk _ _ 1 (scalarBarZero S))) = _ at h
  simp only [ind_mk, inv_inv, one_mul] at h
  exact h

/-- Exact induced one-bar evaluation, retaining both ambient action and subgroup argument. -/
theorem inducedOne_cochain (b : (inducedBarComplex S).X 1 ⟶ W) (g : G) (h : S) :
    b.hom (inducedOne S g h) = W.ρ g⁻¹ (b.hom (inducedOne S 1 h)) := by
  have he := Rep.hom_comm_apply b g⁻¹ (inducedOne S 1 h)
  change b.hom (Representation.ind S.subtype ((Rep.barResolution ℚ S).complex.X 1).ρ
    g⁻¹ (IndV.mk _ _ 1 (scalarBarOne S h))) = _ at he
  simp only [ind_mk, inv_inv, one_mul] at he
  exact he
end Induction

variable (W : Rep.{0} ℚ ModThreeGoodAction.IntegralGL)

/-- Full corner evaluation as the six actual permutation translates of its identity value. -/
theorem finiteApartmentCorner_cochain (b : (inducedBarComplex B).X 0 ⟶ W) :
    b.hom finiteApartmentCorner =
      (b.hom (inducedZero B 1) - W.ρ s (b.hom (inducedZero B 1))) +
      (W.ρ c (b.hom (inducedZero B 1)) - W.ρ (c*s) (b.hom (inducedZero B 1))) +
      (W.ρ c⁻¹ (b.hom (inducedZero B 1)) - W.ρ (c⁻¹*s) (b.hom (inducedZero B 1))) := by
  simp only [finiteApartmentCorner, map_add, map_sub]
  conv_lhs => rw [inducedZero_cochain B W b 1, inducedZero_cochain B W b s,
    inducedZero_cochain B W b c⁻¹, inducedZero_cochain B W b (s*c⁻¹),
    inducedZero_cochain B W b c, inducedZero_cochain B W b (s*c)]
  simp only [inv_one, inv_inv, mul_inv_rev, s_inv_eq_self, map_one, Module.End.one_apply]

/-- Full line evaluation as the three actual cyclic translates of its identity-induced one-bar value. -/
theorem finiteApartmentLine_cochain (b : (inducedBarComplex Q).X 1 ⟶ W) :
    b.hom finiteApartmentLine = b.hom (inducedOne Q 1 finiteLineSwap) +
      W.ρ c (b.hom (inducedOne Q 1 finiteLineSwap)) + W.ρ c⁻¹ (b.hom (inducedOne Q 1 finiteLineSwap)) := by
  rw [finiteApartmentLine, map_add, map_add]
  conv_lhs => rw [inducedOne_cochain Q W b c⁻¹ finiteLineSwap, inducedOne_cochain Q W b c finiteLineSwap]
  rw [inv_inv]

/-- Full plane evaluation as the three actual cyclic translates of its identity-induced one-bar value. -/
theorem finiteApartmentPlane_cochain (b : (inducedBarComplex P).X 1 ⟶ W) :
    b.hom finiteApartmentPlane = b.hom (inducedOne P 1 finitePlaneSwap) +
      W.ρ c (b.hom (inducedOne P 1 finitePlaneSwap)) + W.ρ c⁻¹ (b.hom (inducedOne P 1 finitePlaneSwap)) := by
  rw [finiteApartmentPlane, map_add, map_add]
  conv_lhs => rw [inducedOne_cochain P W b c⁻¹ finitePlaneSwap, inducedOne_cochain P W b c finitePlaneSwap]
  rw [inv_inv]

/-- The finite canonical cycle pairing keeps its complete face values and corner sign. -/
theorem finiteApartmentChain_cochain (b : canonicalFaceCone.X 1 ⟶ W) :
    b.hom finiteApartmentChain =
      -((canonicalCornerCochain W 0 b).hom finiteApartmentCorner +
        (canonicalLineCochain W 1 b).hom finiteApartmentLine -
        (canonicalPlaneCochain W 1 b).hom finiteApartmentPlane) := by
  unfold finiteApartmentChain
  erw [map_neg, map_sub, map_add]
  rfl

end TernaryPoly.OrdinaryBoundaryActualEvaluation
