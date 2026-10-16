module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.SymbolRestriction

@[expose] public section


open Matrix
noncomputable section
namespace TernaryPoly.OrdinaryResidueSymbol
open OrdinaryPlaneEdge OrdinaryResidueSupport SinglePoleSupport SinglePole OrdinaryResidueParabolic SinglePoleCoordinate
open OrdinaryApartmentPresentation OrdinaryApartmentSpanComparison AugmentedFrameComplex

/-- A frame meets the plane in a coordinate pair exactly when its first row is supported in one position. -/
def FrameFirstRowCoordinate (g : ModThreeGoodAction.IntegralGL) : Prop :=
  ∃ i : Fin 3, ∀ j : Fin 3, j ≠ i → g.val 0 j = 0

theorem rowAction_axis_coordinate_iff (g : ModThreeGoodAction.IntegralGL) :
    Coordinate (rowAction g (axis 0)) ↔ FrameFirstRowCoordinate g := by
  rw [axis,rowAction_normalOfRow,coordinate_normalOfRow_iff]
  simp [FrameFirstRowCoordinate,Matrix.vecMul,dotProduct,Pi.single_apply]

/-- The actual integral column line lies in a=0 exactly when its first entry vanishes. -/
theorem frame_line_le_planeZero (g : ModThreeGoodAction.IntegralGL) (j : Fin 3) :
    (line (augmentedLine g j.castSucc)).val ≤ planeZero.val ↔ g.val 0 j = 0 := by
  change (augmentedLine g j.castSucc).val ≤ planeZero.val ↔ _
  rw [IntegralFrameHeightReduction.columnLine_span]
  simp [Submodule.span_le,ModThreeGoodAction.rationalVector]

/-- If the frame has no pair-plane equal to a=0, its actual residue coordinate is zero. -/
theorem coordinate_frame_zero (n : ℕ) (F : OrdinaryFullCoefficient.ResidueHom n (-1))
    (g : ModThreeGoodAction.IntegralGL) (hg : ¬FrameFirstRowCoordinate g) :
    zeroCoordinate n (F.val (frameCycle g)) = 0 := by
  rw [OrdinaryFullCoefficient.hom_frame]
  change literalFiberMap n 0 ((integralResidueAction n (-1) g
    (OrdinaryFullCoefficient.reference (residueAction n (-1)) F)) (axis 0)) = 0
  rw [component_action_zero_of n (-1) g (axis 0) _ ?_,map_zero]
  let r := OrdinaryFullCoefficient.reference (residueAction n (-1)) F
  have hr := OrdinaryFullCoefficient.hom_relations (residueAction n (-1)) F
  exact residue_coordinate_support n (-1) r
    (OrdinaryResiduePeriod.symmetric_of_relations n r hr)
    (OrdinaryResiduePeriod.odd_of_relations n r hr) hr.norm _
    (fun h => hg ((rowAction_axis_coordinate_iff g).mp h))

/-- A two-line chain contributes only when both endpoint lines lie in the selected plane. -/
theorem projection_lineChain_zero (P : OrdinaryIncidence.Plane) (L M : OrdinaryIncidence.Line)
    (h : ¬(L.val ≤ P.val ∧ M.val ≤ P.val)) :
    projection P (GoodApartmentCycles.lineChain (fun _ => True) L M) = 0 := by
  by_cases hL : L.val ≤ P.val
  · have hM : ¬M.val ≤ P.val := fun hm => h ⟨hL,hm⟩
    rw [GoodApartmentCycles.lineChain_reverse, map_neg,projection_lineChain_outside P M L hM,neg_zero]
  · exact projection_lineChain_outside P L M hL

/-- A frame with no incident coordinate pair has zero literal plane-edge projection. -/
theorem project_frame_zero (g : ModThreeGoodAction.IntegralGL) (hg : ¬FrameFirstRowCoordinate g) :
    binaryProject (frameCycle g) = 0 := by
  have h01 : ¬((line (augmentedLine g 0)).val ≤ planeZero.val ∧
      (line (augmentedLine g 1)).val ≤ planeZero.val) := by
    intro h
    have h0 := (frame_line_le_planeZero g 0).mp h.1
    have h1 := (frame_line_le_planeZero g 1).mp h.2
    apply hg
    refine ⟨2,?_⟩
    intro j hj
    fin_cases j
    · exact h0
    · exact h1
    · exact (hj rfl).elim
  have h12 : ¬((line (augmentedLine g 1)).val ≤ planeZero.val ∧
      (line (augmentedLine g 2)).val ≤ planeZero.val) := by
    intro h
    have h1 := (frame_line_le_planeZero g 1).mp h.1
    have h2 := (frame_line_le_planeZero g 2).mp h.2
    apply hg
    refine ⟨0,?_⟩
    intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact h1
    · exact h2
  have h20 : ¬((line (augmentedLine g 2)).val ≤ planeZero.val ∧
      (line (augmentedLine g 0)).val ≤ planeZero.val) := by
    intro h
    have h2 := (frame_line_le_planeZero g 2).mp h.1
    have h0 := (frame_line_le_planeZero g 0).mp h.2
    apply hg
    refine ⟨1,?_⟩
    intro j hj
    fin_cases j
    · exact h0
    · exact (hj rfl).elim
    · exact h2
  have hp : project planeZero (frameCycle g) = 0 := by
    apply Subtype.ext
    rw [project_val,frameCycle_apartment,GoodApartmentCycles.apartmentCycle_coe,
      GoodApartmentCycles.apartmentChain,map_add,map_add,
      projection_lineChain_zero planeZero _ _ h01,projection_lineChain_zero planeZero _ _ h12,
      projection_lineChain_zero planeZero _ _ h20,add_zero,add_zero]
    rfl
  change symbolEquiv.symm (project planeZero (frameCycle g)) = 0
  rw [hp,map_zero]

end TernaryPoly.OrdinaryResidueSymbol
