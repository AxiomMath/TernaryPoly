module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Full.ActionChains
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Apartment.Presentation

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryFullAction
open ModThreeGoodAction AugmentedFrameComplex GoodRelativeChains
open OrdinaryApartmentFrames OrdinaryApartmentPresentation OrdinaryApartmentSpanComparison IntegralFrameHeightReduction
local instance : DecidableEq RationalLine := Classical.decEq _

/-- The unrestricted integral action is the same literal line transport as the frame action. -/
theorem lineAction_integral (g : IntegralGL) (L : RationalLine) :
    lineAction (integral g) (line L) = line (AugmentedChainAction.lineAction g L) := rfl

/-- Every integral frame apartment is transported to the product frame by the full action. -/
theorem frameCycle_equivariant (g h : IntegralGL) :
    cycleAction (integral g) (frameCycle h) = frameCycle (g*h) := by
  rw [frameCycle_apartment,frameCycle_apartment]
  apply Subtype.ext
  have he := GoodApartmentCycles.apartmentChainEquiv_apartment (fun _ => True)
    (subspaceAction (integral g)) (subspaceAction_finrank (integral g)) (fun _ => Iff.rfl)
    (line (augmentedLine h 0)) (line (augmentedLine h 1)) (line (augmentedLine h 2))
  change edgeRepresentation (integral g)
    (GoodApartmentCycles.apartmentChain (fun _ => True) (line (augmentedLine h 0))
      (line (augmentedLine h 1)) (line (augmentedLine h 2))) =
    GoodApartmentCycles.apartmentChain (fun _ => True)
      (lineAction (integral g) (line (augmentedLine h 0)))
      (lineAction (integral g) (line (augmentedLine h 1)))
      (lineAction (integral g) (line (augmentedLine h 2))) at he
  rw [lineAction_integral,lineAction_integral,lineAction_integral,
    AugmentedChainAction.lineAction_augmentedLine,AugmentedChainAction.lineAction_augmentedLine,
    AugmentedChainAction.lineAction_augmentedLine] at he
  exact he

/-- An apartment depends only on its ordered rational lines. -/
theorem frameCycle_lines (g h : IntegralGL) (he : triangleList g = triangleList h) :
    frameCycle g = frameCycle h := by
  apply congrArg OrdinaryApartmentSpanComparison.comparison
  apply congrArg OrdinaryRelativeChains.quotientMap
  apply Subtype.ext
  exact congrArg OrientedListChains.simplex he

/-- Column signs do not change any of the actual rational lines. -/
theorem triangleList_signFrame (g : IntegralGL) (s : Finset (Fin 3)) :
    triangleList (g*signFrame s) = triangleList g := by
  have h (j : Fin 3) : augmentedLine (g*signFrame s) j.castSucc = augmentedLine g j.castSucc := by
    apply Subtype.ext
    rw [columnLine_span,columnLine_span]
    by_cases hj : j ∈ s
    · have hc : (g*signFrame s).val.col j = -g.val.col j := by
        funext i
        change (g*signFrame s).val i j = -g.val i j
        rw [mul_signFrame_entry]
        simp only [signEntry,ite_eq_left hj,mul_neg_one]
      rw [hc]
      have hn : rationalVector (-g.val.col j) = -rationalVector (g.val.col j) := by
        funext i; simp [rationalVector]
      rw [hn,←Set.neg_singleton,Submodule.span_neg]
    · have hc : (g*signFrame s).val.col j = g.val.col j := by
        funext i
        change (g*signFrame s).val i j = g.val i j
        rw [mul_signFrame_entry]
        simp only [signEntry,ite_eq_right hj,mul_one]
      rw [hc]
  exact congrArg (fun x : Fin 3 → RationalLine => [x 0,x 1,x 2]) (funext h)

theorem frameCycle_signFrame (g : IntegralGL) (s : Finset (Fin 3)) :
    frameCycle (g*signFrame s) = frameCycle g :=
  frameCycle_lines _ _ (triangleList_signFrame g s)

theorem frameCycle_cyclic (g : IntegralGL) :
    frameCycle (g*ReferenceCoefficientMatrices.c) = frameCycle g := by
  rw [frameCycle_apartment,frameCycle_apartment]
  have h0 : augmentedLine (g*ReferenceCoefficientMatrices.c) 0 = augmentedLine g 1 := mul_c_line g 0
  have h1 : augmentedLine (g*ReferenceCoefficientMatrices.c) 1 = augmentedLine g 2 := mul_c_line g 1
  have h2 : augmentedLine (g*ReferenceCoefficientMatrices.c) 2 = augmentedLine g 0 := mul_c_line g 2
  rw [h0,h1,h2]
  exact GoodApartmentCycles.apartmentCycle_cyclic _ _ _ _

theorem frameCycle_swap (g : IntegralGL) :
    frameCycle (g*ReferenceCoefficientMatrices.s) = -frameCycle g := by
  rw [frameCycle_apartment,frameCycle_apartment]
  have h0 : augmentedLine (g*ReferenceCoefficientMatrices.s) 0 = augmentedLine g 1 := mul_s_line g 0
  have h1 : augmentedLine (g*ReferenceCoefficientMatrices.s) 1 = augmentedLine g 0 := mul_s_line g 1
  have h2 : augmentedLine (g*ReferenceCoefficientMatrices.s) 2 = augmentedLine g 2 := mul_s_line g 2
  rw [h0,h1,h2]
  exact GoodApartmentCycles.apartmentCycle_swap _ _ _ _

/-- The actual tetrahedron boundary and proper core give the order-three relation on cycles. -/
theorem frameCycle_norm (g : IntegralGL) :
    frameCycle g + frameCycle (g*ReferenceCoefficientMatrices.a) +
      frameCycle (g*ReferenceCoefficientMatrices.a^2) = 0 := by
  have hat : OrientedListChains.Allowed ambient (tetrahedronList g) := by
    apply OrdinaryRelativeChains.allowed_frame_list g _ (by simp [tetrahedronList])
    intro L hL
    simp only [tetrahedronList,List.mem_cons,List.not_mem_nil,or_false] at hL
    rcases hL with rfl | rfl | rfl | rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨3,rfl⟩
    · exact ⟨2,rfl⟩
  have ht : OrientedListChains.simplex (tetrahedronList g) ∈
      OrientedListChains.chains ambient 4 :=
    OrientedListChains.simplex_mem_chains ambient (tetrahedronList g) hat
  have hac : OrientedListChains.Allowed OrdinaryRelativeChains.properAmbient (coreList g) := by
    apply Or.inr
    refine ⟨?_,OrdinaryRelativeChains.coreList_finrank g⟩
    have h := OrdinaryRelativeChains.allowed_frame_list g (coreList g) (by simp [coreList]) (by
      intro L hL
      simp only [coreList,List.mem_cons,List.not_mem_nil,or_false] at hL
      rcases hL with rfl | rfl | rfl
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
      · exact ⟨3,rfl⟩)
    exact h.resolve_left (by simp [coreList])
  have hp : OrientedListChains.simplex (coreList g) ∈
      OrientedListChains.chains OrdinaryRelativeChains.properAmbient 3 :=
    OrientedListChains.simplex_mem_chains OrdinaryRelativeChains.properAmbient (coreList g) hac
  have hid : OrdinaryRelativeChains.triangle g +
      OrdinaryRelativeChains.triangle (g*ReferenceCoefficientMatrices.a) +
      OrdinaryRelativeChains.triangle (g*ReferenceCoefficientMatrices.a^2) =
      OrientedListChains.differential ambient 3 ⟨_,ht⟩ +
        OrdinaryRelativeChains.properInclusion ⟨_,hp⟩ :=
    Subtype.ext (OrdinaryRelativeChains.triangle_norm_boundary g)
  simp only [frameCycle,←map_add]
  rw [hid,map_add,OrdinaryRelativeChains.quotientMap_boundary,
    OrdinaryRelativeChains.quotientMap_proper,add_zero,map_zero]

end TernaryPoly.OrdinaryFullAction
