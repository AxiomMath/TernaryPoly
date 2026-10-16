module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.CoordinateFlag
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Orbit.Completion
public import TernaryPeriodPolynomials.Building.Reference.ApartmentRelations
public import TernaryPeriodPolynomials.Building.Good.ApartmentEquivariance

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryCoordinateApartment
open ModThreeGoodAction GoodIncidenceConnected GoodApartmentCycles
open ReferenceApartmentRelations ReferenceCoefficientMatrices
open RelativeStabilizerCoordinates

/-- The literal inclusion, with the generic chain aliases made explicit. -/
def inclusion : Chains Good →ₗ[ℚ] Chains (fun _ => True) :=
  OrdinaryIncidenceChains.edgeInclusion

/-- Inclusion sends each actual Good flag to the identical ordinary flag. -/
theorem include_flag (L : Line Good) (P : Plane Good) (h : L.val ≤ P.val) :
    inclusion (flagChain Good L P h) =
      flagChain (fun _ => True) (OrdinaryIncidence.goodLine L) (OrdinaryIncidence.goodPlane P) h := by
  exact Finsupp.mapDomain_single

private theorem include_line_common (L M : Line Good) (P : Plane Good)
    (hL : L.val ≤ P.val) (hM : M.val ≤ P.val) :
    inclusion (lineChain Good L M) =
      lineChain (fun _ => True) (OrdinaryIncidence.goodLine L) (OrdinaryIncidence.goodLine M) := by
  rw [lineChain_of_common_plane Good L M P hL hM,map_sub,include_flag,include_flag]
  exact (lineChain_of_common_plane (fun _ => True) (OrdinaryIncidence.goodLine L)
    (OrdinaryIncidence.goodLine M) (OrdinaryIncidence.goodPlane P) hL hM).symm

/-- The canonical two-edge line chain is unchanged by forgetting goodness. -/
theorem include_line (L M : Line Good) :
    inclusion (lineChain Good L M) =
      lineChain (fun _ => True) (OrdinaryIncidence.goodLine L) (OrdinaryIncidence.goodLine M) := by
  classical
  by_cases h : L=M
  · subst M
    simp only [lineChain_self,map_zero]
  · exact include_line_common L M (spanPlane Good L M h)
      (line_le_spanPlane_left Good L M h) (line_le_spanPlane_right Good L M h)

/-- The actual Good apartment includes as the literal ordinary apartment. -/
theorem include_apartment (L M N : Line Good) :
    inclusion (apartmentChain Good L M N) =
      apartmentChain (fun _ => True) (OrdinaryIncidence.goodLine L)
        (OrdinaryIncidence.goodLine M) (OrdinaryIncidence.goodLine N) := by
  simp only [apartmentChain,map_add,include_line]

private theorem coordinate_zero_space : (coordinateLine 0).val=L0 := by
  rw [RelativeOrbitCompletion.L0_span]
  change Submodule.span ℚ {ModThreeGoodAction.rationalVector (fun i => (1 : Mat) i 0)} = _
  apply congrArg (fun v : ModThreeGoodAction.Space => Submodule.span ℚ {v})
  funext i
  fin_cases i <;> norm_num [ModThreeGoodAction.rationalVector,AugmentedFrameComplex.template,
    Matrix.one_apply,Pi.single_apply]

private theorem coordinate_one_le : (coordinateLine 1).val ≤ P0 := by
  apply Submodule.span_le.mpr
  intro v hv
  rcases hv with rfl
  change ModThreeGoodAction.rationalVector (fun i => (1 : Mat) i 1) ∈ P0
  exact (mem_P0 _).mpr (by change ((1 : Mat) 2 1 : ℚ)=0; norm_num [Matrix.one_apply])

private def coordinatePlane : Plane Good :=
  ⟨P0,finrank_P0,⟨coordinateLine 0,by rw [coordinate_zero_space]; exact L0_le_P0⟩⟩

private theorem coordinate_zero_le : (coordinateLine 0).val ≤ coordinatePlane.val := by
  change (coordinateLine 0).val ≤ P0
  rw [coordinate_zero_space]
  exact L0_le_P0

private theorem coordinate_action (g : GoodBuilding.K) (i j : Fin 3)
    (h : (fun k => g.val.val k i)=(fun k => (1 : Mat) k j)) :
    GoodBuilding.lineAction g (coordinateLine i)=coordinateLine j := by
  rw [coordinateLine,GoodUnimodularOrbit.columnLine_action]
  apply Subtype.ext
  exact congrArg (fun v => Submodule.span ℚ {ModThreeGoodAction.rationalVector v}) h

private theorem c_lines :
    GoodBuilding.lineAction cK (coordinateLine 0)=coordinateLine 1 ∧
    GoodBuilding.lineAction cK (coordinateLine 1)=coordinateLine 2 ∧
    GoodBuilding.lineAction cK (coordinateLine 2)=coordinateLine 0 := by
  exact ⟨coordinate_action _ _ _ (by decide +kernel),
    coordinate_action _ _ _ (by decide +kernel),coordinate_action _ _ _ (by decide +kernel)⟩

private theorem s_line : GoodBuilding.lineAction sK (coordinateLine 0)=coordinateLine 1 :=
  coordinate_action _ _ _ (by decide +kernel)

private theorem s_plane : GoodBuilding.planeAction sK coordinatePlane=coordinatePlane := by
  apply Subtype.ext
  change Stabilizes s P0
  rw [stabilizes_P0_iff]
  constructor <;> rfl

private theorem include_base_flag :
    OrdinaryIncidenceChains.edgeInclusion (flagChain Good (coordinateLine 0) coordinatePlane coordinate_zero_le)=
      OrdinaryCoordinateFlag.flagChain := by
  change inclusion _ = _
  rw [include_flag]
  apply congrArg (fun e => Finsupp.single e (1 : ℚ))
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact coordinate_zero_space
  · rfl

private theorem s_base_flag :
    GoodChainComplex.edgeRepresentation sK (flagChain Good (coordinateLine 0) coordinatePlane coordinate_zero_le)=
      flagChain Good (coordinateLine 1) coordinatePlane coordinate_one_le := by
  change apartmentChainEquiv Good (GoodBuilding.subspaceEquiv sK) (act_finrank sK)
    (good_act_iff sK) _ = _
  erw [apartmentChainEquiv_flag]
  change flagChain Good (GoodBuilding.lineAction sK (coordinateLine 0))
    (GoodBuilding.planeAction sK coordinatePlane) _ = _
  simp only [s_line,s_plane]

/-- The first two flags of the reference apartment, with their exact orientation. -/
def segment : OrdinaryIncidenceChains.EdgeChains :=
  OrdinaryCoordinateFlag.flagChain -
    OrdinaryIncidenceChains.edgeRepresentation sK OrdinaryCoordinateFlag.flagChain

private def coordinateChain (i j : Fin 3) : GoodChainComplex.EdgeChains :=
  lineChain Good (coordinateLine i) (coordinateLine j)

private def baseFlag : GoodChainComplex.EdgeChains :=
  flagChain Good (coordinateLine 0) coordinatePlane coordinate_zero_le

private theorem coordinateChain_zero_one : coordinateChain 0 1 =
    baseFlag - GoodChainComplex.edgeRepresentation sK baseFlag := by
  change lineChain Good _ _ = _
  rw [lineChain_of_common_plane Good _ _ coordinatePlane coordinate_zero_le coordinate_one_le]
  exact congrArg (fun z : GoodChainComplex.EdgeChains => baseFlag-z) s_base_flag.symm

private theorem segment_eq : segment=
    OrdinaryIncidenceChains.edgeInclusion (coordinateChain 0 1) := by
  rw [coordinateChain_zero_one,map_sub,OrdinaryIncidenceChains.edgeInclusion_equivariant]
  have hb : OrdinaryIncidenceChains.edgeInclusion baseFlag=OrdinaryCoordinateFlag.flagChain :=
    include_base_flag
  rw [hb]
  rfl

private theorem c_chain :
    GoodChainComplex.edgeRepresentation cK (coordinateChain 0 1)=coordinateChain 1 2 ∧
    GoodChainComplex.edgeRepresentation cK (coordinateChain 1 2)=coordinateChain 2 0 := by
  have h (i j : Fin 3) := apartmentChainEquiv_line Good
    (GoodBuilding.subspaceEquiv cK) (act_finrank cK) (good_act_iff cK)
    (coordinateLine i) (coordinateLine j)
  have h01 := h 0 1
  have h12 := h 1 2
  change GoodChainComplex.edgeRepresentation cK (coordinateChain 0 1)=
    lineChain Good (GoodBuilding.lineAction cK (coordinateLine 0))
      (GoodBuilding.lineAction cK (coordinateLine 1)) at h01
  change GoodChainComplex.edgeRepresentation cK (coordinateChain 1 2)=
    lineChain Good (GoodBuilding.lineAction cK (coordinateLine 1))
      (GoodBuilding.lineAction cK (coordinateLine 2)) at h12
  rw [c_lines.1,c_lines.2.1] at h01
  rw [c_lines.2.1,c_lines.2.2] at h12
  exact ⟨h01,h12⟩

/-- This six-flag expression is the literal included reference apartment, not an abstract class. -/
theorem reference_eq_hexagon :
    (OrdinaryIncidenceChains.cycleInclusion GoodUnimodularOrbit.referenceApartment).val =
      segment + OrdinaryIncidenceChains.edgeRepresentation cK segment +
        OrdinaryIncidenceChains.edgeRepresentation cK
          (OrdinaryIncidenceChains.edgeRepresentation cK segment) := by
  have hr : GoodUnimodularOrbit.referenceApartment.val =
      coordinateChain 0 1 + coordinateChain 1 2 + coordinateChain 2 0 := rfl
  rw [OrdinaryIncidenceChains.cycleInclusion_coe,hr,map_add,map_add,segment_eq,
    ←OrdinaryIncidenceChains.edgeInclusion_equivariant,c_chain.1,
    ←OrdinaryIncidenceChains.edgeInclusion_equivariant,c_chain.2]

end TernaryPoly.OrdinaryCoordinateApartment
