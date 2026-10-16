module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.ConvexSheets
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CechDomains

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set SymmetricSpacePositive SymmetricSpaceCharts SmoothCoveringDeRham
  SymmetricSpaceCovering SymmetricSpaceQuotientManifold
namespace ConvexSheet

/-- The actual overlap inside the anchor sheet is open. -/
theorem overlap_isOpen (S : ConvexSheet) {n : ℕ} (T : Fin n → ConvexSheet) :
    IsOpen (S.overlap T) :=
  S.isOpen_domain.inter (isOpen_iInter_of_finite fun i =>
    liftedDomain_isOpen (T i).quotientDomain_isOpen)

/-- The anchor chart identifies its selected-sheet overlap with the actual finite quotient
intersection. This is a literal equality of the opens used by the two Čech bicomplexes. -/
theorem chartOpen_overlap (S : ConvexSheet) {n : ℕ} (T : Fin n → ConvexSheet) :
    chartOpen S.chart (S.overlap T) = S.quotientDomain ∩ ⋂ i, (T i).quotientDomain := by
  apply Set.ext
  intro q
  constructor
  · rintro ⟨hq,hS,hT⟩
    refine ⟨⟨hq,hS⟩,mem_iInter.mpr fun i => ?_⟩
    have hi := (mem_iInter.mp hT i).2
    have he : coordinateProjection (quotientChart S.chart q) = q :=
      (quotientChart_projection_coordinates S.chart (S.subset_target hS)).symm.trans
        ((quotientChart S.chart).left_inv hq)
    exact (congrArg (fun z : OrbitSpace => z ∈ (T i).quotientDomain) he).mp hi
  · rintro ⟨hq,hT⟩
    refine ⟨hq.1,hq.2,mem_iInter.mpr fun i => ?_⟩
    refine ⟨S.domain_positive hq.2,?_⟩
    have he : coordinateProjection (quotientChart S.chart q) = q :=
      (quotientChart_projection_coordinates S.chart (S.subset_target hq.2)).symm.trans
        ((quotientChart S.chart).left_inv hq.1)
    exact (congrArg (fun z : OrbitSpace => z ∈ (T i).quotientDomain) he).mpr (mem_iInter.mp hT i)

/-- Every actual nonempty-tuple Čech open is represented by the disjoint convex-sheet overlap. -/
theorem cechDomain_eq_chartOpen_overlap {n : ℕ} (t : Fin (n+1) → ConvexSheet) :
    cechDomain quotientDomain t = chartOpen (t 0).chart ((t 0).overlap (fun i => t i.succ)) := by
  rw [chartOpen_overlap]
  ext q
  simp [cechDomain, Fin.forall_fin_succ]

/-- Each selected-sheet component gives an actual quotient open in the finite intersection. -/
def componentOpen (S : ConvexSheet) {n : ℕ} (T : Fin n → ConvexSheet)
    (g : Fin n → DeckGroup) : Set OrbitSpace := chartOpen S.chart (S.component T g)

theorem componentOpen_isOpen (S : ConvexSheet) {n : ℕ} (T : Fin n → ConvexSheet)
    (g : Fin n → DeckGroup) : IsOpen (S.componentOpen T g) :=
  chartOpen_isOpen S.chart (S.component_isOpen T g)

/-- The actual finite quotient overlap is covered by the quotient images of its convex components. -/
theorem overlap_quotient_eq_iUnion (S : ConvexSheet) {n : ℕ} (T : Fin n → ConvexSheet) :
    S.quotientDomain ∩ ⋂ i, (T i).quotientDomain = ⋃ g, S.componentOpen T g := by
  rw [← chartOpen_overlap, overlap_eq_iUnion_components]
  ext q
  simp [componentOpen, chartOpen, exists_and_left]

/-- The genuine quotient component opens remain pairwise disjoint in the anchor chart. -/
theorem componentOpens_pairwise_disjoint (S : ConvexSheet) {n : ℕ} (T : Fin n → ConvexSheet) :
    Pairwise (fun g h : Fin n → DeckGroup =>
      Disjoint (S.componentOpen T g) (S.componentOpen T h)) := by
  intro g h hgh
  apply disjoint_left.mpr
  intro q hqg hqh
  exact (S.components_pairwise_disjoint T hgh).le_bot ⟨hqg.2,hqh.2⟩

/-- Every component's coordinate domain is contained in the actual anchor chart target. -/
theorem component_subset_target (S : ConvexSheet) {n : ℕ} (T : Fin n → ConvexSheet)
    (g : Fin n → DeckGroup) : S.component T g ⊆ (quotientChart S.chart).target :=
  inter_subset_left.trans S.subset_target

end ConvexSheet
end TernaryPoly.SmoothSingularGlobal
