module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SheetGeometry

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set SymmetricSpacePositive SymmetricSpaceCharts SmoothCoveringDeRham
  SymmetricSpaceCovering SymmetricSpaceQuotientManifold

/-- An actual open convex coordinate domain inside a genuine selected covering chart. -/
structure ConvexSheet where
  chart : Space
  domain : Set Coordinates
  isOpen_domain : IsOpen domain
  subset_target : domain ⊆ (quotientChart chart).target
  convex_domain : Convex ℝ domain

namespace ConvexSheet

/-- The actual quotient open represented by the selected convex lifting sheet. -/
def quotientDomain (S : ConvexSheet) : Set OrbitSpace := chartOpen S.chart S.domain

theorem quotientDomain_isOpen (S : ConvexSheet) : IsOpen S.quotientDomain :=
  chartOpen_isOpen S.chart S.isOpen_domain

theorem domain_positive (S : ConvexSheet) : S.domain ⊆ positiveCoordinates :=
  S.subset_target.trans (quotientChart_target_subset S.chart)

/-- Every point in every quotient open lies in a genuine convex-sheet quotient open
contained in that given open. -/
theorem exists_mem_subset {U : Set OrbitSpace} (hU : IsOpen U) {q : OrbitSpace} (hq : q ∈ U) :
    ∃ S : ConvexSheet, q ∈ S.quotientDomain ∧ S.quotientDomain ⊆ U := by
  obtain ⟨S,hqS⟩ := quotientCharts_cover q
  have hx : quotientChart S q ∈ chartDomain S U :=
    ⟨(quotientChart S).map_source hqS, by
      simpa only [mem_preimage, (quotientChart S).left_inv hqS] using hq⟩
  obtain ⟨r,hr,hb⟩ := Metric.isOpen_iff.mp (chartDomain_isOpen S hU) _ hx
  refine ⟨⟨S,Metric.ball (quotientChart S q) r,Metric.isOpen_ball,
    fun x hx => (hb hx).1,convex_ball _ _⟩,?_,?_⟩
  · exact ⟨hqS,Metric.mem_ball_self hr⟩
  · exact chartOpen_subset_of_chartDomain S hb

/-- All genuine convex sheets form an actual open cover of the quotient. -/
theorem covers : Set.univ ⊆ ⋃ S : ConvexSheet, S.quotientDomain := by
  intro q _
  obtain ⟨S,hS,_⟩ := exists_mem_subset isOpen_univ (mem_univ q)
  exact mem_iUnion.mpr ⟨S,hS⟩

/-- The portion of a finite quotient overlap inside one actual selected anchor sheet. -/
def overlap (S : ConvexSheet) {n : ℕ} (T : Fin n → ConvexSheet) : Set Coordinates :=
  S.domain ∩ ⋂ i, liftedDomain (T i).quotientDomain

/-- A genuine component of that overlap, specified by actual relative deck labels. -/
def component (S : ConvexSheet) {n : ℕ} (T : Fin n → ConvexSheet)
    (g : Fin n → DeckGroup) : Set Coordinates :=
  S.domain ∩ ⋂ i, deckMap (g i) '' (T i).domain

theorem component_convex (S : ConvexSheet) {n : ℕ} (T : Fin n → ConvexSheet)
    (g : Fin n → DeckGroup) : Convex ℝ (S.component T g) :=
  S.convex_domain.inter (convex_iInter fun i =>
    deckMap_convex_image (g i) (T i).convex_domain (T i).domain_positive)

theorem component_isOpen (S : ConvexSheet) {n : ℕ} (T : Fin n → ConvexSheet)
    (g : Fin n → DeckGroup) : IsOpen (S.component T g) :=
  S.isOpen_domain.inter (isOpen_iInter_of_finite fun i =>
    deckMap_image_isOpen (T i).isOpen_domain (T i).domain_positive (g i))

/-- Actual sheet labels select the genuine convex overlap component containing a point. -/
theorem overlap_eq_iUnion_components (S : ConvexSheet) {n : ℕ} (T : Fin n → ConvexSheet) :
    S.overlap T = ⋃ g : Fin n → DeckGroup, S.component T g := by
  ext x
  constructor
  · rintro ⟨hx,hT⟩
    refine mem_iUnion.mpr ⟨fun i => sheetElement (T i).chart x,hx,?_⟩
    apply mem_iInter.mpr
    intro i
    have hi := mem_iInter.mp hT i
    refine ⟨baseCoordinate (T i).chart x,baseCoordinate_mem_chartOpen (T i).chart hi,?_⟩
    exact baseCoordinate_sheet (T i).chart
      (liftedDomain_mono (chartOpen_subset (T i).chart (T i).domain) hi)
  · intro hx
    obtain ⟨g,hS,hT⟩ := mem_iUnion.mp hx
    refine ⟨hS,mem_iInter.mpr fun i => ?_⟩
    change x ∈ liftedDomain (chartOpen (T i).chart (T i).domain)
    rw [liftedDomain_chartOpen_eq_iUnion (T i).chart (T i).subset_target]
    exact mem_iUnion.mpr ⟨g i,mem_iInter.mp hT i⟩

/-- Different tuples of actual relative sheet labels give disjoint overlap components. -/
theorem components_pairwise_disjoint (S : ConvexSheet) {n : ℕ} (T : Fin n → ConvexSheet) :
    Pairwise (fun g h : Fin n → DeckGroup => Disjoint (S.component T g) (S.component T h)) := by
  intro g h hgh
  apply disjoint_left.mpr
  intro x hx hy
  apply hgh
  funext i
  exact (sheetElement_deck_image (T i).chart (T i).subset_target (g i) (mem_iInter.mp hx.2 i)).symm.trans
    (sheetElement_deck_image (T i).chart (T i).subset_target (h i) (mem_iInter.mp hy.2 i))

end ConvexSheet
end TernaryPoly.SmoothSingularGlobal
