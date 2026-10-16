module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.ConvexOverlaps
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CoverFormAugmentation
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FrameAugmentation

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set CategoryTheory
open SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts
namespace ConvexSheet

/-- Only genuinely nonempty components are used for the local contractible resolutions. -/
def ComponentIndex (S : ConvexSheet) {n : ℕ} (T : Fin n → ConvexSheet) :=
  {g : Fin n → DeckGroup // (S.component T g).Nonempty}

/-- Deleting empty components does not change the actual finite quotient overlap. -/
theorem overlap_quotient_eq_iUnion_nonempty (S : ConvexSheet) {n : ℕ}
    (T : Fin n → ConvexSheet) :
    S.quotientDomain ∩ ⋂ i, (T i).quotientDomain =
      ⋃ g : S.ComponentIndex T, S.componentOpen T g.val := by
  rw [S.overlap_quotient_eq_iUnion T]
  apply Set.ext
  intro q
  constructor
  · intro hq
    obtain ⟨g,hg⟩ := mem_iUnion.mp hq
    exact mem_iUnion.mpr ⟨⟨g,quotientChart S.chart q,hg.2⟩,hg⟩
  · intro hq
    obtain ⟨g,hg⟩ := mem_iUnion.mp hq
    exact mem_iUnion.mpr ⟨g.val,hg⟩

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F)

/-- On each actual component the true smooth coefficient augmentation is a quasi-isomorphism. -/
theorem component_formAugmentation_quasiIso (S : ConvexSheet) {n : ℕ}
    (T : Fin n → ConvexSheet) (g : S.ComponentIndex T) :
    QuasiIso (coveringFormAugmentation ρ (S.componentOpen_isOpen T g.val)) :=
  coveringFormAugmentation_quasiIso_convex ρ S.chart (S.component_isOpen T g.val)
    (S.component_subset_target T g.val) (S.component_convex T g.val)

omit [FiniteDimensional ℝ F] in
/-- On each actual nonempty convex component the true equivariant singular coefficient
augmentation is a quasi-isomorphism through its literal covering frame. -/
theorem component_singularAugmentation_quasiIso (S : ConvexSheet) {n : ℕ}
    (T : Fin n → ConvexSheet) (g : S.ComponentIndex T) :
    QuasiIso (coveringSingularAugmentation ρ (S.componentOpen T g.val)) := by
  let : ContractibleSpace (TopCat.of (S.component T g.val)) :=
    (S.component_convex T g.val).contractibleSpace g.property
  exact coveringSingularAugmentation_quasiIso ρ
    (chartSingularFrame S.chart (S.component_subset_target T g.val))

/-- The component comparison is the actual span through coefficient sections on the actual
quotient component open, in every degree. -/
def componentComparison (S : ConvexSheet) {n : ℕ} (T : Fin n → ConvexSheet)
    (g : S.ComponentIndex T) (k : ℕ) :
    (coveringComplex ρ (S.componentOpen_isOpen T g.val)).homology k ≅
      (coveringCochains ρ (S.componentOpen T g.val)).homology k := by
  letI := component_formAugmentation_quasiIso ρ S T g
  letI := component_singularAugmentation_quasiIso ρ S T g
  exact SmoothSingularComparison.comparison
    (coveringFormAugmentation ρ (S.componentOpen_isOpen T g.val))
    (coveringSingularAugmentation ρ (S.componentOpen T g.val)) k

end ConvexSheet
end TernaryPoly.SmoothSingularGlobal
