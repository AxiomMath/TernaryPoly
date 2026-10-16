module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.DisjointResolutions
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.ComponentResolutions

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set CategoryTheory
open SmoothCoveringDeRham SymmetricSpaceCovering

/-- The actual nonempty convex components form a disjoint open cover of each literal Čech overlap. -/
def cechComponentCover {n : ℕ} (t : Fin (n+1) → ConvexSheet) :
    DisjointQuotientCover (cechDomain ConvexSheet.quotientDomain t)
      ((t 0).ComponentIndex (fun i => t i.succ)) where
  domain g := (t 0).componentOpen (fun i => t i.succ) g.val
  isOpen_domain g := (t 0).componentOpen_isOpen (fun i => t i.succ) g.val
  subset g := by
    intro q hq
    rw [ConvexSheet.cechDomain_eq_chartOpen_overlap, ConvexSheet.chartOpen_overlap,
      ConvexSheet.overlap_quotient_eq_iUnion_nonempty]
    exact mem_iUnion.mpr ⟨g,hq⟩
  disjoint := by
    intro g h hgh
    apply (t 0).componentOpens_pairwise_disjoint (fun i => t i.succ)
    intro he
    exact hgh (Subtype.ext he)
  covers := by
    rw [ConvexSheet.cechDomain_eq_chartOpen_overlap, ConvexSheet.chartOpen_overlap,
      ConvexSheet.overlap_quotient_eq_iUnion_nonempty]

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F)

/-- The actual coefficient augmentation resolves smooth forms on every finite nonempty-tuple
Čech overlap of the genuine convex-sheet cover. All component and gluing hypotheses are proved. -/
theorem cechOverlap_formAugmentation_quasiIso {n : ℕ} (t : Fin (n+1) → ConvexSheet) :
    QuasiIso (coveringFormAugmentation ρ (cechDomain_isOpen ConvexSheet.quotientDomain
      ConvexSheet.quotientDomain_isOpen t)) :=
  (cechComponentCover t).formAugmentation_quasiIso ρ _
    (fun g => ConvexSheet.component_formAugmentation_quasiIso ρ (t 0) (fun i => t i.succ) g)

omit [FiniteDimensional ℝ F] in
/-- The actual coefficient augmentation resolves genuine equivariant singular Hom cochains on
every finite Čech overlap of the genuine convex-sheet cover, by actual disjoint simplex gluing. -/
theorem cechOverlap_singularAugmentation_quasiIso {n : ℕ} (t : Fin (n+1) → ConvexSheet) :
    QuasiIso (coveringSingularAugmentation ρ (cechDomain ConvexSheet.quotientDomain t)) :=
  (cechComponentCover t).singularAugmentation_quasiIso ρ
    (fun g => ConvexSheet.component_singularAugmentation_quasiIso ρ (t 0) (fun i => t i.succ) g)

end TernaryPoly.SmoothSingularGlobal
