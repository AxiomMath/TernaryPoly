module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.GluingMayerVietoris

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothDeRhamGluing
open Set SmoothLocalDeRham SmoothCoveringDeRham SymmetricSpaceCharts SymmetricSpaceCovering CategoryTheory
open scoped ContDiff Topology

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) {U V : Set OrbitSpace} (hU : IsOpen U) (hV : IsOpen V)

/-- Direct sum of the two genuine quotient-compact-support complexes. -/
def compactPairComplex : CochainComplex (ModuleCat ℝ) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of ℝ (CompactSupportForm ρ U n × CompactSupportForm ρ V n))
    (fun n => ModuleCat.ofHom ((compactDifferential ρ hU n).prodMap (compactDifferential ρ hV n))) (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro p
      exact Prod.ext (compactDifferential_squared ρ hU n p.1) (compactDifferential_squared ρ hV n p.2))

def compactIntersectionMap : compactCoveringComplex ρ (hU.inter hV) ⟶ compactPairComplex ρ hU hV :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (intersectionExtension ρ hU hV n)) (by
    intro n
    simp only [compactCoveringComplex, compactPairComplex, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro w
    apply Prod.ext
    · exact compactZeroExtend_d (hU.inter hV) hU inter_subset_left w
    · change compactDifferential ρ hV n (-compactZeroExtend (hU.inter hV) inter_subset_right n w) =
        -compactZeroExtend (hU.inter hV) inter_subset_right (n + 1) (compactDifferential ρ (hU.inter hV) n w)
      rw [map_neg, compactZeroExtend_d (hU.inter hV) hV inter_subset_right])

theorem unionExtension_d (n : ℕ) (p : CompactSupportForm ρ U n × CompactSupportForm ρ V n) :
    compactDifferential ρ (hU.union hV) n (unionExtension ρ hU hV n p) =
      unionExtension ρ hU hV (n + 1) (compactDifferential ρ hU n p.1, compactDifferential ρ hV n p.2) := by
  change compactDifferential ρ (hU.union hV) n
    (compactZeroExtend hU subset_union_left n p.1 + compactZeroExtend hV subset_union_right n p.2) =
    compactZeroExtend hU subset_union_left (n + 1) (compactDifferential ρ hU n p.1) +
      compactZeroExtend hV subset_union_right (n + 1) (compactDifferential ρ hV n p.2)
  exact (map_add (compactDifferential ρ (hU.union hV) n) _ _).trans
    (congrArg₂ (· + ·) (compactZeroExtend_d hU (hU.union hV) subset_union_left p.1)
      (compactZeroExtend_d hV (hU.union hV) subset_union_right p.2))

def compactUnionMap : compactPairComplex ρ hU hV ⟶ compactCoveringComplex ρ (hU.union hV) :=
  CochainComplex.ofHom (X := compactPairComplex ρ hU hV)
    (Y := compactCoveringComplex ρ (hU.union hV))
    (fun n => ModuleCat.ofHom (unionExtension ρ hU hV n)) (by
      intro n
      simp only [compactCoveringComplex, compactPairComplex, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro p
      exact unionExtension_d ρ hU hV n p)

/-- The actual compact-support Mayer-Vietoris short complex, with zero-extension maps. -/
def compactSequence : ShortComplex (CochainComplex (ModuleCat ℝ) ℕ) :=
  ShortComplex.mk (compactIntersectionMap ρ hU hV) (compactUnionMap ρ hU hV) (by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro w
    exact unionExtension_intersectionExtension ρ hU hV n w)

/-- Genuine compact-support Mayer-Vietoris short exactness in every degree. -/
theorem compactSequence_shortExact : (compactSequence ρ hU hV).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    intro p
    exact compact_kernel_exact hU hV p
  · apply (ModuleCat.mono_iff_injective _).mpr
    exact intersectionExtension_injective ρ hU hV n
  · apply (ModuleCat.epi_iff_surjective _).mpr
    exact unionExtension_surjective ρ hU hV n

end TernaryPoly.SmoothDeRhamGluing
