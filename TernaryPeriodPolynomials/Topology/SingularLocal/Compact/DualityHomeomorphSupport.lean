module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.DualityCoverHomeomorph
public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.HomeomorphCompactIso

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactDuality
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalCoefficient SingularLocalHomology SingularCoverNaturality SingularLocalSupport
open EquivariantSingularSmall
variable {G : Type} [Group G] {E E' B B' : TopCat.{0}}
  [MulAction G E] [ContinuousConstSMul G E] [MulAction G E'] [ContinuousConstSMul G E']
  {p : E ⟶ B} {p' : E' ⟶ B'}
  [hp : Fact (IsQuotientCoveringMap p G)] [hp' : Fact (IsQuotientCoveringMap p' G)]
  (h : CoverHomeomorph (G := G) p p') (V : Rep.{0} ℚ G)

/-- Genuine equivariant covering homeomorphisms induce actual support-cochain isomorphisms. -/
def coveringSupportIso (K : Set B') :
    supportCochains p' V K ≅ supportCochains p V (h.base ⁻¹' K) := by
  have := coveringCochainMap_isIso h V
  have := coveringCochainMap_isIso (h.restrict Kᶜ) V
  exact kernel.mapIso (localRestriction p' Kᶜ V) (localRestriction p (h.base ⁻¹' K)ᶜ V)
    (asIso (coveringCochainMap h V)) (asIso (coveringCochainMap (h.restrict Kᶜ) V))
    (coveringCochainMap_restriction h V Kᶜ).symm

/-- The actual support isomorphism retains literal ambient geometric cochain pullback. -/
theorem coveringSupportIso_inclusion (K : Set B') :
    (coveringSupportIso h V K).hom ≫ supportInclusion p V (h.base ⁻¹' K) =
      supportInclusion p' V K ≫ coveringCochainMap h V := by
  unfold coveringSupportIso
  erw [kernel.lift_ι]
  rfl

/-- Actual support homeomorphism pullback commutes with genuine support enlargement. -/
theorem coveringSupportIso_natural (K L : Set B') (hKL : K ⊆ L) :
    supportMap p' V K L hKL ≫ (coveringSupportIso h V L).hom =
      (coveringSupportIso h V K).hom ≫ supportMap p V (h.base ⁻¹' K) (h.base ⁻¹' L) (Set.preimage_mono hKL) := by
  apply (cancel_mono (supportInclusion p V (h.base ⁻¹' L))).mp
  rw [Category.assoc,coveringSupportIso_inclusion,← Category.assoc,supportMap_inclusion,
    Category.assoc,supportMap_inclusion,coveringSupportIso_inclusion]

/-- The actual compact-support cohomology diagrams agree under inverse-image reindexing. -/
def coveringCompactDiagramIso (a : ℕ) : compactCohomologyDiagram p' V a ≅
    (SingularLocalCapHomeomorph.compactOrderIso h.base).equivalence.functor ⋙ compactCohomologyDiagram p V a :=
  NatIso.ofComponents (fun K => (homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.up ℕ) a).mapIso
    (coveringSupportIso h V (K : Set B'))) (fun {K L} f => by
      change homologyMap (supportMap p' V K L (leOfHom f)) a ≫
        homologyMap (coveringSupportIso h V L).hom a =
          homologyMap (coveringSupportIso h V K).hom a ≫
            homologyMap (supportMap p V (h.base ⁻¹' (K : Set B')) (h.base ⁻¹' (L : Set B'))
              (Set.preimage_mono (leOfHom f))) a
      rw [← homologyMap_comp,← homologyMap_comp,coveringSupportIso_natural])

/-- Genuine compact-support cohomology is preserved by the actual covering homeomorphism. -/
def coveringCompactIso (a : ℕ) : compactCohomology p' V a ≅ compactCohomology p V a :=
  colim.mapIso (coveringCompactDiagramIso h V a) ≪≫
    Functor.Final.colimitIso (SingularLocalCapHomeomorph.compactOrderIso h.base).equivalence.functor
      (compactCohomologyDiagram p V a)

/-- The actual compact-support isomorphism has the literal fixed-support formula. -/
theorem coveringCompactIso_classMap (a : ℕ) (K : Compacts B') :
    compactClassMap p' V K a ≫ (coveringCompactIso h V a).hom =
      homologyMap (coveringSupportIso h V K).hom a ≫
        compactClassMap p V (SingularLocalCapHomeomorph.compactOrderIso h.base K) a := by
  unfold coveringCompactIso compactClassMap
  erw [Iso.trans_hom,Functor.mapIso_hom,colim_map,ι_colimMap_assoc]
  erw [Functor.Final.ι_colimitIso_hom]
  rfl

end TernaryPoly.SingularLocalCompactDuality
