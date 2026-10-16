module

public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.SmallRestrictedCover
public import Mathlib.Topology.IsLocalHomeomorph

@[expose] public section


noncomputable section
namespace TernaryPoly.CoveringEuclideanCharts
open CategoryTheory TopologicalSpace
open EquivariantSingularSmall
variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)]

/-- A continuous right inverse of the actual restricted covering projection. -/
structure Section (D : Opens B) where
  map : TopCat.of D ⟶ TopCat.of (p ⁻¹' (D : Set B))
  right_inv : map ≫ restrictedProjection p (D : Set B) = 𝟙 _

/-- Every actual section point lies over the same literal base point. -/
theorem Section.projection {D : Opens B} (s : Section p D) (x : D) :
    p (s.map x).val = x.val :=
  congrArg (fun f => (f x).val) s.right_inv

/-- An actual section restricts to every smaller open set by the literal subtype inclusions. -/
def Section.restrict {U : Opens B} (s : Section p U) (D : Opens B) (hDU : D ≤ U) : Section p D where
  map := TopCat.ofHom ⟨fun x => ⟨(s.map ⟨x.val,hDU x.property⟩).val,by
      change p (s.map ⟨x.val,hDU x.property⟩).val ∈ D
      rw [Section.projection p s]
      exact x.property⟩,
    (continuous_subtype_val.comp (s.map.hom.continuous.comp
      (continuous_subtype_val.subtype_mk (fun x : D => hDU x.property)))).subtype_mk (fun x => by
        change p (s.map ⟨x.val,hDU x.property⟩).val ∈ D
        rw [Section.projection p s]
        exact x.property)⟩
  right_inv := by
    ext x
    exact Section.projection p s ⟨x.val,hDU x.property⟩

/-- Restricting a section keeps the actual lifted point in the original covering space. -/
theorem Section.restrict_apply {U : Opens B} (s : Section p U) (D : Opens B) (hDU : D ≤ U) (x : D) :
    ((Section.restrict p s D hDU).map x).val = (s.map ⟨x.val,hDU x.property⟩).val := rfl

include hp

/-- The inverse of an actual covering chart gives a continuous section around every base point. -/
theorem exists_local_section (x : B) :
    ∃ U : Opens B, x ∈ U ∧ Nonempty (Section p U) := by
  obtain ⟨y,rfl⟩ := hp.out.surjective x
  let c := hp.out.isCoveringMap.isLocalHomeomorph.localInverseAt y
  let U : Opens B := ⟨c.source,c.open_source⟩
  have hc (z : U) : p (c z) = z.val :=
    hp.out.isCoveringMap.isLocalHomeomorph.apply_localInverseAt_of_mem z.property
  refine ⟨U,hp.out.isCoveringMap.isLocalHomeomorph.apply_self_mem_localInverseAt_source,⟨?_⟩⟩
  refine ⟨TopCat.ofHom ⟨fun z => ⟨c z,?_⟩,?_⟩,?_⟩
  · change p (c z) ∈ U
    rw [hc]
    exact z.property
  · exact (c.continuousOn.comp_continuous continuous_subtype_val (fun z => z.property)).subtype_mk _
  · ext z
    exact hc z

end TernaryPoly.CoveringEuclideanCharts
