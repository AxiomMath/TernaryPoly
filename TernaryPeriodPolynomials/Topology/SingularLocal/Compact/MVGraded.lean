module

public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.MayerVietorisKeep

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactMV
open CategoryTheory Limits FreeActionLinearization EquivariantSingularResolution EquivariantSingularSmall
open EquivariantSingularMayerVietoris SphereOddDegree SphereOddDegree.AffineBarycentricSubdivision
open scoped Classical

variable (G : Type) [Group G] (E : TopCat.{0}) [MulAction G E] [ContinuousConstSMul G E]

/-- The equivariant coordinate projection retaining precisely simplices subordinate to A.
This is a graded map only; no commutation with the differential is asserted. -/
def gradedKeep (A : Set E) (hA : InvariantSet G E A) (n : ℕ) : (equivariantChains G E).X n ⟶ (equivariantChains G E).X n :=
  Rep.ofHom ⟨(keepHom ℚ E (IsSubordinate A)).hom,keepHom_equivariant G E n _ (subordinate_invariant G E A hA n)⟩

/-- On A-supported chains, the actual graded keep map is the identity inclusion. -/
theorem subordinateInclusion_keep (A : Set E) (hA : InvariantSet G E A) (n : ℕ) :
    (subordinateInclusion G E A hA).f n ≫ gradedKeep G E A hA n = (subordinateInclusion G E A hA).f n := by
  ext c
  exact keepHom_eq_self_of_mem c.property

/-- The actual graded projection of A-supported chains into the A∩D-supported chains. -/
def gradedKeepIntersection (A D : Set E) (hA : InvariantSet G E A) (hD : InvariantSet G E D) (n : ℕ) :
    (subordinateComplex G E A hA).X n ⟶
      (subordinateComplex G E (A ∩ D) (invariant_inter G E A D hA hD)).X n :=
  Rep.ofHom ⟨(((keepHom ℚ E (IsSubordinate D)).hom.comp
    (subChainSubmodule ℚ E A n).subtype).codRestrict (subChainSubmodule ℚ E (A ∩ D) n) (by
      intro c
      have h := keepHom_mem_subChainSubmodule (R := ℚ) (X := E) (S := D) c.property
      simpa only [Set.inter_comm,LinearMap.comp_apply,Submodule.subtype_apply] using h)),fun g => by
        apply LinearMap.ext
        intro c
        apply Subtype.ext
        exact keepHom_smul G E n (IsSubordinate D) (subordinate_invariant G E D hD n) g c.val⟩

/-- The two genuine ways to keep D-simplices of an A-supported chain agree literally. -/
theorem gradedKeepIntersection_inclusion (A D : Set E)
    (hA : InvariantSet G E A) (hD : InvariantSet G E D) (n : ℕ) :
    gradedKeepIntersection G E A D hA hD n ≫
      (subordinateInclusion G E (A ∩ D) (invariant_inter G E A D hA hD)).f n =
    (subordinateInclusion G E A hA).f n ≫ gradedKeep G E D hD n := by
  ext c
  rfl

/-- A genuine graded equivariant cochain annihilating A∩D splits into cochains annihilating A and D.
The two pieces are graded cochains; the proof asserts no extension-by-zero cochain map. -/
theorem graded_cochain_decomposition (A D : Set E)
    (hA : InvariantSet G E A) (hD : InvariantSet G E D) (W : Rep.{0} ℚ G) (n : ℕ)
    (c : (equivariantChains G E).X n ⟶ W)
    (hc : (subordinateInclusion G E (A ∩ D) (invariant_inter G E A D hA hD)).f n ≫ c = 0) :
    ∃ x y : (equivariantChains G E).X n ⟶ W,
      (subordinateInclusion G E A hA).f n ≫ x = 0 ∧
      (subordinateInclusion G E D hD).f n ≫ y = 0 ∧ x + y = c := by
  let x := gradedKeep G E D hD n ≫ c
  refine ⟨x,c-x,?_,?_,add_sub_cancel _ _⟩
  · change (subordinateInclusion G E A hA).f n ≫ gradedKeep G E D hD n ≫ c = 0
    rw [← Category.assoc,← gradedKeepIntersection_inclusion,Category.assoc,hc,comp_zero]
  · dsimp [x]
    rw [Preadditive.comp_sub,← Category.assoc,subordinateInclusion_keep,sub_self]

end TernaryPoly.SingularLocalCompactMV
