module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.MVGraded

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactMV
open CategoryTheory Limits FreeActionLinearization EquivariantSingularResolution EquivariantSingularSmall
open EquivariantSingularMayerVietoris SphereOddDegree SphereOddDegree.AffineBarycentricSubdivision
open scoped Classical

variable (E : TopCat.{0})

/-- Coordinate projection onto any actual simplex family lands in its genuine generator span. -/
theorem keep_mem_predicateSpan (n : ℕ) (P : SingularSimplex E n → Prop) (c : (underlyingChains E).X n) :
    (keepHom ℚ E P).hom c ∈ predicateSpan E n P := by
  rw [← (generatorBasis E n).linearCombination_repr c,Finsupp.linearCombination_apply,Finsupp.sum,map_sum]
  apply Submodule.sum_mem
  intro σ hσ
  rw [map_smul,generatorBasis_apply,keepHom_generator]
  split_ifs with h
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ,h,rfl⟩)
  · simp

/-- Coordinate projection is the identity on the span of its retained simplex family. -/
theorem keep_eq_self_predicateSpan (n : ℕ) (P : SingularSimplex E n → Prop)
    (c : (underlyingChains E).X n) (hc : c ∈ predicateSpan E n P) : (keepHom ℚ E P).hom c = c := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨σ,hσ,rfl⟩ := hc
    rw [keepHom_generator,ite_eq_left hσ]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add,hx,hy]
  | smul r x _ hx => rw [map_smul,hx]

variable (G : Type) [Group G] [MulAction G E] [ContinuousConstSMul G E]
  (𝒰 : OpenCoverData E) (h𝒰 : InvariantCover G E 𝒰)

/-- A genuine equivariant graded retraction onto small singular chains.
No commutation of this coordinate projection with the differential is claimed. -/
def smallGradedRetraction (n : ℕ) : (equivariantChains G E).X n ⟶ (smallComplex G E 𝒰 h𝒰).X n :=
  Rep.ofHom ⟨((keepHom ℚ E (IsSmallSimplex 𝒰)).hom.codRestrict
    (predicateSpan E n (IsSmallSimplex 𝒰)) (keep_mem_predicateSpan E n _)),fun g => by
      apply LinearMap.ext
      intro c
      apply Subtype.ext
      exact keepHom_smul G E n (IsSmallSimplex 𝒰) (small_invariant G E 𝒰 h𝒰 n) g c⟩

/-- The actual small-chain inclusion followed by the graded retraction is the identity in each degree. -/
theorem smallInclusion_gradedRetraction (n : ℕ) :
    (smallInclusion G E 𝒰 h𝒰).f n ≫ smallGradedRetraction E G 𝒰 h𝒰 n = 𝟙 _ := by
  ext c
  apply Subtype.ext
  exact keep_eq_self_predicateSpan E n (IsSmallSimplex 𝒰) c.val c.property

/-- Restriction to genuine small cochains is surjective in every degree for arbitrary representations. -/
theorem smallRestriction_surjective (V : Rep.{0} ℚ G) (n : ℕ) :
    Function.Surjective ((smallRestriction G E 𝒰 h𝒰 V).f n) := by
  intro c
  change (smallComplex G E 𝒰 h𝒰).X n ⟶ V at c
  refine ⟨smallGradedRetraction E G 𝒰 h𝒰 n ≫ c,?_⟩
  change (smallInclusion G E 𝒰 h𝒰).f n ≫ smallGradedRetraction E G 𝒰 h𝒰 n ≫ c = c
  rw [← Category.assoc,smallInclusion_gradedRetraction,Category.id_comp]

/-- The actual small-cochain comparison is epi as a morphism of cochain complexes. -/
instance smallRestriction_epi (V : Rep.{0} ℚ G) : Epi (smallRestriction G E 𝒰 h𝒰 V) :=
  HomologicalComplex.epi_of_epi_f _ (fun n => (ModuleCat.epi_iff_surjective _).mpr
    (smallRestriction_surjective E G 𝒰 h𝒰 V n))

end TernaryPoly.SingularLocalCompactMV
