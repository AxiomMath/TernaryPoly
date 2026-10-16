module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.MVMaps
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.MVLocalGraded
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactMV
open CategoryTheory Limits HomologicalComplex SingularLocalCoefficient
open SingularLocalSupport EquivariantSingularSmall

/-- A degreewise cocycle in an actual restriction kernel has an element of the actual kernel complex. -/
theorem kernel_degree_exists {C D : CochainComplex (ModuleCat.{0} ℚ) ℕ} (r : C ⟶ D)
    (n : ℕ) (x : C.X n) (hx : r.f n x = 0) : ∃ y : (kernel r).X n, (kernel.ι r).f n y = x := by
  have h := (ShortComplex.kernelSequence_exact r).map
    (HomologicalComplex.eval (ModuleCat.{0} ℚ) (ComplexShape.up ℕ) n)
  have he := h.moduleCat_range_eq_ker
  have hmem : x ∈ LinearMap.ker (r.f n).hom := hx
  change x ∈ LinearMap.ker ((ShortComplex.kernelSequence r).map
    (HomologicalComplex.eval (ModuleCat.{0} ℚ) (ComplexShape.up ℕ) n)).g.hom at hmem
  rw [← he] at hmem
  exact hmem

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)

/-- The actual support-sum map is surjective in every cochain degree. -/
theorem supportSum_surjective (K L : Set B) (n : ℕ) : Function.Surjective ((supportSum p V K L).f n) := by
  intro c
  let z := (supportInclusion p V (K ∪ L)).f n c
  have hz : (localRestriction p (Kᶜ ∩ Lᶜ) V).f n z = 0 := by
    rw [← Set.compl_union]
    have h := congrArg (fun f => f c)
      (HomologicalComplex.congr_hom (kernel.condition (localRestriction p (K ∪ L)ᶜ V)) n)
    change (localRestriction p (K ∪ L)ᶜ V).f n z = 0 at h
    exact h
  obtain ⟨x,y,hx,hy,hxy⟩ := local_cochain_decomposition p V Kᶜ Lᶜ n z hz
  obtain ⟨x',hx'⟩ := kernel_degree_exists (localRestriction p Kᶜ V) n x hx
  obtain ⟨y',hy'⟩ := kernel_degree_exists (localRestriction p Lᶜ V) n y hy
  let iK : supportCochains p V K ⟶ supportCochains p V K ⊞ supportCochains p V L := biprod.inl
  let iL : supportCochains p V L ⟶ supportCochains p V K ⊞ supportCochains p V L := biprod.inr
  refine ⟨iK.f n x' + iL.f n y',?_⟩
  apply (ModuleCat.mono_iff_injective ((supportInclusion p V (K ∪ L)).f n)).mp inferInstance
  rw [map_add,map_add]
  have hK := congrArg (fun f => f x') (HomologicalComplex.congr_hom
    (show (iK ≫ supportSum p V K L) ≫ supportInclusion p V (K ∪ L) = supportInclusion p V K by
      rw [show iK ≫ supportSum p V K L = supportMap p V K (K ∪ L) Set.subset_union_left from biprod.inl_desc _ _,
        supportMap_inclusion]) n)
  have hL := congrArg (fun f => f y') (HomologicalComplex.congr_hom
    (show (iL ≫ supportSum p V K L) ≫ supportInclusion p V (K ∪ L) = supportInclusion p V L by
      rw [show iL ≫ supportSum p V K L = supportMap p V L (K ∪ L) Set.subset_union_right from biprod.inr_desc _ _,
        supportMap_inclusion]) n)
  change (supportInclusion p V (K ∪ L)).f n ((supportSum p V K L).f n (iK.f n x')) = (supportInclusion p V K).f n x' at hK
  change (supportInclusion p V (K ∪ L)).f n ((supportSum p V K L).f n (iL.f n y')) = (supportInclusion p V L).f n y' at hL
  change (supportInclusion p V K).f n x' = x at hx'
  change (supportInclusion p V L).f n y' = y at hy'
  rw [hx'] at hK
  rw [hy'] at hL
  rw [hK,hL]
  exact hxy

/-- The genuine support-sum cochain map is an epimorphism. -/
instance supportSum_epi (K L : Set B) : Epi (supportSum p V K L) :=
  epi_of_epi_f _ (fun n => (ModuleCat.epi_iff_surjective _).mpr (supportSum_surjective p V K L n))

/-- The actual fixed-support kernel sequence is short exact as a sequence of cochain complexes. -/
theorem fixedKernelSequence_shortExact (K L : Set B) : (fixedKernelSequence p V K L).ShortExact where
  exact := fixedKernelSequence_exact p V K L
  mono_f := inferInstanceAs (Mono (kernel.ι (supportSum p V K L)))
  epi_g := supportSum_epi p V K L

end TernaryPoly.SingularLocalCompactMV
