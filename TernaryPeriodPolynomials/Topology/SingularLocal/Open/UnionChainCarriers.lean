module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Open.UnionCompactDiagram
public import TernaryPeriodPolynomials.Topology.SingularLocal.Excision.Naturality

@[expose] public section

noncomputable section
namespace TernaryPoly.SingularLocalOpenUnion
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalHomology SingularLocalExcision EquivariantSingularSmall
open FreeActionLinearization CoveringSingularOrbits SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision
open scoped Classical
variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G) [IsCancelSMul G E]

/-- A geometric elementary chain whose simplex lies in A is the actual inclusion of
a chain on the restricted covering, using inverse actual coefficient pushforward. -/
theorem single_in_localInclusion (A : Set B) (k : ℕ) (σ : SingularSimplex B k)
    (hσ : IsSubordinate A σ) (c : FiberCoefficient p hp.out V (atVertex σ)) :
    ∃ z : (restrictedLocalChains p A V).X k,
      (localInclusion p A V).f k z = DFinsupp.single σ c := by
  obtain ⟨τ,hτ⟩ := exists_pushSimplex_of_subordinate A k hσ
  change projection (sInclusion A) k τ = σ at hτ
  subst σ
  let e := coefficientPushforward (restrictedProjection p A) p (sInclusion (p ⁻¹' A))
    (sInclusion A) (restricted_square p A) (restrictedQuotientCovering p A) hp.out
    (fun _ _ => rfl) V (atVertex τ)
  refine ⟨DFinsupp.single τ (e.symm c),?_⟩
  change (localSpaceMap (sInclusion (p ⁻¹' A)) (fun _ _ => rfl) V
    (restrictedProjection p A) p (restrictedQuotientCovering p A) hp.out).f k _ = _
  exact (localSpaceMap_single (sInclusion (p ⁻¹' A)) (fun _ _ => rfl) V
    (restrictedProjection p A) p (sInclusion A) (restricted_square p A)
    (restrictedQuotientCovering p A) hp.out k τ (e.symm c)).trans
      (congrArg (DFinsupp.single (projection (sInclusion A) k τ)) (e.apply_symm_apply c))

/-- Every actual finite local chain has a compact carrier and an actual preimage on
the restricted covering over that carrier. Compactness uses genuine simplex images
and finite dependent-sum induction, without restrictions on the coefficient module. -/
theorem local_chain_compact_carrier (k : ℕ) (c : (localChains p hp.out V).X k) :
    ∃ K : Set B, IsCompact K ∧ ∃ z : (restrictedLocalChains p K V).X k,
      (localInclusion p K V).f k z = c := by
  induction c using DFinsupp.induction with
  | h0 => exact ⟨∅,isCompact_empty,0,map_zero _⟩
  | ha σ v c _ _ ih =>
    obtain ⟨K,hK,z,hz⟩ := ih
    let A := Set.range (mvSimplexMap σ)
    have hA : IsCompact A := isCompact_range (mvSimplexMap σ).continuous
    obtain ⟨w,hw⟩ := single_in_localInclusion p V A k σ (Set.Subset.refl _) v
    refine ⟨A ∪ K,hA.union hK,
      (nestedLocalInclusion p A (A ∪ K) Set.subset_union_left V).f k w +
        (nestedLocalInclusion p K (A ∪ K) Set.subset_union_right V).f k z,?_⟩
    rw [map_add]
    have h₁ := congrArg (fun f => f w) (HomologicalComplex.congr_hom
      (nestedLocalInclusion_inclusion p A (A ∪ K) Set.subset_union_left V) k)
    have h₂ := congrArg (fun f => f z) (HomologicalComplex.congr_hom
      (nestedLocalInclusion_inclusion p K (A ∪ K) Set.subset_union_right V) k)
    exact congrArg₂ (· + ·) (h₁.trans hw) (h₂.trans hz)

/-- Every actual local chain on an increasing open union comes from one stage. -/
theorem local_chain_stage (U : ℕ → Opens B) (hU : Monotone U)
    (hcover : (⋃ i, (U i : Set B)) = Set.univ) (k : ℕ) (c : (localChains p hp.out V).X k) :
    ∃ i, ∃ z : (restrictedLocalChains p (U i) V).X k, (localInclusion p (U i) V).f k z = c := by
  obtain ⟨K,hK,z,hz⟩ := local_chain_compact_carrier p V k c
  obtain ⟨i,hKi⟩ := compact_subset_stage U hU hcover K hK
  exact ⟨i,(nestedLocalInclusion p K (U i) hKi V).f k z,
    (congrArg (fun f => f z) (HomologicalComplex.congr_hom
      (nestedLocalInclusion_inclusion p K (U i) hKi V) k)).trans hz⟩

end TernaryPoly.SingularLocalOpenUnion
