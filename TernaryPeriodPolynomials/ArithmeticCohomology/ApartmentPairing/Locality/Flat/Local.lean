module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Flat.Interior
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Localize

@[expose] public section


/-!
# Lemma 3.3, G3: the compactified flat chain is carried by a chart and the complement of a support

`flatChain_mem_sub` and `hexBoundary_mem_sub`: the six chamber squares make up a 2-chain carried by any set
containing all the chamber images, and its boundary hexagon is carried by any set containing the boundary
(`fk_edge_not_interior`).  `fk_mem_cover`: a chamber point over a support set `P` lies in the interior, hence
in the flat (`fk_interior_flat`), so lies in the image of any set `T` containing the flat points over `P`.
These give the hypotheses of `localize_relative_chain` for the flat chain.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.Lemma33.Locality

open CategoryTheory Limits TernaryPoly TernaryPoly.FreeActionLinearization
  TernaryPoly.EquivariantSingularResolution SphereOddDegree SphereOddDegree.AffineBarycentricSubdivision
  TernaryPoly.SymmetricSpaceRationalGluing TernaryPoly.SymmetricSpaceFlagCoordinates
  TernaryPoly.SymmetricSpacePositive
  TernaryPeriodPolynomials.Argument.Lemma33

theorem isSubordinate_affSimplex {X : TopCat.{0}} (f : C(ℝ × ℝ, X)) (U : Set X) {n : ℕ}
    (p : Fin (n + 1) → ℝ × ℝ) (S : Set (ℝ × ℝ)) (hS : Convex ℝ S) (hp : ∀ i, p i ∈ S)
    (hf : ∀ q ∈ S, f q ∈ U) : IsSubordinate U (affSimplex f p) := by
  rintro _ ⟨x, rfl⟩
  have hmem : affineMap n p x ∈ S := by
    change ∑ i, x.weights i • p i ∈ S
    exact hS.sum_mem (fun i _ => x.weights_nonneg i) x.total_of_fintype (fun i _ => hp i)
  exact hf _ hmem

theorem fk_edge_not_interior (k : ℕ) (q : ℝ × ℝ) (h : q.1 ≤ 0 ∨ q.2 ≤ 0) :
    fk k q ∉ Set.range embedding := by
  intro hmem
  have hci := (chart_preimage_embedding (hexW k)).subset hmem
  obtain ⟨hs, ht⟩ := hci
  change 0 < max q.1 0 at hs
  change 0 < max q.2 0 at ht
  rcases h with h | h
  · exact absurd hs (by simp [h])
  · exact absurd ht (by simp [h])

theorem sing_mem_sub_of_isSubordinate {X : TopCat.{0}} {n : ℕ} (U : Set X) (σ : SingularSimplex X n)
    (h : IsSubordinate U σ) : sing X σ ∈ subChainSubmodule ℚ X U n :=
  chainGenerator_mem_subChainSubmodule h

theorem flatChain_mem_sub (U : Set (TopCat.of Glued))
    (h : ∀ (k : ℕ) (q : ℝ × ℝ), fk k q ∈ U) :
    flatChain ∈ subChainSubmodule ℚ (TopCat.of Glued) U 2 := by
  have hsq : ∀ k, sqChain (fk k) ∈ subChainSubmodule ℚ (TopCat.of Glued) U 2 := by
    intro k
    unfold sqChain tri
    refine Submodule.add_mem _ ?_ ?_
    · exact sing_mem_sub_of_isSubordinate U _
        (isSubordinate_affSimplex (fk k) U _ Set.univ convex_univ (fun _ => trivial)
          (fun q _ => h k q))
    · exact sing_mem_sub_of_isSubordinate U _
        (isSubordinate_affSimplex (fk k) U _ Set.univ convex_univ (fun _ => trivial)
          (fun q _ => h k q))
  unfold flatChain
  refine Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.add_mem _
    (Submodule.sub_mem _ (hsq 0) (hsq 1)) (hsq 2)) (hsq 3)) (hsq 4)) (hsq 5)

theorem convex_second_zero : Convex ℝ {q : ℝ × ℝ | q.2 = 0} := by
  have : {q : ℝ × ℝ | q.2 = 0} = Set.univ ×ˢ {0} := by ext q; simp
  rw [this]
  exact convex_univ.prod (convex_singleton _)

theorem convex_first_zero : Convex ℝ {q : ℝ × ℝ | q.1 = 0} := by
  have : {q : ℝ × ℝ | q.1 = 0} = {0} ×ˢ Set.univ := by ext q; simp
  rw [this]
  exact (convex_singleton _).prod convex_univ

theorem hexBoundary_mem_sub (U : Set (TopCat.of Glued)) (hU : (Set.range embedding)ᶜ ⊆ U) :
    hexBoundary ∈ subChainSubmodule ℚ (TopCat.of Glued) U 1 := by
  have hs1 : ∀ k, sing (TopCat.of Glued) (seg (fk k) pv pa) ∈
      subChainSubmodule ℚ (TopCat.of Glued) U 1 := by
    intro k
    unfold seg
    refine sing_mem_sub_of_isSubordinate U _
      (isSubordinate_affSimplex (fk k) U _ {q : ℝ × ℝ | q.2 = 0} convex_second_zero ?_ ?_)
    · intro i
      fin_cases i <;> simp [pv, pa]
    · intro q hq
      exact hU (fk_edge_not_interior k q (Or.inr (le_of_eq hq)))
  have hs2 : ∀ k, sing (TopCat.of Glued) (seg (fk k) pv pb) ∈
      subChainSubmodule ℚ (TopCat.of Glued) U 1 := by
    intro k
    unfold seg
    refine sing_mem_sub_of_isSubordinate U _
      (isSubordinate_affSimplex (fk k) U _ {q : ℝ × ℝ | q.1 = 0} convex_first_zero ?_ ?_)
    · intro i
      fin_cases i <;> simp [pv, pb]
    · intro q hq
      exact hU (fk_edge_not_interior k q (Or.inl (le_of_eq hq)))
  have hk : ∀ k, sing (TopCat.of Glued) (seg (fk k) pv pa) - sing (TopCat.of Glued) (seg (fk k) pv pb) ∈
      subChainSubmodule ℚ (TopCat.of Glued) U 1 := fun k => Submodule.sub_mem _ (hs1 k) (hs2 k)
  unfold hexBoundary
  refine Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.sub_mem _ (Submodule.add_mem _
    (Submodule.sub_mem _ (hk 0) (hk 1)) (hk 2)) (hk 3)) (hk 4)) (hk 5)

/-- Every point of the chamber maps lies in the image of the chart box or off the support set `P`. -/
theorem fk_mem_cover (T : Set Space) (P : Set (TopCat.of Glued)) (hP : P ⊆ Set.range embedding)
    (hPT : ∀ S : Space, S ∈ flat → embedding S ∈ P → S ∈ T) (k : ℕ) (q : ℝ × ℝ) :
    fk k q ∈ embedding '' T ∪ Pᶜ := by
  by_cases hq : fk k q ∈ P
  · obtain ⟨S, hS⟩ := hP hq
    exact Or.inl ⟨S, hPT S (fk_interior_flat k q S hS) (hS ▸ hq), hS⟩
  · exact Or.inr hq

end TernaryPeriodPolynomials.Argument.Lemma33.Locality
