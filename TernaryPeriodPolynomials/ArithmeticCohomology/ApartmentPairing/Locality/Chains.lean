module

public import TernaryPeriodPolynomials.Topology.SingularHomology.IteratedSubdivisionHomotopySmall
public import TernaryPeriodPolynomials.Topology.SingularHomology.SubordinateChains

@[expose] public section


/-!
# Locality for singular chains: splitting a chain along a three-set open cover

For a singular chain `c` of `X` whose boundary lies in the chains over an open set `A`, and an open cover
`X = T ∪ A ∪ B`, there are chains `cT`, `cA`, `cB` over `T`, `A`, `B` and a chain `u` with
`c = cT + cA + cB + ∂u`; moreover `∂cT` is a sum of a chain over `T ∩ A` and a chain over `T ∩ B`
(`localize_chain`).  This is obtained by iterated barycentric subdivision (`small_threeCover_decomp`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.Lemma33.Locality

open CategoryTheory SphereOddDegree SphereOddDegree.AffineBarycentricSubdivision

variable {X : TopCat.{0}}

/-- The cover of `X` by three sets. -/
def threeCover (T A B : Set X) (hT : IsOpen T) (hA : IsOpen A) (hB : IsOpen B)
    (hcov : T ∪ A ∪ B = Set.univ) : OpenCoverData X where
  sets := {T, A, B}
  isOpen_mem U hU := by
    rcases hU with rfl | rfl | rfl
    · exact hT
    · exact hA
    · exact hB
  covers x := by
    have : x ∈ T ∪ A ∪ B := by rw [hcov]; trivial
    rcases this with (h | h) | h
    · exact ⟨T, by simp, h⟩
    · exact ⟨A, by simp, h⟩
    · exact ⟨B, by simp, h⟩

/-- Decomposition of small chains for a three-set cover. -/
theorem small_threeCover_decomp (T A B : Set X) (hT : IsOpen T) (hA : IsOpen A) (hB : IsOpen B)
    (hcov : T ∪ A ∪ B = Set.univ) (n : ℕ) {s : singularChainGroup ℚ X n}
    (hs : s ∈ smallChainSubmodule ℚ X (threeCover T A B hT hA hB hcov) n) :
    ∃ t ∈ subChainSubmodule ℚ X T n, ∃ a ∈ subChainSubmodule ℚ X A n,
      ∃ b ∈ subChainSubmodule ℚ X B n, s = t + a + b := by
  refine smallChainSubmodule_induction (p := fun s => ∃ t ∈ subChainSubmodule ℚ X T n,
    ∃ a ∈ subChainSubmodule ℚ X A n, ∃ b ∈ subChainSubmodule ℚ X B n, s = t + a + b) ?_ ?_ ?_ ?_ hs
  · intro σ hσ
    obtain ⟨U, hU, hsub⟩ := hσ
    rcases hU with rfl | rfl | rfl
    · exact ⟨_, chainGenerator_mem_subChainSubmodule hsub, 0, Submodule.zero_mem _, 0,
        Submodule.zero_mem _, by simp⟩
    · exact ⟨0, Submodule.zero_mem _, _, chainGenerator_mem_subChainSubmodule hsub, 0,
        Submodule.zero_mem _, by simp⟩
    · exact ⟨0, Submodule.zero_mem _, 0, Submodule.zero_mem _, _,
        chainGenerator_mem_subChainSubmodule hsub, by simp⟩
  · exact ⟨0, Submodule.zero_mem _, 0, Submodule.zero_mem _, 0, Submodule.zero_mem _, by simp⟩
  · rintro x y ⟨t, ht, a, ha, b, hb, rfl⟩ ⟨t', ht', a', ha', b', hb', rfl⟩
    exact ⟨t + t', Submodule.add_mem _ ht ht', a + a', Submodule.add_mem _ ha ha', b + b',
      Submodule.add_mem _ hb hb', by abel⟩
  · rintro r x ⟨t, ht, a, ha, b, hb, rfl⟩
    exact ⟨r • t, Submodule.smul_mem _ _ ht, r • a, Submodule.smul_mem _ _ ha, r • b,
      Submodule.smul_mem _ _ hb, by simp [smul_add, add_assoc]⟩

/-- The projection of chains onto the simplices subordinate to `S`. -/
def projSub (S : Set X) (n : ℕ) : singularChainGroup ℚ X n ⟶ singularChainGroup ℚ X n :=
  Limits.Sigma.desc fun σ : singularSimplices X n =>
    ModuleCat.ofHom
      (if IsSubordinate S σ then LinearMap.toSpanSingleton ℚ (singularChainGroup ℚ X n)
        (chainGenerator ℚ X n σ) else 0)

theorem projSub_generator (S : Set X) (n : ℕ) (σ : singularSimplices X n) :
    (projSub S n).hom (chainGenerator ℚ X n σ) =
      if IsSubordinate S σ then chainGenerator ℚ X n σ else 0 := by
  have h := Limits.Sigma.ι_comp_desc (fun σ : singularSimplices X n =>
    ModuleCat.ofHom
      (if IsSubordinate S σ then LinearMap.toSpanSingleton ℚ (singularChainGroup ℚ X n)
        (chainGenerator ℚ X n σ) else 0)) σ
  have h2 : (projSub S n).hom (chainGenerator ℚ X n σ) = (ModuleCat.ofHom
      (if IsSubordinate S σ then LinearMap.toSpanSingleton ℚ (singularChainGroup ℚ X n)
        (chainGenerator ℚ X n σ) else 0)).hom (1 : ℚ) := congrArg (fun f => f.hom (1 : ℚ)) h
  rw [h2]
  by_cases hS : IsSubordinate S σ
  · simp [hS]
  · simp [hS]

theorem projSub_of_mem (S : Set X) (n : ℕ) {x : singularChainGroup ℚ X n}
    (hx : x ∈ subChainSubmodule ℚ X S n) : (projSub S n).hom x = x := by
  refine subChainSubmodule_induction (p := fun x => (projSub S n).hom x = x) ?_ ?_ ?_ ?_ hx
  · intro σ hσ
    rw [projSub_generator, ite_eq_left hσ]
  · simp
  · intro x y hx hy
    simp [hx, hy]
  · intro a x hx
    simp [hx]

theorem projSub_mem (S : Set X) (n : ℕ) (x : singularChainGroup ℚ X n) :
    (projSub S n).hom x ∈ subChainSubmodule ℚ X S n := by
  have hx : x ∈ Submodule.span ℚ (Set.range (chainGenerator ℚ X n)) := by
    rw [chainGenerator_span_top]; trivial
  refine Submodule.span_induction (p := fun x _ => (projSub S n).hom x ∈ subChainSubmodule ℚ X S n)
    ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨σ, rfl⟩
    rw [projSub_generator]
    by_cases hσ : IsSubordinate S σ
    · rw [ite_eq_left hσ]; exact chainGenerator_mem_subChainSubmodule hσ
    · rw [ite_eq_right hσ]; exact Submodule.zero_mem _
  · simp
  · intro x y _ _ hx hy
    simpa using Submodule.add_mem _ hx hy
  · intro a x _ hx
    simpa using Submodule.smul_mem _ a hx

theorem projSub_projSub (T S : Set X) (n : ℕ) (x : singularChainGroup ℚ X n) :
    (projSub T n).hom ((projSub S n).hom x) = (projSub (T ∩ S) n).hom x := by
  have hx : x ∈ Submodule.span ℚ (Set.range (chainGenerator ℚ X n)) := by
    rw [chainGenerator_span_top]; trivial
  refine Submodule.span_induction (p := fun x _ =>
    (projSub T n).hom ((projSub S n).hom x) = (projSub (T ∩ S) n).hom x) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨σ, rfl⟩
    rw [projSub_generator, projSub_generator]
    by_cases hS : IsSubordinate S σ
    · by_cases hT : IsSubordinate T σ
      · have hTS : IsSubordinate (T ∩ S) σ := Set.subset_inter hT hS
        rw [ite_eq_left hS, projSub_generator, ite_eq_left hT, ite_eq_left hTS]
      · have hTS : ¬ IsSubordinate (T ∩ S) σ := fun h => hT (h.trans Set.inter_subset_left)
        rw [ite_eq_left hS, projSub_generator, ite_eq_right hT, ite_eq_right hTS]
    · have hTS : ¬ IsSubordinate (T ∩ S) σ := fun h => hS (h.trans Set.inter_subset_right)
      rw [ite_eq_right hS, map_zero, ite_eq_right hTS]
  · simp
  · intro x y _ _ hx hy
    simp [hx, hy]
  · intro a x _ hx
    simp [hx]

/-- **Basis argument**: a chain subordinate to `T` that is a sum of chains subordinate to `A` and
`B` is a sum of chains subordinate to `T ∩ A` and `T ∩ B`. -/
theorem sub_inter_add (T A B : Set X) (n : ℕ) {x a b : singularChainGroup ℚ X n}
    (hxT : x ∈ subChainSubmodule ℚ X T n) (ha : a ∈ subChainSubmodule ℚ X A n)
    (hb : b ∈ subChainSubmodule ℚ X B n) (hx : x = a + b) :
    ∃ a' ∈ subChainSubmodule ℚ X (T ∩ A) n, ∃ b' ∈ subChainSubmodule ℚ X (T ∩ B) n, x = a' + b' := by
  refine ⟨(projSub T n).hom a, ?_, (projSub T n).hom b, ?_, ?_⟩
  · rw [← projSub_of_mem A n ha, projSub_projSub]; exact projSub_mem _ _ _
  · rw [← projSub_of_mem B n hb, projSub_projSub]; exact projSub_mem _ _ _
  · rw [← map_add, ← hx, projSub_of_mem T n hxT]

/-- **Localization of relative chains.**  If `T, A, B` are open sets covering `X` and `c` is an
`(n+1)`-chain whose boundary is subordinate to `A`, then `c` is, up to a boundary, the sum of a chain
`cT` subordinate to `T`, a chain subordinate to `A` and a chain subordinate to `B`; moreover
`∂ cT` is a sum of a chain subordinate to `T ∩ A` and a chain subordinate to `T ∩ B`. -/
theorem localize_chain (T A B : Set X) (hT : IsOpen T) (hA : IsOpen A) (hB : IsOpen B)
    (hcov : T ∪ A ∪ B = Set.univ) (n : ℕ) (c : singularChainGroup ℚ X (n + 1))
    (hc : (singularBoundary ℚ X n).hom c ∈ subChainSubmodule ℚ X A n) :
    ∃ cT ∈ subChainSubmodule ℚ X T (n + 1), ∃ cA ∈ subChainSubmodule ℚ X A (n + 1),
      ∃ cB ∈ subChainSubmodule ℚ X B (n + 1), ∃ u : singularChainGroup ℚ X (n + 2),
        c = cT + cA + cB + (singularBoundary ℚ X (n + 1)).hom u ∧
        ∃ a' ∈ subChainSubmodule ℚ X (T ∩ A) n, ∃ b' ∈ subChainSubmodule ℚ X (T ∩ B) n,
          (singularBoundary ℚ X n).hom cT = a' + b' := by
  set 𝒰 := threeCover T A B hT hA hB hcov with h𝒰
  have hsmall : (singularBoundary ℚ X n).hom c ∈ smallChainSubmodule ℚ X 𝒰 n := by
    refine subChainSubmodule_le_smallChainSubmodule (𝒰 := 𝒰) (S := A) ?_ n hc
    simp [h𝒰, threeCover]
  obtain ⟨N, hN1, hN2⟩ := exists_iteratedSubdivision_homotopy_boundary_mem_smallChains 𝒰 ℚ n c hsmall
  have hform := barycentricSubdivisionIter_boundary_formula ℚ X N (n + 1) c
  set s := barycentricSubdivisionIterLinearMap ℚ X N (n + 1) c +
    barycentricSubdivisionIterHomotopyLinearMap ℚ X N n ((singularBoundary ℚ X n).hom c) with hs
  have hsmem : s ∈ smallChainSubmodule ℚ X 𝒰 (n + 1) := Submodule.add_mem _ hN1 hN2
  set u := barycentricSubdivisionIterHomotopyLinearMap ℚ X N (n + 1) c with hu
  have hcs : c = s + (singularBoundary ℚ X (n + 1)).hom u := by
    have := hform
    simp only [barycentricSubdivisionIterHomotopyBoundaryTerm] at this
    have h3 : c = barycentricSubdivisionIterLinearMap ℚ X N (n + 1) c +
        ((singularBoundary ℚ X (n + 1)).hom u +
          barycentricSubdivisionIterHomotopyLinearMap ℚ X N n ((singularBoundary ℚ X n).hom c)) := by
      rw [← this]; abel
    exact h3.trans (by rw [hs]; abel)
  obtain ⟨cT, hcT, cA, hcA, cB, hcB, hsdec⟩ := small_threeCover_decomp T A B hT hA hB hcov (n + 1) hsmem
  refine ⟨cT, hcT, cA, hcA, cB, hcB, u, ?_, ?_⟩
  · rw [hcs, hsdec]
  · have hdd : (singularBoundary ℚ X n).hom ((singularBoundary ℚ X (n + 1)).hom u) = 0 := by
      exact singularBoundary_boundary_zero ℚ X n u
    have h1 : (singularBoundary ℚ X n).hom cT = (singularBoundary ℚ X n).hom c -
        (singularBoundary ℚ X n).hom cA - (singularBoundary ℚ X n).hom cB := by
      have := congrArg (fun y => (singularBoundary ℚ X n).hom y) hcs
      simp only [map_add, hdd, add_zero, hsdec] at this
      rw [this]; abel
    have hTm := singularBoundary_maps_subChainSubmodule (R := ℚ) (X := X) (S := T) n cT hcT
    refine sub_inter_add T A B n hTm (a := (singularBoundary ℚ X n).hom c -
      (singularBoundary ℚ X n).hom cA) (b := -(singularBoundary ℚ X n).hom cB) ?_ ?_ ?_
    · exact Submodule.sub_mem _ hc (singularBoundary_maps_subChainSubmodule n cA hcA)
    · exact Submodule.neg_mem _ (singularBoundary_maps_subChainSubmodule n cB hcB)
    · rw [h1]; abel

end TernaryPeriodPolynomials.Argument.Lemma33.Locality
