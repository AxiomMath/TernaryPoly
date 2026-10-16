module

public import TernaryPeriodPolynomials.Building.OrientedChain.ChainJoin
public import Mathlib.Data.List.Permutation

@[expose] public section


noncomputable section
namespace TernaryPoly.OrientedSimplexPermutation
open OrientedListChains
variable {V W : Type*}

/-- Permuting an actual oriented simplex changes only its rational scalar. -/
theorem simplex_perm_smul {l m : List V} (h : l.Perm m) :
    ∃ q : ℚ, simplex l = q • simplex m := by
  induction h with
  | nil => exact ⟨1,(one_smul ℚ _).symm⟩
  | cons a h ih =>
    obtain ⟨q,hq⟩ := ih
    refine ⟨q,?_⟩
    rw [← cons_simplex,← cons_simplex,hq,map_smul]
  | swap a b l =>
    refine ⟨-1,?_⟩
    rw [neg_one_smul]
    exact simplex_swap_eq_neg _ _ _
  | trans h₁ h₂ ih₁ ih₂ =>
    obtain ⟨q,hq⟩ := ih₁
    obtain ⟨r,hr⟩ := ih₂
    exact ⟨q*r,by rw [hq,hr,smul_smul]⟩

/-- Any chosen ordering of an image multiset lifts to an actual ordering of the source list. -/
theorem exists_perm_map (f : V → W) (l : List V) (b : List W)
    (h : (l.map f).Perm b) : ∃ m : List V, m.Perm l ∧ m.map f = b := by
  have hb : b ∈ (l.map f).permutations := List.mem_permutations.mpr h.symm
  rw [← List.map_permutations] at hb
  obtain ⟨m,hm,he⟩ := List.mem_map.mp hb
  exact ⟨m,List.mem_permutations.mp hm,he⟩

/-- Image-face equality and nondegeneracy give an exactly aligned source ordering. -/
theorem exists_perm_map_of_toFinset (f : V → W) (l : List V) (b : List W)
    (hl : (l.map f).Nodup) (hb : b.Nodup)
    [DecidableEq W] (he : (l.map f).toFinset = b.toFinset) :
    ∃ m : List V, m.Perm l ∧ m.map f = b :=
  exists_perm_map f l b (List.perm_of_nodup_nodup_toFinset_eq hl hb he)

end TernaryPoly.OrientedSimplexPermutation
