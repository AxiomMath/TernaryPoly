module

public import TernaryPeriodPolynomials.PeriodPolynomial.FareyDuality.Hecke.FareyNeighbours

@[expose] public section


/-!
# Injectivity of the edge chain map on antisymmetric chains

Formalized by Claude Sonnet 5.5.

The coordinate functional `ell a b` of an oriented pair of cusps on the library's oriented chains (`ellRaw_relation`: it
kills the alternation relations), `ell_theta1_ne` (only the two orientations of the edge `{a, b}` have a nonzero
coordinate), and `Th1_injective_anti`: `Th1` is injective on antisymmetric chains of oriented dual edges.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeDuality

open CategoryTheory TernaryPoly TernaryPoly.BinaryModularSymbol TernaryPoly.RankTwoAugmentedFrames
open TernaryPeriodPolynomials.Argument.FareyTree
open scoped MonoidAlgebra Classical

/-- The coordinate of an oriented pair `(a, b)` on lists of length two. -/
def ellVal (a b : Line) : List Line → ℚ
  | [x, y] => if x = a ∧ y = b then 1 else if x = b ∧ y = a then -1 else 0
  | _ => 0

theorem ellVal_of_length (a b : Line) (l : List Line) (h : l.length ≠ 2) : ellVal a b l = 0 := by
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩
  · rfl
  · rfl
  · exact absurd rfl h
  · rfl

/-- The coordinate functional on the raw lists. -/
def ellRaw (a b : Line) : OrientedListChains.Raw Line →ₗ[ℚ] ℚ :=
  Finsupp.linearCombination ℚ (ellVal a b)

theorem ellRaw_simplex (a b : Line) (l : List Line) :
    ellRaw a b (OrientedListChains.rawSimplex l) = ellVal a b l := by
  simp [ellRaw, OrientedListChains.rawSimplex]

theorem ellRaw_relation {a b : Line} (hab : a ≠ b) {c : OrientedListChains.Raw Line}
    (hc : c ∈ OrientedListChains.relations Line) :
    ellRaw a b c = 0 ∧ ∀ l ∈ c.support, 2 ≤ l.length := by
  induction hc with
  | swap x y l =>
    constructor
    · rw [map_add, ellRaw_simplex, ellRaw_simplex]
      rcases l with _ | ⟨z, t⟩
      · by_cases h1 : x = a ∧ y = b
        · obtain ⟨rfl, rfl⟩ := h1
          simp [ellVal, hab]
        · by_cases h2 : x = b ∧ y = a
          · obtain ⟨rfl, rfl⟩ := h2
            simp [ellVal, hab, hab.symm]
          · have h3 : ¬ (y = a ∧ x = b) := fun h => h2 ⟨h.2, h.1⟩
            have h4 : ¬ (y = b ∧ x = a) := fun h => h1 ⟨h.2, h.1⟩
            simp [ellVal, h1, h2, h3, h4]
      · rw [ellVal_of_length _ _ _ (by simp), ellVal_of_length _ _ _ (by simp), add_zero]
    · intro m hm
      have := Finsupp.support_add hm
      simp only [Finset.mem_union, OrientedListChains.rawSimplex] at this
      rcases this with h | h
      · have h' := Finset.mem_singleton.mp (Finsupp.support_single_subset h)
        subst h'; simp
      · have h' := Finset.mem_singleton.mp (Finsupp.support_single_subset h)
        subst h'; simp
  | @cons x d hc ih =>
    obtain ⟨_, ih2⟩ := ih
    constructor
    · rw [OrientedListChains.rawCons, Finsupp.lmapDomain_apply, ellRaw, Finsupp.linearCombination_mapDomain,
        Finsupp.linearCombination_apply]
      apply Finset.sum_eq_zero
      intro l hl
      show d l • ellVal a b (x :: l) = 0
      rw [ellVal_of_length _ _ _ (by have := ih2 l hl; simp; omega), smul_zero]
    · intro m hm
      rw [OrientedListChains.rawCons, Finsupp.lmapDomain_apply] at hm
      have := Finsupp.mapDomain_support hm
      rw [Finset.mem_image] at this
      obtain ⟨l, hl, rfl⟩ := this
      have := ih2 l hl
      simp
      omega
  | zero => simp
  | add hc hd ihc ihd =>
    constructor
    · rw [map_add, ihc.1, ihd.1, add_zero]
    · intro m hm
      rcases Finset.mem_union.mp (Finsupp.support_add hm) with h | h
      · exact ihc.2 m h
      · exact ihd.2 m h
  | smul q hc ih =>
    constructor
    · rw [map_smul, ih.1, smul_zero]
    · intro m hm
      exact ih.2 m (Finsupp.support_smul hm)

/-- The coordinate functional of an oriented pair on oriented chains. -/
def ell (a b : Line) (hab : a ≠ b) : OrientedListChains.Chain Line →ₗ[ℚ] ℚ :=
  (OrientedListChains.relations Line).liftQ (ellRaw a b)
    (fun _ hc => LinearMap.mem_ker.mpr (ellRaw_relation hab hc).1)

theorem ell_simplex {a b : Line} (hab : a ≠ b) (l : List Line) :
    ell a b hab (OrientedListChains.simplex l) = ellVal a b l := by
  rw [ell, OrientedListChains.simplex, Submodule.mkQ_apply, Submodule.liftQ_apply, ellRaw_simplex]


theorem p0_of_edge (δ : IntegralGL)
    (h : (δ • cusp1 = cusp1 ∧ δ • cusp2 = cusp2) ∨ (δ • cusp1 = cusp2 ∧ δ • cusp2 = cusp1)) :
    δ • p0 = p0 ∨ δ • p0 = p0.swap := by
  have m1 : δ • cusp1 ∈ (δ • triPlus).1 := smul_mem_tri_smul (by simp [triPlus])
  have m2 : δ • cusp2 ∈ (δ • triPlus).1 := smul_mem_tri_smul (by simp [triPlus])
  have n1 : δ • cusp1 ∈ (δ • triMinus).1 := smul_mem_tri_smul mem_triMinus_cusps12.1
  have n2 : δ • cusp2 ∈ (δ • triMinus).1 := smul_mem_tri_smul mem_triMinus_cusps12.2
  have hP : cusp1 ∈ (δ • triPlus).1 ∧ cusp2 ∈ (δ • triPlus).1 := by
    rcases h with ⟨a, b⟩ | ⟨a, b⟩
    · rw [a] at m1; rw [b] at m2; exact ⟨m1, m2⟩
    · rw [a] at m1; rw [b] at m2; exact ⟨m2, m1⟩
  have hM : cusp1 ∈ (δ • triMinus).1 ∧ cusp2 ∈ (δ • triMinus).1 := by
    rcases h with ⟨a, b⟩ | ⟨a, b⟩
    · rw [a] at n1; rw [b] at n2; exact ⟨n1, n2⟩
    · rw [a] at n1; rw [b] at n2; exact ⟨n2, n1⟩
  have hne : δ • triPlus ≠ δ • triMinus := fun e => triPlus_ne_triMinus (MulAction.injective δ e)
  rcases tri_over_standard_edge hP.1 hP.2 with e1 | e1 <;> rcases tri_over_standard_edge hM.1 hM.2 with e2 | e2
  · exact absurd (e1.trans e2.symm) hne
  · left; exact Subtype.ext (Prod.ext e1 e2)
  · right; exact Subtype.ext (Prod.ext e1 e2)
  · exact absurd (e1.trans e2.symm) hne

theorem ell_theta1 {a b : Line} (hab : a ≠ b) (γ : IntegralGL) :
    ell a b hab (theta1 (γ • p0)) = detQ γ * ellVal a b [γ • cusp1, γ • cusp2] := by
  rw [theta1_apply, chD_apply, map_smul, sig1, chAct_simplex, ell_simplex]
  rfl

theorem ell_theta1_ne {a b : Line} (hab : a ≠ b) {γ0 : IntegralGL} (ha : γ0 • cusp1 = a)
    (hb : γ0 • cusp2 = b) (q : OTE) (hq : ell a b hab (theta1 q) ≠ 0) :
    q = γ0 • p0 ∨ q = (γ0 • p0).swap := by
  obtain ⟨γ, rfl⟩ := ote_transitive q
  rw [ell_theta1] at hq
  have hv : ellVal a b [γ • cusp1, γ • cusp2] ≠ 0 := fun h => hq (by rw [h, mul_zero])
  simp only [ellVal] at hv
  have hcase : (γ • cusp1 = a ∧ γ • cusp2 = b) ∨ (γ • cusp1 = b ∧ γ • cusp2 = a) := by
    by_cases h1 : γ • cusp1 = a ∧ γ • cusp2 = b
    · exact Or.inl h1
    · by_cases h2 : γ • cusp1 = b ∧ γ • cusp2 = a
      · exact Or.inr h2
      · exfalso; exact hv (by simp [h1, h2])
  have hδ : (γ0⁻¹ * γ) • cusp1 = cusp1 ∧ (γ0⁻¹ * γ) • cusp2 = cusp2 ∨
      (γ0⁻¹ * γ) • cusp1 = cusp2 ∧ (γ0⁻¹ * γ) • cusp2 = cusp1 := by
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      rw [mul_smul, mul_smul, h1, h2, ← ha, ← hb, inv_smul_smul, inv_smul_smul]
      exact ⟨rfl, rfl⟩
    · right
      rw [mul_smul, mul_smul, h1, h2, ← ha, ← hb, inv_smul_smul, inv_smul_smul]
      exact ⟨rfl, rfl⟩
  have key : γ • p0 = γ0 • ((γ0⁻¹ * γ) • p0) := by rw [smul_smul, mul_inv_cancel_left]
  rcases p0_of_edge _ hδ with e | e
  · left; rw [key, e]
  · right; rw [key, e]; rfl

theorem Th1_apply (c : MonoidAlgebra ℚ OTE) :
    Th1 c = ∑ q ∈ c.coeff.support, c.coeff q • theta1 q := by
  simp [Th1, Finsupp.linearCombination_apply, Finsupp.sum]


theorem detQ_ne_zero (g : IntegralGL) : detQ g ≠ 0 := by
  intro h
  have := detQ_mul_self g
  rw [h, zero_mul] at this
  exact zero_ne_one this

theorem theta1_swap (q : OTE) : theta1 q.swap = - theta1 q := by
  obtain ⟨γ, rfl⟩ := ote_transitive q
  have : (γ • p0).swap = (γ * sOne) • p0 := by
    rw [OTE.swap_smul, mul_smul, sOne_smul_p0]
  rw [this, theta1_apply, theta1_apply, map_mul]
  change chD γ (chD sOne sig1) = _
  have h : chD sOne sig1 = - sig1 := by
    rw [chD_apply, sig1, chAct_simplex]
    simp only [List.map_cons, List.map_nil, sOne_cusp1, sOne_cusp2, detQ_sOne]
    exact neg_one_smul ℚ _
  rw [h, map_neg]

theorem Th1_injective_anti {c : PE} (hc : c ∈ antiSub) (h : Th1 c = 0) : c = 0 := by
  apply MonoidAlgebra.coeff_eq_zero.mp
  ext q0
  obtain ⟨γ0, hγ0⟩ := ote_transitive q0
  have hab : γ0 • cusp1 ≠ γ0 • cusp2 := fun e => cusp1_ne_cusp2 (MulAction.injective γ0 e)
  have h0 := congrArg (ell (γ0 • cusp1) (γ0 • cusp2) hab) h
  rw [Th1_apply, map_sum, map_zero] at h0
  simp only [map_smul, smul_eq_mul] at h0
  set w : OTE → ℚ := fun q => ell (γ0 • cusp1) (γ0 • cusp2) hab (theta1 q) with hw
  have hw0 : ∀ q, q ≠ q0 → q ≠ q0.swap → w q = 0 := by
    intro q h1 h2
    by_contra hne
    rcases ell_theta1_ne hab rfl rfl q hne with e | e
    · exact h1 (by rw [e, hγ0])
    · exact h2 (by rw [e, hγ0])
  have hwq0 : w q0 = detQ γ0 := by
    rw [hw]; dsimp only
    rw [← hγ0, ell_theta1]
    simp [ellVal]
  have hwq1 : w q0.swap = - detQ γ0 := by
    rw [hw]; dsimp only
    rw [← hγ0]
    have : (γ0 • p0).swap = (γ0 * sOne) • p0 := by
      rw [OTE.swap_smul, mul_smul, sOne_smul_p0]
    rw [this, ell_theta1, map_mul, mul_smul, mul_smul, sOne_cusp1, sOne_cusp2, detQ_sOne]
    simp [ellVal]
  have hne : q0 ≠ q0.swap := (OTE.swap_ne q0).symm
  have hsum : ∑ q ∈ c.coeff.support, c.coeff q * w q =
      c.coeff q0 * w q0 + c.coeff q0.swap * w q0.swap := by
    have e1 : ∑ q ∈ c.coeff.support, c.coeff q * w q =
        ∑ q ∈ c.coeff.support ∪ {q0, q0.swap}, c.coeff q * w q := by
      apply Finset.sum_subset Finset.subset_union_left
      intro q _ hq
      rw [Finsupp.notMem_support_iff.mp hq, zero_mul]
    have e2 : ∑ q ∈ ({q0, q0.swap} : Finset OTE), c.coeff q * w q =
        ∑ q ∈ c.coeff.support ∪ {q0, q0.swap}, c.coeff q * w q := by
      apply Finset.sum_subset Finset.subset_union_right
      intro q _ hq
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hq
      rw [hw0 q hq.1 hq.2, mul_zero]
    rw [e1, ← e2, Finset.sum_pair hne]
  rw [hsum, hwq0, hwq1, coeff_antisymm hc q0] at h0
  have h2 : detQ γ0 * (2 * c.coeff q0) = 0 := by linarith
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 (detQ_ne_zero γ0)
  · simpa using h3

end TernaryPeriodPolynomials.Argument.HeckeDuality
