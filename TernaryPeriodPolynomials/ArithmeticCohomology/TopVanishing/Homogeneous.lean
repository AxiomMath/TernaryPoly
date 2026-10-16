module

public import TernaryPeriodPolynomials.ArithmeticCohomology.TopVanishing.Basic

@[expose] public section


/-!
# The homogeneous complex

The bar complex with vertices in a group `G`, acted on by a subgroup `Λ` by left multiplication,
as a permutation complex with a single point in index `0`, free action in positive indices and
exact. Its low-degree boundaries are the alternating homogeneous differentials.
-/

noncomputable section

namespace TernaryPeriodPolynomials.TopVanishing

open TernaryPeriodPolynomials.Duality

variable {G : Type} [Group G]

/-- Linear maps out of chains agree when they agree on basis chains. -/
theorem lin_ext_single {S M : Type} [AddCommMonoid M] [Module ℂ M]
    {F F' : (S →₀ ℂ) →ₗ[ℂ] M}
    (h : ∀ s, F (Finsupp.single s 1) = F' (Finsupp.single s 1)) : F = F' := by
  apply Finsupp.lhom_ext
  intro s a
  have hs : Finsupp.single s a = a • Finsupp.single s (1 : ℂ) := by simp
  rw [hs, map_smul, map_smul, h]

/-- The alternating face boundary of the homogeneous complex. -/
def homogeneousBoundary (k : ℕ) : ((Fin (k + 1) → G) →₀ ℂ) →ₗ[ℂ] ((Fin k → G) →₀ ℂ) :=
  Finsupp.linearCombination ℂ (fun x =>
    ∑ i : Fin (k + 1), ((-1 : ℂ) ^ (i : ℕ)) • Finsupp.single (x ∘ Fin.succAbove i) 1)

omit [Group G] in
theorem homogeneousBoundary_single (k : ℕ) (x : Fin (k + 1) → G) :
    homogeneousBoundary k (Finsupp.single x 1) =
      ∑ i : Fin (k + 1), ((-1 : ℂ) ^ (i : ℕ)) • Finsupp.single (x ∘ Fin.succAbove i) 1 := by
  unfold homogeneousBoundary
  rw [Finsupp.linearCombination_single, one_smul]

/-- The cone on a vertex `g`: prepend `g` to every tuple. -/
def homogeneousCone (g : G) (k : ℕ) : ((Fin k → G) →₀ ℂ) →ₗ[ℂ] ((Fin (k + 1) → G) →₀ ℂ) :=
  Finsupp.lmapDomain ℂ ℂ (fun x : Fin k → G => (Fin.cons g x : Fin (k + 1) → G))

omit [Group G] in
theorem homogeneousCone_single (g : G) (k : ℕ) (x : Fin k → G) (a : ℂ) :
    homogeneousCone g k (Finsupp.single x a) =
      Finsupp.single (Fin.cons g x : Fin (k + 1) → G) a := by
  simp [homogeneousCone]

omit [Group G] in
theorem single_eq_cone (k : ℕ) (x : Fin (k + 1) → G) :
    Finsupp.single x (1 : ℂ) = homogeneousCone (x 0) k (Finsupp.single (Fin.tail x) 1) := by
  rw [homogeneousCone_single, Fin.cons_self_tail x]

omit [Group G] in
theorem cons_comp_succAbove_zero (g : G) (k : ℕ) (x : Fin (k + 1) → G) :
    (Fin.cons g x : Fin (k + 1 + 1) → G) ∘ Fin.succAbove 0 = x := by
  funext a
  simp

omit [Group G] in
theorem cons_comp_succAbove_succ (g : G) (k : ℕ) (x : Fin (k + 1) → G) (j : Fin (k + 1)) :
    (Fin.cons g x : Fin (k + 1 + 1) → G) ∘ Fin.succAbove j.succ =
      (Fin.cons g (x ∘ Fin.succAbove j) : Fin (k + 1) → G) := by
  funext a
  rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨a', rfl⟩
  · simp
  · simp [Fin.succ_succAbove_succ]

omit [Group G] in
/-- The cone contracts the homogeneous complex: the augmentation case. -/
theorem homogeneousBoundary_cone_zero (g : G) (v : (Fin 0 → G) →₀ ℂ) :
    homogeneousBoundary 0 (homogeneousCone g 0 v) = v := by
  have h : homogeneousBoundary (G := G) 0 ∘ₗ homogeneousCone g 0 = LinearMap.id :=
    lin_ext_single fun x => by
      simp only [LinearMap.comp_apply, LinearMap.id_apply, homogeneousCone_single,
        homogeneousBoundary_single]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, pow_zero,
        one_smul]
      exact congrArg (fun y => Finsupp.single y (1 : ℂ)) (Subsingleton.elim _ _)
  exact LinearMap.congr_fun h v

omit [Group G] in
theorem homogeneousBoundary_cons (g : G) (k : ℕ) (x : Fin (k + 1) → G) :
    homogeneousBoundary (k + 1) (Finsupp.single (Fin.cons g x : Fin (k + 1 + 1) → G) 1) =
      Finsupp.single x 1 - ∑ j : Fin (k + 1), ((-1 : ℂ) ^ (j : ℕ)) •
        Finsupp.single (Fin.cons g (x ∘ Fin.succAbove j) : Fin (k + 1) → G) 1 := by
  have hsum := Fin.sum_univ_succ (fun i : Fin (k + 1 + 1) =>
    ((-1 : ℂ) ^ (i : ℕ)) •
      Finsupp.single ((Fin.cons g x : Fin (k + 1 + 1) → G) ∘ Fin.succAbove i) (1 : ℂ))
  rw [homogeneousBoundary_single, hsum]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ, cons_comp_succAbove_zero,
    cons_comp_succAbove_succ, mul_neg, mul_one, neg_smul, Finset.sum_neg_distrib,
    ← sub_eq_add_neg]

omit [Group G] in
theorem homogeneousBoundary_cone_single (g : G) (k : ℕ) (x : Fin (k + 1) → G) :
    homogeneousBoundary (k + 1) (homogeneousCone g (k + 1) (Finsupp.single x 1)) +
      homogeneousCone g k (homogeneousBoundary k (Finsupp.single x 1)) = Finsupp.single x 1 := by
  have h2 : homogeneousCone g k (homogeneousBoundary k (Finsupp.single x 1)) =
      ∑ j : Fin (k + 1), ((-1 : ℂ) ^ (j : ℕ)) •
        Finsupp.single (Fin.cons g (x ∘ Fin.succAbove j) : Fin (k + 1) → G) 1 := by
    rw [homogeneousBoundary_single, map_sum]
    simp only [map_smul, homogeneousCone_single]
  rw [h2, homogeneousCone_single, homogeneousBoundary_cons]
  exact sub_add_cancel _ _

omit [Group G] in
/-- The cone contracts the homogeneous complex. -/
theorem homogeneousBoundary_cone (g : G) (k : ℕ) (v : (Fin (k + 1) → G) →₀ ℂ) :
    homogeneousBoundary (k + 1) (homogeneousCone g (k + 1) v) +
      homogeneousCone g k (homogeneousBoundary k v) = v := by
  have h : homogeneousBoundary (k + 1) ∘ₗ homogeneousCone g (k + 1) +
      homogeneousCone g k ∘ₗ homogeneousBoundary k = (LinearMap.id : _ →ₗ[ℂ] _) :=
    lin_ext_single fun x => by
      simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply]
      exact homogeneousBoundary_cone_single g k x
  exact LinearMap.congr_fun h v

omit [Group G] in
theorem homogeneousBoundary_comp_cone_succ (k : ℕ)
    (ih : homogeneousBoundary (G := G) k ∘ₗ homogeneousBoundary (k + 1) = 0) (g : G)
    (w : (Fin (k + 1 + 1) → G) →₀ ℂ) :
    homogeneousBoundary (k + 1) (homogeneousBoundary (k + 1 + 1)
      (homogeneousCone g (k + 1 + 1) w)) = 0 := by
  have e1 := homogeneousBoundary_cone g (k + 1) w
  have e2 := homogeneousBoundary_cone g k (homogeneousBoundary (k + 1) w)
  have e3 : homogeneousBoundary k (homogeneousBoundary (k + 1) w) = 0 := by
    simpa using LinearMap.congr_fun ih w
  rw [e3, map_zero, add_zero] at e2
  have e4 : homogeneousBoundary (k + 1 + 1) (homogeneousCone g (k + 1 + 1) w) =
      w - homogeneousCone g (k + 1) (homogeneousBoundary (k + 1) w) := eq_sub_of_add_eq e1
  rw [e4, map_sub, e2, sub_self]

omit [Group G] in
theorem homogeneousBoundary_comp_cone_zero (g : G) (w : (Fin (0 + 1) → G) →₀ ℂ) :
    homogeneousBoundary 0 (homogeneousBoundary (0 + 1) (homogeneousCone g (0 + 1) w)) = 0 := by
  have e1 := homogeneousBoundary_cone g 0 w
  have e4 : homogeneousBoundary (0 + 1) (homogeneousCone g (0 + 1) w) =
      w - homogeneousCone g 0 (homogeneousBoundary 0 w) := eq_sub_of_add_eq e1
  rw [e4, map_sub, homogeneousBoundary_cone_zero, sub_self]

omit [Group G] in
theorem homogeneousBoundary_comp (k : ℕ) :
    homogeneousBoundary (G := G) k ∘ₗ homogeneousBoundary (k + 1) = 0 := by
  induction k with
  | zero =>
    refine lin_ext_single fun x => ?_
    rw [single_eq_cone (0 + 1) x]
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    exact homogeneousBoundary_comp_cone_zero _ _
  | succ k ih =>
    refine lin_ext_single fun x => ?_
    rw [single_eq_cone (k + 1 + 1) x]
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    exact homogeneousBoundary_comp_cone_succ k ih _ _

variable (Λ : Subgroup G)

theorem homogeneousBoundary_equivariant (k : ℕ) :
    Equivariant Λ (homogeneousBoundary (G := G) k) := by
  apply equivariant_of_single
  intro γ s
  rw [homogeneousBoundary_single, homogeneousBoundary_single, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : (γ • s) ∘ Fin.succAbove i = γ • (s ∘ Fin.succAbove i) := by
    funext a
    rfl
  rw [map_smul, chainAct_single, hi]

/-- The homogeneous complex: index `k` carries the `k`-tuples of vertices. -/
def homogeneousComplex : PermutationComplex Λ where
  cell k := Fin k → G
  action := fun k => inferInstanceAs (MulAction Λ (Fin k → G))
  d := fun k => homogeneousBoundary (G := G) k
  equivariant := fun k => homogeneousBoundary_equivariant Λ k
  d_comp_d := fun k => homogeneousBoundary_comp k

instance homogeneousComplex_unique : Unique ((homogeneousComplex Λ).cell 0) :=
  inferInstanceAs (Unique (Fin 0 → G))

theorem smul_pi_eq_self {k : ℕ} (γ : Λ) (s : Fin (k + 1) → G) (h : γ • s = s) : γ = 1 := by
  exact Subtype.ext (mul_right_cancel (a := γ.val) (c := 1) (b := s 0)
    ((congrFun h 0).trans (one_mul _).symm))

theorem homogeneousComplex_free : (homogeneousComplex Λ).Free := by
  intro k γ s h
  exact smul_pi_eq_self Λ γ s h

theorem homogeneousComplex_exact : (homogeneousComplex Λ).Exact := by
  unfold PermutationComplex.Exact
  refine ⟨?_, ?_⟩
  · rw [LinearMap.range_eq_top]
    intro v
    exact ⟨homogeneousCone (1 : G) 0 v, homogeneousBoundary_cone_zero (1 : G) v⟩
  · intro k v hv
    have hv' : homogeneousBoundary (G := G) k v = 0 := LinearMap.mem_ker.mp hv
    have h := homogeneousBoundary_cone (1 : G) k v
    rw [hv', map_zero, add_zero] at h
    exact LinearMap.mem_range.mpr ⟨homogeneousCone (1 : G) (k + 1) v, h⟩

omit [Group G] in
theorem differentialFourRaw_eq (f : (Fin 5 → G) → ℂ) (x : Fin 6 → G) :
    differentialFourRaw f x =
      Finsupp.linearCombination ℂ f (homogeneousBoundary 5 (Finsupp.single x 1)) := by
  have h0 : x ∘ Fin.succAbove (0 : Fin 6) = ![x 1, x 2, x 3, x 4, x 5] := by
    funext j; fin_cases j <;> rfl
  have h1 : x ∘ Fin.succAbove (1 : Fin 6) = ![x 0, x 2, x 3, x 4, x 5] := by
    funext j; fin_cases j <;> rfl
  have h2 : x ∘ Fin.succAbove (2 : Fin 6) = ![x 0, x 1, x 3, x 4, x 5] := by
    funext j; fin_cases j <;> rfl
  have h3 : x ∘ Fin.succAbove (3 : Fin 6) = ![x 0, x 1, x 2, x 4, x 5] := by
    funext j; fin_cases j <;> rfl
  have h4 : x ∘ Fin.succAbove (4 : Fin 6) = ![x 0, x 1, x 2, x 3, x 5] := by
    funext j; fin_cases j <;> rfl
  have h5 : x ∘ Fin.succAbove (5 : Fin 6) = ![x 0, x 1, x 2, x 3, x 4] := by
    funext j; fin_cases j <;> rfl
  have v0 : ((0 : Fin 6) : ℕ) = 0 := rfl
  have v1 : ((1 : Fin 6) : ℕ) = 1 := rfl
  have v2 : ((2 : Fin 6) : ℕ) = 2 := rfl
  have v3 : ((3 : Fin 6) : ℕ) = 3 := rfl
  have v4 : ((4 : Fin 6) : ℕ) = 4 := rfl
  have v5 : ((5 : Fin 6) : ℕ) = 5 := rfl
  unfold differentialFourRaw
  rw [homogeneousBoundary_single, map_sum, Fin.sum_univ_six]
  simp only [map_smul, Finsupp.linearCombination_single, smul_eq_mul,
    h0, h1, h2, h3, h4, h5, v0, v1, v2, v3, v4, v5]
  ring

omit [Group G] in
theorem differentialThreeRaw_eq (θ : (Fin 4 → G) → ℂ) (x : Fin 5 → G) :
    differentialThreeRaw θ x =
      Finsupp.linearCombination ℂ θ (homogeneousBoundary 4 (Finsupp.single x 1)) := by
  have h0 : x ∘ Fin.succAbove (0 : Fin 5) = ![x 1, x 2, x 3, x 4] := by
    funext j; fin_cases j <;> rfl
  have h1 : x ∘ Fin.succAbove (1 : Fin 5) = ![x 0, x 2, x 3, x 4] := by
    funext j; fin_cases j <;> rfl
  have h2 : x ∘ Fin.succAbove (2 : Fin 5) = ![x 0, x 1, x 3, x 4] := by
    funext j; fin_cases j <;> rfl
  have h3 : x ∘ Fin.succAbove (3 : Fin 5) = ![x 0, x 1, x 2, x 4] := by
    funext j; fin_cases j <;> rfl
  have h4 : x ∘ Fin.succAbove (4 : Fin 5) = ![x 0, x 1, x 2, x 3] := by
    funext j; fin_cases j <;> rfl
  have v0 : ((0 : Fin 5) : ℕ) = 0 := rfl
  have v1 : ((1 : Fin 5) : ℕ) = 1 := rfl
  have v2 : ((2 : Fin 5) : ℕ) = 2 := rfl
  have v3 : ((3 : Fin 5) : ℕ) = 3 := rfl
  have v4 : ((4 : Fin 5) : ℕ) = 4 := rfl
  unfold differentialThreeRaw
  rw [homogeneousBoundary_single, map_sum, Fin.sum_univ_five]
  simp only [map_smul, Finsupp.linearCombination_single, smul_eq_mul,
    h0, h1, h2, h3, h4, v0, v1, v2, v3, v4]
  ring

end TernaryPeriodPolynomials.TopVanishing
