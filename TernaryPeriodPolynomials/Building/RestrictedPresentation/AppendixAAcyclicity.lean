module

public import TernaryPeriodPolynomials.Building.Ambient.TwoFilling
public import TernaryPeriodPolynomials.Building.Proper.SpanKernel
public import TernaryPeriodPolynomials.Building.Proper.PlaneFilling
public import TernaryPeriodPolynomials.Building.Span.ChainComparison
public import TernaryPeriodPolynomials.Building.RankTwo.GoodFilling
public import TernaryPeriodPolynomials.Building.RankTwo.VertexLinks
public import TernaryPeriodPolynomials.Building.RankTwo.HeightOne
public import TernaryPeriodPolynomials.Building.RankTwo.HeightZero
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Orbit.Completion

@[expose] public section


/-!
# Appendix A: rank-two acyclicity and restricted acyclicity of the good complex

Formalized by Claude Sonnet 5.5.

Paper: Appendix A:

* "We will use the corresponding rank-two fact. The full augmented-frame complex in rank
  two is the contractible filled Farey complex ... The link of a bad vertex is therefore a bi-infinite
  path of good vertices ... Removing those bad stars successively proves that the good rank-two
  subcomplex is connected and weakly contractible, and hence contractible by Whitehead's theorem."
* "... The vanishing of the corresponding homology of `X` therefore gives
  `H̃₀(Y;ℚ) = H₁(Y;ℚ) = H₂(Y;ℚ) = 0`. This is the restricted acyclicity needed in
  Proposition 3.1."

Here `X = BA₃(ℤ)` is `AugmentedFrameComplex.ambient` and `Y` the full good subcomplex
`AugmentedFrameComplex.good`; chains are the finite oriented-list chains of
`OrientedListChains` (`chains C m` has `m` vertices, so `m = 0` is the augmentation).

**Inputs.** Church-Putman's Theorem C (`X` is 2-connected) is not cited as an axiom: the degree-two
part is the library's own `AmbientTwoFilling.ambient_two_filling` (hence `good_two_filling` via the
bad-star eliminations of `GoodChainFilling`), and `H̃₀(Y)`, `H₁(Y)` are derived below from the library's
presentation machinery (`SpanChainComparison.comparison_surjective`, `ProperSpanKernel`, the per-plane
rank-two fillings of `ProperPlaneFilling`) without going through `X`.

**What "contractible" means here.** Mathlib has no simplicial homotopy theory, so contractibility is
not stated; the homological content, which is what the paper uses from it (the long exact sequences
of the filtration), is: every reduced rational cycle of every degree bounds
(`Acyclic`).  Weak contractibility implies this by the Hurewicz theorem.
-/

open TernaryPoly TernaryPoly.OrientedListChains

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.AppendixAAcyclicity

/-- Every cycle with `m` vertices bounds a chain with `m + 1` vertices: reduced rational homology of the
precomplex vanishes in degree `m - 1` (`m = 0`: the complex is nonempty; `m = 1`: connected). -/
def CyclesBound {V : Type*} (C : PreAbstractSimplicialComplex V) (m : ℕ) : Prop :=
  ∀ c ∈ chains C m, boundary c = 0 → ∃ b ∈ chains C (m + 1), boundary b = c

/-- Vanishing of reduced rational homology in all degrees. -/
def Acyclic {V : Type*} (C : PreAbstractSimplicialComplex V) : Prop := ∀ m, CyclesBound C m

/-- Nonempty complexes: the augmentation cycles bound. -/
theorem cyclesBound_zero {V : Type*} (C : PreAbstractSimplicialComplex V) (v : V)
    (hv : ({v} : Finset V) ∈ C) : CyclesBound C 0 := by
  classical
  intro c hc _hd
  clear _hd
  have hform : ∃ t : ℚ, c = t • simplex ([] : List V) := by
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨l, hlen, _, rfl⟩ := hc
      obtain rfl := List.length_eq_zero_iff.mp hlen
      exact ⟨1, by simp⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, rfl⟩ := hx
      obtain ⟨t, rfl⟩ := hy
      exact ⟨s + t, by rw [add_smul]⟩
    | smul q x _ hx =>
      obtain ⟨s, rfl⟩ := hx
      exact ⟨q * s, by rw [smul_smul]⟩
  obtain ⟨t, rfl⟩ := hform
  refine ⟨t • simplex [v], (chains C 1).smul_mem t (simplex_mem_chains C [v] (Or.inr ?_)), ?_⟩
  · simpa using hv
  · rw [map_smul, boundary_cons]
    simp

/-- Complexes with at most `N` vertices per face have no chains with more than `N` vertices. -/
theorem chains_eq_bot_of_card {V : Type*} (C : PreAbstractSimplicialComplex V) (N : ℕ)
    (hC : ∀ s ∈ C, s.card ≤ N) (m : ℕ) (hm : N < m) : chains C m = ⊥ := by
  classical
  apply le_bot_iff.mp
  apply Submodule.span_le.mpr
  rintro _ ⟨l, hlen, hl, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_bot]
  apply simplex_eq_zero_of_not_nodup
  intro hnd
  rcases hl with rfl | hl
  · simp at hlen; omega
  · have := hC _ hl
    rw [List.toFinset_card_of_nodup hnd] at this
    omega


/-! ### Rank two -/

section RankTwo

open RankTwoAugmentedFrames

theorem cyclesBound_of_top {V : Type*} (C : PreAbstractSimplicialComplex V) (N : ℕ)
    (hC : ∀ s ∈ C, s.card ≤ N) (htop : ∀ c ∈ chains C N, boundary c = 0 → c = 0) :
    ∀ m, N ≤ m → CyclesBound C m := by
  intro m hm c hc hd
  rcases Nat.eq_or_lt_of_le hm with rfl | hlt
  · exact ⟨0, (chains C _).zero_mem, by rw [htop c hc hd, map_zero]⟩
  · rw [chains_eq_bot_of_card C N hC m hlt, Submodule.mem_bot] at hc
    exact ⟨0, (chains C _).zero_mem, by rw [hc, map_zero]⟩

/-- **The rank-two augmented-frame complex (filled Farey complex) is acyclic**: connected, `H₁ = 0`, and
no cycles in higher degree (it is a 2-dimensional complex without top-dimensional cycles). -/
theorem rank_two_ambient_acyclic : Acyclic RankTwoAugmentedFrames.ambient := by
  have hC : ∀ s ∈ RankTwoAugmentedFrames.ambient, s.card ≤ 3 :=
    fun s hs => RankTwoVertexLinks.ambient_card_le_three hs
  intro m
  by_cases hm : 3 ≤ m
  · exact cyclesBound_of_top _ 3 hC
      (fun c hc hd => RankTwoVertexLinks.top_cycle_eq_zero hc hd) m hm
  · interval_cases m
    · exact cyclesBound_zero _ RankTwoHeightZero.zeroVertex (singleton_mem_ambient _)
    · exact fun c hc hd => RankTwoHeightZero.ambient_reduced_zero_filling hc hd
    · exact fun c hc hd => RankTwoHeightOne.ambient_one_cycle_filling hc hd

/-- A nonzero residue functional detects a rank-two line. -/
theorem exists_good_rank_two (φ : RankTwoGoodComplex.Functional) (hφ : φ ≠ 0) :
    ∃ L : RationalLine2, RankTwoGoodComplex.Good φ L := by
  have hex : ∃ j : Fin 2, φ (Pi.single j 1) ≠ 0 := by
    by_contra h
    push Not at h
    apply hφ
    apply LinearMap.pi_ext
    intro i x
    have hx : (Pi.single i x : RankTwoGoodComplex.ResidueSpace) = x • Pi.single i 1 := by
      funext k
      by_cases hk : k = i <;> simp [hk]
    rw [hx, map_smul, h i]
    simp
  obtain ⟨j, hj⟩ := hex
  let v : IntegralVector := Pi.single j 1
  have hvne : rationalVector v ≠ 0 := by
    intro h
    have := congrFun h j
    simp [rationalVector, v] at this
  have hprim : Primitive v := by
    fin_cases j <;> simp [Primitive, content, v]
  refine ⟨vectorLine (rationalVector v) hvne, ?_⟩
  rw [RankTwoGoodComplex.good_iff_primitive φ _ hprim rfl]
  have hred : RankTwoGoodComplex.reduction v = Pi.single j 1 := by
    funext i
    simp only [RankTwoGoodComplex.reduction, v, Pi.single_apply]
    split_ifs <;> simp
  rw [hred]
  exact hj

/-- **The good rank-two complex of a nonzero residue functional is acyclic.** -/
theorem rank_two_good_acyclic (φ : RankTwoGoodComplex.Functional) (hφ : φ ≠ 0) :
    Acyclic (RankTwoGoodComplex.good φ) := by
  have hC : ∀ s ∈ RankTwoGoodComplex.good φ, s.card ≤ 3 :=
    fun s hs => RankTwoVertexLinks.ambient_card_le_three hs.1
  intro m
  by_cases hm : 3 ≤ m
  · exact cyclesBound_of_top _ 3 hC
      (fun c hc hd => RankTwoVertexLinks.subcomplex_top_cycle_eq_zero _
        (RankTwoGoodComplex.good_le_ambient φ) hc hd) m hm
  · interval_cases m
    · obtain ⟨L, hL⟩ := exists_good_rank_two φ hφ
      exact cyclesBound_zero _ L ⟨singleton_mem_ambient L, by simpa using hL⟩
    · exact fun c hc hd => RankTwoGoodFilling.zero_cycle_filling φ hφ hc hd
    · exact fun c hc hd => RankTwoGoodOne.one_cycle_filling φ hc hd

end RankTwo

/-! ### Rank three: the good complex `Y` -/

section RankThree

open AugmentedFrameComplex ModThreeGoodAction

theorem good_two_filling : CyclesBound good 3 :=
  fun _ hc hd => AmbientTwoFilling.good_two_filling hc hd

/-- `H₁(Y;ℚ) = 0`.  Proof: the apartment image `edgeMap z` of a good one-cycle is a cycle of the incidence
graph `𝒯↑`; by the (library) surjectivity of the comparison `ℚ ⊗ (relative Good chains) → St↑` it is
`edgeMap ∂t` for a good triangle chain `t`; the difference `z - ∂t` has zero apartment image and bounds
proper-span triangles by the rank-two filling of every plane. -/
theorem good_one_filling : CyclesBound good 2 := by
  intro z hz hd
  have hcyc : GoodChainComplex.boundary (SpanChainComparison.edgeMap z) = 0 := by
    rw [SpanChainComparison.boundary_edgeMap hz, hd, map_zero]
  obtain ⟨x, hx⟩ := SpanChainComparison.comparison_surjective
    ⟨SpanChainComparison.edgeMap z, hcyc⟩
  obtain ⟨t, rfl⟩ := Submodule.mkQ_surjective _ x
  have ht : SpanChainComparison.edgeMap (boundary t.val) = SpanChainComparison.edgeMap z :=
    congrArg Subtype.val hx
  have hbt : boundary t.val ∈ chains good 2 := boundary_mem_chains good 2 t.property
  have hz' : z - boundary t.val ∈ chains good 2 := (chains good 2).sub_mem hz hbt
  have hdz' : boundary (z - boundary t.val) = 0 := by
    rw [map_sub, hd, boundary_squared, sub_zero]
  have hez' : SpanChainComparison.edgeMap (z - boundary t.val) = 0 := by
    rw [map_sub, ht, sub_self]
  obtain ⟨q, hq, hdq⟩ := ProperSpanKernel.proper_kernel_filling_actual _ hz' hdz' hez'
  refine ⟨t.val + q, (chains good 3).add_mem t.property (chains_mono properGood_le_good 3 hq), ?_⟩
  rw [map_add, hdq]
  abel

/-- Two good lines are joined by a good one-chain: they lie in a common rational plane, which is the plane of
an integral chart, and the good complex of the plane is connected (the rank-two statement). -/
theorem good_pair_filling (L M : RationalLine) (hL : Good L.val) (hM : Good M.val) :
    ∃ b ∈ chains good 2, boundary b = simplex [L] - simplex [M] := by
  classical
  by_cases hLM : L = M
  · subst hLM
    exact ⟨0, (chains good 2).zero_mem, by simp⟩
  · have hP2 : Module.finrank ℚ (L.val ⊔ M.val : RationalSubspace) = 2 :=
      GoodIncidenceConnected.finrank_sup_of_distinct_lines L.val M.val L.property M.property
        (fun h => hLM (Subtype.ext h))
    obtain ⟨g0, hg0⟩ := RelativeOrbitCompletion.plane_completion _ hP2
    have hsup : (augmentedLine g0 0).val ⊔ (augmentedLine g0 1).val = L.val ⊔ M.val :=
      (RelativeOrbitCompletion.mapSpace_P0 g0).symm.trans hg0
    have hne : augmentedLine g0 0 ≠ augmentedLine g0 1 := by
      intro h
      rw [h, sup_idem] at hsup
      have h1 : Module.finrank ℚ (L.val ⊔ M.val : RationalSubspace) = 1 := by
        rw [← hsup]
        exact (augmentedLine g0 1).property
      omega
    have he : ({augmentedLine g0 0, augmentedLine g0 1} : Finset RationalLine) ∈ ambient := by
      apply subset_augmentedFrame_mem g0 (Finset.insert_nonempty _ _)
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
    obtain ⟨g, hg⟩ := ProperPlaneChart.exists_plane_of_edge _ _ hne he
    have hpl : ProperPlaneChart.plane g = L.val ⊔ M.val := hg.trans hsup
    have hLle : L.val ≤ ProperPlaneChart.plane g := hpl ▸ le_sup_left
    have hMle : M.val ≤ ProperPlaneChart.plane g := hpl ▸ le_sup_right
    have hfun : ProperPlaneGood.planeFunctional g ≠ 0 :=
      ProperPlaneGood.planeFunctional_ne_zero g L hLle hL
    have hsimp : ∀ N : RationalLine, Good N.val → N.val ≤ ProperPlaneChart.plane g →
        simplex [N] ∈ chains (ProperPlaneGood.goodPlane g) 1 := by
      intro N hN hle
      apply simplex_mem_chains _ [N] (Or.inr ?_)
      refine ⟨⟨RationalLineBasis.singleton_mem_ambient N, ?_⟩, ?_⟩
      · intro x hx
        simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
          Finset.mem_singleton] at hx
        subst hx
        exact hN
      · intro x hx
        simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
          Finset.mem_singleton] at hx
        subst hx
        exact hle
    have hc : simplex [L] - simplex [M] ∈ chains (ProperPlaneGood.goodPlane g) 1 :=
      ((chains _ 1).sub_mem (hsimp L hL hLle) (hsimp M hM hMle))
    have hd : boundary (simplex [L] - simplex [M]) = 0 := by
      simp only [map_sub, boundary_cons, boundary_nil, map_zero, sub_zero]
      simp
    obtain ⟨b, hb, hdb⟩ := ProperPlaneFilling.zero_cycle_filling g hfun hc hd
    exact ⟨b, chains_mono (ProperPlaneGood.goodPlane_le_good g) 2 hb, hdb⟩

/-- `H̃₀(Y;ℚ) = 0`: the good complex is connected. -/
theorem good_zero_filling : CyclesBound good 1 := by
  classical
  obtain ⟨L₀, hL₀fr, hL₀g⟩ := ModThreeGoodAction.exists_good_line
  let L0 : RationalLine := ⟨L₀, hL₀fr⟩
  intro c hc hd
  have hform : ∃ b ∈ chains good 2, ∃ t : ℚ, c = boundary b + t • simplex [L0] := by
    clear hd
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨l, hlen, hl, rfl⟩ := hc
      obtain ⟨N, rfl⟩ := List.length_eq_one_iff.mp hlen
      have hN : Good N.val := by
        rcases hl with h | h
        · simp at h
        · exact h.2 N (by simp)
      obtain ⟨b, hb, hdb⟩ := good_pair_filling N L0 hN hL₀g
      exact ⟨b, hb, 1, by rw [hdb]; simp⟩
    | zero => exact ⟨0, (chains good 2).zero_mem, 0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨b, hb, s, rfl⟩ := hx
      obtain ⟨b', hb', t, rfl⟩ := hy
      exact ⟨b + b', (chains good 2).add_mem hb hb', s + t, by rw [map_add, add_smul]; abel⟩
    | smul q x _ hx =>
      obtain ⟨b, hb, s, rfl⟩ := hx
      exact ⟨q • b, (chains good 2).smul_mem q hb, q * s, by
        rw [map_smul, smul_add, smul_smul]⟩
  obtain ⟨b, hb, t, rfl⟩ := hform
  have ht : t = 0 := by
    have h0 : boundary (boundary b + t • simplex [L0]) = 0 := hd
    rw [map_add, boundary_squared, zero_add, map_smul, boundary_cons] at h0
    simp only [boundary_nil, map_zero, sub_zero] at h0
    let f : List RationalLine → ℚ := fun l => if l = [] then 1 else 0
    have hf : SpanChainComparison.AlternatingLists f := by
      intro p a b' s
      simp [f]
    have := congrArg (SpanChainComparison.evaluate f hf) h0
    simpa [f] using this
  refine ⟨b, hb, ?_⟩
  rw [ht, zero_smul, add_zero]

/-- `Y` is nonempty: the augmentation cycles bound. -/
theorem good_neg_one_filling : CyclesBound good 0 := by
  obtain ⟨L₀, hL₀fr, hL₀g⟩ := ModThreeGoodAction.exists_good_line
  exact cyclesBound_zero good ⟨L₀, hL₀fr⟩
    ⟨RationalLineBasis.singleton_mem_ambient ⟨L₀, hL₀fr⟩, by simpa using hL₀g⟩

/-- **Appendix A, restricted acyclicity**: `H̃₀(Y;ℚ) = H₁(Y;ℚ) = H₂(Y;ℚ) = 0` (and `Y ≠ ∅`). -/
theorem restricted_acyclicity :
    CyclesBound good 0 ∧ CyclesBound good 1 ∧ CyclesBound good 2 ∧ CyclesBound good 3 :=
  ⟨good_neg_one_filling, good_zero_filling, good_one_filling, good_two_filling⟩

end RankThree

end TernaryPeriodPolynomials.Argument.Statements.AppendixAAcyclicity
