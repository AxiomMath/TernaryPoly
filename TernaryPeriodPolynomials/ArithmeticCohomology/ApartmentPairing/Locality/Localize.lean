module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.CrossRelation
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.ECap
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Chains
public import TernaryPeriodPolynomials.Topology.SingularHomology.SubChainSubspaceBridge

@[expose] public section


/-!
# Locality for Poincaré duality: localization of the translate-sum pairing

Generic statements about a quotient covering `p : E ⟶ B` (deck group `G`, representation `V`):

* `isSubordinate_pushSimplex_iff`, `isSubordinate_projection_iff`, `isSubordinate_smul'`: subordination
  of pushed-forward, projected and translated simplices;
* `cap_eq_zero_of_front`: the cap of a cochain vanishing on `A`-subordinate simplices kills `A`-chains;
* `capE_pushforward`: for a local section `s : Y ⟶ E` over `ι : Y ⟶ B` (`s ≫ p = ι`), the cap of the
  geometric cochain `φ` with `ι_* c` is, in the coinvariant model, `capE` of the chain `s_* c`;
* `Yco_cap_eq_zero_of_back`, `Yco_cap_boundary`: the translate-sum pairing `Yco` of a cap vanishes when
  the chain is supported where `y` vanishes (together with its translates) and on cap boundaries of a
  cocycle.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.Lemma33.Locality

open CategoryTheory Limits TernaryPoly TernaryPoly.FreeActionLinearization
  TernaryPoly.CoveringSingularOrbits TernaryPoly.SingularLocalCoefficient
  TernaryPoly.SingularLocalHomology TernaryPoly.SingularLocalCap TernaryPoly.EquivariantSingularResolution
open SphereOddDegree SphereOddDegree.AlexanderWhitney SphereOddDegree.AffineBarycentricSubdivision

section Subordinate

theorem isSubordinate_pushSimplex_iff {X Y : TopCat.{0}} (f : X ⟶ Y) (S : Set Y) {n : ℕ}
    (σ : SingularSimplex X n) :
    IsSubordinate S (pushSimplex f n σ) ↔ IsSubordinate (f ⁻¹' S) σ := by
  unfold IsSubordinate
  rw [show mvSimplexMap (pushSimplex f n σ) =
      singularSimplexAsContinuousMap Y n (pushSimplex f n σ) from rfl, pushSimplex_continuousMap]
  constructor
  · intro h x hx
    obtain ⟨y, rfl⟩ := hx
    exact h ⟨y, rfl⟩
  · intro h z hz
    obtain ⟨y, rfl⟩ := hz
    exact h ⟨y, rfl⟩

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B)

theorem isSubordinate_projection_iff (S : Set B) {n : ℕ} (τ : SingularSimplex E n) :
    IsSubordinate S (projection p n τ) ↔ IsSubordinate (p ⁻¹' S) τ :=
  isSubordinate_pushSimplex_iff p S τ

theorem isSubordinate_smul' (g : G) {S : Set E} (hS : ∀ x, x ∈ S → g • x ∈ S) {n : ℕ}
    (τ : SingularSimplex E n) (h : IsSubordinate S τ) : IsSubordinate S (g • τ) := by
  rw [singular_smul_eq_map, show (TopCat.toSSet.map (scalarMap G E g)).app
      (Opposite.op (SimplexCategory.mk n)) τ = pushSimplex (scalarMap G E g) n τ from rfl,
    isSubordinate_pushSimplex_iff]
  intro x hx
  exact hS _ (h hx)

end Subordinate

section Cap

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  [IsCancelSMul G E] (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) (V : Rep.{0} ℚ G)

omit [ContinuousConstSMul G E] [IsCancelSMul G E] in
theorem capSimplex_eq_zero_of_front (a b : ℕ) (φ : VertexCochain p hp V a)
    (σ : SingularSimplex B (a+b)) (h : φ (frontSimplex B a b σ) = 0) :
    capSimplex p hp V a b σ φ = 0 := by
  rw [capSimplex_apply]
  have key : ∀ x : FiberCoefficient p hp (↑V) (atVertex (frontSimplex B a b σ)), x = 0 →
      DFinsupp.single (β := fun τ : SingularSimplex B b => FiberCoefficient p hp (↑V) (atVertex τ))
        (backSimplex B a b σ)
        (coefficientTransportLinear p hp (simplexPullPath (backMap a b) σ).symm
          (coefficientTransportLinear p hp (simplexPullPath (frontMap a b) σ) x)) = 0 := by
    intro x hx
    subst hx
    erw [map_zero]
    exact DFinsupp.single_zero _
  exact key _ h

omit [ContinuousConstSMul G E] [IsCancelSMul G E] in
/-- A cochain vanishing on `A`-subordinate simplices caps every `A`-chain to zero. -/
theorem cap_eq_zero_of_front (a b : ℕ) (φ : VertexCochain p hp V a) {A : Set B}
    (hφ : ∀ σ : SingularSimplex B a, IsSubordinate A σ → φ σ = 0)
    {c : singularChainGroup ℚ B (a+b)} (hc : c ∈ subChainSubmodule ℚ B A (a+b)) :
    cap p hp V a b φ c = 0 := by
  refine subChainSubmodule_induction (S := A) (p := fun x => cap p hp V a b φ x = 0) ?_ ?_ ?_ ?_ hc
  · intro σ hσ
    rw [cap_generator]
    exact capSimplex_eq_zero_of_front p hp V a b φ σ (hφ _ (isSubordinate_front B a b σ hσ))
  · exact map_zero _
  · intro x y hx hy
    rw [map_add, hx, hy, add_zero]
  · intro r x hx
    rw [map_smul, hx, smul_zero]

theorem projection_pushSimplex {Y : TopCat.{0}} (s : Y ⟶ E) (n : ℕ) (σ : SingularSimplex Y n) :
    projection p n (pushSimplex s n σ) = pushSimplex (s ≫ p) n σ := by
  unfold projection pushSimplex
  rw [Functor.map_comp]
  rfl

/-- **Cap through a local section.** If `s : Y ⟶ E` lifts `ι : Y ⟶ B` then capping the geometric
cochain with `ι_* c` is, in the coinvariant model, `capE` of the chain `s_* c` of `E`. -/
theorem capE_pushforward {Y : TopCat.{0}} (s : Y ⟶ E) (ι : Y ⟶ B) (hsι : s ≫ p = ι) (a b : ℕ)
    (φ : VertexCochain p hp V a) (c : singularChainGroup ℚ Y (a+b)) :
    capE V a b (vertexToFunction p hp φ) ((singularChainMap ℚ s (a+b)).hom c) =
      (degreeEquiv p hp V b).symm (cap p hp V a b φ ((singularChainMap ℚ ι (a+b)).hom c)) := by
  have h : (capE V a b (vertexToFunction p hp φ)).comp (singularChainMap ℚ s (a+b)).hom =
      ((degreeEquiv p hp V b).symm.toLinearMap).comp
        ((cap p hp V a b φ).comp (singularChainMap ℚ ι (a+b)).hom) := by
    apply chainDesc_ext
    intro σ
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, singularChainMap_generator,
      capE_generator, cap_generator]
    symm
    have hl : projection p (a+b) (pushSimplex s (a+b) σ) = pushSimplex ι (a+b) σ := by
      rw [← hsι]
      exact projection_pushSimplex p s (a+b) σ
    exact capSimplex_lift p hp V a b φ (σ := pushSimplex ι (a+b) σ) ⟨pushSimplex s (a+b) σ, hl⟩
  exact LinearMap.congr_fun h c

/-- The translate-sum pairing of a cap with a chain supported away from `Z` (invariantly) vanishes. -/
theorem Yco_cap_eq_zero_of_back (a b : ℕ) (φ : VertexCochain p hp V a)
    (y : singularChainGroup ℚ E b →ₗ[ℚ] ℚ)
    (hfin : ∀ τ : SingularSimplex E b, {g : G | y (chainGenerator ℚ E b (g • τ)) ≠ 0}.Finite)
    {Z : Set E}
    (hyZ : ∀ τ : SingularSimplex E b, IsSubordinate Zᶜ τ → y (chainGenerator ℚ E b τ) = 0)
    {UB : Set B} (hUB : p ⁻¹' UB ⊆ Zᶜ)
    {c : singularChainGroup ℚ B (a+b)} (hc : c ∈ subChainSubmodule ℚ B UB (a+b)) :
    Yco V y hfin ((degreeEquiv p hp V b).symm (cap p hp V a b φ c)) = 0 := by
  refine subChainSubmodule_induction (S := UB)
    (p := fun x => Yco V y hfin ((degreeEquiv p hp V b).symm (cap p hp V a b φ x)) = 0)
    ?_ ?_ ?_ ?_ hc
  · intro σ hσ
    rw [cap_generator, capSimplex_lift p hp V a b φ (chosenLift p hp (a+b) σ), Yco_generator,
      Ysimp_apply]
    apply Finset.sum_eq_zero
    intro g _
    have h1 : IsSubordinate (p ⁻¹' UB) (chosenLift p hp (a+b) σ).val := by
      rw [← isSubordinate_projection_iff]
      rw [(chosenLift p hp (a+b) σ).property]
      exact hσ
    have h2 : IsSubordinate (p ⁻¹' UB) (backSimplex E a b (chosenLift p hp (a+b) σ).val) :=
      isSubordinate_back E a b _ h1
    have h3 : IsSubordinate (p ⁻¹' UB)
        (g • backSimplex E a b (chosenLift p hp (a+b) σ).val) := by
      refine isSubordinate_smul' g ?_ _ h2
      intro x hx
      change p (g • x) ∈ UB
      rw [hp.map_smul]
      exact hx
    rw [hyZ _ (h3.mono hUB), zero_smul]
  · simp
  · intro x y hx hy
    rw [map_add, map_add, map_add, hx, hy, add_zero]
  · intro r x hx
    rw [map_smul, map_smul, map_smul, hx, smul_zero]

/-- The translate-sum pairing of the cap of a boundary vanishes for a cocycle. -/
theorem Yco_cap_boundary (a b : ℕ) (φ : VertexCochain p hp V a)
    (hφ : differential p hp V a φ = 0)
    (y : singularChainGroup ℚ E b →ₗ[ℚ] ℚ)
    (hy : ∀ e, y ((singularBoundary ℚ E b).hom e) = 0)
    (hfin : ∀ τ : SingularSimplex E b, {g : G | y (chainGenerator ℚ E b (g • τ)) ≠ 0}.Finite)
    (u : singularChainGroup ℚ B (a+b+1)) :
    Yco V y hfin ((degreeEquiv p hp V b).symm
      (cap p hp V a b φ ((singularBoundary ℚ B (a+b)).hom u))) = 0 := by
  rw [cap_leibniz, hφ]
  have h0 : cap p hp V (a+1) b (0 : VertexCochain p hp V (a+1)) (scalarCastLeft B a b u) = 0 := by
    have : cap p hp V (a+1) b (0 : VertexCochain p hp V (a+1)) = 0 := by
      apply scalarChain_ext
      intro σ
      rw [cap_generator]
      simp
    rw [this]; rfl
  rw [h0, zero_add, map_zsmul]
  have hb := LinearMap.congr_fun (degreeEquiv_symm_boundary p hp V b)
    (cap p hp V a (b+1) φ u)
  change (degreeEquiv p hp V b).symm (boundary p hp V b _) =
    (coinvariantChains G E V).d (b+1) b ((degreeEquiv p hp V (b+1)).symm _) at hb
  rw [hb, map_zsmul, Yco_d V y hfin hy, smul_zero]

/-- Chains of a subspace whose image under the inclusion is subordinate to `S` are subordinate to the
preimage of `S`. -/
theorem mem_sub_of_inclusion_mem {B : TopCat.{0}} (U S : Set B) (n : ℕ)
    (x : singularChainGroup ℚ (TopCat.of U) n)
    (hx : (singularChainMap ℚ (sInclusion U) n).hom x ∈ subChainSubmodule ℚ B S n) :
    x ∈ subChainSubmodule ℚ (TopCat.of U) (Subtype.val ⁻¹' S) n := by
  have hnat : ∀ z : singularChainGroup ℚ (TopCat.of U) n,
      (singularChainMap ℚ (sInclusion U) n).hom ((projSub (Subtype.val ⁻¹' S) n).hom z) =
        (projSub S n).hom ((singularChainMap ℚ (sInclusion U) n).hom z) := by
    intro z
    have : (singularChainMap ℚ (sInclusion U) n).hom ∘ₗ (projSub (Subtype.val ⁻¹' S) n).hom =
        (projSub S n).hom ∘ₗ (singularChainMap ℚ (sInclusion U) n).hom := by
      apply chainDesc_ext
      intro σ
      simp only [LinearMap.comp_apply, projSub_generator, singularChainMap_generator]
      have hiff : IsSubordinate S (pushSimplex (sInclusion U) n σ) ↔
          IsSubordinate (Subtype.val ⁻¹' S) σ := isSubordinate_pushSimplex_iff _ _ _
      by_cases h : IsSubordinate (Subtype.val ⁻¹' S) σ
      · rw [ite_eq_left h, ite_eq_left (hiff.mpr h), singularChainMap_generator]
      · rw [ite_eq_right h, ite_eq_right (fun h' => h (hiff.mp h')), map_zero]
    exact LinearMap.congr_fun this z
  have h1 : (singularChainMap ℚ (sInclusion U) n).hom ((projSub (Subtype.val ⁻¹' S) n).hom x) =
      (singularChainMap ℚ (sInclusion U) n).hom x := by
    rw [hnat, projSub_of_mem S n hx]
  have hinj : Function.Injective (singularChainMap ℚ (sInclusion U) n).hom :=
    singularChainMap_injective_of_pushSimplex_injective _ _ (pushSimplex_sInclusion_injective U n)
  have h2 := hinj h1
  rw [← h2]
  exact projSub_mem _ _ _

/-- **Localization of the translate-sum pairing.**  Let `UT, UA, UB` be an open cover of the base,
`y` a scalar cocycle of `E` that vanishes (together with all its translates) on the preimage of `UB`,
and `s` a section of `E` over `UT`.  For a relative chain `c` (`∂c` over `UA`) there is a chain `cY` of
`UT`, whose boundary splits into a part over `UA` and a part over `UB`, such that for every
representation `V` and every cocycle `φ` vanishing on `UA`-simplices the pairing `Yco` of the cap of
`φ` with `c` equals the pairing of the cap of the section-lifted chain `s_* cY`.  The chain `cY` depends
only on `c` and the cover. -/
theorem localize_pairing
    (UT UA UB : Set B) (hUT : IsOpen UT) (hUA : IsOpen UA) (hUB : IsOpen UB)
    (hcov : UT ∪ UA ∪ UB = Set.univ)
    (y : singularChainGroup ℚ E 3 →ₗ[ℚ] ℚ) (hy : ∀ e, y ((singularBoundary ℚ E 3).hom e) = 0)
    (hfin : ∀ τ : SingularSimplex E 3, {g : G | y (chainGenerator ℚ E 3 (g • τ)) ≠ 0}.Finite)
    {Z : Set E}
    (hyZ : ∀ τ : SingularSimplex E 3, IsSubordinate Zᶜ τ → y (chainGenerator ℚ E 3 τ) = 0)
    (hUBZ : p ⁻¹' UB ⊆ Zᶜ)
    (c : singularChainGroup ℚ B 5) (hc : (singularBoundary ℚ B 4).hom c ∈ subChainSubmodule ℚ B UA 4)
    (s : TopCat.of UT ⟶ E) (hs : s ≫ p = sInclusion UT) :
    ∃ cY : singularChainGroup ℚ (TopCat.of UT) 5,
      (∃ aY ∈ subChainSubmodule ℚ (TopCat.of UT) (Subtype.val ⁻¹' UA) 4,
       ∃ bY ∈ subChainSubmodule ℚ (TopCat.of UT) (Subtype.val ⁻¹' UB) 4,
        (singularBoundary ℚ (TopCat.of UT) 4).hom cY = aY + bY) ∧
      ∀ (V : Rep.{0} ℚ G) (φ : VertexCochain p hp V 2) (_ : differential p hp V 2 φ = 0)
        (_ : ∀ σ : SingularSimplex B 2, IsSubordinate UA σ → φ σ = 0),
      Yco V y hfin ((degreeEquiv p hp V 3).symm (cap p hp V 2 3 φ c)) =
        Yco V y hfin (capE V 2 3 (vertexToFunction p hp φ) ((singularChainMap ℚ s 5).hom cY)) := by
  obtain ⟨cT, hcT, cA, hcA, cB, hcB, u, hcd, a', ha', b', hb', hdcT⟩ :=
    localize_chain UT UA UB hUT hUA hUB hcov 4 c hc
  obtain ⟨cY, hcY⟩ := (subChainCorestrict_bijective (R := ℚ) UT 5).2 ⟨cT, hcT⟩
  have hcY' : (singularChainMap ℚ (sInclusion UT) 5).hom cY = cT := congrArg Subtype.val hcY
  have ha'T : a' ∈ subChainSubmodule ℚ B UT 4 :=
    subChainSubmodule_mono Set.inter_subset_left 4 ha'
  have hb'T : b' ∈ subChainSubmodule ℚ B UT 4 :=
    subChainSubmodule_mono Set.inter_subset_left 4 hb'
  have ha'A : a' ∈ subChainSubmodule ℚ B UA 4 :=
    subChainSubmodule_mono Set.inter_subset_right 4 ha'
  have hb'B : b' ∈ subChainSubmodule ℚ B UB 4 :=
    subChainSubmodule_mono Set.inter_subset_right 4 hb'
  obtain ⟨aY, haY⟩ := (subChainCorestrict_bijective (R := ℚ) UT 4).2 ⟨a', ha'T⟩
  obtain ⟨bY, hbY⟩ := (subChainCorestrict_bijective (R := ℚ) UT 4).2 ⟨b', hb'T⟩
  have haY' : (singularChainMap ℚ (sInclusion UT) 4).hom aY = a' := congrArg Subtype.val haY
  have hbY' : (singularChainMap ℚ (sInclusion UT) 4).hom bY = b' := congrArg Subtype.val hbY
  have hinj : Function.Injective (singularChainMap ℚ (sInclusion UT) 4).hom :=
    singularChainMap_injective_of_pushSimplex_injective _ _ (pushSimplex_sInclusion_injective UT 4)
  have hbd : (singularBoundary ℚ (TopCat.of UT) 4).hom cY = aY + bY := by
    apply hinj
    have h1 := singularChainMap_boundary_apply ℚ (sInclusion UT) 4 cY
    rw [map_add, haY', hbY', ← hdcT, ← hcY']
    exact h1.symm
  have hmA : aY ∈ subChainSubmodule ℚ (TopCat.of UT) (Subtype.val ⁻¹' UA) 4 :=
    mem_sub_of_inclusion_mem UT UA 4 aY (by rw [haY']; exact ha'A)
  have hmB : bY ∈ subChainSubmodule ℚ (TopCat.of UT) (Subtype.val ⁻¹' UB) 4 :=
    mem_sub_of_inclusion_mem UT UB 4 bY (by rw [hbY']; exact hb'B)
  refine ⟨cY, ⟨aY, hmA, bY, hmB, hbd⟩, ?_⟩
  intro V φ hφd hφA
  have hcap : (degreeEquiv p hp V 3).symm (cap p hp V 2 3 φ c) =
      (degreeEquiv p hp V 3).symm (cap p hp V 2 3 φ cT) +
      (degreeEquiv p hp V 3).symm (cap p hp V 2 3 φ cA) +
      (degreeEquiv p hp V 3).symm (cap p hp V 2 3 φ cB) +
      (degreeEquiv p hp V 3).symm (cap p hp V 2 3 φ ((singularBoundary ℚ B 5).hom u)) := by
    rw [hcd]
    simp only [map_add]
  have hA0 : cap p hp V 2 3 φ cA = 0 := cap_eq_zero_of_front p hp V 2 3 φ hφA hcA
  have hB0 := Yco_cap_eq_zero_of_back p hp V 2 3 φ y hfin hyZ hUBZ hcB
  have hu0 := Yco_cap_boundary p hp V 2 3 φ hφd y hy hfin u
  have hT := capE_pushforward p hp V s (sInclusion UT) hs 2 3 φ cY
  have hT' : capE V 2 3 (vertexToFunction p hp φ) ((singularChainMap ℚ s 5).hom cY) =
      (degreeEquiv p hp V 3).symm (cap p hp V 2 3 φ cT) := by
    rw [← hcY']; exact hT
  rw [hcap, map_add, map_add, map_add, hA0, map_zero, map_zero, hB0, hu0, hT']
  simp

end Cap

section Section

variable {G : Type} [Group G] {E : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (V : Rep.{0} ℚ G)

/-- **The pairing on a chain of a section domain.**  If all translates `g ≠ 1` of the pushed-forward
back faces are killed by `y`, the translate-sum pairing of the cap of `s_* c` is the plain pairing
`y ∘ (φ ∩ -)` of the pulled-back cochains on `Y`. -/
theorem Yco_capE_pushforward {Y : TopCat.{0}} (s : Y ⟶ E) (x : SingularSimplex E 2 → V)
    (y : singularChainGroup ℚ E 3 →ₗ[ℚ] ℚ)
    (hfin : ∀ τ : SingularSimplex E 3, {g : G | y (chainGenerator ℚ E 3 (g • τ)) ≠ 0}.Finite)
    (hone : ∀ (ρ : SingularSimplex Y 3) (g : G), g ≠ 1 →
      y (chainGenerator ℚ E 3 (g • pushSimplex s 3 ρ)) = 0)
    (c : singularChainGroup ℚ Y 5) :
    Yco V y hfin (capE V 2 3 x ((singularChainMap ℚ s 5).hom c)) =
      capPairF Y (ModuleCat.of ℚ V) 2 3 (y.comp (singularChainMap ℚ s 3).hom)
        (chainDesc fun σ => x (pushSimplex s 2 σ)) c := by
  have h : (Yco V y hfin).comp ((capE V 2 3 x).comp (singularChainMap ℚ s 5).hom) =
      capPairF Y (ModuleCat.of ℚ V) 2 3 (y.comp (singularChainMap ℚ s 3).hom)
        (chainDesc fun σ => x (pushSimplex s 2 σ)) := by
    apply chainDesc_ext
    intro σ
    rw [LinearMap.comp_apply, LinearMap.comp_apply, singularChainMap_generator]
    erw [capE_generator V 2 3 x (pushSimplex s 5 σ)]
    rw [Yco_generator]
    erw [capPairF_generator]
    rw [chainDesc_generator]
    have hb : backSimplex E 2 3 (pushSimplex s 5 σ) = pushSimplex s 3 (backSimplex Y 2 3 σ) :=
      (backSimplex_naturality s 2 3 σ).symm
    have hf : frontSimplex E 2 3 (pushSimplex s 5 σ) = pushSimplex s 2 (frontSimplex Y 2 3 σ) :=
      (frontSimplex_naturality s 2 3 σ).symm
    rw [hb, hf]
    rw [Ysimp_apply_of_superset V y hfin _ {1}]
    · simp [singularChainMap_generator]
    · intro g hg
      by_contra hne
      exact hg (hone _ g (by simpa using hne))
  exact LinearMap.congr_fun h c

end Section

section Relative

theorem subChainSubmodule_empty {X : TopCat.{0}} (n : ℕ) :
    subChainSubmodule ℚ X (∅ : Set X) n = ⊥ := by
  unfold subChainSubmodule
  rw [Submodule.span_eq_bot]
  rintro _ ⟨σ, hσ, rfl⟩
  exfalso
  have : Set.range (mvSimplexMap σ) ⊆ (∅ : Set X) := hσ
  have h0 : (Set.range (mvSimplexMap σ)).Nonempty := by
    obtain ⟨x⟩ : Nonempty (Delta n) := inferInstance
    exact ⟨_, x, rfl⟩
  obtain ⟨z, hz⟩ := h0
  exact (this hz)

theorem singularChainMap_mem_sub {X Y : TopCat.{0}} (f : X ⟶ Y) (S : Set Y) (n : ℕ)
    {c : singularChainGroup ℚ X n} (hc : c ∈ subChainSubmodule ℚ X (f ⁻¹' S) n) :
    (singularChainMap ℚ f n).hom c ∈ subChainSubmodule ℚ Y S n := by
  refine subChainSubmodule_induction (S := f ⁻¹' S)
    (p := fun x => (singularChainMap ℚ f n).hom x ∈ subChainSubmodule ℚ Y S n) ?_ ?_ ?_ ?_ hc
  · intro σ hσ
    rw [singularChainMap_generator]
    exact chainGenerator_mem_subChainSubmodule ((isSubordinate_pushSimplex_iff f S σ).mpr hσ)
  · simp
  · intro x y hx hy
    rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro r x hx
    rw [map_smul]; exact Submodule.smul_mem _ r hx

/-- **Localization of a relative 2-chain** (not necessarily a cycle): a chain `F` of `T ∪ A` whose
boundary lies over `A` is, up to a boundary, the sum of a chain `FT` over `T` (with boundary over
`T ∩ A`) and a chain over `A`. -/
theorem localize_relative_chain {X : TopCat.{0}} (T A : Set X) (hT : IsOpen T) (hA : IsOpen A)
    (F : singularChainGroup ℚ X 2) (hF : F ∈ subChainSubmodule ℚ X (T ∪ A) 2)
    (hFA : (singularBoundary ℚ X 1).hom F ∈ subChainSubmodule ℚ X A 1) :
    ∃ FT ∈ subChainSubmodule ℚ X T 2, ∃ FA ∈ subChainSubmodule ℚ X A 2,
      ∃ u : singularChainGroup ℚ X 3, F = FT + FA + (singularBoundary ℚ X 2).hom u ∧
        (singularBoundary ℚ X 1).hom FT ∈ subChainSubmodule ℚ X (T ∩ A) 1 := by
  set U : Set X := T ∪ A with hU
  let ι := sInclusion U
  obtain ⟨F', hF'⟩ := (subChainCorestrict_bijective (R := ℚ) U 2).2 ⟨F, hF⟩
  have hF'' : (singularChainMap ℚ ι 2).hom F' = F := congrArg Subtype.val hF'
  have hbd : (singularChainMap ℚ ι 1).hom ((singularBoundary ℚ (TopCat.of U) 1).hom F') =
      (singularBoundary ℚ X 1).hom F := by
    rw [← hF'']
    exact (singularChainMap_boundary_apply ℚ ι 1 F').symm
  have hFA' : (singularBoundary ℚ (TopCat.of U) 1).hom F' ∈
      subChainSubmodule ℚ (TopCat.of U) (Subtype.val ⁻¹' A) 1 :=
    mem_sub_of_inclusion_mem U A 1 _ (by rw [hbd]; exact hFA)
  obtain ⟨cT, hcT, cA, hcA, cB, hcB, u, hcd, a', ha', b', hb', hdcT⟩ :=
    localize_chain (X := TopCat.of U) (Subtype.val ⁻¹' T) (Subtype.val ⁻¹' A) ∅
      (hT.preimage continuous_subtype_val) (hA.preimage continuous_subtype_val) isOpen_empty
      (by ext x; simp only [Set.mem_union, Set.mem_preimage, Set.mem_empty_iff_false, or_false,
            Set.mem_univ, iff_true]; exact x.2) 1 F' hFA'
  have hcB0 : cB = 0 := by
    have : cB ∈ (⊥ : Submodule ℚ (singularChainGroup ℚ (TopCat.of U) (1+1))) := by
      rw [← subChainSubmodule_empty (X := TopCat.of U) (1+1)]; exact hcB
    simpa using this
  have hb0 : b' = 0 := by
    have : b' ∈ (⊥ : Submodule ℚ (singularChainGroup ℚ (TopCat.of U) 1)) := by
      rw [← subChainSubmodule_empty (X := TopCat.of U) 1]
      exact subChainSubmodule_mono (by simp) 1 hb'
    simpa using this
  refine ⟨(singularChainMap ℚ ι 2).hom cT, singularChainMap_mem_sub ι T 2 hcT,
    (singularChainMap ℚ ι 2).hom cA, singularChainMap_mem_sub ι A 2 hcA,
    (singularChainMap ℚ ι 3).hom u, ?_, ?_⟩
  · rw [← hF'', hcd, hcB0, map_add, map_add, map_add, map_zero, add_zero]
    have := singularChainMap_boundary_apply ℚ ι 2 u
    rw [this]
  · have h2 : (singularBoundary ℚ X 1).hom ((singularChainMap ℚ ι 2).hom cT) =
        (singularChainMap ℚ ι 1).hom ((singularBoundary ℚ (TopCat.of U) 1).hom cT) :=
      singularChainMap_boundary_apply ℚ ι 1 cT
    rw [h2, hdcT, hb0, add_zero]
    exact singularChainMap_mem_sub ι (T ∩ A) 1 ha'

end Relative

end TernaryPeriodPolynomials.Argument.Lemma33.Locality
