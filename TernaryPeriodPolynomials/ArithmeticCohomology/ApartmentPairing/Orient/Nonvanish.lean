module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Chains
public import TernaryPeriodPolynomials.Topology.SingularHomology.SmallChainsHomologyInjectivity
public import TernaryPeriodPolynomials.Topology.SingularHomology.SubChainSubspaceBridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Orient.TopCellDegree

@[expose] public section


/-!
# The local class of a positively oriented tetrahedron around the origin is non-zero

`lamPos_ne_zero : lamPos ≠ 0`, hence `dT0_ne_zero : dT0 ≠ 0` (with `dT0_eq_neg_lamPos`), without any
bridge or global input.  The proof is a two-step Mayer–Vietoris (suspension) argument carried out
directly on the explicit tetrahedron `wT = (B₁, A, B₂, B₃)` in the language of `SphereOddDegree`
(`chainGenerator`, `subChainSubmodule`, the small-chain boundary witness):

* `exists_filling_of_relCls_zero`: if the class of `σ_wT` vanished in `H₃(ℝ³, ℝ³ ∖ 0)` then the
  2-cycle `∂σ_wT` would bound a 3-chain `ρ₀` of the punctured space `XT`.
* `two_cover_split`: if `a + b = ∂ρ` with `a, b` supported in the members of an open cover `{A, B}`,
  then `∂a = ∂w` for a chain `w` supported in `A ∩ B` (subdivision of `ρ` by
  `exists_small_boundary_witness`, then `projSub`).
* Level one: `XT` is covered by `UU = XT ∖ (closed negative axis)` and `VV = XT ∖ (closed positive
  axis)`; the vertical axis meets the faces of `wT` at heights `7/5` (face `F0`) and `-1` (face `F1`)
  and misses `F2, F3`, so `∂σ = a + b` with `a` over `UU` and `b = -[F1]` over `VV`.  Hence the
  three edges of `F1` bound a chain `wY` of the band `YT = UU ∩ VV`.
* Level two (`winding_obstruction`): `YT` is covered by `W1`, `W2` (the band minus the east / west
  half-lines).  The functional `epsFun` counting boundary points in `{x₂ > 0}` kills `∂` of chains
  supported in `W1 ∩ W2 ⊆ {x₂ ≠ 0}` (`epsFun_boundary`, by the intermediate value theorem), while
  on `∂(E₂₃ - E₁₃)` it equals `-1` (`eps_edge`).

The exact value of `lamPos` is not computable: `localTopIso` contains the non-canonical
`zeroReducedHomologyIso`, which is only fixed by a dimension count.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.Lemma33.Orient

open CategoryTheory SphereOddDegree SphereOddDegree.AffineBarycentricSubdivision
open TernaryPeriodPolynomials.Argument.Lemma33.Locality TernaryPoly.RationalSphere

variable {Y : TopCat.{0}}

/-- **Mayer–Vietoris splitting.**  If `a + b = ∂ρ` with `a` supported in `A` and `b` in `B` (an open
cover), then `∂a` is the boundary of a chain supported in `A ∩ B`. -/
theorem two_cover_split (A B : Set Y) (hA : IsOpen A) (hB : IsOpen B) (hcov : A ∪ B = Set.univ)
    (m : ℕ) (a b : singularChainGroup ℚ Y (m + 1)) (ha : a ∈ subChainSubmodule ℚ Y A (m + 1))
    (hb : b ∈ subChainSubmodule ℚ Y B (m + 1)) (ρ : singularChainGroup ℚ Y (m + 2))
    (hρ : (singularBoundary ℚ Y (m + 1)).hom ρ = a + b) :
    ∃ w ∈ subChainSubmodule ℚ Y (A ∩ B) (m + 1),
      (singularBoundary ℚ Y m).hom w = (singularBoundary ℚ Y m).hom a := by
  have hcov3 : A ∪ B ∪ B = Set.univ := by rw [Set.union_assoc, Set.union_self]; exact hcov
  set 𝒰 := threeCover A B B hA hB hB hcov3 with h𝒰
  have hAm : A ∈ 𝒰.sets := by simp [h𝒰, threeCover]
  have hBm : B ∈ 𝒰.sets := by simp [h𝒰, threeCover]
  have hsmall : (singularBoundary ℚ Y (m + 1)).hom ρ ∈ smallChainSubmodule ℚ Y 𝒰 (m + 1) := by
    rw [hρ]
    exact Submodule.add_mem _ (subChainSubmodule_le_smallChainSubmodule hAm _ ha)
      (subChainSubmodule_le_smallChainSubmodule hBm _ hb)
  obtain ⟨ρ', hρ's, hρ'⟩ := exists_small_boundary_witness 𝒰 ℚ (m + 1) ρ hsmall
  obtain ⟨tt, htt, aa, haa, bb, hbb, hdec⟩ :=
    small_threeCover_decomp A B B hA hB hB hcov3 (m + 2) hρ's
  have hd : (singularBoundary ℚ Y (m + 1)).hom ρ' = a + b := hρ'.trans hρ
  have hBsum : aa + bb ∈ subChainSubmodule ℚ Y B (m + 2) := Submodule.add_mem _ haa hbb
  set w := a - (singularBoundary ℚ Y (m + 1)).hom tt with hw
  have hwA : w ∈ subChainSubmodule ℚ Y A (m + 1) :=
    Submodule.sub_mem _ ha (singularBoundary_maps_subChainSubmodule (m + 1) tt htt)
  have hwB : w ∈ subChainSubmodule ℚ Y B (m + 1) := by
    have : w = (singularBoundary ℚ Y (m + 1)).hom (aa + bb) - b := by
      have h2 := congrArg (fun r => (singularBoundary ℚ Y (m + 1)).hom r) hdec
      simp only [map_add] at h2
      rw [hw, map_add]
      have h3 : a + b = (singularBoundary ℚ Y (m + 1)).hom tt +
          ((singularBoundary ℚ Y (m + 1)).hom aa + (singularBoundary ℚ Y (m + 1)).hom bb) := by
        rw [← hd, h2, add_assoc]
      exact sub_eq_sub_iff_add_eq_add.mpr (by rw [h3]; abel)
    rw [this]
    exact Submodule.sub_mem _ (singularBoundary_maps_subChainSubmodule (m + 1) _ hBsum) hb
  refine ⟨w, ?_, ?_⟩
  · have e1 : (projSub A (m + 1)).hom w = w := projSub_of_mem A _ hwA
    have e2 : (projSub B (m + 1)).hom w = w := projSub_of_mem B _ hwB
    have e3 : (projSub (A ∩ B) (m + 1)).hom w = w := by
      rw [← projSub_projSub, e2, e1]
    rw [← e3]
    exact projSub_mem _ _ _
  · rw [hw, map_sub, singularBoundary_boundary_zero, sub_zero]



/-- The point of a singular `0`-simplex. -/
def pt0 (σ : singularSimplices Y 0) : Y :=
  singularSimplexAsContinuousMap Y 0 σ (Convexity.StdSimplex.single 0)

/-- The functional counting (with coefficients) the points of `P`. -/
def epsFun (P : Set Y) : singularChainGroup ℚ Y 0 ⟶ ModuleCat.of ℚ ℚ :=
  Limits.Sigma.desc fun σ : singularSimplices Y 0 =>
    ModuleCat.ofHom (if pt0 σ ∈ P then LinearMap.id else 0)

theorem epsFun_generator (P : Set Y) (σ : singularSimplices Y 0) :
    (epsFun P).hom (chainGenerator ℚ Y 0 σ) = if pt0 σ ∈ P then 1 else 0 := by
  have h := Limits.Sigma.ι_comp_desc (fun σ : singularSimplices Y 0 =>
    ModuleCat.ofHom (if pt0 σ ∈ P then LinearMap.id else 0 : ℚ →ₗ[ℚ] ℚ)) σ
  have h2 := congrArg (fun f => f.hom (1 : ℚ)) h
  change (epsFun P).hom (chainGenerator ℚ Y 0 σ) = _ at h2
  by_cases hP : pt0 σ ∈ P
  · simp [hP] at h2 ⊢; exact h2
  · simp [hP] at h2 ⊢; exact h2


theorem pt0_faceSimplex (τ : singularSimplices Y 1) (i : Fin 2) :
    pt0 (AlexanderWhitney.faceSimplex Y 0 i τ) =
      singularSimplexAsContinuousMap Y 1 τ (Convexity.StdSimplex.single (i.succAbove 0)) := by
  have : pt0 (AlexanderWhitney.faceSimplex Y 0 i τ) =
      singularSimplexAsContinuousMap Y 1 τ (Convexity.StdSimplex.map i.succAbove (Convexity.StdSimplex.single 0)) := rfl
  rw [this, Convexity.StdSimplex.map_single]

theorem epsFun_boundary_generator (P S : Set Y)
    (hP : ∀ τ : singularSimplices Y 1, IsSubordinate S τ →
      (singularSimplexAsContinuousMap Y 1 τ (Convexity.StdSimplex.single 0) ∈ P ↔
        singularSimplexAsContinuousMap Y 1 τ (Convexity.StdSimplex.single 1) ∈ P))
    (τ : singularSimplices Y 1) (hτ : IsSubordinate S τ) :
    (epsFun P).hom ((singularBoundary ℚ Y 0).hom (chainGenerator ℚ Y 1 τ)) = 0 := by
  rw [singularBoundary_chainGenerator_formula, Fin.sum_univ_two, map_add, map_smul, map_smul,
    epsFun_generator, epsFun_generator, pt0_faceSimplex, pt0_faceSimplex]
  have h0 : (Fin.succAbove (0 : Fin 2) 0 : Fin 2) = 1 := rfl
  have h1 : (Fin.succAbove (1 : Fin 2) 0 : Fin 2) = 0 := rfl
  rw [h0, h1]
  have := hP τ hτ
  by_cases h : singularSimplexAsContinuousMap Y 1 τ (Convexity.StdSimplex.single 0) ∈ P
  · have h' := this.mp h
    simp [h, h']
  · have h' : singularSimplexAsContinuousMap Y 1 τ (Convexity.StdSimplex.single 1) ∉ P := fun h'' => h (this.mpr h'')
    simp [h, h']

theorem epsFun_boundary (P S : Set Y)
    (hP : ∀ τ : singularSimplices Y 1, IsSubordinate S τ →
      (singularSimplexAsContinuousMap Y 1 τ (Convexity.StdSimplex.single 0) ∈ P ↔
        singularSimplexAsContinuousMap Y 1 τ (Convexity.StdSimplex.single 1) ∈ P))
    {t : singularChainGroup ℚ Y 1} (ht : t ∈ subChainSubmodule ℚ Y S 1) :
    (epsFun P).hom ((singularBoundary ℚ Y 0).hom t) = 0 := by
  refine subChainSubmodule_induction (p := fun t => (epsFun P).hom ((singularBoundary ℚ Y 0).hom t) = 0)
    ?_ ?_ ?_ ?_ ht
  · intro σ hσ
    exact epsFun_boundary_generator P S hP σ hσ
  · simp
  · intro x y hx hy
    simp [hx, hy]
  · intro a x hx
    simp [hx]


instance : PreconnectedSpace (Delta 1) := inferInstance

/-- Endpoints of a simplex avoiding `{c = 0}` have the same sign of `c`. -/
theorem sign_const (c : Y → ℝ) (hc : Continuous c) (S : Set Y) (hS : ∀ y ∈ S, c y ≠ 0)
    (τ : singularSimplices Y 1) (hτ : IsSubordinate S τ) :
    singularSimplexAsContinuousMap Y 1 τ (Convexity.StdSimplex.single 0) ∈ {y | 0 < c y} ↔
      singularSimplexAsContinuousMap Y 1 τ (Convexity.StdSimplex.single 1) ∈ {y | 0 < c y} := by
  set f : Delta 1 → ℝ := fun t => c (singularSimplexAsContinuousMap Y 1 τ t) with hf
  have hfc : Continuous f := hc.comp (singularSimplexAsContinuousMap Y 1 τ).continuous
  have hne : ∀ t, f t ≠ 0 := fun t => hS _ (hτ ⟨t, rfl⟩)
  set a : Delta 1 := Convexity.StdSimplex.single 0
  set b : Delta 1 := Convexity.StdSimplex.single 1
  show 0 < f a ↔ 0 < f b
  constructor
  · intro ha
    by_contra hb
    have hb' : f b ≤ 0 := not_lt.mp hb
    obtain ⟨t, ht⟩ := intermediate_value_univ b a hfc ⟨hb', ha.le⟩
    exact hne t ht
  · intro hb
    by_contra ha
    have ha' : f a ≤ 0 := not_lt.mp ha
    obtain ⟨t, ht⟩ := intermediate_value_univ a b hfc ⟨ha', hb.le⟩
    exact hne t ht


/-- **Second level of the suspension argument.** If two open sets `W₁, W₂` cover `Y`, the overlap
avoids `{c = 0}` for a continuous `c`, and `c₁ + c₂` bounds with `c_i` supported in `W_i`, then the
algebraic count of the boundary points of `c₁` in `{c > 0}` vanishes. -/
theorem winding_obstruction (W₁ W₂ : Set Y) (h₁ : IsOpen W₁) (h₂ : IsOpen W₂)
    (hcov : W₁ ∪ W₂ = Set.univ) (c : Y → ℝ) (hc : Continuous c)
    (hW : ∀ y ∈ W₁ ∩ W₂, c y ≠ 0) (c₁ c₂ : singularChainGroup ℚ Y 1)
    (hc₁ : c₁ ∈ subChainSubmodule ℚ Y W₁ 1) (hc₂ : c₂ ∈ subChainSubmodule ℚ Y W₂ 1)
    (ρ : singularChainGroup ℚ Y 2) (hρ : (singularBoundary ℚ Y 1).hom ρ = c₁ + c₂) :
    (epsFun {y | 0 < c y}).hom ((singularBoundary ℚ Y 0).hom c₁) = 0 := by
  obtain ⟨w, hw, hdw⟩ := two_cover_split W₁ W₂ h₁ h₂ hcov 0 c₁ c₂ hc₁ hc₂ ρ hρ
  rw [← hdw]
  exact epsFun_boundary _ _ (sign_const c hc _ hW) hw


/-! ### Affine simplices of Euclidean space in the language of `SphereOddDegree` -/

/-- Euclidean space as a bundled space. -/
abbrev ET : TopCat.{0} := TopCat.of E3

/-- The affine map from the standard `n`-simplex with the given vertices. -/
def affN (n : ℕ) (w : Fin (n + 1) → E3) : C(Delta n, ET) where
  toFun t := ∑ k, t.weights k • w k
  continuous_toFun := by
    refine continuous_finsetSum _ (fun i _ => ?_)
    exact (Convexity.StdSimplex.continuous_weights_apply ℝ i).smul continuous_const

/-- The affine singular simplex. -/
def affSimp (n : ℕ) (w : Fin (n + 1) → E3) : singularSimplices ET n :=
  continuousMapAsSingularSimplex ET n (affN n w)

theorem affSimp_map (n : ℕ) (w : Fin (n + 1) → E3) :
    singularSimplexAsContinuousMap ET n (affSimp n w) = affN n w :=
  Equiv.apply_symm_apply _ _

theorem sum_stdSimplex_map_E {m n : ℕ} (g : Fin (m + 1) → Fin (n + 1))
    (z : Convexity.StdSimplex ℝ (Fin (m + 1))) (p : Fin (n + 1) → E3) :
    ∑ i, (Convexity.StdSimplex.map g z).weights i • p i =
      ∑ k, z.weights k • p (g k) := by
  classical
  have h : ∀ i, (Convexity.StdSimplex.map g z).weights i =
      ∑ k with g k = i, z.weights k := by
    intro i
    rw [Convexity.StdSimplex.weights_map, Finsupp.mapDomain_fintype, Finsupp.coe_finsetSum,
      Finset.sum_apply, Finset.sum_filter]
    exact Finset.sum_congr rfl fun k _ => Finsupp.single_apply
  simp_rw [h, Finset.sum_smul]
  rw [← Finset.sum_fiberwise Finset.univ g (fun k => z.weights k • p (g k))]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k hk => ?_))
  rw [(Finset.mem_filter.mp hk).2]

theorem faceSimplex_affSimp (n : ℕ) (j : Fin (n + 2)) (w : Fin (n + 2) → E3) :
    AlexanderWhitney.faceSimplex ET n j (affSimp (n + 1) w) =
      affSimp n (fun k => w (j.succAbove k)) := by
  apply (ET.toSSetObjEquiv _).injective
  refine ContinuousMap.ext (fun t => ?_)
  have h1 : (ET.toSSetObjEquiv _) (AlexanderWhitney.faceSimplex ET n j (affSimp (n + 1) w)) t =
      singularSimplexAsContinuousMap ET (n + 1) (affSimp (n + 1) w) (Convexity.StdSimplex.map j.succAbove t) := rfl
  rw [h1, affSimp_map]
  change ∑ i, (Convexity.StdSimplex.map j.succAbove t).weights i • w i = _
  rw [sum_stdSimplex_map_E]
  rfl

theorem isSubordinate_affSimp (S : Set ET) (n : ℕ) (w : Fin (n + 1) → E3) :
    IsSubordinate S (affSimp n w) ↔ ∀ t, affN n w t ∈ S := by
  unfold IsSubordinate
  change Set.range (singularSimplexAsContinuousMap ET n (affSimp n w)) ⊆ S ↔ _
  rw [affSimp_map]
  constructor
  · intro h t; exact h ⟨t, rfl⟩
  · rintro h _ ⟨t, rfl⟩; exact h t


/-! ### The covers -/

theorem continuous_coord (i : Fin 3) : Continuous fun x : E3 => x i := by fun_prop

/-- The closed ray `{x₁ = x₂ = 0, x₃ ≤ 0}`. -/
def Rm : Set E3 := {x | x 0 = 0 ∧ x 1 = 0 ∧ x 2 ≤ 0}

/-- The closed ray `{x₁ = x₂ = 0, x₃ ≥ 0}`. -/
def Rp : Set E3 := {x | x 0 = 0 ∧ x 1 = 0 ∧ 0 ≤ x 2}

theorem isClosed_Rm : IsClosed Rm :=
  ((isClosed_eq (continuous_coord 0) continuous_const).inter
    ((isClosed_eq (continuous_coord 1) continuous_const).inter
      (isClosed_le (continuous_coord 2) continuous_const)))

theorem isClosed_Rp : IsClosed Rp :=
  ((isClosed_eq (continuous_coord 0) continuous_const).inter
    ((isClosed_eq (continuous_coord 1) continuous_const).inter
      (isClosed_le continuous_const (continuous_coord 2))))

/-- The punctured space as a bundled space. -/
abbrev XT : TopCat.{0} := TopCat.of (Punctured 3)

/-- The complement of the closed negative axis, in the punctured space. -/
def UU : Set XT := {x | x.1 ∉ Rm}

/-- The complement of the closed positive axis, in the punctured space. -/
def VV : Set XT := {x | x.1 ∉ Rp}

theorem isOpen_UU : IsOpen UU :=
  (isClosed_Rm.isOpen_compl).preimage continuous_subtype_val

theorem isOpen_VV : IsOpen VV :=
  (isClosed_Rp.isOpen_compl).preimage continuous_subtype_val

theorem UU_union_VV : UU ∪ VV = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_contra h
  simp only [Set.mem_union, UU, VV, Set.mem_ofPred_eq, not_or, not_not] at h
  obtain ⟨h1, h2⟩ := h
  apply x.2
  have e0 : x.1 0 = 0 := h1.1
  have e1 : x.1 1 = 0 := h1.2.1
  have e2 : x.1 2 = 0 := le_antisymm h1.2.2 h2.2.2
  ext i
  fin_cases i <;> simp [e0, e1, e2]

/-- The overlap: forms off the vertical axis. -/
def SS : Set XT := UU ∩ VV

/-- The band as a bundled space. -/
abbrev YT : TopCat.{0} := TopCat.of SS

/-- The `x₂`-coordinate on the band. -/
def cY (y : YT) : ℝ := y.1.1 1

theorem continuous_cY : Continuous cY :=
  (continuous_coord 1).comp (continuous_subtype_val.comp continuous_subtype_val)

/-- The band minus the closed east half-line. -/
def W1 : Set YT := {y | ¬(y.1.1 1 = 0 ∧ 0 ≤ y.1.1 0)}

/-- The band minus the closed west half-line. -/
def W2 : Set YT := {y | ¬(y.1.1 1 = 0 ∧ y.1.1 0 ≤ 0)}

theorem isOpen_W1 : IsOpen W1 := by
  have : IsClosed {y : YT | y.1.1 1 = 0 ∧ 0 ≤ y.1.1 0} :=
    (isClosed_eq ((continuous_coord 1).comp (continuous_subtype_val.comp continuous_subtype_val))
      continuous_const).inter
      (isClosed_le continuous_const
        ((continuous_coord 0).comp (continuous_subtype_val.comp continuous_subtype_val)))
  exact this.isOpen_compl

theorem isOpen_W2 : IsOpen W2 := by
  have : IsClosed {y : YT | y.1.1 1 = 0 ∧ y.1.1 0 ≤ 0} :=
    (isClosed_eq ((continuous_coord 1).comp (continuous_subtype_val.comp continuous_subtype_val))
      continuous_const).inter
      (isClosed_le ((continuous_coord 0).comp (continuous_subtype_val.comp continuous_subtype_val))
        continuous_const)
  exact this.isOpen_compl

theorem band_ne (y : YT) : ¬(y.1.1 0 = 0 ∧ y.1.1 1 = 0) := by
  rintro ⟨h0, h1⟩
  have hU := y.2.1
  have hV := y.2.2
  have hne : y.1.1 2 ≠ 0 := by
    intro h2
    apply y.1.2
    ext i
    fin_cases i <;> simp [h0, h1, h2]
  rcases lt_or_gt_of_ne hne with h | h
  · exact hU ⟨h0, h1, h.le⟩
  · exact hV ⟨h0, h1, h.le⟩

theorem W1_union_W2 : W1 ∪ W2 = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  by_contra h
  simp only [Set.mem_union, W1, W2, Set.mem_ofPred_eq, not_or, not_not] at h
  obtain ⟨⟨h1, h2⟩, ⟨_, h4⟩⟩ := h
  exact band_ne y ⟨le_antisymm h4 h2, h1⟩

theorem W_inter_ne : ∀ y ∈ W1 ∩ W2, cY y ≠ 0 := by
  rintro y ⟨h1, h2⟩ h0
  simp only [W1, W2, Set.mem_ofPred_eq, cY] at h1 h2 h0
  rcases lt_trichotomy (y.1.1 0) 0 with h | h | h
  · exact h2 ⟨h0, h.le⟩
  · exact h1 ⟨h0, h.ge⟩
  · exact h1 ⟨h0, h.le⟩


/-! ### The explicit tetrahedron -/

/-- Vertices of the explicit positively oriented tetrahedron `(B₁, A, B₂, B₃)`. -/
def vB1 : E3 := mk3 2 (-1) (-1)
def vA : E3 := mk3 (1 / 4) (1 / 8) 2
def vB2 : E3 := mk3 (-1) 2 (-1)
def vB3 : E3 := mk3 (-1) (-1) (-1)

def wT : Fin (3 + 1) → E3 := ![vB1, vA, vB2, vB3]

/-- The four faces (each omitting one vertex). -/
def F0 : Fin 3 → E3 := ![vA, vB2, vB3]
def F1 : Fin 3 → E3 := ![vB1, vB2, vB3]
def F2 : Fin 3 → E3 := ![vB1, vA, vB3]
def F3 : Fin 3 → E3 := ![vB1, vA, vB2]

theorem face0_eq : (fun k => wT ((0 : Fin 4).succAbove k)) = F0 := by
  funext k; fin_cases k <;> rfl
theorem face1_eq : (fun k => wT ((1 : Fin 4).succAbove k)) = F1 := by
  funext k; fin_cases k <;> rfl
theorem face2_eq : (fun k => wT ((2 : Fin 4).succAbove k)) = F2 := by
  funext k; fin_cases k <;> rfl
theorem face3_eq : (fun k => wT ((3 : Fin 4).succAbove k)) = F3 := by
  funext k; fin_cases k <;> rfl

/-- The edges of the bottom face. -/
def E23 : Fin 2 → E3 := ![vB2, vB3]
def E13 : Fin 2 → E3 := ![vB1, vB3]
def E12 : Fin 2 → E3 := ![vB1, vB2]

theorem edge0_eq : (fun k => F1 ((0 : Fin 3).succAbove k)) = E23 := by
  funext k; fin_cases k <;> rfl
theorem edge1_eq : (fun k => F1 ((1 : Fin 3).succAbove k)) = E13 := by
  funext k; fin_cases k <;> rfl
theorem edge2_eq : (fun k => F1 ((2 : Fin 3).succAbove k)) = E12 := by
  funext k; fin_cases k <;> rfl

theorem affN_coord2 (w : Fin 3 → E3) (t : Delta 2) (i : Fin 3) :
    affN 2 w t i = t.weights 0 * w 0 i + t.weights 1 * w 1 i +
      t.weights 2 * w 2 i := by
  simp [affN, Fin.sum_univ_three]

theorem affN_coord1 (w : Fin 2 → E3) (t : Delta 1) (i : Fin 3) :
    affN 1 w t i = t.weights 0 * w 0 i + t.weights 1 * w 1 i := by
  simp [affN, Fin.sum_univ_two]

theorem delta2_facts (t : Delta 2) :
    t.weights 0 + t.weights 1 + t.weights 2 = 1 ∧ 0 ≤ t.weights 0 ∧
      0 ≤ t.weights 1 ∧ 0 ≤ t.weights 2 := by
  refine ⟨?_, t.weights_nonneg 0, t.weights_nonneg 1, t.weights_nonneg 2⟩
  have h : ∑ k, t.weights k = 1 := t.total_of_fintype
  rw [Fin.sum_univ_three] at h
  exact h

theorem delta1_facts (t : Delta 1) :
    t.weights 0 + t.weights 1 = 1 ∧ 0 ≤ t.weights 0 ∧ 0 ≤ t.weights 1 := by
  refine ⟨?_, t.weights_nonneg 0, t.weights_nonneg 1⟩
  have h : ∑ k, t.weights k = 1 := t.total_of_fintype
  rw [Fin.sum_univ_two] at h
  exact h

theorem ne_zero_of_coords (x : E3) (h : ¬(x 0 = 0 ∧ x 1 = 0)) : x ≠ 0 := by
  rintro rfl
  exact h ⟨rfl, rfl⟩

/-- The top face meets the axis only at height `7/5 > 0`. -/
theorem F0_geom (t : Delta 2) : affN 2 F0 t ≠ 0 ∧ affN 2 F0 t ∉ Rm := by
  obtain ⟨hs, n0, n1, n2⟩ := delta2_facts t
  have h0 : affN 2 F0 t 0 = t.weights 0 * (1/4 : ℝ) + t.weights 1 * (-1 : ℝ) + t.weights 2 * (-1 : ℝ) := by
    rw [affN_coord2]; simp [F0, vA, vB2, vB3, mk3]
  have h1 : affN 2 F0 t 1 = t.weights 0 * (1/8 : ℝ) + t.weights 1 * (2 : ℝ) + t.weights 2 * (-1 : ℝ) := by
    rw [affN_coord2]; simp [F0, vA, vB2, vB3, mk3]
  have h2 : affN 2 F0 t 2 = t.weights 0 * (2 : ℝ) + t.weights 1 * (-1 : ℝ) + t.weights 2 * (-1 : ℝ) := by
    rw [affN_coord2]; simp [F0, vA, vB2, vB3, mk3]
  constructor
  · intro h
    have e0 : affN 2 F0 t 0 = 0 := by rw [h]; rfl
    have e1 : affN 2 F0 t 1 = 0 := by rw [h]; rfl
    have e2 : affN 2 F0 t 2 = 0 := by rw [h]; rfl
    linarith
  · rintro ⟨e0, e1, e2⟩
    linarith

/-- The bottom face meets the axis only at height `-1 < 0`. -/
theorem F1_geom (t : Delta 2) : affN 2 F1 t ≠ 0 ∧ affN 2 F1 t ∉ Rp := by
  obtain ⟨hs, n0, n1, n2⟩ := delta2_facts t
  have h0 : affN 2 F1 t 0 = t.weights 0 * (2 : ℝ) + t.weights 1 * (-1 : ℝ) + t.weights 2 * (-1 : ℝ) := by
    rw [affN_coord2]; simp [F1, vB1, vB2, vB3, mk3]
  have h1 : affN 2 F1 t 1 = t.weights 0 * (-1 : ℝ) + t.weights 1 * (2 : ℝ) + t.weights 2 * (-1 : ℝ) := by
    rw [affN_coord2]; simp [F1, vB1, vB2, vB3, mk3]
  have h2 : affN 2 F1 t 2 = t.weights 0 * (-1 : ℝ) + t.weights 1 * (-1 : ℝ) + t.weights 2 * (-1 : ℝ) := by
    rw [affN_coord2]; simp [F1, vB1, vB2, vB3, mk3]
  constructor
  · intro h
    have e0 : affN 2 F1 t 0 = 0 := by rw [h]; rfl
    have e2 : affN 2 F1 t 2 = 0 := by rw [h]; rfl
    linarith
  · rintro ⟨e0, e1, e2⟩
    linarith

theorem F2_geom (t : Delta 2) : ¬(affN 2 F2 t 0 = 0 ∧ affN 2 F2 t 1 = 0) := by
  obtain ⟨hs, n0, n1, n2⟩ := delta2_facts t
  have h0 : affN 2 F2 t 0 = t.weights 0 * (2 : ℝ) + t.weights 1 * (1/4 : ℝ) + t.weights 2 * (-1 : ℝ) := by
    rw [affN_coord2]; simp [F2, vB1, vA, vB3, mk3]
  have h1 : affN 2 F2 t 1 = t.weights 0 * (-1 : ℝ) + t.weights 1 * (1/8 : ℝ) + t.weights 2 * (-1 : ℝ) := by
    rw [affN_coord2]; simp [F2, vB1, vA, vB3, mk3]
  rintro ⟨e0, e1⟩
  linarith

theorem F3_geom (t : Delta 2) : ¬(affN 2 F3 t 0 = 0 ∧ affN 2 F3 t 1 = 0) := by
  obtain ⟨hs, n0, n1, n2⟩ := delta2_facts t
  have h0 : affN 2 F3 t 0 = t.weights 0 * (2 : ℝ) + t.weights 1 * (1/4 : ℝ) + t.weights 2 * (-1 : ℝ) := by
    rw [affN_coord2]; simp [F3, vB1, vA, vB2, mk3]
  have h1 : affN 2 F3 t 1 = t.weights 0 * (-1 : ℝ) + t.weights 1 * (1/8 : ℝ) + t.weights 2 * (2 : ℝ) := by
    rw [affN_coord2]; simp [F3, vB1, vA, vB2, mk3]
  rintro ⟨e0, e1⟩
  linarith

theorem E23_geom (t : Delta 1) :
    ¬(affN 1 E23 t 0 = 0 ∧ affN 1 E23 t 1 = 0) ∧ ¬(affN 1 E23 t 1 = 0 ∧ 0 ≤ affN 1 E23 t 0) := by
  obtain ⟨hs, n0, n1⟩ := delta1_facts t
  have h0 : affN 1 E23 t 0 = t.weights 0 * (-1 : ℝ) + t.weights 1 * (-1 : ℝ) := by
    rw [affN_coord1]; simp [E23, vB2, vB3, mk3]
  have h1 : affN 1 E23 t 1 = t.weights 0 * (2 : ℝ) + t.weights 1 * (-1 : ℝ) := by
    rw [affN_coord1]; simp [E23, vB2, vB3, mk3]
  constructor
  · rintro ⟨e0, e1⟩; linarith
  · rintro ⟨e1, e0⟩; linarith

theorem E13_geom (t : Delta 1) :
    ¬(affN 1 E13 t 0 = 0 ∧ affN 1 E13 t 1 = 0) ∧ affN 1 E13 t 1 ≠ 0 := by
  obtain ⟨hs, n0, n1⟩ := delta1_facts t
  have h0 : affN 1 E13 t 0 = t.weights 0 * (2 : ℝ) + t.weights 1 * (-1 : ℝ) := by
    rw [affN_coord1]; simp [E13, vB1, vB3, mk3]
  have h1 : affN 1 E13 t 1 = t.weights 0 * (-1 : ℝ) + t.weights 1 * (-1 : ℝ) := by
    rw [affN_coord1]; simp [E13, vB1, vB3, mk3]
  constructor
  · rintro ⟨e0, e1⟩; linarith
  · intro e1; linarith

theorem E12_geom (t : Delta 1) :
    ¬(affN 1 E12 t 0 = 0 ∧ affN 1 E12 t 1 = 0) ∧ ¬(affN 1 E12 t 1 = 0 ∧ affN 1 E12 t 0 ≤ 0) := by
  obtain ⟨hs, n0, n1⟩ := delta1_facts t
  have h0 : affN 1 E12 t 0 = t.weights 0 * (2 : ℝ) + t.weights 1 * (-1 : ℝ) := by
    rw [affN_coord1]; simp [E12, vB1, vB2, mk3]
  have h1 : affN 1 E12 t 1 = t.weights 0 * (-1 : ℝ) + t.weights 1 * (2 : ℝ) := by
    rw [affN_coord1]; simp [E12, vB1, vB2, mk3]
  constructor
  · rintro ⟨e0, e1⟩; linarith
  · rintro ⟨e1, e0⟩; linarith


/-! ### Lifting affine simplices to the punctured space and to the band -/

theorem push_inj (S : Set (Y)) (n : ℕ) : Function.Injective (singularChainMap ℚ (sInclusion S) n).hom :=
  singularChainMap_injective_of_pushSimplex_injective (sInclusion S) n
    (pushSimplex_sInclusion_injective S n)

theorem lift_X (n : ℕ) (w : Fin (n + 1) → E3) (hZ : ∀ t, affN n w t ≠ 0) :
    ∃ τ : singularSimplices XT n, pushSimplex (sInclusion (Punctured 3)) n τ = affSimp n w ∧
      ∀ t, ((singularSimplexAsContinuousMap XT n τ) t).1 = affN n w t := by
  have hs : IsSubordinate (Punctured 3 : Set ET) (affSimp n w) := by
    rw [isSubordinate_affSimp]
    intro t h
    exact hZ t h
  obtain ⟨τ, hτ⟩ := exists_pushSimplex_of_subordinate (X := ET) (Punctured 3) n hs
  refine ⟨τ, hτ, fun t => ?_⟩
  have := congrArg (fun σ => singularSimplexAsContinuousMap ET n σ t) hτ
  simp only [pushSimplex_continuousMap, affSimp_map] at this
  exact this

theorem lift_Y (n : ℕ) (w : Fin (n + 1) → E3) (hB : ∀ t, ¬(affN n w t 0 = 0 ∧ affN n w t 1 = 0)) :
    ∃ υ : singularSimplices YT n, ∃ τ : singularSimplices XT n,
      pushSimplex (sInclusion SS) n υ = τ ∧ pushSimplex (sInclusion (Punctured 3)) n τ = affSimp n w ∧
        ∀ t, ((singularSimplexAsContinuousMap YT n υ) t).1.1 = affN n w t := by
  obtain ⟨τ, hτ, hτt⟩ := lift_X n w (fun t => ne_zero_of_coords _ (hB t))
  have hs : IsSubordinate SS τ := by
    intro x ⟨t, ht⟩
    subst ht
    have hb := hB t
    rw [← hτt t] at hb
    refine ⟨?_, ?_⟩
    · intro h; exact hb ⟨h.1, h.2.1⟩
    · intro h; exact hb ⟨h.1, h.2.1⟩
  obtain ⟨υ, hυ⟩ := exists_pushSimplex_of_subordinate (X := XT) SS n hs
  refine ⟨υ, τ, hυ, hτ, fun t => ?_⟩
  have := congrArg (fun σ => singularSimplexAsContinuousMap XT n σ t) hυ
  simp only [pushSimplex_continuousMap] at this
  rw [← hτt t, ← this]
  rfl


theorem affN_vertex (n : ℕ) (w : Fin (n + 1) → E3) (k : Fin (n + 1)) :
    affN n w (Convexity.StdSimplex.single k) = w k := by
  simp [affN, Finsupp.single_apply]

/-- The count of boundary points in `{x₂ > 0}` of an edge lifted to the band. -/
theorem eps_edge (υ : singularSimplices YT 1) (w : Fin 2 → E3)
    (hυ : ∀ t, ((singularSimplexAsContinuousMap YT 1 υ) t).1.1 = affN 1 w t) :
    (epsFun {y : YT | 0 < cY y}).hom ((singularBoundary ℚ YT 0).hom (chainGenerator ℚ YT 1 υ)) =
      (if 0 < w 1 1 then 1 else 0) - (if 0 < w 0 1 then 1 else 0) := by
  rw [singularBoundary_chainGenerator_formula, Fin.sum_univ_two, map_add, map_smul, map_smul,
    epsFun_generator, epsFun_generator, pt0_faceSimplex, pt0_faceSimplex]
  have h0 : (Fin.succAbove (0 : Fin 2) 0 : Fin 2) = 1 := rfl
  have h1 : (Fin.succAbove (1 : Fin 2) 0 : Fin 2) = 0 := rfl
  rw [h0, h1]
  have c1 : cY (singularSimplexAsContinuousMap YT 1 υ (Convexity.StdSimplex.single 1)) = w 1 1 := by
    unfold cY; rw [hυ, affN_vertex]
  have c0 : cY (singularSimplexAsContinuousMap YT 1 υ (Convexity.StdSimplex.single 0)) = w 0 1 := by
    unfold cY; rw [hυ, affN_vertex]
  simp only [Set.mem_ofPred_eq, c1, c0]
  by_cases a : 0 < w 1 1 <;> by_cases b : 0 < w 0 1 <;> simp [a, b]


theorem tetra_boundary_expand :
    (singularBoundary ℚ ET 2).hom (chainGenerator ℚ ET 3 (affSimp 3 wT)) =
      chainGenerator ℚ ET 2 (affSimp 2 F0) - chainGenerator ℚ ET 2 (affSimp 2 F1) +
        chainGenerator ℚ ET 2 (affSimp 2 F2) - chainGenerator ℚ ET 2 (affSimp 2 F3) := by
  rw [singularBoundary_chainGenerator_formula, Fin.sum_univ_four]
  simp only [faceSimplex_affSimp, face0_eq, face1_eq, face2_eq, face3_eq]
  simp [pow_succ]
  abel

theorem bottom_boundary_expand :
    (singularBoundary ℚ ET 1).hom (chainGenerator ℚ ET 2 (affSimp 2 F1)) =
      chainGenerator ℚ ET 1 (affSimp 1 E23) - chainGenerator ℚ ET 1 (affSimp 1 E13) +
        chainGenerator ℚ ET 1 (affSimp 1 E12) := by
  rw [singularBoundary_chainGenerator_formula, Fin.sum_univ_three]
  simp only [faceSimplex_affSimp, edge0_eq, edge1_eq, edge2_eq]
  simp
  abel


/-- The inclusion of the punctured space. -/
abbrev incX : XT ⟶ ET := sInclusion (X := ET) (Punctured 3)

/-- The inclusion of the band into the punctured space. -/
abbrev incS : YT ⟶ XT := sInclusion (X := XT) SS

/-- **The boundary of the explicit tetrahedron does not bound in the punctured space.** -/
theorem no_filling (ρ : singularChainGroup ℚ XT 3) (zX : singularChainGroup ℚ XT 2)
    (hz : (singularChainMap ℚ incX 2).hom zX =
      (singularBoundary ℚ ET 2).hom (chainGenerator ℚ ET 3 (affSimp 3 wT)))
    (hρ : (singularBoundary ℚ XT 2).hom ρ = zX) : False := by
  obtain ⟨τ0, h0, c0⟩ := lift_X 2 F0 (fun t => (F0_geom t).1)
  obtain ⟨τ1, h1, c1⟩ := lift_X 2 F1 (fun t => (F1_geom t).1)
  obtain ⟨τ2, h2, c2⟩ := lift_X 2 F2 (fun t => ne_zero_of_coords _ (F2_geom t))
  obtain ⟨τ3, h3, c3⟩ := lift_X 2 F3 (fun t => ne_zero_of_coords _ (F3_geom t))
  have push_gen : ∀ (τ : singularSimplices XT 2) (σ : singularSimplices ET 2),
      pushSimplex incX 2 τ = σ →
      (singularChainMap ℚ incX 2).hom (chainGenerator ℚ XT 2 τ) =
        chainGenerator ℚ ET 2 σ := by
    intro τ σ h; rw [singularChainMap_generator, h]
  have hzX : zX = chainGenerator ℚ XT 2 τ0 - chainGenerator ℚ XT 2 τ1 + chainGenerator ℚ XT 2 τ2 -
      chainGenerator ℚ XT 2 τ3 := by
    apply push_inj (Y := ET) (Punctured 3) 2
    rw [hz, tetra_boundary_expand]
    simp only [map_sub, map_add, push_gen _ _ h0, push_gen _ _ h1, push_gen _ _ h2,
      push_gen _ _ h3]
  -- subordination
  have s0 : IsSubordinate UU τ0 := by
    rintro _ ⟨t, rfl⟩
    show (singularSimplexAsContinuousMap XT 2 τ0 t).1 ∉ Rm
    rw [c0]; exact (F0_geom t).2
  have s1 : IsSubordinate VV τ1 := by
    rintro _ ⟨t, rfl⟩
    show (singularSimplexAsContinuousMap XT 2 τ1 t).1 ∉ Rp
    rw [c1]; exact (F1_geom t).2
  have s2 : IsSubordinate UU τ2 := by
    rintro _ ⟨t, rfl⟩
    show (singularSimplexAsContinuousMap XT 2 τ2 t).1 ∉ Rm
    rw [c2]; exact fun h => F2_geom t ⟨h.1, h.2.1⟩
  have s3 : IsSubordinate UU τ3 := by
    rintro _ ⟨t, rfl⟩
    show (singularSimplexAsContinuousMap XT 2 τ3 t).1 ∉ Rm
    rw [c3]; exact fun h => F3_geom t ⟨h.1, h.2.1⟩
  set a := chainGenerator ℚ XT 2 τ0 + chainGenerator ℚ XT 2 τ2 - chainGenerator ℚ XT 2 τ3 with ha_def
  set b := - chainGenerator ℚ XT 2 τ1 with hb_def
  have ha : a ∈ subChainSubmodule ℚ XT UU 2 :=
    Submodule.sub_mem _ (Submodule.add_mem _ (chainGenerator_mem_subChainSubmodule s0)
      (chainGenerator_mem_subChainSubmodule s2)) (chainGenerator_mem_subChainSubmodule s3)
  have hb : b ∈ subChainSubmodule ℚ XT VV 2 :=
    Submodule.neg_mem _ (chainGenerator_mem_subChainSubmodule s1)
  have hab : zX = a + b := by rw [hzX, ha_def, hb_def]; abel
  obtain ⟨w, hw, hdw⟩ := two_cover_split UU VV isOpen_UU isOpen_VV UU_union_VV 1 a b ha hb ρ
    (by rw [hρ, hab])
  have hd0 : (singularBoundary ℚ XT 1).hom zX = 0 := by
    rw [← hρ]; exact singularBoundary_boundary_zero ℚ XT 1 ρ
  have hda : (singularBoundary ℚ XT 1).hom a = (singularBoundary ℚ XT 1).hom (chainGenerator ℚ XT 2 τ1) := by
    rw [hab, map_add, hb_def, map_neg] at hd0
    exact eq_of_sub_eq_zero (by rw [sub_eq_add_neg]; exact hd0)
  -- the three edges of the bottom face, lifted to the band
  obtain ⟨υ0, σ0, p0, q0, d0⟩ := lift_Y 1 E23 (fun t => (E23_geom t).1)
  obtain ⟨υ1, σ1, p1, q1, d1⟩ := lift_Y 1 E13 (fun t => (E13_geom t).1)
  obtain ⟨υ2, σ2, p2, q2, d2⟩ := lift_Y 1 E12 (fun t => (E12_geom t).1)
  have push_gen2 : ∀ (υ : singularSimplices YT 1) (σ : singularSimplices XT 1) (ε : singularSimplices ET 1),
      pushSimplex incS 1 υ = σ → pushSimplex incX 1 σ = ε →
      (singularChainMap ℚ incX 1).hom ((singularChainMap ℚ incS 1).hom (chainGenerator ℚ YT 1 υ)) =
        chainGenerator ℚ ET 1 ε := by
    intro υ σ ε h h'
    rw [singularChainMap_generator, h, singularChainMap_generator, h']
  have push_g1 : (singularChainMap ℚ incX 2).hom (chainGenerator ℚ XT 2 τ1) =
      chainGenerator ℚ ET 2 (affSimp 2 F1) := by
    rw [singularChainMap_generator, h1]
  set aY := (chainGenerator ℚ YT 1 υ0 - chainGenerator ℚ YT 1 υ1) + chainGenerator ℚ YT 1 υ2 with haY_def
  have haY : (singularChainMap ℚ incS 1).hom aY =
      (singularBoundary ℚ XT 1).hom (chainGenerator ℚ XT 2 τ1) := by
    apply push_inj (Y := ET) (Punctured 3) 1
    have e1 : (singularChainMap ℚ incX 1).hom ((singularBoundary ℚ XT 1).hom (chainGenerator ℚ XT 2 τ1)) =
        (singularBoundary ℚ ET 1).hom ((singularChainMap ℚ incX 2).hom (chainGenerator ℚ XT 2 τ1)) :=
      (singularChainMap_boundary_apply ℚ incX 1 _).symm
    rw [e1, push_g1, bottom_boundary_expand, haY_def]
    simp only [map_sub, map_add, push_gen2 _ _ _ p0 q0, push_gen2 _ _ _ p1 q1, push_gen2 _ _ _ p2 q2]
  -- the filling in the band
  have hw' : w ∈ subChainSubmodule ℚ XT SS 2 := hw
  obtain ⟨wY, hwY⟩ : ∃ wY : singularChainGroup ℚ YT 2, (singularChainMap ℚ incS 2).hom wY = w := by
    obtain ⟨y, hy⟩ := (subChainCorestrict_bijective (R := ℚ) (X := XT) SS 2).2 ⟨w, hw'⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  have hbdY : (singularBoundary ℚ YT 1).hom wY = aY := by
    apply push_inj (Y := XT) SS 1
    have e2 : (singularChainMap ℚ incS 1).hom ((singularBoundary ℚ YT 1).hom wY) =
        (singularBoundary ℚ XT 1).hom ((singularChainMap ℚ incS 2).hom wY) :=
      (singularChainMap_boundary_apply ℚ incS 1 _).symm
    rw [e2, hwY, hdw, hda, haY]
  -- subordination to the two half-bands
  have t0 : IsSubordinate W1 υ0 := by
    rintro _ ⟨t, rfl⟩
    show ¬(((singularSimplexAsContinuousMap YT 1 υ0) t).1.1 1 = 0 ∧ 0 ≤ ((singularSimplexAsContinuousMap YT 1 υ0) t).1.1 0)
    rw [d0 t]; exact (E23_geom t).2
  have t1 : IsSubordinate W1 υ1 := by
    rintro _ ⟨t, rfl⟩
    show ¬(((singularSimplexAsContinuousMap YT 1 υ1) t).1.1 1 = 0 ∧ 0 ≤ ((singularSimplexAsContinuousMap YT 1 υ1) t).1.1 0)
    rw [d1 t]; exact fun h => (E13_geom t).2 h.1
  have t2 : IsSubordinate W2 υ2 := by
    rintro _ ⟨t, rfl⟩
    show ¬(((singularSimplexAsContinuousMap YT 1 υ2) t).1.1 1 = 0 ∧ ((singularSimplexAsContinuousMap YT 1 υ2) t).1.1 0 ≤ 0)
    rw [d2 t]; exact (E12_geom t).2
  have key := winding_obstruction W1 W2 isOpen_W1 isOpen_W2 W1_union_W2 cY continuous_cY W_inter_ne
    (chainGenerator ℚ YT 1 υ0 - chainGenerator ℚ YT 1 υ1) (chainGenerator ℚ YT 1 υ2)
    (Submodule.sub_mem _ (chainGenerator_mem_subChainSubmodule t0)
      (chainGenerator_mem_subChainSubmodule t1))
    (chainGenerator_mem_subChainSubmodule t2) wY (by rw [hbdY, haY_def])
  rw [map_sub, map_sub, eps_edge υ0 E23 d0, eps_edge υ1 E13 d1] at key
  norm_num [E23, E13, vB1, vB2, vB3, mk3] at key


/-! ### From the vanishing of the local class to a filling in the punctured space -/

section Rel

open TernaryPoly TernaryPoly.RationalRelativeSingular TernaryPoly.RationalSingularAugmentation
  TernaryPoly.ContractibleSingularHomology HomologicalComplex

theorem relπ_eq_zero_iff' {Z : Type} [TopologicalSpace Z] (S : Set Z) (n : ℕ) (x : (chains Z).X n) :
    ((relπ S).f n).hom x = 0 ↔
      x ∈ LinearMap.range ((RationalRelativeSingular.inclusion S).f n).hom := by
  have hS := (RelativeChainSequence.shortExact (RationalRelativeSingular.inclusion S))
  have := (hS.map_of_exact (HomologicalComplex.eval (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) n)).exact
  have e := this.moduleCat_range_eq_ker
  have h : x ∈ LinearMap.range ((RationalRelativeSingular.inclusion S).f n).hom ↔
      x ∈ LinearMap.ker ((relπ S).f n).hom := SetLike.ext_iff.mp e x
  exact LinearMap.mem_ker.symm.trans h.symm

theorem exists_filling_of_relCls_zero (c : (chains E3).X 3) (hc : RelCycle (Punctured 3) c)
    (h0 : relCls (Punctured 3) c hc = 0) :
    ∃ β : (chains E3).X 4, ∃ ρ₀ : (chains (Punctured 3)).X 3,
      ((RationalRelativeSingular.inclusion (Punctured 3)).f 3).hom ρ₀ =
        c - ((chains E3).d 4 3).hom β := by
  set K := relativeChains (Punctured 3) with hK
  have hx : (K.d 3 2).hom (((relπ (Punctured 3)).f 3).hom c) = 0 := hc
  have hcls : (K.homologyπ 3).hom (cmk K (((relπ (Punctured 3)).f 3).hom c) hx) = 0 := h0
  obtain ⟨b, hb⟩ := SphereOddDegree.exists_d_eq_iCycles_of_homologyπ_zero K 3 _ hcls
  have hic : (K.iCycles 3).hom (cmk K (((relπ (Punctured 3)).f 3).hom c) hx) =
      ((relπ (Punctured 3)).f 3).hom c :=
    HomologicalComplex.i_cyclesMk K _ 2 next_three hx
  rw [hic] at hb
  have hsurj : Function.Surjective ((relπ (Punctured 3)).f 4).hom :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨β, rfl⟩ := hsurj b
  have hcomm := congrArg (fun m => m.hom β) ((relπ (Punctured 3)).comm 4 3)
  change (K.d 4 3).hom (((relπ (Punctured 3)).f 4).hom β) =
    ((relπ (Punctured 3)).f 3).hom (((chains E3).d 4 3).hom β) at hcomm
  have hz : ((relπ (Punctured 3)).f 3).hom (c - ((chains E3).d 4 3).hom β) = 0 := by
    rw [map_sub, ← hcomm, hb, sub_self]
  obtain ⟨ρ₀, hρ₀⟩ := (relπ_eq_zero_iff' (Punctured 3) 3 _).mp hz
  exact ⟨β, ρ₀, hρ₀⟩

end Rel


/-! ### The explicit tetrahedron is positively oriented around the origin -/

/-- Positive weights with `∑ τₖ wₖ = 0`. -/
def tauT : Fin (3 + 1) → ℝ := ![7 / 36, 1 / 3, 5 / 24, 19 / 72]

theorem tauT_pos : ∀ k, 0 < tauT k := by
  intro k; fin_cases k <;> simp [tauT]

theorem tauT_rel : ∑ k, tauT k • wT k = 0 := by
  ext c
  fin_cases c <;> simp [tauT, wT, vB1, vA, vB2, vB3, mk3, Fin.sum_univ_four] <;> norm_num

theorem edgeDet_wT : 0 < edgeDet wT := by
  simp [edgeDet, Matrix.det_fin_three, wT, vB1, vA, vB2, vB3, mk3]
  norm_num

open TernaryPoly TernaryPoly.EuclideanLocalHomology TernaryPoly.RationalRelativeSingular
  TernaryPoly.RationalSingularAugmentation TernaryPoly.ContractibleSingularHomology in
/-- **The local class of a positively oriented tetrahedron around the origin is non-zero.** -/
theorem lamPos_ne_zero : lamPos ≠ 0 := by
  intro h0
  have hF := facesAvoid_of_rel wT tauT tauT_pos tauT_rel edgeDet_wT
  have e : lamPos = degAff wT hF := (degAff_universal wT hF tauT tauT_pos tauT_rel edgeDet_wT).symm
  have hc : RelCycle (Punctured 3) (sing (TopCat.of E3) (simpOf (affEMap wT))) :=
    simplex_relCycle (affEMap wT) hF
  have hdeg : degRel (sing (TopCat.of E3) (simpOf (affEMap wT))) hc = 0 := by
    rw [← h0, e]; rfl
  have hrel : relCls (Punctured 3) (sing (TopCat.of E3) (simpOf (affEMap wT))) hc = 0 := by
    have hinj : Function.Injective (localTopIso 1).hom.hom :=
      (ModuleCat.mono_iff_injective _).mp inferInstance
    apply hinj
    rw [map_zero]
    exact hdeg
  obtain ⟨β, ρ₀, hρ₀⟩ := exists_filling_of_relCls_zero _ hc hrel
  refine no_filling ρ₀ ((singularBoundary ℚ XT 2).hom ρ₀) ?_ rfl
  have e1 : (singularChainMap ℚ incX 2).hom ((singularBoundary ℚ XT 2).hom ρ₀) =
      (singularBoundary ℚ ET 2).hom ((singularChainMap ℚ incX 3).hom ρ₀) :=
    (singularChainMap_boundary_apply ℚ incX 2 _).symm
  rw [e1]
  have e2 : (singularChainMap ℚ incX 3).hom ρ₀ =
      ((RationalRelativeSingular.inclusion (Punctured 3)).f 3).hom ρ₀ := rfl
  rw [e2, hρ₀]
  have e3 : sing (TopCat.of E3) (simpOf (affEMap wT)) = chainGenerator ℚ ET 3 (affSimp 3 wT) := rfl
  rw [e3]
  have e4 : ((chains E3).d 3 2).hom = (singularBoundary ℚ ET 2).hom := rfl
  have e5 : ((chains E3).d 4 3).hom = (singularBoundary ℚ ET 3).hom := rfl
  rw [e5, map_sub, singularBoundary_boundary_zero ℚ ET 2 β, sub_zero]

/-- **The local degree of the standard top cell is non-zero.** -/
theorem dT0_ne_zero : TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree.dT0 ≠ 0 :=
  dT0_ne_zero_iff.mpr lamPos_ne_zero

end TernaryPeriodPolynomials.Argument.Lemma33.Orient
