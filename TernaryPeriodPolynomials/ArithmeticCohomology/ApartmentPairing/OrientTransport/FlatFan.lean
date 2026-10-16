module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.FlatHexM
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.ThomScale

@[expose] public section


/-!
# The planar fan of the six chambers has degree `lam2`

`fanChain` is the sum, over the six Weyl chambers `k`, of `(-1)^k` times the two straight triangles `Λ_k(T₁), Λ_k(T₂)` with
`Λ_k = hexLam k` (the affine image of the chamber square), the planar model of the compactified flat near its centre.  All the triangles
have the origin as the image of the centre; the boundary is the outer hexagon.  `fan_degree`: its planar local degree is `lam2`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport

open TernaryPeriodPolynomials.Argument.Lemma33.Locality
open TernaryPeriodPolynomials.Argument.Lemma33.Orient
open CategoryTheory Limits HomologicalComplex TernaryPoly TernaryPoly.RationalRelativeSingular
  TernaryPoly.EuclideanLocalHomology TernaryPoly.RationalSingularAugmentation
  TernaryPoly.ContractibleSingularHomology TernaryPoly.RationalSphere SphereOddDegree
  SphereOddDegree.AffineBarycentricSubdivision

/-- A straight triangle of the plane, the image of three points of the square under `hexLam k`. -/
def fanTri (k : Fin 6) (a b c : ℝ × ℝ) : singularChainGroup ℚ (TopCat.of R2) 2 :=
  chainGenerator ℚ (TopCat.of R2) 2 (affSimp 2 ![hexLam k a, hexLam k b, hexLam k c])

/-- A straight edge. -/
def fanEdge (x y : R2) : singularChainGroup ℚ (TopCat.of R2) 1 :=
  chainGenerator ℚ (TopCat.of R2) 1 (affSimp 1 ![x, y])

/-- The planar fan: six chambers, two triangles each, with the chamber sign `(-1)^k`. -/
def fanChain : singularChainGroup ℚ (TopCat.of R2) 2 :=
  ∑ k : Fin 6, ((-1 : ℚ) ^ k.val) • (fanTri k (0, 0) (1, 0) (1, 1) + fanTri k (0, 0) (1, 1) (0, 1))

theorem bd_tri (a b c : R2) :
    (singularBoundary ℚ (TopCat.of R2) 1).hom (chainGenerator ℚ (TopCat.of R2) 2 (affSimp 2 ![a, b, c])) =
      fanEdge b c - fanEdge a c + fanEdge a b := by
  rw [singularBoundary_chainGenerator_formula, Fin.sum_univ_three]
  simp only [faceSimplex_affSimp]
  simp [pow_succ, fanEdge, Fin.succAbove]
  abel

theorem bd_fanTri (k : Fin 6) (a b c : ℝ × ℝ) :
    (singularBoundary ℚ (TopCat.of R2) 1).hom (fanTri k a b c) =
      fanEdge (hexLam k b) (hexLam k c) - fanEdge (hexLam k a) (hexLam k c) +
        fanEdge (hexLam k a) (hexLam k b) := bd_tri _ _ _


theorem hexLam_wall_even (k : Fin 6) (hk : k = 0 ∨ k = 2 ∨ k = 4) (u : ℝ) :
    hexLam k (1, u) = hexLam (k + 1) (1, u) := by
  rcases hk with rfl | rfl | rfl <;>
  · ext i; fin_cases i <;> simp [hexLam, hexM, mk2]

theorem hexLam_wall_odd (k : Fin 6) (hk : k = 1 ∨ k = 3 ∨ k = 5) (u : ℝ) :
    hexLam k (u, 1) = hexLam (k + 1) (u, 1) := by
  rcases hk with rfl | rfl | rfl <;>
  · ext i; fin_cases i <;> simp [hexLam, hexM, mk2]

theorem hexLam_center (k : Fin 6) : hexLam k (1, 1) = 0 := by
  ext i; fin_cases i <;> simp [hexLam, mk2]

/-- The outer hexagon. -/
def fanOuter : singularChainGroup ℚ (TopCat.of R2) 1 :=
  ∑ k : Fin 6, ((-1 : ℚ) ^ k.val) •
    (fanEdge (hexLam k (0, 0)) (hexLam k (1, 0)) - fanEdge (hexLam k (0, 0)) (hexLam k (0, 1)))

theorem bd_fanChain :
    (singularBoundary ℚ (TopCat.of R2) 1).hom fanChain = fanOuter := by
  have e0 : ∀ u : ℝ, hexLam 0 (1, u) = hexLam 1 (1, u) := fun u => hexLam_wall_even 0 (by decide) u
  have e2 : ∀ u : ℝ, hexLam 2 (1, u) = hexLam 3 (1, u) := fun u => hexLam_wall_even 2 (by decide) u
  have e4 : ∀ u : ℝ, hexLam 4 (1, u) = hexLam 5 (1, u) := fun u => hexLam_wall_even 4 (by decide) u
  have o1 : ∀ u : ℝ, hexLam 1 (u, 1) = hexLam 2 (u, 1) := fun u => hexLam_wall_odd 1 (by decide) u
  have o3 : ∀ u : ℝ, hexLam 3 (u, 1) = hexLam 4 (u, 1) := fun u => hexLam_wall_odd 3 (by decide) u
  have o5 : ∀ u : ℝ, hexLam 5 (u, 1) = hexLam 0 (u, 1) := fun u => hexLam_wall_odd 5 (by decide) u
  unfold fanChain fanOuter
  simp only [Fin.sum_univ_six, map_add, map_smul, bd_fanTri]
  simp only [hexLam_center]
  norm_num
  simp only [e0, e2, e4, o1, o3, o5]
  abel

/-- The point inside the first triangle. -/
def fanP : R2 := mk2 2 (4 / 3)

/-- The points off the segment `[0, P]`. -/
def fanA : Set R2 := {x | ∀ s : ℝ, 0 ≤ s → s ≤ 1 → x ≠ s • fanP}

theorem delta1_facts'' (t : Delta 1) :
    0 ≤ t.weights 0 ∧ 0 ≤ t.weights 1 ∧ t.weights 0 + t.weights 1 = 1 := by
  refine ⟨t.weights_nonneg 0, t.weights_nonneg 1, ?_⟩
  have := t.total_of_fintype
  rwa [Fin.sum_univ_two] at this

theorem fanEdge_mem (x y : R2) (h : ∀ t : Delta 1, affMapN 1 ![x, y] t ∈ fanA) :
    fanEdge x y ∈ subChainSubmodule ℚ (TopCat.of R2) fanA 1 :=
  chainGenerator_mem_subChainSubmodule (isSubordinate_affSimp h)

theorem outer_edge_A (k : Fin 6) (b : ℝ × ℝ) (hb : b = (1, 0) ∨ b = (0, 1)) :
    fanEdge (hexLam k (0, 0)) (hexLam k b) ∈ subChainSubmodule ℚ (TopCat.of R2) fanA 1 := by
  apply fanEdge_mem
  intro t s hs0 hs1 heq
  obtain ⟨h0, h1, hsum⟩ := delta1_facts'' t
  have c0 := congrArg (fun v : R2 => v 0) heq
  have c1 := congrArg (fun v : R2 => v 1) heq
  fin_cases k <;> rcases hb with rfl | rfl <;>
  · simp [affMapN, Fin.sum_univ_two, hexLam, hexM, mk2, fanP] at c0 c1
    linarith

theorem fanOuter_mem : fanOuter ∈ subChainSubmodule ℚ (TopCat.of R2) fanA 1 := by
  unfold fanOuter
  refine Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_))
  · exact outer_edge_A k (1, 0) (Or.inl rfl)
  · exact outer_edge_A k (0, 1) (Or.inr rfl)

theorem fan_boundary_mem :
    (singularBoundary ℚ (TopCat.of R2) 1).hom fanChain ∈ subChainSubmodule ℚ (TopCat.of R2) fanA 1 := by
  rw [bd_fanChain]; exact fanOuter_mem

theorem fanA_sub : fanA ⊆ ({0}ᶜ : Set R2) := by
  intro x hx h0
  exact hx 0 le_rfl zero_le_one (by rw [Set.mem_singleton_iff.mp h0, zero_smul])

theorem fan_cycle : ((localChains 2).d 2 1).hom ((locR2.f 2).hom fanChain) = 0 :=
  locR2_cycle_of_boundary_mem fanA_sub fan_boundary_mem

/-! ### Translation of the origin to the point `P` -/

/-- Translation by `-P`. -/
def transP : TopCat.of R2 ⟶ TopCat.of R2 := TopCat.ofHom ⟨fun x => x - fanP, by fun_prop⟩

/-- The homotopy `x ↦ x - sP` from the identity to the translation. -/
def transHomotopy : ContinuousMap.Homotopy (TopCat.ofHom (ContinuousMap.id R2)).hom transP.hom where
  toFun p := p.2 - (p.1 : ℝ) • fanP
  continuous_toFun := by fun_prop
  map_zero_left x := by
    change (x : R2) - ((0 : unitInterval) : ℝ) • fanP = x
    simp
  map_one_left x := by
    change (x : R2) - ((1 : unitInterval) : ℝ) • fanP = (x : R2) - fanP
    simp

theorem pushSimplex_affSimp_trans (n : ℕ) (w : Fin (n + 1) → R2) :
    pushSimplex transP n (affSimp n w) = affSimp n (fun i => w i - fanP) := by
  apply (TopCat.toSSetObjEquiv (TopCat.of R2) (Opposite.op (SimplexCategory.mk n))).injective
  rw [toSSetObjEquiv_affSimp]
  apply ContinuousMap.ext
  intro x
  change (affMapN n w) x - fanP = (affMapN n fun i => w i - fanP) x
  have hs : ∑ i, x.weights i = 1 := x.total_of_fintype
  simp only [affMapN, ContinuousMap.coe_mk, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hs, one_smul]

/-- A translated straight triangle. -/
def fanTriP (k : Fin 6) (a b c : ℝ × ℝ) : singularChainGroup ℚ (TopCat.of R2) 2 :=
  chainGenerator ℚ (TopCat.of R2) 2 (affSimp 2 ![hexLam k a - fanP, hexLam k b - fanP, hexLam k c - fanP])

theorem push_fanTri (k : Fin 6) (a b c : ℝ × ℝ) :
    (singularChainMap ℚ transP 2).hom (fanTri k a b c) = fanTriP k a b c := by
  unfold fanTri fanTriP
  rw [singularChainMap_generator, pushSimplex_affSimp_trans]
  congr 2
  funext i
  fin_cases i <;> rfl

theorem push_fanChain :
    (singularChainMap ℚ transP 2).hom fanChain =
      ∑ k : Fin 6, ((-1 : ℚ) ^ k.val) • (fanTriP k (0, 0) (1, 0) (1, 1) + fanTriP k (0, 0) (1, 1) (0, 1)) := by
  unfold fanChain
  simp only [map_sum, map_smul, map_add, push_fanTri]

theorem fanTriP_mem (k : Fin 6) (a b c : ℝ × ℝ)
    (h : ∀ t : Delta 2, affMapN 2 ![hexLam k a - fanP, hexLam k b - fanP, hexLam k c - fanP] t ≠ 0) :
    fanTriP k a b c ∈ subChainSubmodule ℚ (TopCat.of R2) ({0}ᶜ : Set R2) 2 :=
  chainGenerator_mem_subChainSubmodule (isSubordinate_affSimp (fun t ht => h t (Set.mem_singleton_iff.mp ht)))

theorem delta2_facts'' (t : Delta 2) :
    0 ≤ t.weights 0 ∧ 0 ≤ t.weights 1 ∧ 0 ≤ t.weights 2 ∧
      t.weights 0 + t.weights 1 + t.weights 2 = 1 := by
  refine ⟨t.weights_nonneg 0, t.weights_nonneg 1, t.weights_nonneg 2, ?_⟩
  have := t.total_of_fintype
  rwa [Fin.sum_univ_three] at this

theorem fanT1_other (k : Fin 6) (hk : k ≠ 0) :
    fanTriP k (0, 0) (1, 0) (1, 1) ∈ subChainSubmodule ℚ (TopCat.of R2) ({0}ᶜ : Set R2) 2 := by
  apply fanTriP_mem
  intro t heq
  obtain ⟨h0, h1, h2, hsum⟩ := delta2_facts'' t
  have c0 := congrArg (fun v : R2 => v 0) heq
  have c1 := congrArg (fun v : R2 => v 1) heq
  fin_cases k
  · exact absurd rfl hk
  all_goals
    simp [affMapN, Fin.sum_univ_three, hexLam, hexM, mk2, fanP] at c0 c1
    linarith

theorem fanT2_all (k : Fin 6) :
    fanTriP k (0, 0) (1, 1) (0, 1) ∈ subChainSubmodule ℚ (TopCat.of R2) ({0}ᶜ : Set R2) 2 := by
  apply fanTriP_mem
  intro t heq
  obtain ⟨h0, h1, h2, hsum⟩ := delta2_facts'' t
  have c0 := congrArg (fun v : R2 => v 0) heq
  have c1 := congrArg (fun v : R2 => v 1) heq
  fin_cases k
  all_goals
    simp [affMapN, Fin.sum_univ_three, hexLam, hexM, mk2, fanP] at c0 c1
    linarith

theorem push_fanChain_split :
    ∃ R ∈ subChainSubmodule ℚ (TopCat.of R2) ({0}ᶜ : Set R2) 2,
      (singularChainMap ℚ transP 2).hom fanChain = fanTriP 0 (0, 0) (1, 0) (1, 1) + R := by
  refine ⟨fanTriP 0 (0, 0) (1, 1) (0, 1) +
    (((-1 : ℚ) ^ 1) • (fanTriP 1 (0, 0) (1, 0) (1, 1) + fanTriP 1 (0, 0) (1, 1) (0, 1)) +
    (((-1 : ℚ) ^ 2) • (fanTriP 2 (0, 0) (1, 0) (1, 1) + fanTriP 2 (0, 0) (1, 1) (0, 1)) +
    (((-1 : ℚ) ^ 3) • (fanTriP 3 (0, 0) (1, 0) (1, 1) + fanTriP 3 (0, 0) (1, 1) (0, 1)) +
    (((-1 : ℚ) ^ 4) • (fanTriP 4 (0, 0) (1, 0) (1, 1) + fanTriP 4 (0, 0) (1, 1) (0, 1)) +
    ((-1 : ℚ) ^ 5) • (fanTriP 5 (0, 0) (1, 0) (1, 1) + fanTriP 5 (0, 0) (1, 1) (0, 1)))))), ?_, ?_⟩
  · refine Submodule.add_mem _ (fanT2_all 0) ?_
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.add_mem _ (fanT1_other 1 (by decide)) (fanT2_all 1))) ?_
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.add_mem _ (fanT1_other 2 (by decide)) (fanT2_all 2))) ?_
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.add_mem _ (fanT1_other 3 (by decide)) (fanT2_all 3))) ?_
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.add_mem _ (fanT1_other 4 (by decide)) (fanT2_all 4))) ?_
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ (fanT1_other 5 (by decide)) (fanT2_all 5))
  · rw [push_fanChain]
    simp only [Fin.sum_univ_six]
    norm_num
    abel

/-! ### The linear map carrying the reference triangle to the translated first triangle -/

/-- The linear map `(x, y) ↦ (2x/3, 2x/9 + 2y/9)`, of positive determinant. -/
def fanL : R2 →ₗ[ℝ] R2 where
  toFun x := mk2 (2 / 3 * x 0) (2 / 9 * x 0 + 2 / 9 * x 1)
  map_add' x y := by ext i; fin_cases i <;> simp [mk2] <;> ring
  map_smul' c x := by ext i; fin_cases i <;> simp [mk2] <;> ring

theorem fanL_apply (x : R2) : fanL x = mk2 (2 / 3 * x 0) (2 / 9 * x 0 + 2 / 9 * x 1) := rfl

/-- The map `fanL` as a morphism of spaces. -/
def fanLHom : TopCat.of R2 ⟶ TopCat.of R2 :=
  TopCat.ofHom ⟨fanL, LinearMap.continuous_of_finiteDimensional _⟩

/-- The path of linear maps from `fanL` to the identity. -/
def fanLHomotopy : ContinuousMap.Homotopy fanLHom.hom (TopCat.ofHom (ContinuousMap.id R2)).hom where
  toFun p := (p.1 : ℝ) • (p.2 : R2) + (1 - (p.1 : ℝ)) • fanL p.2
  continuous_toFun := by
    have : Continuous (fun x : R2 => fanL x) := LinearMap.continuous_of_finiteDimensional _
    fun_prop
  map_zero_left x := by
    change ((0 : unitInterval) : ℝ) • (x : R2) + (1 - ((0 : unitInterval) : ℝ)) • fanL x = fanL x
    simp
  map_one_left x := by
    change ((1 : unitInterval) : ℝ) • (x : R2) + (1 - ((1 : unitInterval) : ℝ)) • fanL x = x
    simp

theorem fanLHomotopy_ne_zero (t : unitInterval) (x : R2) (hx : x ≠ 0) :
    (t : ℝ) • x + (1 - (t : ℝ)) • fanL x ≠ 0 := by
  intro h
  have ht0 := t.2.1
  have ht1 := t.2.2
  have c0 := congrArg (fun v : R2 => v 0) h
  have c1 := congrArg (fun v : R2 => v 1) h
  simp [fanL_apply, mk2] at c0 c1
  apply hx
  have hx0 : x 0 = 0 := by
    have : ((t : ℝ) + (1 - t) * (2 / 3)) * x 0 = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · nlinarith
    · exact h'
  have hx1 : x 1 = 0 := by
    have : ((t : ℝ) + (1 - t) * (2 / 9)) * x 1 = 0 := by rw [hx0] at c1; linarith
    rcases mul_eq_zero.mp this with h' | h'
    · nlinarith
    · exact h'
  ext i; fin_cases i <;> simp [hx0, hx1]

theorem fanL_ref :
    (singularChainMap ℚ fanLHom 2).hom (chainGenerator ℚ (TopCat.of R2) 2 (affSimp 2 rtri)) =
      fanTriP 0 (0, 0) (1, 0) (1, 1) := by
  unfold fanTriP
  rw [singularChainMap_generator]
  have : pushSimplex fanLHom 2 (affSimp 2 rtri) = affSimp 2 (fun i => fanL (rtri i)) :=
    pushSimplex_affSimp fanL (LinearMap.continuous_of_finiteDimensional _) 2 rtri
  rw [this]
  congr 2
  funext i
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [fanL_apply, hexLam, hexM, mk2, fanP, rtri, rt] <;> norm_num

theorem fanL_degree :
    ∃ hf : ((localChains 2).d 2 1).hom ((locR2.f 2).hom (fanTriP 0 (0, 0) (1, 0) (1, 1))) = 0,
      degR2 (fanTriP 0 (0, 0) (1, 0) (1, 1)) hf = lam2 := by
  obtain ⟨hf, hg, h⟩ := degR2_homotopy fanLHom (TopCat.ofHom (ContinuousMap.id R2)) fanLHomotopy
    {v : R2 | 1 < ‖v‖}
    (by
      intro t x hx
      have hx0 : x ≠ 0 := by
        intro h0
        have : (1 : ℝ) < ‖x‖ := hx
        rw [h0, norm_zero] at this
        linarith
      exact fanLHomotopy_ne_zero t x hx0)
    (chainGenerator ℚ (TopCat.of R2) 2 (affSimp 2 rtri)) tri_boundary_mem
  have e : (singularChainMap ℚ (TopCat.ofHom (ContinuousMap.id R2)) 2).hom
      (chainGenerator ℚ (TopCat.of R2) 2 (affSimp 2 rtri)) =
      chainGenerator ℚ (TopCat.of R2) 2 (affSimp 2 rtri) :=
    congrArg (fun F => F.hom (chainGenerator ℚ (TopCat.of R2) 2 (affSimp 2 rtri)))
      (singularChainMap_id ℚ (TopCat.of R2) 2)
  have hf' : ((localChains 2).d 2 1).hom ((locR2.f 2).hom (fanTriP 0 (0, 0) (1, 0) (1, 1))) = 0 := by
    rw [← fanL_ref]; exact hf
  refine ⟨hf', ?_⟩
  have h1 := degR2_congr _ _ fanL_ref hf hf'
  have h2 := degR2_congr _ _ e hg (locR2_cycle_of_boundary_mem unitBall_compl_subset2 tri_boundary_mem)
  unfold lam2
  exact h1.symm.trans (h.trans h2)

/-- **The planar fan of the six chambers has local degree `lam2`.** -/
theorem fan_degree (h : ((localChains 2).d 2 1).hom ((locR2.f 2).hom fanChain) = 0) :
    degR2 fanChain h = lam2 := by
  obtain ⟨hf, hg, h0⟩ := degR2_homotopy (TopCat.ofHom (ContinuousMap.id R2)) transP transHomotopy fanA
    (by
      intro t x hx hx0
      apply hx (t : ℝ) t.2.1 t.2.2
      have : x - (t : ℝ) • fanP = 0 := hx0
      exact sub_eq_zero.mp this)
    fanChain fan_boundary_mem
  have e : (singularChainMap ℚ (TopCat.ofHom (ContinuousMap.id R2)) 2).hom fanChain = fanChain :=
    congrArg (fun F => F.hom fanChain) (singularChainMap_id ℚ (TopCat.of R2) 2)
  have h1 := degR2_congr _ _ e hf h
  obtain ⟨R, hR, hsplit⟩ := push_fanChain_split
  obtain ⟨hY, hYdeg⟩ := fanL_degree
  have hRloc : (locR2.f 2).hom R = 0 := locR2_sub_zero (fun x hx => hx) 2 hR
  have hsum : ((localChains 2).d 2 1).hom ((locR2.f 2).hom (fanTriP 0 (0, 0) (1, 0) (1, 1) + R)) = 0 := by
    rw [map_add, hRloc, add_zero]; exact hY
  have h2 := degR2_congr _ _ hsplit hg hsum
  have h3 : degR2 (fanTriP 0 (0, 0) (1, 0) (1, 1) + R) hsum = degR2 (fanTriP 0 (0, 0) (1, 0) (1, 1)) hY := by
    apply degR2_eq_of_sub _ _ hsum hY 0
    rw [map_add, hRloc, add_zero, map_zero, add_zero]
  rw [← hYdeg]
  exact h1.symm.trans (h0.trans (h2.trans h3))

end TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport
