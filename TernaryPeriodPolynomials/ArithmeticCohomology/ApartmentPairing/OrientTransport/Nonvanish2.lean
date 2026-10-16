module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Orient.Nonvanish
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.LocalEval

@[expose] public section


/-!
# The local class of the positively oriented reference triangle around the origin is non-zero

`lam2_ne_zero : lam2 ≠ 0`.  The dimension-two analogue of the `lamPos_ne_zero` (`Orient/Nonvanish.lean`), by the same method:
if the class of the triangle `σ` in `H₂(ℝ², ℝ² ∖ 0)` vanished, the loop `∂σ` would bound a 2-chain `ρ₀` of the punctured plane
(`exists_filling_of_degR2_zero`).  The punctured plane is covered by the complements of the closed negative and positive
`x`-axes; the three edges split as a chain `a` over the first and `b` over the second cover, so (`two_cover_split` in
`winding_obstruction`, B2) the algebraic count of boundary points of `a` in `{x₂ > 0}` vanishes, whereas it is `1`.

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

theorem next_two'' : (ComplexShape.down ℕ).next 2 = 1 :=
  (ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 2 1 from rfl)

/-- If the planar local degree of a relative cycle vanishes, the chain is a boundary plus a chain of the punctured plane. -/
theorem exists_filling_of_degR2_zero (c : (chains R2).X 2)
    (h : ((localChains 2).d 2 1).hom ((locR2.f 2).hom c) = 0) (h0 : degR2 c h = 0) :
    ∃ β : (chains R2).X 3, ∃ ρ₀ : (chains (Punctured 2)).X 2,
      ((RationalRelativeSingular.inclusion (Punctured 2)).f 2).hom ρ₀ = c - ((chains R2).d 3 2).hom β := by
  set K := localChains 2 with hK
  have hinj : Function.Injective (localTopIso 0).hom.hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hcls : (K.homologyπ 2).hom (K.cyclesMk ((locR2.f 2).hom c) 1 next_two'' h) = 0 := by
    apply hinj
    rw [map_zero]
    exact h0
  obtain ⟨b, hb⟩ := SphereOddDegree.exists_d_eq_iCycles_of_homologyπ_zero K 2 _ hcls
  have hic : (K.iCycles 2).hom (K.cyclesMk ((locR2.f 2).hom c) 1 next_two'' h) = (locR2.f 2).hom c :=
    HomologicalComplex.i_cyclesMk K _ 1 next_two'' h
  rw [hic] at hb
  have hsurj : Function.Surjective ((relπ (Punctured 2)).f 3).hom :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨β, rfl⟩ := hsurj b
  have hcomm := congrArg (fun m => m.hom β) (locR2.comm 3 2)
  change (K.d 3 2).hom ((locR2.f 3).hom β) = (locR2.f 2).hom (((chains R2).d 3 2).hom β) at hcomm
  have hz : (locR2.f 2).hom (c - ((chains R2).d 3 2).hom β) = 0 := by
    rw [map_sub, ← hcomm]
    exact sub_eq_zero.mpr hb.symm
  obtain ⟨ρ₀, hρ₀⟩ := (relπ_eq_zero_iff' (Punctured 2) 2 _).mp hz
  exact ⟨β, ρ₀, hρ₀⟩

/-! ### The punctured plane and its two covers -/

theorem continuous_coord2 (i : Fin 2) : Continuous fun x : R2 => x i := by fun_prop

/-- The closed ray `{x₂ = 0, x₁ ≤ 0}`. -/
def Rm2 : Set R2 := {x | x 1 = 0 ∧ x 0 ≤ 0}

/-- The closed ray `{x₂ = 0, x₁ ≥ 0}`. -/
def Rp2 : Set R2 := {x | x 1 = 0 ∧ 0 ≤ x 0}

theorem isClosed_Rm2 : IsClosed Rm2 :=
  (isClosed_eq (continuous_coord2 1) continuous_const).inter
    (isClosed_le (continuous_coord2 0) continuous_const)

theorem isClosed_Rp2 : IsClosed Rp2 :=
  (isClosed_eq (continuous_coord2 1) continuous_const).inter
    (isClosed_le continuous_const (continuous_coord2 0))

/-- The punctured plane as a bundled space. -/
abbrev XP : TopCat.{0} := TopCat.of (Punctured 2)

def UU2 : Set XP := {x | x.1 ∉ Rm2}
def VV2 : Set XP := {x | x.1 ∉ Rp2}

theorem isOpen_UU2 : IsOpen UU2 := (isClosed_Rm2.isOpen_compl).preimage continuous_subtype_val
theorem isOpen_VV2 : IsOpen VV2 := (isClosed_Rp2.isOpen_compl).preimage continuous_subtype_val

theorem UU2_union_VV2 : UU2 ∪ VV2 = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_contra h
  simp only [Set.mem_union, UU2, VV2, Set.mem_ofPred_eq, not_or, not_not] at h
  obtain ⟨h1, h2⟩ := h
  apply x.2
  have e0 : x.1 0 = 0 := le_antisymm h1.2 h2.2
  have e1 : x.1 1 = 0 := h1.1
  ext i
  fin_cases i <;> simp [e0, e1]

/-- The second coordinate on the punctured plane. -/
def cP (y : XP) : ℝ := y.1 1

theorem continuous_cP : Continuous cP := (continuous_coord2 1).comp continuous_subtype_val

theorem cP_ne : ∀ y ∈ UU2 ∩ VV2, cP y ≠ 0 := by
  intro y hy h0
  obtain ⟨h1, h2⟩ := hy
  have h1' : y.1 ∉ Rm2 := h1
  have h2' : y.1 ∉ Rp2 := h2
  rcases le_total (y.1 0) 0 with h | h
  · exact h1' ⟨h0, h⟩
  · exact h2' ⟨h0, h⟩

/-! ### The reference triangle -/

theorem rtri_0_0 : rtri 0 0 = 3 := by simp [rtri, rt, mk2]
theorem rtri_0_1 : rtri 0 1 = 0 := by simp [rtri, rt, mk2]
theorem rtri_1_0 : rtri 1 0 = 0 := by simp [rtri, rt, mk2]
theorem rtri_1_1 : rtri 1 1 = 3 := by simp [rtri, rt, mk2]
theorem rtri_2_0 : rtri 2 0 = -3 := by simp [rtri, rt, mk2]
theorem rtri_2_1 : rtri 2 1 = -3 := by simp [rtri, rt, mk2]

theorem affMapN1_apply (w : Fin 2 → R2) (t : Delta 1) (i : Fin 2) :
    affMapN 1 w t i = t.weights 0 * w 0 i + t.weights 1 * w 1 i := by
  simp [affMapN, Fin.sum_univ_two]

theorem delta1_facts' (t : Delta 1) :
    0 ≤ t.weights 0 ∧ 0 ≤ t.weights 1 ∧ t.weights 0 + t.weights 1 = 1 := by
  refine ⟨t.weights_nonneg 0, t.weights_nonneg 1, ?_⟩
  have := t.total_of_fintype
  rwa [Fin.sum_univ_two] at this

/-- Lifting an affine simplex avoiding the origin to the punctured plane. -/
theorem lift_P (n : ℕ) (w : Fin (n + 1) → R2) (hZ : ∀ t, affMapN n w t ≠ 0) :
    ∃ τ : singularSimplices XP n, pushSimplex (sInclusion (Punctured 2)) n τ = affSimp n w ∧
      ∀ t, ((singularSimplexAsContinuousMap XP n τ) t).1 = affMapN n w t := by
  have hs : IsSubordinate (Punctured 2 : Set (TopCat.of R2)) (affSimp n w) :=
    isSubordinate_affSimp (fun t h => hZ t h)
  obtain ⟨τ, hτ⟩ := exists_pushSimplex_of_subordinate (X := TopCat.of R2) (Punctured 2) n hs
  refine ⟨τ, hτ, fun t => ?_⟩
  have := congrArg (fun σ => singularSimplexAsContinuousMap (TopCat.of R2) n σ t) hτ
  simp only [pushSimplex_continuousMap, asContinuousMap_affSimp] at this
  exact this

theorem affMapN_vertex2 (n : ℕ) (w : Fin (n + 1) → R2) (k : Fin (n + 1)) :
    affMapN n w (Convexity.StdSimplex.single k) = w k := by
  simp [affMapN, Finsupp.single_apply]

/-- The count of boundary points in `{x₂ > 0}` of an edge of the punctured plane. -/
theorem eps_edge2 (υ : singularSimplices XP 1) (w : Fin 2 → R2)
    (hυ : ∀ t, ((singularSimplexAsContinuousMap XP 1 υ) t).1 = affMapN 1 w t) :
    (epsFun {y : XP | 0 < cP y}).hom ((singularBoundary ℚ XP 0).hom (chainGenerator ℚ XP 1 υ)) =
      (if 0 < w 1 1 then 1 else 0) - (if 0 < w 0 1 then 1 else 0) := by
  rw [singularBoundary_chainGenerator_formula, Fin.sum_univ_two, map_add, map_smul, map_smul,
    epsFun_generator, epsFun_generator, pt0_faceSimplex, pt0_faceSimplex]
  have h0 : (Fin.succAbove (0 : Fin 2) 0 : Fin 2) = 1 := rfl
  have h1 : (Fin.succAbove (1 : Fin 2) 0 : Fin 2) = 0 := rfl
  rw [h0, h1]
  have c1 : cP (singularSimplexAsContinuousMap XP 1 υ (Convexity.StdSimplex.single 1)) = w 1 1 := by
    unfold cP; rw [hυ, affMapN_vertex2]
  have c0 : cP (singularSimplexAsContinuousMap XP 1 υ (Convexity.StdSimplex.single 0)) = w 0 1 := by
    unfold cP; rw [hυ, affMapN_vertex2]
  simp only [Set.mem_ofPred_eq, c1, c0]
  by_cases a : 0 < w 1 1 <;> by_cases b : 0 < w 0 1 <;> simp [a, b]

/-- The edge opposite to the vertex `j` of the reference triangle. -/
def edgeV (j : Fin 3) : Fin 2 → R2 := fun i => rtri (j.succAbove i)

theorem edge_coord (j : Fin 3) (t : Delta 1) (i : Fin 2) :
    affMapN 1 (edgeV j) t i = t.weights 0 * rtri (j.succAbove 0) i +
      t.weights 1 * rtri (j.succAbove 1) i := affMapN1_apply _ t i

theorem ne_zero_of_coords2 (x : R2) (h : ¬(x 0 = 0 ∧ x 1 = 0)) : x ≠ 0 := by
  intro hx
  apply h
  rw [hx]
  exact ⟨rfl, rfl⟩

theorem E0_geom (t : Delta 1) : affMapN 1 (edgeV 0) t ≠ 0 ∧ affMapN 1 (edgeV 0) t ∉ Rp2 := by
  obtain ⟨h0, h1, hs⟩ := delta1_facts' t
  have c0 := edge_coord 0 t 0
  have c1 := edge_coord 0 t 1
  simp [Fin.succAbove, rtri_1_0, rtri_1_1, rtri_2_0, rtri_2_1] at c0 c1
  refine ⟨ne_zero_of_coords2 _ ?_, ?_⟩
  · rintro ⟨e0, e1⟩
    rw [c0] at e0
    rw [c1] at e1
    linarith
  · rintro ⟨e1, e0⟩
    rw [c0] at e0
    rw [c1] at e1
    linarith

theorem E1_geom (t : Delta 1) : affMapN 1 (edgeV 1) t ≠ 0 ∧ affMapN 1 (edgeV 1) t ∉ Rm2 := by
  obtain ⟨h0, h1, hs⟩ := delta1_facts' t
  have c0 := edge_coord 1 t 0
  have c1 := edge_coord 1 t 1
  simp [Fin.succAbove, rtri_0_0, rtri_0_1, rtri_2_0, rtri_2_1] at c0 c1
  refine ⟨ne_zero_of_coords2 _ ?_, ?_⟩
  · rintro ⟨e0, e1⟩
    rw [c0] at e0
    rw [c1] at e1
    linarith
  · rintro ⟨e1, e0⟩
    rw [c0] at e0
    rw [c1] at e1
    linarith

theorem E2_geom (t : Delta 1) : affMapN 1 (edgeV 2) t ≠ 0 ∧ affMapN 1 (edgeV 2) t ∉ Rm2 := by
  obtain ⟨h0, h1, hs⟩ := delta1_facts' t
  have c0 := edge_coord 2 t 0
  have c1 := edge_coord 2 t 1
  simp [Fin.succAbove, rtri_0_0, rtri_0_1, rtri_1_0, rtri_1_1] at c0 c1
  refine ⟨ne_zero_of_coords2 _ ?_, ?_⟩
  · rintro ⟨e0, e1⟩
    rw [c0] at e0
    rw [c1] at e1
    linarith
  · rintro ⟨e1, e0⟩
    rw [c0] at e0
    rw [c1] at e1
    linarith

theorem tri_boundary_expand :
    (singularBoundary ℚ (TopCat.of R2) 1).hom (chainGenerator ℚ (TopCat.of R2) 2 (affSimp 2 rtri)) =
      chainGenerator ℚ (TopCat.of R2) 1 (affSimp 1 (edgeV 0)) -
        chainGenerator ℚ (TopCat.of R2) 1 (affSimp 1 (edgeV 1)) +
        chainGenerator ℚ (TopCat.of R2) 1 (affSimp 1 (edgeV 2)) := by
  rw [singularBoundary_chainGenerator_formula, Fin.sum_univ_three]
  simp only [faceSimplex_affSimp]
  simp [pow_succ]
  abel

/-- The inclusion of the punctured plane. -/
abbrev incP : XP ⟶ TopCat.of R2 := sInclusion (X := TopCat.of R2) (Punctured 2)

/-- **The boundary of the reference triangle does not bound in the punctured plane.** -/
theorem no_filling2 (ρ : singularChainGroup ℚ XP 2)
    (hz : (singularChainMap ℚ incP 1).hom ((singularBoundary ℚ XP 1).hom ρ) =
      (singularBoundary ℚ (TopCat.of R2) 1).hom
        (chainGenerator ℚ (TopCat.of R2) 2 (affSimp 2 rtri))) : False := by
  obtain ⟨τ0, h0, c0⟩ := lift_P 1 (edgeV 0) (fun t => (E0_geom t).1)
  obtain ⟨τ1, h1, c1⟩ := lift_P 1 (edgeV 1) (fun t => (E1_geom t).1)
  obtain ⟨τ2, h2, c2⟩ := lift_P 1 (edgeV 2) (fun t => (E2_geom t).1)
  have push_gen : ∀ (τ : singularSimplices XP 1) (σ : singularSimplices (TopCat.of R2) 1),
      pushSimplex incP 1 τ = σ →
      (singularChainMap ℚ incP 1).hom (chainGenerator ℚ XP 1 τ) = chainGenerator ℚ (TopCat.of R2) 1 σ := by
    intro τ σ h; rw [singularChainMap_generator, h]
  have hzX : (singularBoundary ℚ XP 1).hom ρ =
      chainGenerator ℚ XP 1 τ0 - chainGenerator ℚ XP 1 τ1 + chainGenerator ℚ XP 1 τ2 := by
    apply push_inj (Y := TopCat.of R2) (Punctured 2) 1
    rw [hz, tri_boundary_expand]
    simp only [map_sub, map_add, push_gen _ _ h0, push_gen _ _ h1, push_gen _ _ h2]
  have s0 : IsSubordinate VV2 τ0 := by
    rintro _ ⟨t, rfl⟩
    show (singularSimplexAsContinuousMap XP 1 τ0 t).1 ∉ Rp2
    rw [c0]; exact (E0_geom t).2
  have s1 : IsSubordinate UU2 τ1 := by
    rintro _ ⟨t, rfl⟩
    show (singularSimplexAsContinuousMap XP 1 τ1 t).1 ∉ Rm2
    rw [c1]; exact (E1_geom t).2
  have s2 : IsSubordinate UU2 τ2 := by
    rintro _ ⟨t, rfl⟩
    show (singularSimplexAsContinuousMap XP 1 τ2 t).1 ∉ Rm2
    rw [c2]; exact (E2_geom t).2
  have ha : (-chainGenerator ℚ XP 1 τ1 + chainGenerator ℚ XP 1 τ2) ∈ subChainSubmodule ℚ XP UU2 1 :=
    Submodule.add_mem _ (Submodule.neg_mem _ (chainGenerator_mem_subChainSubmodule s1))
      (chainGenerator_mem_subChainSubmodule s2)
  have hb : chainGenerator ℚ XP 1 τ0 ∈ subChainSubmodule ℚ XP VV2 1 :=
    chainGenerator_mem_subChainSubmodule s0
  have key := winding_obstruction UU2 VV2 isOpen_UU2 isOpen_VV2 UU2_union_VV2 cP continuous_cP cP_ne
    _ _ ha hb ρ (by rw [hzX]; abel)
  simp only [map_add, map_neg] at key
  rw [eps_edge2 τ1 (edgeV 1) c1, eps_edge2 τ2 (edgeV 2) c2] at key
  simp [edgeV, Fin.succAbove, rtri_0_1, rtri_1_1, rtri_2_1] at key
  norm_num at key

/-- **The local degree of the positively oriented reference triangle is non-zero.** -/
theorem lam2_ne_zero : lam2 ≠ 0 := by
  intro h0
  obtain ⟨β, ρ₀, hρ₀⟩ := exists_filling_of_degR2_zero _ (locR2_cycle_of_boundary_mem unitBall_compl_subset2
    tri_boundary_mem) h0
  refine no_filling2 ρ₀ ?_
  have e1 : (singularChainMap ℚ incP 1).hom ((singularBoundary ℚ XP 1).hom ρ₀) =
      (singularBoundary ℚ (TopCat.of R2) 1).hom ((singularChainMap ℚ incP 2).hom ρ₀) :=
    (singularChainMap_boundary_apply ℚ incP 1 _).symm
  rw [e1]
  have e2 : (singularChainMap ℚ incP 2).hom ρ₀ =
      ((RationalRelativeSingular.inclusion (Punctured 2)).f 2).hom ρ₀ := rfl
  rw [e2, hρ₀]
  have e5 : ((chains R2).d 3 2).hom = (singularBoundary ℚ (TopCat.of R2) 2).hom := rfl
  rw [e5, map_sub, singularBoundary_boundary_zero ℚ (TopCat.of R2) 1 β, sub_zero]

end TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport
