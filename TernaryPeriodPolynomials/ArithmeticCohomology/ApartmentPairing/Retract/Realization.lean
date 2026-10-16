module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.ConeRecursion
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.FlatAffine
public import TernaryPeriodPolynomials.SymmetricSpace.Rational.GluingInterior

@[expose] public section



/-!
# Realization of affine chains of positive definite forms as singular chains of the bordification

`PDMat` is the cone of positive definite real `3 × 3` matrices (the `Q`-coordinates of the well-rounded
retract); `nu : PDMat → Glued`, `Q ↦ [Q⁻¹]` (trace-normalized inverse, through the embedding of the
symmetric space), is continuous.  An ordered affine simplex of `PDMat` (`y : Fin (n+1) → PDMat`) becomes
the singular simplex `affSing y = nu ∘ (barycentric combination of y)` of `Glued`, with the face formula
`affSing_face`; `realize` is the induced linear map from formal affine chains
(`ConeRecursion`) to the singular chains `underlyingChains (TopCat.of Glued)`, and `d_realize` says it is a
chain map for the formal simplicial boundary `dAff`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.Lemma33.Retract

open CategoryTheory TernaryPoly TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceRationalGluing
  TernaryPoly.EquivariantSingularResolution TernaryPoly.FreeActionLinearization Finsupp

/-- Real symmetric `3 × 3` matrices (all real matrices). -/
abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ

/-- Positive definite forms. -/
abbrev PDMat := {M : Mat // M.PosDef}

theorem posDef_comb {n : ℕ} (t : Convexity.StdSimplex ℝ (Fin (n + 1))) (y : Fin (n + 1) → PDMat) :
    (∑ i, t.weights i • (y i).1).PosDef := by
  classical
  set s : Finset (Fin (n + 1)) := Finset.univ.filter fun i => 0 < t.weights i with hs
  have hne : s.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hz : ∀ i, t.weights i = 0 := fun i => by
      have h1 : ¬ 0 < t.weights i := fun hi =>
        Finset.notMem_empty i (h ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
      exact le_antisymm (not_lt.mp h1) (t.weights_nonneg i)
    have h1 : ∑ i, t.weights i = 1 := t.total_of_fintype
    rw [Finset.sum_eq_zero (fun i _ => hz i)] at h1
    exact zero_ne_one h1
  have e : ∑ i, t.weights i • (y i).1 = ∑ i ∈ s, t.weights i • (y i).1 := by
    rw [hs, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : 0 < t.weights i
    · simp [hi]
    · have : t.weights i = 0 := le_antisymm (not_lt.mp hi) (t.weights_nonneg i)
      simp [this]
  rw [e]
  exact Matrix.posDef_sum hne fun i hi => (y i).2.smul (Finset.mem_filter.mp hi).2

/-- The affine map from the standard simplex to positive definite forms. -/
def affMap (n : ℕ) (y : AffSimp PDMat n) : C(Convexity.StdSimplex ℝ (Fin (n + 1)), PDMat) where
  toFun t := ⟨∑ i, t.weights i • (y i).1, posDef_comb t y⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine continuous_finsetSum _ (fun i _ => ?_)
    exact (Convexity.StdSimplex.continuous_weights_apply ℝ i).smul continuous_const

theorem affMap_val (n : ℕ) (y : AffSimp PDMat n) (t : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    (affMap n y t).1 = ∑ i, t.weights i • (y i).1 := rfl

/-- From a positive definite form to the trace-one inverse form. -/
def nuSpace (M : PDMat) : Space := ⟨normalize M.1⁻¹, normalize_mem _ M.2.inv⟩

theorem continuous_inv_pd : Continuous fun M : PDMat => M.1⁻¹ := by
  rw [continuous_iff_continuousAt]
  intro M
  have h1 : ContinuousAt (Inv.inv : Mat → Mat) M.1 := by
    refine continuousAt_matrix_inv _ ?_
    have hdet : M.1.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp M.2.isUnit).ne_zero
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hdet
  exact h1.comp continuous_subtype_val.continuousAt

theorem continuous_nuSpace : Continuous nuSpace := by
  refine Continuous.subtype_mk ?_ _
  have hi := continuous_inv_pd
  have htr : Continuous fun M : PDMat => (M.1⁻¹).trace := hi.matrix_trace
  exact (htr.inv₀ fun M => (M.2.inv.trace_pos).ne').smul hi

/-- The embedding of positive definite forms into the bordification: `Q ↦ [Q⁻¹]`. -/
def nu : C(PDMat, Glued) :=
  ⟨fun M => embedding (nuSpace M), continuous_embedding.comp continuous_nuSpace⟩

/-- The singular simplex of an ordered affine simplex of positive definite forms. -/
def affSing {n : ℕ} (y : AffSimp PDMat n) : SingularSimplex (TopCat.of Glued) n :=
  ((TopCat.of Glued).toSSetObjEquiv _).symm (nu.comp (affMap n y))

theorem sum_stdSimplex_map_mat {m n : ℕ} (g : Fin (m + 1) → Fin (n + 1))
    (z : Convexity.StdSimplex ℝ (Fin (m + 1))) (p : Fin (n + 1) → Mat) :
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

theorem affSing_face {n : ℕ} (y : AffSimp PDMat (n + 1)) (j : Fin (n + 2)) :
    (TopCat.toSSet.obj (TopCat.of Glued)).δ j (affSing y) = affSing (AffSimp.face j y) := by
  apply ((TopCat.of Glued).toSSetObjEquiv _).injective
  ext z
  rw [TopCat.toSSetObjEquiv_δ_apply]
  simp only [affSing, Equiv.apply_symm_apply]
  change nu (affMap (n + 1) y (Convexity.StdSimplex.map j.succAbove z)) = nu (affMap n (AffSimp.face j y) z)
  congr 1
  apply Subtype.ext
  rw [affMap_val, affMap_val]
  exact sum_stdSimplex_map_mat j.succAbove z (fun i => (y i).1)

/-- Realization of formal affine chains as singular chains of the bordification. -/
def realize (n : ℕ) : AffChain PDMat n →ₗ[ℚ] (underlyingChains (TopCat.of Glued)).X n :=
  linearCombination ℚ (fun y => sing (TopCat.of Glued) (affSing y))

theorem realize_single {n : ℕ} (y : AffSimp PDMat n) (a : ℚ) :
    realize n (single y a) = a • sing (TopCat.of Glued) (affSing y) := by
  simp [realize]

theorem d_realize (n : ℕ) (c : AffChain PDMat (n + 1)) :
    ((underlyingChains (TopCat.of Glued)).d (n + 1) n).hom (realize (n + 1) c) =
      realize n (dAff PDMat n c) := by
  have h : ((underlyingChains (TopCat.of Glued)).d (n + 1) n).hom ∘ₗ realize (n + 1) =
      realize n ∘ₗ dAff PDMat n := by
    apply Finsupp.lhom_ext
    intro y a
    have e : single y a = a • single y (1 : ℚ) := by simp
    rw [e]
    simp only [LinearMap.comp_apply, map_smul]
    congr 1
    rw [realize_single, one_smul, d_sing, dAff_single, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, realize_single, one_smul, affSing_face, ← Int.cast_smul_eq_zsmul ℚ]
    simp
  exact LinearMap.congr_fun h c

end TernaryPeriodPolynomials.Argument.Lemma33.Retract
