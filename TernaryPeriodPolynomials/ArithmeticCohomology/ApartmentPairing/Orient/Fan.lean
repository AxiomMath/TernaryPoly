module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Orient.AffineSimplex

@[expose] public section


/-!
# The fan theorem: the local degree of a cone chain of affine simplices

For a formal affine 3-chain `z` of positive definite forms and the linear map `Lc`
(`Q ↦ (-Q₁₂, -Q₂₃, -Q₁₃)`), `fan_degree` computes the local degree `degRel (realizeVia Lc 3 z)` at
the origin of `ℝ³`: if the boundary of the chain stays at distance `≥ ρ` from the origin and some point
`P` of norm `< ρ` lies in the interior of exactly one (positively oriented) simplex `y₀` of `z` and
outside all other simplices, then the degree is `z y₀ * lamPos`.  The proof moves `P` to the origin by
the homotopy `x ↦ x - sP` of pairs (`relCls_homotopy`); the simplices not containing `P` become chains
in the punctured space, and the remaining one is a tetrahedron around the origin, to which the
universality of `lamPos` (`degAff_universal`) applies.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical
open TernaryPoly TernaryPoly.SymmetricSpacePositive
  CategoryTheory Limits HomologicalComplex TernaryPoly.RationalSingularAugmentation
  TernaryPoly.RationalRelativeSingular TernaryPoly.ContractibleSingularHomology
  TernaryPoly.FreeActionLinearization TernaryPoly.EuclideanLocalHomology TernaryPoly.RationalSphere
  TernaryPeriodPolynomials.Argument.Lemma33
  TernaryPeriodPolynomials.Argument.Lemma33.Retract
  TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree

namespace TernaryPeriodPolynomials.Argument.Lemma33.Orient

/-! ### Translation of the origin -/

/-- Translation by `-P`. -/
def translC (P : E3) : C(E3, E3) where
  toFun x := x - P
  continuous_toFun := continuous_id.sub continuous_const

/-- The vertices of the Euclidean image of a formal simplex of forms. -/
def wy (y : AffSimp PDMat 3) : Fin (3 + 1) → E3 := fun k => Lc (y k)

theorem Lc_affMap {n : ℕ} (y : AffSimp PDMat n) (t : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    Lc (affMap n y t) = ∑ k, t.weights k • Lc (y k) := by
  ext i
  fin_cases i <;>
    simp [Lc, Lraw, affMap_val, Matrix.sum_apply, Finset.sum_neg_distrib, Matrix.smul_apply]

theorem affEMap_sub (w : Fin (3 + 1) → E3) (P : E3) (t : Dl) :
    affEMap (fun k => w k - P) t = affEMap w t - P := by
  simp only [affEMap, ContinuousMap.coe_mk, smul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_smul, show ∑ k, t.weights k = 1 from t.total_of_fintype, one_smul]

theorem affVia_transl (P : E3) (y : AffSimp PDMat 3) :
    affVia ((translC P).comp Lc) y = simpOf (affEMap (fun k => wy y k - P)) := by
  apply ((TopCat.of E3).toSSetObjEquiv _).injective
  refine ContinuousMap.ext (fun t => ?_)
  rw [affVia_apply]
  change translC P (Lc (affMap 3 y t)) = affEMap (fun k => wy y k - P) t
  rw [affEMap_sub]
  change Lc (affMap 3 y t) - P = _
  rw [Lc_affMap]
  rfl


/-! ### The translated chain -/

theorem chain_transl (P : E3) (z : AffChain PDMat 3) :
    ((chainMap (translC P)).f 3).hom (realizeVia Lc 3 z) =
      ∑ y ∈ z.support, z y • sing (TopCat.of E3) (simpOf (affEMap (fun k => wy y k - P))) := by
  rw [chainMap_realizeVia, realizeVia, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [affVia_transl]

theorem relπ_sing_zero (f : C(Dl, E3)) (h : ∀ t, f t ≠ 0) :
    ((relπ (Punctured 3)).f 3).hom (sing (TopCat.of E3) (simpOf f)) = 0 := by
  have hm := sing_mem_range (Punctured 3) (simpOf f) (by
    intro t
    have : (TopCat.of E3).toSSetObjEquiv _ (simpOf f) t = f t := by simp [simpOf]
    rw [this]
    exact h t)
  obtain ⟨b, hb⟩ := hm
  rw [← hb]
  exact congrArg (fun m => m.hom b) (congrArg (fun m => m.f 3) (cokernel.condition (inclusion (Punctured 3))))

theorem translate_maps (P : E3) (ρ : ℝ) (hP : ‖P‖ < ρ) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (x : E3)
    (hx : ρ ≤ ‖x‖) : x - s • P ≠ 0 := by
  intro h
  have h1 : x = s • P := sub_eq_zero.mp h
  have h2 : ‖x‖ ≤ ‖P‖ := by
    rw [h1, norm_smul, Real.norm_of_nonneg hs0]
    nlinarith [norm_nonneg P]
  linarith


theorem edgeDet_sub (w : Fin (3 + 1) → E3) (P : E3) : edgeDet (fun k => w k - P) = edgeDet w := by
  unfold edgeDet
  congr 1
  ext i j
  simp

/-- **The fan theorem** (locality of the local degree).  Let `z` be a formal affine 3-chain of forms
whose linearization `C = realizeVia Lc 3 z` has boundary at distance `≥ ρ` from the origin, and let
`P` be a point of norm `< ρ` lying in the interior of exactly one simplex `y₀` of `z`, which is
positively oriented.  Then the local degree of `C` at the origin is the coefficient of `y₀`
times the universal number `lamPos`. -/
theorem fan_degree (z : AffChain PDMat 3) (ρ : ℝ)
    (hbd : ∀ y ∈ (dAff PDMat 2 z).support, ∀ t, ρ ≤ ‖Lc (affMap 2 y t)‖)
    (P : E3) (hP : ‖P‖ < ρ) (y₀ : AffSimp PDMat 3)
    (hout : ∀ y ∈ z.support, y ≠ y₀ → ∀ t, affEMap (wy y) t ≠ P)
    (σ : Fin (3 + 1) → ℝ) (hσ : ∀ k, 0 < σ k) (hσ1 : ∑ k, σ k = 1)
    (hσP : ∑ k, σ k • wy y₀ k = P) (hdet : 0 < edgeDet (wy y₀)) :
    ∃ h : RelCycle (Punctured 3) (realizeVia Lc 3 z), degRel (realizeVia Lc 3 z) h = z y₀ * lamPos := by
  set C : AbF.obj ((chains E3).X 3) := realizeVia Lc 3 z with hC
  set S : Set E3 := {x | ρ ≤ ‖x‖} with hS
  have hCS : RelCycle S C := by
    apply relCycle_of_mem_range
    have h : ((chains E3).d 3 2).hom C = realizeVia Lc 2 (dAff PDMat 2 z) := d_realizeVia Lc 2 z
    rw [h]
    exact realizeVia_mem_range Lc S 2 _ (fun y hy t => hbd y hy t)
  have hmaps : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ x ∈ S, x - s • P ≠ 0 := fun s h0 h1 x hx =>
    translate_maps P ρ hP s h0 h1 x hx
  have hid : Set.MapsTo (ContinuousMap.id E3) S (Punctured 3) := fun x hx h0 => by
    have := hmaps 0 le_rfl zero_le_one x hx
    exact this (by simpa using h0)
  have htr : Set.MapsTo (translC P) S (Punctured 3) := fun x hx h0 => by
    have := hmaps 1 zero_le_one le_rfl x hx
    exact this (by simpa [translC] using h0)
  let Hh : ContinuousMap.Homotopy (ContinuousMap.id E3) (translC P) :=
    { toFun := fun p => p.2 - (p.1 : ℝ) • P
      continuous_toFun := continuous_snd.sub (continuous_subtype_val.comp continuous_fst |>.smul continuous_const)
      map_zero_left := fun x => by simp
      map_one_left := fun x => by simp [translC] }
  have hC1 : RelCycle (Punctured 3) (AbF.map ((chainMap (ContinuousMap.id E3)).f 3) C) :=
    RelCycle.map _ S _ hid C hCS
  have hC2 : RelCycle (Punctured 3) (AbF.map ((chainMap (translC P)).f 3) C) :=
    RelCycle.map _ S _ htr C hCS
  have key := relCls_homotopy (ContinuousMap.id E3) (translC P) S (Punctured 3) hid htr Hh
    (fun s x hx h0 => hmaps s s.2.1 s.2.2 x hx h0) C hCS hC1 hC2
  have hid_eq : AbF.map ((chainMap (ContinuousMap.id E3)).f 3) C = C := by
    simp [chainMap_id]
  have hC0 : RelCycle (Punctured 3) C := by rw [← hid_eq]; exact hC1
  refine ⟨hC0, ?_⟩
  have step1 : degRel C hC0 = degRel (AbF.map ((chainMap (translC P)).f 3) C) hC2 := by
    unfold degRel
    congr 1
    rw [← key]
    exact relCls_congr _ _ _ _ _ hid_eq.symm
  rw [step1]
  -- the translated simplices
  have hfaces : ∀ y ∈ z.support, y ≠ y₀ → ∀ t, affEMap (fun k => wy y k - P) t ≠ 0 := by
    intro y hy hne t h0
    rw [affEMap_sub] at h0
    exact hout y hy hne t (sub_eq_zero.mp h0)
  have hrel : ∑ k, σ k • (wy y₀ k - P) = 0 := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hσ1, one_smul, hσP, sub_self]
  have hdet' : 0 < edgeDet (fun k => wy y₀ k - P) := by rw [edgeDet_sub]; exact hdet
  have hfa := facesAvoid_of_rel _ σ hσ hrel hdet'
  have hs0 : RelCycle (Punctured 3) (sing (TopCat.of E3) (simpOf (affEMap (fun k => wy y₀ k - P)))) :=
    simplex_relCycle _ hfa
  have hscal := degRel_of_relπ_eq (AbF.map ((chainMap (translC P)).f 3) C)
    (sing (TopCat.of E3) (simpOf (affEMap (fun k => wy y₀ k - P)))) hC2 hs0 (z y₀) (by
      change ((relπ (Punctured 3)).f 3).hom (((chainMap (translC P)).f 3).hom (realizeVia Lc 3 z)) = _
      rw [chain_transl, map_sum]
      simp only [map_smul]
      rw [Finset.sum_eq_single y₀]
      · intro y hy hne
        rw [relπ_sing_zero _ (hfaces y hy hne), smul_zero]
      · intro hy
        rw [Finsupp.notMem_support_iff.mp hy, zero_smul])
  rw [hscal]
  congr 1
  exact degAff_universal _ hfa σ hσ hrel hdet'

end TernaryPeriodPolynomials.Argument.Lemma33.Orient
