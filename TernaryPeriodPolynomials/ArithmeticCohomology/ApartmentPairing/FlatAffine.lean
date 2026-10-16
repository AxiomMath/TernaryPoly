module

public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.ResolutionChains
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

@[expose] public section


/-!
# Affine singular simplices in the plane and their boundaries

Singular `n`-simplices of a space `X` of the form `f ∘ (barycentric combination of p)` for a
continuous `f : ℝ × ℝ → X`, with the alternating-face boundary formulas (`d_seg`, `d_tri`) for the
generating chains `sing X σ` of the singular chain complex used by the bordification chains.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory AlgebraicTopology
open TernaryPoly TernaryPoly.EquivariantSingularResolution TernaryPoly.FreeActionLinearization

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33

/-! ### Affine singular simplices in the plane -/

/-- The affine map from the standard simplex onto the simplex spanned by `p` in the plane. -/
def affineMap (n : ℕ) (p : Fin (n + 1) → ℝ × ℝ) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)), ℝ × ℝ) where
  toFun x := ∑ i, x.weights i • p i
  continuous_toFun := by
    refine continuous_finsetSum _ (fun i _ => ?_)
    exact (Convexity.StdSimplex.continuous_weights_apply ℝ i).smul continuous_const

/-- The affine singular simplex `f ∘ (barycentric combination of p)`. -/
def affSimplex {X : TopCat.{0}} (f : C(ℝ × ℝ, X)) {n : ℕ} (p : Fin (n + 1) → ℝ × ℝ) :
    SingularSimplex X n :=
  (X.toSSetObjEquiv _).symm (f.comp (affineMap n p))

theorem sum_stdSimplex_map {m n : ℕ} (g : Fin (m + 1) → Fin (n + 1))
    (z : Convexity.StdSimplex ℝ (Fin (m + 1))) (p : Fin (n + 1) → ℝ × ℝ) :
    ∑ i, (Convexity.StdSimplex.map g z).weights i • p i =
      ∑ k, z.weights k • p (g k) := by
  classical
  have h : ∀ i, (Convexity.StdSimplex.map g z).weights i = ∑ k with g k = i, z.weights k := by
    intro i
    rw [Convexity.StdSimplex.weights_map, Finsupp.mapDomain_fintype, Finsupp.coe_finsetSum,
      Finset.sum_apply, Finset.sum_filter]
    exact Finset.sum_congr rfl fun k _ => Finsupp.single_apply
  simp_rw [h, Finset.sum_smul]
  rw [← Finset.sum_fiberwise Finset.univ g (fun k => z.weights k • p (g k))]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k hk => ?_))
  rw [(Finset.mem_filter.mp hk).2]

theorem affSimplex_face {X : TopCat.{0}} (f : C(ℝ × ℝ, X)) {n : ℕ} (p : Fin (n + 2) → ℝ × ℝ)
    (j : Fin (n + 2)) :
    (TopCat.toSSet.obj X).δ j (affSimplex f p) = affSimplex f (fun i => p (j.succAbove i)) := by
  apply (X.toSSetObjEquiv _).injective
  ext z
  rw [TopCat.toSSetObjEquiv_δ_apply]
  simp only [affSimplex, Equiv.apply_symm_apply]
  change f (∑ i, (Convexity.StdSimplex.map j.succAbove z).weights i • p i) =
    f (∑ k, z.weights k • p (j.succAbove k))
  rw [sum_stdSimplex_map]

/-- The singular chain of one singular simplex. -/
def sing (X : TopCat.{0}) {n : ℕ} (σ : SingularSimplex X n) : (underlyingChains X).X n :=
  ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℚ ℚ) σ).hom 1

theorem d_sing (X : TopCat.{0}) {n : ℕ} (σ : SingularSimplex X (n + 1)) :
    ((underlyingChains X).d (n + 1) n).hom (sing X σ) =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) • sing X ((TopCat.toSSet.obj X).δ i σ) := by
  have h := congrArg (fun f => f.hom (1 : ℚ))
    ((TopCat.toSSet.obj X).ιChainComplex_d (R := ModuleCat.of ℚ ℚ) σ)
  simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply,
    LinearMap.smul_apply] at h
  convert h using 1 <;> rfl

/-- A point as a singular `0`-simplex. -/
def vert {X : TopCat.{0}} (f : C(ℝ × ℝ, X)) (a : ℝ × ℝ) : SingularSimplex X 0 := affSimplex f ![a]

/-- The affine segment from `a` to `b`. -/
def seg {X : TopCat.{0}} (f : C(ℝ × ℝ, X)) (a b : ℝ × ℝ) : SingularSimplex X 1 :=
  affSimplex f ![a, b]

/-- The affine triangle with vertices `a, b, c`. -/
def tri {X : TopCat.{0}} (f : C(ℝ × ℝ, X)) (a b c : ℝ × ℝ) : SingularSimplex X 2 :=
  affSimplex f ![a, b, c]

theorem d_seg {X : TopCat.{0}} (f : C(ℝ × ℝ, X)) (a b : ℝ × ℝ) :
    ((underlyingChains X).d 1 0).hom (sing X (seg f a b)) = sing X (vert f b) - sing X (vert f a) := by
  rw [d_sing, Fin.sum_univ_two]
  have h0 : (TopCat.toSSet.obj X).δ 0 (seg f a b) = vert f b := by
    rw [seg, affSimplex_face]
    congr 1
  have h1 : (TopCat.toSSet.obj X).δ 1 (seg f a b) = vert f a := by
    rw [seg, affSimplex_face]
    congr 1
    funext i
    fin_cases i
    rfl
  rw [h0, h1]
  simp [sub_eq_add_neg]

theorem d_tri {X : TopCat.{0}} (f : C(ℝ × ℝ, X)) (a b c : ℝ × ℝ) :
    ((underlyingChains X).d 2 1).hom (sing X (tri f a b c)) =
      sing X (seg f b c) - sing X (seg f a c) + sing X (seg f a b) := by
  rw [d_sing, Fin.sum_univ_three]
  have h0 : (TopCat.toSSet.obj X).δ 0 (tri f a b c) = seg f b c := by
    rw [tri, affSimplex_face]
    congr 1
  have h1 : (TopCat.toSSet.obj X).δ 1 (tri f a b c) = seg f a c := by
    rw [tri, affSimplex_face]
    congr 1
    funext i
    fin_cases i <;> rfl
  have h2 : (TopCat.toSSet.obj X).δ 2 (tri f a b c) = seg f a b := by
    rw [tri, affSimplex_face]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [h0, h1, h2]
  simp [sub_eq_add_neg, add_comm]


theorem affineMap_zero (a : ℝ × ℝ) (z : Convexity.StdSimplex ℝ (Fin 1)) : affineMap 0 ![a] z = a := by
  simp only [affineMap, ContinuousMap.coe_mk]
  simp

end TernaryPeriodPolynomials.Argument.Lemma33
