module

public import TernaryPeriodPolynomials.Topology.SingularHomology.AlexanderWhitney
public import TernaryPeriodPolynomials.Topology.SingularHomology.BarycentricSubdivisionHomotopyOperator
public import TernaryPeriodPolynomials.Topology.SingularHomology.AffineBarycentricSubdivision

@[expose] public section


/-!
# Affine singular simplices, Alexander-Whitney faces and linear projections

For a real topological vector space `V`, `affSimp n w` is the affine singular `n`-simplex with vertices
`w : Fin (n+1) → V` (`affMapN`).  Its Alexander-Whitney front and back faces are the affine simplices on the first
`a+1` and last `b+1` vertices (`frontSimplex_affSimp`, `backSimplex_affSimp`), and a continuous linear map `L`
pushes it forward to the affine simplex on the images of the vertices (`pushSimplex_affSimp`).  These are the
bookkeeping lemmas for the Alexander-Whitney cap of a product simplex in `ℝ³ × ℝ²` (orientation transport of Lemma 3.3).

Formalized by Claude Sonnet 5.5.
-/

open SphereOddDegree SphereOddDegree.AlexanderWhitney SphereOddDegree.AffineBarycentricSubdivision
open CategoryTheory
open scoped Simplicial

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport

variable {V W : Type} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul ℝ V]
  [AddCommGroup W] [Module ℝ W] [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul ℝ W]

/-- The affine map from the standard simplex onto the simplex with vertices `w`. -/
def affMapN (n : ℕ) (w : Fin (n + 1) → V) : C(Delta n, V) where
  toFun t := ∑ k, t.weights k • w k
  continuous_toFun := by
    refine continuous_finsetSum _ (fun i _ => ?_)
    exact (Convexity.StdSimplex.continuous_weights_apply ℝ i).smul continuous_const

/-- The affine singular simplex with vertices `w`. -/
def affSimp (n : ℕ) (w : Fin (n + 1) → V) : singularSimplices (TopCat.of V) n :=
  continuousMapAsSingularSimplex (TopCat.of V) n (affMapN n w)

theorem asContinuousMap_affSimp (n : ℕ) (w : Fin (n + 1) → V) :
    singularSimplexAsContinuousMap (TopCat.of V) n (affSimp n w) = affMapN n w := by
  simp [affSimp, singularSimplexAsContinuousMap, continuousMapAsSingularSimplex]

omit [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] in
theorem sum_map_smul {m n : ℕ} (g : Fin (m + 1) → Fin (n + 1)) (x : Delta m) (w : Fin (n + 1) → V) :
    ∑ j, (Convexity.StdSimplex.map g x : Delta n).weights j • w j =
      ∑ i, x.weights i • w (g i) := by
  simp only [SphereOddDegree.AffineBarycentricSubdivision.weights_map_apply]
  simp only [Finset.sum_smul]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ) (g := g)
    (fun i _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [(Finset.mem_filter.mp hi).2]

theorem toSSetObjEquiv_affSimp (n : ℕ) (w : Fin (n + 1) → V) :
    (TopCat.of V).toSSetObjEquiv (Opposite.op (⦋n⦌ : SimplexCategory)) (affSimp n w) = affMapN n w :=
  Equiv.apply_symm_apply _ _

theorem frontSimplex_affSimp (a b : ℕ) (w : Fin (a + b + 1) → V) :
    frontSimplex (TopCat.of V) a b (affSimp (a + b) w) =
      affSimp a (fun i => w (Fin.castLE (by omega) i)) := by
  apply (TopCat.toSSetObjEquiv (TopCat.of V) (Opposite.op (⦋a⦌ : SimplexCategory))).injective
  rw [frontSimplex, toSSetObjEquiv_map_op_naturality]
  apply ContinuousMap.ext
  intro x
  rw [toSSetObjEquiv_affSimp, toSSetObjEquiv_affSimp]
  change ∑ j, (Convexity.StdSimplex.map (frontFace a b).toOrderHom x : Delta (a + b)).weights j • w j =
      ∑ i, x.weights i • w (Fin.castLE (by omega : a + 1 ≤ a + b + 1) i)
  exact sum_map_smul _ x w

theorem backSimplex_affSimp (a b : ℕ) (w : Fin (a + b + 1) → V) :
    backSimplex (TopCat.of V) a b (affSimp (a + b) w) =
      affSimp b (fun i => w ⟨i.val + a, by omega⟩) := by
  apply (TopCat.toSSetObjEquiv (TopCat.of V) (Opposite.op (⦋b⦌ : SimplexCategory))).injective
  rw [backSimplex, toSSetObjEquiv_map_op_naturality]
  apply ContinuousMap.ext
  intro x
  rw [toSSetObjEquiv_affSimp, toSSetObjEquiv_affSimp]
  change ∑ j, (Convexity.StdSimplex.map (backFace a b).toOrderHom x : Delta (a + b)).weights j • w j =
      ∑ i : Fin (b + 1), x.weights i • w ⟨i.val + a, by omega⟩
  exact sum_map_smul _ x w

theorem pushSimplex_affSimp (L : V →ₗ[ℝ] W) (hL : Continuous L) (n : ℕ) (w : Fin (n + 1) → V) :
    pushSimplex (TopCat.ofHom (⟨L, hL⟩ : C(V, W))) n (affSimp n w) = affSimp n (fun i => L (w i)) := by
  apply (TopCat.toSSetObjEquiv (TopCat.of W) (Opposite.op (⦋n⦌ : SimplexCategory))).injective
  rw [toSSetObjEquiv_affSimp]
  apply ContinuousMap.ext
  intro x
  change L ((affMapN n w) x) = (affMapN n fun i => L (w i)) x
  simp [affMapN, map_sum, map_smul]

end TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport
