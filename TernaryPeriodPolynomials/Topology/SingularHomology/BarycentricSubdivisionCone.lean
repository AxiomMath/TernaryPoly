module

/-
SPDX-License-Identifier: Apache-2.0
Adapted from akopjan/HamSandwich.
Original module: HamSandwich.SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionCone
Ported to the Lean 4.33.0.
-/
public import TernaryPeriodPolynomials.Topology.SingularHomology.BarycentricBoundaryCancellation
public import TernaryPeriodPolynomials.Topology.SingularHomology.BarycentricSubdivisionChainMap
public import Mathlib

@[expose] public section


/-!
# The cone operator for the barycentric subdivision homotopy

This file defines the affine **cone over a point** construction at the level of
the topological standard simplices, bundles it as a continuous map, extends it to
singular chains of `Δⁿ`, and proves the boundary identity

```text
∂ Cone_v(c) = c - Cone_v(∂ c)
```

in the exact degree-indexed form needed for the recursive proof that barycentric
subdivision is chain-homotopic to the identity.

For a point `v : Δⁿ` and a (continuous) `k`-simplex `τ : Δᵏ → Δⁿ`, the cone
`Cone_v(τ) : Δᵏ⁺¹ → Δⁿ` sends the new apex vertex to `v` and the remaining
vertices to the vertices of `τ`.  In barycentric coordinates, writing
`x = (t, x₁, …, x_{k+1})` for a point of `Δᵏ⁺¹`,

```text
Cone_v(τ)(x) = t · v + (1 - t) · τ( x₁/(1-t), …, x_{k+1}/(1-t) )
```

away from `t = 1`, and `= v` at `t = 1` (the apex).

This file does **not** assert the barycentric subdivision homotopy itself; it only
builds the cone operator and its boundary formula.
-/

open scoped BigOperators
open CategoryTheory AlgebraicTopology Simplicial SimplexCategory Limits
open Finset Convexity

namespace SphereOddDegree
namespace AffineBarycentricSubdivision

/-! ## 1. The normalized tail of a point of `Δᵏ⁺¹` -/

/-- The (un-normalized) coordinate function of the normalized tail of a point
`x : Δᵏ⁺¹`: the `i`-th coordinate is `x_{i+1} / (1 - x₀)`.  (Lean's `/0 = 0`
convention makes this total; the genuine simplex point is `coneTail` below.) -/
noncomputable def coneTailFun {k : ℕ} (x : Delta (k + 1)) : Fin (k + 1) → ℝ :=
  fun i => x.weights i.succ / (1 - x.weights 0)

/-
When `x₀ ≠ 1`, the normalized tail coordinates form a genuine point of `Δᵏ`.
-/
theorem coneTailFun_mem {k : ℕ} (x : Delta (k + 1))
    (hx : x.weights 0 ≠ 1) :
    (∀ i, 0 ≤ coneTailFun x i) ∧ ∑ i, coneTailFun x i = 1 := by
  refine' ⟨ fun i => _, _ ⟩;
  · exact div_nonneg ( x.weights_nonneg _ ) ( sub_nonneg.2 ( x.weights_apply_le_one 0 ) );
  · have h_sum : ∑ i : Fin (k + 1), x.weights i.succ = 1 - x.weights 0 := by
      have hs := x.total_of_fintype
      rw [Fin.sum_univ_succ] at hs
      exact eq_sub_of_add_eq' hs
    unfold coneTailFun;
    rw [ ← Finset.sum_div, h_sum, div_self ( sub_ne_zero_of_ne <| Ne.symm hx ) ]

/-- The normalized tail of `x : Δᵏ⁺¹`, as a point of `Δᵏ`.  Away from the apex
(`x₀ = 1`) it is the genuine normalized tail; at the apex it is given an
irrelevant fallback value. -/
noncomputable def coneTail {k : ℕ} (x : Delta (k + 1)) : Delta k :=
  if h : x.weights 0 = 1 then StdSimplex.single (0 : Fin (k + 1))
  else ofWeights (coneTailFun x) (coneTailFun_mem x h).1 (coneTailFun_mem x h).2

/-
Coordinate formula for `coneTail` away from the apex.
-/
theorem coneTail_apply {k : ℕ} (x : Delta (k + 1))
    (hx : x.weights 0 ≠ 1) (i : Fin (k + 1)) :
    (coneTail x).weights i = x.weights i.succ / (1 - x.weights 0) := by
  simp [coneTail, hx, coneTailFun]

/-! ## 2. The affine cone map -/

/-- The coordinate function of the cone of `τ` over `v` at the point `x`. -/
noncomputable def affineConeMapFun {n k : ℕ} (v : Delta n) (τ : Delta k → Delta n)
    (x : Delta (k + 1)) : Fin (n + 1) → ℝ :=
  fun j => x.weights 0 * v.weights j + (1 - x.weights 0) * (τ (coneTail x)).weights j

/-
The cone coordinate function always defines a point of `Δⁿ`.
-/
theorem affineConeMapFun_mem {n k : ℕ} (v : Delta n) (τ : Delta k → Delta n)
    (x : Delta (k + 1)) :
    (∀ j, 0 ≤ affineConeMapFun v τ x j) ∧ ∑ j, affineConeMapFun v τ x j = 1 := by
  refine' ⟨ fun j => _, _ ⟩;
  · exact add_nonneg ( mul_nonneg ( x.weights_nonneg 0 ) ( v.weights_nonneg j ) ) ( mul_nonneg ( sub_nonneg.mpr ( x.weights_apply_le_one 0 ) ) ( ( τ ( coneTail x ) ).weights_nonneg j ) );
  · unfold affineConeMapFun;
    simp +decide [ Finset.sum_add_distrib, ← Finset.mul_sum _ _ _ ]

/-- **The affine cone map** `Cone_v(τ) : Δᵏ⁺¹ → Δⁿ`. -/
noncomputable def affineConeMap {n k : ℕ} (v : Delta n) (τ : Delta k → Delta n) :
    Delta (k + 1) → Delta n :=
  fun x => ofWeights (affineConeMapFun v τ x) (affineConeMapFun_mem v τ x).1
    (affineConeMapFun_mem v τ x).2

@[simp] theorem affineConeMap_coord {n k : ℕ} (v : Delta n) (τ : Delta k → Delta n)
    (x : Delta (k + 1)) (j : Fin (n + 1)) :
    (affineConeMap v τ x).weights j
      = x.weights 0 * v.weights j + (1 - x.weights 0) * (τ (coneTail x)).weights j := rfl

/-! ## 3. Vertex formulas -/

/-
The cone sends the apex vertex `0` to `v`.
-/
theorem affineConeMap_vertex_zero {n k : ℕ} (v : Delta n) (τ : Delta k → Delta n) :
    affineConeMap v τ (StdSimplex.single (0 : Fin (k + 1 + 1))) = v := by
  ext j
  simp [affineConeMap_coord]

/-
The cone sends the vertex `i+1` to the vertex `τ(i)` of `τ`.
-/
theorem affineConeMap_vertex_succ {n k : ℕ} (v : Delta n) (τ : Delta k → Delta n)
    (i : Fin (k + 1)) :
    affineConeMap v τ (StdSimplex.single i.succ) = τ (StdSimplex.single i) := by
  have h0 : (StdSimplex.single (R := ℝ) i.succ).weights 0 = 0 := by
    simp [Fin.succ_ne_zero]
  have ht : coneTail (StdSimplex.single (R := ℝ) i.succ) = StdSimplex.single i := by
    ext t
    rw [coneTail_apply _ (by rw [h0]; norm_num), h0, sub_zero, div_one]
    simp [Finsupp.single_apply]
  ext j
  rw [affineConeMap_coord, h0, ht]
  ring

/-! ## 4. Continuity and the bundled continuous cone map -/

/-
`coneTail` is continuous away from the apex.
-/
theorem continuousOn_coneTail {k : ℕ} :
    ContinuousOn (coneTail (k := k)) {x | (x : Delta (k + 1)).weights 0 ≠ 1} := by
  -- Write `S := {x : Delta (k+1) | x₀ ≠ 1}`.
  set S : Set (Delta (k + 1)) := {x | x.weights 0 ≠ 1};
  have h_cont_tail : ContinuousOn (fun x : Delta (k + 1) => ⇑(coneTail x).weights) S := by
    refine ContinuousOn.congr (f := fun x i => x.weights i.succ / (1 - x.weights 0)) ?_ ?_
    · exact continuousOn_pi.mpr fun i => ContinuousOn.div
        (StdSimplex.continuous_weights_apply ℝ _).continuousOn
        (continuousOn_const.sub (StdSimplex.continuous_weights_apply ℝ _).continuousOn)
        fun x hx => sub_ne_zero_of_ne <| Ne.symm hx
    · intro x hx; funext i; exact coneTail_apply x hx i
  rw [ continuousOn_iff_continuous_domRestrict ] at *;
  exact (StdSimplex.isEmbedding_toFun_comp_weights ℝ _).continuous_iff.mpr h_cont_tail

/-
The cone of a continuous `τ` over `v` is continuous.
-/
theorem continuous_affineConeMap {n k : ℕ} (v : Delta n) (τ : C(Delta k, Delta n)) :
    Continuous (affineConeMap v (⇑τ)) := by
  refine (StdSimplex.isEmbedding_toFun_comp_weights ℝ _).continuous_iff.mpr ?_
  refine' continuous_pi fun j => _;
  -- The function $B(x) = (1 - x 0) * ((τ (coneTail x)) j)$ is continuous because it is a product of continuous functions.
  have hB_cont : Continuous (fun x : Delta (k + 1) =>
      (1 - x.weights 0) * (τ (coneTail x)).weights j) := by
    refine' continuous_iff_continuousAt.mpr _;
    intro x;
    by_cases hx : x.weights 0 = 1;
    · refine' tendsto_iff_norm_sub_tendsto_zero.mpr _;
      refine' squeeze_zero ( fun _ => norm_nonneg _ ) ( fun e => _ ) ( Continuous.tendsto' ( show Continuous fun e : Delta ( k + 1 ) => abs (1 - e.weights 0) from Continuous.abs <| continuous_const.sub <| StdSimplex.continuous_weights_apply ℝ 0 ) _ _ <| by aesop );
      simp +decide [ hx ];
      exact mul_le_of_le_one_right ( abs_nonneg _ ) ( abs_le.mpr ⟨ by linarith [ ( τ ( coneTail e ) ).weights_nonneg j ], by linarith [ ( τ ( coneTail e ) ).weights_apply_le_one j ] ⟩ );
    · refine' ContinuousAt.mul _ _;
      · exact ContinuousAt.sub continuousAt_const (StdSimplex.continuous_weights_apply ℝ 0).continuousAt
      · exact (StdSimplex.continuous_weights_apply ℝ j).continuousAt.comp
          (τ.continuous.continuousAt.comp (continuousOn_coneTail.continuousAt
            (IsOpen.mem_nhds (isOpen_compl_singleton.preimage
              (StdSimplex.continuous_weights_apply ℝ 0)) hx)))
  convert! Continuous.add ( Continuous.mul ( StdSimplex.continuous_weights_apply ℝ 0 ) continuous_const ) hB_cont using 1

/-- **The bundled continuous cone map** `Cone_v(τ) : C(Δᵏ⁺¹, Δⁿ)`. -/
noncomputable def affineConeContinuousMap {n k : ℕ} (v : Delta n) (τ : C(Delta k, Delta n)) :
    C(Delta (k + 1), Delta n) :=
  ⟨affineConeMap v (⇑τ), continuous_affineConeMap v τ⟩

@[simp] theorem affineConeContinuousMap_apply {n k : ℕ} (v : Delta n) (τ : C(Delta k, Delta n))
    (x : Delta (k + 1)) : affineConeContinuousMap v τ x = affineConeMap v (⇑τ) x := rfl

/-! ## 5. Face formulas -/

/-- On the image of the face injection, the coface retains the original coordinate. -/
theorem cofaceTop_apply_image (n : ℕ) (j : Fin (n + 2)) (y : Delta n) (i : Fin (n + 1)) :
    (cofaceTop n j y).weights (j.succAbove i) = y.weights i := by
  show (StdSimplex.map (Fin.succAbove j) y).weights (j.succAbove i) = y.weights i
  rw [weights_map_apply, Finset.sum_eq_single i]
  · intro b hb hbi
    exact (hbi (Fin.succAbove_right_injective (Finset.mem_filter.mp hb).2)).elim
  · intro h
    exact (h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)).elim

/-
**Face opposite the apex.** Restricting the cone along the `0`-th coface
recovers the base simplex `τ`.
-/
theorem cone_face_zero {n k : ℕ} (v : Delta n) (τ : Delta k → Delta n) :
    (fun y : Delta k => affineConeMap v τ (cofaceTop k 0 y)) = τ := by
  funext y
  have h0 : (cofaceTop k 0 y).weights 0 = 0 := cofaceTop_apply_base k 0 y
  have ht : coneTail (cofaceTop k 0 y) = y := by
    ext i
    rw [coneTail_apply _ (by rw [h0]; norm_num), h0, sub_zero, div_one]
    simpa using cofaceTop_apply_image k 0 y i
  ext j
  rw [affineConeMap_coord, h0, ht]
  ring

/-- Internal cofaces retain the apex coordinate. -/
theorem cofaceTop_succ_zero (k : ℕ) (j : Fin (k + 2)) (y : Delta (k + 1)) :
    (cofaceTop (k + 1) j.succ y).weights 0 = y.weights 0 := by
  simpa only [Fin.succ_succAbove_zero] using cofaceTop_apply_image (k + 1) j.succ y 0

/-
**Tail commutes with internal cofaces.** For `y` away from the apex, the
normalized tail of `cofaceTop (k+1) (j+1) y` is the `j`-th coface of the
normalized tail of `y`.
-/
theorem coneTail_cofaceTop_succ {k : ℕ} (j : Fin (k + 1 + 1)) (y : Delta (k + 1))
    (hy : y.weights 0 ≠ 1) :
    coneTail (cofaceTop (k + 1) j.succ y) = cofaceTop k j (coneTail y) := by
  have h0 := cofaceTop_succ_zero k j y
  have hn : (cofaceTop (k + 1) j.succ y).weights 0 ≠ 1 := by rw [h0]; exact hy
  ext i
  rw [coneTail_apply _ hn, h0]
  refine Fin.succAboveCases j ?_ (fun t => ?_) i
  · rw [cofaceTop_apply_base, cofaceTop_apply_base, zero_div]
  · rw [←Fin.succ_succAbove_succ, cofaceTop_apply_image, cofaceTop_apply_image,
      coneTail_apply y hy]

/-
**Every other face.** Restricting the cone along the `(j+1)`-th coface gives
the cone over the `j`-th face of `τ`.
-/
theorem cone_face_succ {n k : ℕ} (v : Delta n) (τ : Delta (k + 1) → Delta n)
    (j : Fin (k + 1 + 1)) :
    (fun y : Delta (k + 1) => affineConeMap v τ (cofaceTop (k + 1) j.succ y))
      = (fun y : Delta (k + 1) => affineConeMap v (fun z : Delta k => τ (cofaceTop k j z)) y) := by
  funext y
  ext c
  simp only [affineConeMap_coord, cofaceTop_succ_zero]
  by_cases hy : y.weights 0 = 1
  · simp [hy]
  · rw [coneTail_cofaceTop_succ j y hy]

/-! ## 6. The cone on singular simplices and chains of `Δⁿ` -/

/-- The cone of a singular `k`-simplex of `Δⁿ` over `v`, as a singular
`(k+1)`-simplex of `Δⁿ`. -/
noncomputable def coneSimplex (n k : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) k) :
    singularSimplices (TopCat.of (Delta n)) (k + 1) :=
  continuousMapAsSingularSimplex (TopCat.of (Delta n)) (k + 1)
    (affineConeContinuousMap v (singularSimplexAsContinuousMap (TopCat.of (Delta n)) k σ))

/-- The continuous map underlying `coneSimplex`. -/
theorem coneSimplex_continuousMap (n k : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) k) :
    singularSimplexAsContinuousMap (TopCat.of (Delta n)) (k + 1) (coneSimplex n k v σ)
      = affineConeContinuousMap v (singularSimplexAsContinuousMap (TopCat.of (Delta n)) k σ) := by
  rw [coneSimplex, singularSimplexAsContinuousMap, continuousMapAsSingularSimplex,
    Equiv.apply_symm_apply]

/-- The `0`-simplex with value `v` at every vertex. -/
noncomputable def constSimplex0 (n : ℕ) (v : Delta n) :
    singularSimplices (TopCat.of (Delta n)) 0 :=
  continuousMapAsSingularSimplex (TopCat.of (Delta n)) 0
    (ContinuousMap.const (Delta 0) v)

/-
**Apex face of `coneSimplex`.** The `0`-th boundary face of the cone of `σ`
is `σ`.
-/
theorem coneSimplex_face_zero (n k : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) k) :
    AlexanderWhitney.faceSimplex (TopCat.of (Delta n)) k 0 (coneSimplex n k v σ) = σ := by
  have h_cont : (singularSimplexAsContinuousMap (TopCat.of (Delta n)) (k + 1) (coneSimplex n k v σ)).comp (cofaceTop k 0) = singularSimplexAsContinuousMap (TopCat.of (Delta n)) k σ := by
    ext y : 1
    rw [ContinuousMap.comp_apply, coneSimplex_continuousMap, affineConeContinuousMap_apply]
    exact congr_fun (cone_face_zero v _) y
  apply singularSimplices_ext;
  convert! h_cont using 1

/-
**Internal faces of `coneSimplex`.** The `(j+1)`-th boundary face of the cone
of `σ` is the cone of the `j`-th boundary face of `σ`.
-/
theorem coneSimplex_face_succ (n k : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) (k + 1)) (j : Fin (k + 1 + 1)) :
    AlexanderWhitney.faceSimplex (TopCat.of (Delta n)) (k + 1) j.succ (coneSimplex n (k + 1) v σ)
      = coneSimplex n k v (AlexanderWhitney.faceSimplex (TopCat.of (Delta n)) k j σ) := by
  apply singularSimplices_ext; simp [faceSimplex_continuousMap, coneSimplex_continuousMap];
  ext y : 1; simp [affineConeContinuousMap_apply, ContinuousMap.comp_apply];
  convert! congrFun ( cone_face_succ v ( singularSimplexAsContinuousMap ( TopCat.of ( Delta n ) ) (k + 1) σ ) j ) y using 1

/-
**The second face of a 1-dimensional cone.** The `1`-st boundary face of the
cone of a `0`-simplex `σ` is the simplex with value `v` at every vertex.
-/
theorem coneSimplex_face_one_zero (n : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) 0) :
    AlexanderWhitney.faceSimplex (TopCat.of (Delta n)) 0 1 (coneSimplex n 0 v σ)
      = constSimplex0 n v := by
  apply singularSimplices_ext;
  rw [ faceSimplex_continuousMap, coneSimplex_continuousMap ];
  ext y : 1
  simp only [ContinuousMap.comp_apply, affineConeContinuousMap_apply]
  have h1 : (cofaceTop 0 1 y).weights 0 = 1 := by
    have h := cofaceTop_apply_image 0 1 y 0
    rw [Fin.succAbove_of_castSucc_lt _ _ (by decide)] at h
    rw [show (0 : Fin 2) = Fin.castSucc 0 from rfl, h]
    simp
  ext j
  rw [affineConeMap_coord, h1]
  simp [singularSimplexAsContinuousMap, constSimplex0, continuousMapAsSingularSimplex]

/-! ## 7. The cone on chains -/

/-- The cone of a basis generator `[σ]`. -/
noncomputable def coneGenerator (R : Type) [CommRing R] (n k : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) k) :
    singularChainGroup R (TopCat.of (Delta n)) (k + 1) :=
  chainGenerator R (TopCat.of (Delta n)) (k + 1) (coneSimplex n k v σ)

/-- The `R`-linear map `R → C_{k+1}(Δⁿ; R)` sending `1` to `coneGenerator … σ`. -/
noncomputable def coneGeneratorHom (R : Type) [CommRing R] (n k : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) k) :
    ModuleCat.of R R ⟶ singularChainGroup R (TopCat.of (Delta n)) (k + 1) :=
  ModuleCat.ofHom
    { toFun := fun r => r • coneGenerator R n k v σ
      map_add' := by intro r s; exact add_smul r s _
      map_smul' := by intro a r; exact mul_smul a r _ }

/-- **The cone operator on chains** `Cone_v : C_k(Δⁿ; R) → C_{k+1}(Δⁿ; R)`. -/
noncomputable def coneLinearMap (R : Type) [CommRing R] (n k : ℕ) (v : Delta n) :
    singularChainGroup R (TopCat.of (Delta n)) k
      ⟶ singularChainGroup R (TopCat.of (Delta n)) (k + 1) :=
  Sigma.desc fun σ : singularSimplices (TopCat.of (Delta n)) k => coneGeneratorHom R n k v σ

/-
The cone operator has the prescribed value on a basis generator.
-/
theorem coneLinearMap_generator (R : Type) [CommRing R] (n k : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) k) :
    (coneLinearMap R n k v).hom (chainGenerator R (TopCat.of (Delta n)) k σ)
      = coneGenerator R n k v σ := by
  convert! one_smul _ _;
  convert! congr_arg ( fun f : ModuleCat.of R R ⟶ singularChainGroup R ( TopCat.of ( Delta n ) ) ( k + 1 ) => f.hom 1 ) ( Sigma.ι_comp_desc ( fun σ => coneGeneratorHom R n k v σ ) σ ) using 1

/-! ## 8. The boundary formula -/

/-
**Boundary of the cone (base degree).** In degree `0`,
`∂ Cone_v([σ]) = [σ] - [const_v]`.
-/
theorem singularBoundary_coneGenerator_zero (R : Type) [CommRing R] (n : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) 0) :
    (singularBoundary R (TopCat.of (Delta n)) 0).hom (coneGenerator R n 0 v σ)
      = chainGenerator R (TopCat.of (Delta n)) 0 σ
        - chainGenerator R (TopCat.of (Delta n)) 0 (constSimplex0 n v) := by
  convert! singularBoundary_chainGenerator_formula R ( TopCat.of ( Delta n ) ) 0 ( coneSimplex n 0 v σ ) using 1;
  rw [ Fin.sum_univ_two ] ; norm_num [ sub_eq_add_neg ];
  rw [ coneSimplex_face_zero, coneSimplex_face_one_zero ]

/-
**Boundary of the cone (successor degree).** For `σ` of degree `m+1`,
`∂ Cone_v([σ]) = [σ] - Cone_v(∂[σ])`.
-/
theorem singularBoundary_coneGenerator_succ (R : Type) [CommRing R] (n m : ℕ) (v : Delta n)
    (σ : singularSimplices (TopCat.of (Delta n)) (m + 1)) :
    (singularBoundary R (TopCat.of (Delta n)) (m + 1)).hom (coneGenerator R n (m + 1) v σ)
      = chainGenerator R (TopCat.of (Delta n)) (m + 1) σ
        - (coneLinearMap R n m v).hom
            ((singularBoundary R (TopCat.of (Delta n)) m).hom
              (chainGenerator R (TopCat.of (Delta n)) (m + 1) σ)) := by
  convert! singularBoundary_chainGenerator_formula R ( TopCat.of ( Delta n ) ) ( m + 1 ) ( coneSimplex n ( m + 1 ) v σ ) using 1;
  rw [ Fin.sum_univ_succ ];
  simp +decide [ singularBoundary_chainGenerator_formula, coneSimplex_face_zero, coneSimplex_face_succ, coneLinearMap_generator ];
  simp +decide [ pow_succ', neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg ];
  rfl

/-
**The cone chain-homotopy identity (successor degree).**
`∂ ∘ Cone + Cone ∘ ∂ = id` on `C_{m+1}(Δⁿ; R)`.
-/
theorem singularBoundary_coneLinearMap (R : Type) [CommRing R] (n m : ℕ) (v : Delta n) :
    coneLinearMap R n (m + 1) v ≫ singularBoundary R (TopCat.of (Delta n)) (m + 1)
        + singularBoundary R (TopCat.of (Delta n)) m ≫ coneLinearMap R n m v
      = 𝟙 (singularChainGroup R (TopCat.of (Delta n)) (m + 1)) := by
  apply Sigma.hom_ext
  intro σ
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change (singularBoundary R (TopCat.of (Delta n)) (m + 1)).hom
      ((coneLinearMap R n (m + 1) v).hom (chainGenerator R (TopCat.of (Delta n)) (m + 1) σ)) +
    (coneLinearMap R n m v).hom ((singularBoundary R (TopCat.of (Delta n)) m).hom
      (chainGenerator R (TopCat.of (Delta n)) (m + 1) σ)) =
    chainGenerator R (TopCat.of (Delta n)) (m + 1) σ
  rw [coneLinearMap_generator, singularBoundary_coneGenerator_succ, sub_add_cancel]

end AffineBarycentricSubdivision
end SphereOddDegree