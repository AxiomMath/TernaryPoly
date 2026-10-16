module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.L2Prism
public import Mathlib.Tactic.Module

@[expose] public section


/-!
# The double prism on homogeneous chains

For elements `h, k` of a group `G` put `g = (1, h, h k)`. The double prism `Q_{h,k}` sends a simplex
`(x₀, …, x_n)` to the signed sum of the `(n+2)`-simplices which triangulate the product of the
simplex with a two-step path: the monotone lattice paths of `[n] × [2]` from `(0, 0)` to `(n, 2)`
visit vertices `(i, l)`, and each path gives the simplex of the values `x_i g_l`. The sign of a
path is `(-1)^s`, where `s` is the sum, over the steps in the second direction, of the number of
steps in the first direction still to come. Explicitly, with `x_i h k` read as `x_i (h k)`,

* `Q (x₀) = (x₀, x₀h, x₀hk)`,
* `Q (x₀, x₁) = (x₀, x₀h, x₀hk, x₁hk) - (x₀, x₀h, x₁h, x₁hk) + (x₀, x₁, x₁h, x₁hk)`,
* `Q (x₀, x₁, x₂)` is the sum of the six terms
  `+ (x₀, x₀h, x₀hk, x₁hk, x₂hk)`, `- (x₀, x₀h, x₁h, x₁hk, x₂hk)`, `+ (x₀, x₀h, x₁h, x₂h, x₂hk)`,
  `+ (x₀, x₁, x₁h, x₁hk, x₂hk)`, `- (x₀, x₁, x₁h, x₂h, x₂hk)`, `+ (x₀, x₁, x₂, x₂h, x₂hk)`.

Together with the prism `P_h (x₀, …, x_n) = Σ_i (-1)^i (x₀, …, x_i, x_i h, …, x_n h)` and right
translation `R_h` of all vertices, the double prism satisfies

  `∂ Q_{h,k} = Q_{h,k} ∂ + P_k R_h - P_{hk} + P_h`,

where in dimension `0` the term `Q_{h,k} ∂` is absent. This file defines the double prism in
dimensions `0, 1, 2` on explicit simplices, proves this identity in each dimension, and shows that
the double prism commutes with left translation, hence preserves the chains which are null modulo
a subgroup.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.L2DoublePrism

open TernaryPeriodPolynomials.TopVanishing
  (homogeneousBoundary lin_ext_single)
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains (NullChains)
open TernaryPeriodPolynomials.BoundaryDuality.ChainCalculus
  (Chains leftTranslate rightTranslate leftTranslate_single)
open TernaryPeriodPolynomials.BoundaryDuality.L2Prism
  (prism0 prism1 prism2 prism0_vec prism1_vec prism2_vec homogeneousBoundary_vec2
    homogeneousBoundary_vec3 homogeneousBoundary_vec4 homogeneousBoundary_vec5
    leftTranslate_vec1 leftTranslate_vec2 leftTranslate_vec3 leftTranslate_vec4
    leftTranslate_vec5 rightTranslate_vec1 rightTranslate_vec2 rightTranslate_vec3
    leftTranslate_sub_mem_null)

variable {G : Type} [Group G]

/-! ### The double prism operators -/

/-- The double prism in dimension `0`: `Q_{h,k} (x₀) = (x₀, x₀ h, x₀ h k)`. -/
def dprism0 (h k : G) : Chains G 0 →ₗ[ℂ] Chains G 2 :=
  Finsupp.linearCombination ℂ fun (x : Fin (0 + 1) → G) =>
    Finsupp.single ![x 0, x 0 * h, x 0 * (h * k)] (1 : ℂ)

/-- The double prism in dimension `1`:
`Q_{h,k} (x₀, x₁) = (x₀, x₀h, x₀hk, x₁hk) - (x₀, x₀h, x₁h, x₁hk) + (x₀, x₁, x₁h, x₁hk)`. -/
def dprism1 (h k : G) : Chains G 1 →ₗ[ℂ] Chains G 3 :=
  Finsupp.linearCombination ℂ fun (x : Fin (1 + 1) → G) =>
    Finsupp.single ![x 0, x 0 * h, x 0 * (h * k), x 1 * (h * k)] (1 : ℂ) -
      Finsupp.single ![x 0, x 0 * h, x 1 * h, x 1 * (h * k)] (1 : ℂ) +
        Finsupp.single ![x 0, x 1, x 1 * h, x 1 * (h * k)] (1 : ℂ)

/-- The double prism in dimension `2`: the signed sum over the six lattice paths of `[2] × [2]`,
`Q_{h,k} (x₀, x₁, x₂) = (x₀, x₀h, x₀hk, x₁hk, x₂hk) - (x₀, x₀h, x₁h, x₁hk, x₂hk)
  + (x₀, x₀h, x₁h, x₂h, x₂hk) + (x₀, x₁, x₁h, x₁hk, x₂hk) - (x₀, x₁, x₁h, x₂h, x₂hk)
  + (x₀, x₁, x₂, x₂h, x₂hk)`. -/
def dprism2 (h k : G) : Chains G 2 →ₗ[ℂ] Chains G 4 :=
  Finsupp.linearCombination ℂ fun (x : Fin (2 + 1) → G) =>
    Finsupp.single ![x 0, x 0 * h, x 0 * (h * k), x 1 * (h * k), x 2 * (h * k)] (1 : ℂ) -
      Finsupp.single ![x 0, x 0 * h, x 1 * h, x 1 * (h * k), x 2 * (h * k)] (1 : ℂ) +
        Finsupp.single ![x 0, x 0 * h, x 1 * h, x 2 * h, x 2 * (h * k)] (1 : ℂ) +
          Finsupp.single ![x 0, x 1, x 1 * h, x 1 * (h * k), x 2 * (h * k)] (1 : ℂ) -
            Finsupp.single ![x 0, x 1, x 1 * h, x 2 * h, x 2 * (h * k)] (1 : ℂ) +
              Finsupp.single ![x 0, x 1, x 2, x 2 * h, x 2 * (h * k)] (1 : ℂ)

/-- The double prism in dimension `0` on a basis chain. -/
theorem dprism0_single (h k : G) (x : Fin (0 + 1) → G) :
    dprism0 h k (Finsupp.single x (1 : ℂ)) =
      Finsupp.single ![x 0, x 0 * h, x 0 * (h * k)] (1 : ℂ) := by
  unfold dprism0
  rw [Finsupp.linearCombination_single, one_smul]

/-- The double prism in dimension `1` on a basis chain. -/
theorem dprism1_single (h k : G) (x : Fin (1 + 1) → G) :
    dprism1 h k (Finsupp.single x (1 : ℂ)) =
      Finsupp.single ![x 0, x 0 * h, x 0 * (h * k), x 1 * (h * k)] (1 : ℂ) -
        Finsupp.single ![x 0, x 0 * h, x 1 * h, x 1 * (h * k)] (1 : ℂ) +
          Finsupp.single ![x 0, x 1, x 1 * h, x 1 * (h * k)] (1 : ℂ) := by
  unfold dprism1
  rw [Finsupp.linearCombination_single, one_smul]

/-- The double prism in dimension `2` on a basis chain. -/
theorem dprism2_single (h k : G) (x : Fin (2 + 1) → G) :
    dprism2 h k (Finsupp.single x (1 : ℂ)) =
      Finsupp.single ![x 0, x 0 * h, x 0 * (h * k), x 1 * (h * k), x 2 * (h * k)] (1 : ℂ) -
        Finsupp.single ![x 0, x 0 * h, x 1 * h, x 1 * (h * k), x 2 * (h * k)] (1 : ℂ) +
          Finsupp.single ![x 0, x 0 * h, x 1 * h, x 2 * h, x 2 * (h * k)] (1 : ℂ) +
            Finsupp.single ![x 0, x 1, x 1 * h, x 1 * (h * k), x 2 * (h * k)] (1 : ℂ) -
              Finsupp.single ![x 0, x 1, x 1 * h, x 2 * h, x 2 * (h * k)] (1 : ℂ) +
                Finsupp.single ![x 0, x 1, x 2, x 2 * h, x 2 * (h * k)] (1 : ℂ) := by
  unfold dprism2
  rw [Finsupp.linearCombination_single, one_smul]

/-- The double prism of a vertex `(a)`. -/
theorem dprism0_vec (h k a : G) :
    dprism0 h k (Finsupp.single ![a] (1 : ℂ)) =
      Finsupp.single ![a, a * h, a * (h * k)] (1 : ℂ) :=
  dprism0_single h k ![a]

/-- The double prism of an edge `(a, b)`. -/
theorem dprism1_vec (h k a b : G) :
    dprism1 h k (Finsupp.single ![a, b] (1 : ℂ)) =
      Finsupp.single ![a, a * h, a * (h * k), b * (h * k)] (1 : ℂ) -
        Finsupp.single ![a, a * h, b * h, b * (h * k)] (1 : ℂ) +
          Finsupp.single ![a, b, b * h, b * (h * k)] (1 : ℂ) :=
  dprism1_single h k ![a, b]

/-- The double prism of a triangle `(a, b, c)`. -/
theorem dprism2_vec (h k a b c : G) :
    dprism2 h k (Finsupp.single ![a, b, c] (1 : ℂ)) =
      Finsupp.single ![a, a * h, a * (h * k), b * (h * k), c * (h * k)] (1 : ℂ) -
        Finsupp.single ![a, a * h, b * h, b * (h * k), c * (h * k)] (1 : ℂ) +
          Finsupp.single ![a, a * h, b * h, c * h, c * (h * k)] (1 : ℂ) +
            Finsupp.single ![a, b, b * h, b * (h * k), c * (h * k)] (1 : ℂ) -
              Finsupp.single ![a, b, b * h, c * h, c * (h * k)] (1 : ℂ) +
                Finsupp.single ![a, b, c, c * h, c * (h * k)] (1 : ℂ) :=
  dprism2_single h k ![a, b, c]

/-! ### The boundary identities -/

/-- Boundary identity in dimension `0` on a vertex `(a)`. -/
theorem dprism0_boundary_vec (h k a : G) :
    homogeneousBoundary 2 (dprism0 h k (Finsupp.single ![a] (1 : ℂ))) =
      prism0 k (rightTranslate h 0 (Finsupp.single ![a] (1 : ℂ))) -
        prism0 (h * k) (Finsupp.single ![a] (1 : ℂ)) + prism0 h (Finsupp.single ![a] (1 : ℂ)) := by
  rw [dprism0_vec, homogeneousBoundary_vec3 a (a * h) (a * (h * k)), rightTranslate_vec1,
    prism0_vec k (a * h), prism0_vec (h * k) a, prism0_vec h a, mul_assoc a h k]

/-- Boundary identity in dimension `0`:
`∂ Q_{h,k} = P_k R_h - P_{hk} + P_h` on vertex chains. -/
theorem dprism0_boundary (h k : G) (c : Chains G 0) :
    homogeneousBoundary 2 (dprism0 h k c) =
      prism0 k (rightTranslate h 0 c) - prism0 (h * k) c + prism0 h c := by
  have key : (homogeneousBoundary 2 ∘ₗ dprism0 h k : Chains G 0 →ₗ[ℂ] Chains G 1) =
      prism0 k ∘ₗ rightTranslate h 0 - prism0 (h * k) + prism0 h :=
    lin_ext_single fun x => by
      obtain ⟨a, rfl⟩ : ∃ a : G, x = ![a] := ⟨x 0, by funext j; fin_cases j; rfl⟩
      simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply]
      exact dprism0_boundary_vec h k a
  exact LinearMap.congr_fun key c

/-- Boundary identity in dimension `1` on an edge `(a, b)`. -/
theorem dprism1_boundary_vec (h k a b : G) :
    homogeneousBoundary 3 (dprism1 h k (Finsupp.single ![a, b] (1 : ℂ))) =
      dprism0 h k (homogeneousBoundary 1 (Finsupp.single ![a, b] (1 : ℂ))) +
        prism1 k (rightTranslate h 1 (Finsupp.single ![a, b] (1 : ℂ))) -
          prism1 (h * k) (Finsupp.single ![a, b] (1 : ℂ)) +
            prism1 h (Finsupp.single ![a, b] (1 : ℂ)) := by
  rw [dprism1_vec, map_add, map_sub,
    homogeneousBoundary_vec4 a (a * h) (a * (h * k)) (b * (h * k)),
    homogeneousBoundary_vec4 a (a * h) (b * h) (b * (h * k)),
    homogeneousBoundary_vec4 a b (b * h) (b * (h * k)), homogeneousBoundary_vec2 a b, map_sub,
    dprism0_vec h k b, dprism0_vec h k a, rightTranslate_vec2, prism1_vec k (a * h) (b * h),
    prism1_vec (h * k) a b, prism1_vec h a b]
  simp only [mul_assoc]
  module

/-- Boundary identity in dimension `1`:
`∂ Q_{h,k} = Q_{h,k} ∂ + P_k R_h - P_{hk} + P_h` on edge chains. -/
theorem dprism1_boundary (h k : G) (c : Chains G 1) :
    homogeneousBoundary 3 (dprism1 h k c) =
      dprism0 h k (homogeneousBoundary 1 c) + prism1 k (rightTranslate h 1 c) -
        prism1 (h * k) c + prism1 h c := by
  have key : (homogeneousBoundary 3 ∘ₗ dprism1 h k : Chains G 1 →ₗ[ℂ] Chains G 2) =
      dprism0 h k ∘ₗ homogeneousBoundary 1 + prism1 k ∘ₗ rightTranslate h 1 -
        prism1 (h * k) + prism1 h :=
    lin_ext_single fun x => by
      obtain ⟨a, b, rfl⟩ : ∃ a b : G, x = ![a, b] :=
        ⟨x 0, x 1, by funext j; fin_cases j <;> rfl⟩
      simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply]
      exact dprism1_boundary_vec h k a b
  exact LinearMap.congr_fun key c

/-- Boundary identity in dimension `2` on a triangle `(a, b, d)`. -/
theorem dprism2_boundary_vec (h k a b d : G) :
    homogeneousBoundary 4 (dprism2 h k (Finsupp.single ![a, b, d] (1 : ℂ))) =
      dprism1 h k (homogeneousBoundary 2 (Finsupp.single ![a, b, d] (1 : ℂ))) +
        prism2 k (rightTranslate h 2 (Finsupp.single ![a, b, d] (1 : ℂ))) -
          prism2 (h * k) (Finsupp.single ![a, b, d] (1 : ℂ)) +
            prism2 h (Finsupp.single ![a, b, d] (1 : ℂ)) := by
  rw [dprism2_vec]
  simp only [map_add, map_sub]
  rw [homogeneousBoundary_vec5 a (a * h) (a * (h * k)) (b * (h * k)) (d * (h * k)),
    homogeneousBoundary_vec5 a (a * h) (b * h) (b * (h * k)) (d * (h * k)),
    homogeneousBoundary_vec5 a (a * h) (b * h) (d * h) (d * (h * k)),
    homogeneousBoundary_vec5 a b (b * h) (b * (h * k)) (d * (h * k)),
    homogeneousBoundary_vec5 a b (b * h) (d * h) (d * (h * k)),
    homogeneousBoundary_vec5 a b d (d * h) (d * (h * k)), homogeneousBoundary_vec3 a b d]
  simp only [map_add, map_sub]
  rw [dprism1_vec h k b d, dprism1_vec h k a d, dprism1_vec h k a b, rightTranslate_vec3,
    prism2_vec k (a * h) (b * h) (d * h), prism2_vec (h * k) a b d, prism2_vec h a b d]
  simp only [mul_assoc]
  module

/-- Boundary identity in dimension `2`:
`∂ Q_{h,k} = Q_{h,k} ∂ + P_k R_h - P_{hk} + P_h` on triangle chains. -/
theorem dprism2_boundary (h k : G) (c : Chains G 2) :
    homogeneousBoundary 4 (dprism2 h k c) =
      dprism1 h k (homogeneousBoundary 2 c) + prism2 k (rightTranslate h 2 c) -
        prism2 (h * k) c + prism2 h c := by
  have key : (homogeneousBoundary 4 ∘ₗ dprism2 h k : Chains G 2 →ₗ[ℂ] Chains G 3) =
      dprism1 h k ∘ₗ homogeneousBoundary 2 + prism2 k ∘ₗ rightTranslate h 2 -
        prism2 (h * k) + prism2 h :=
    lin_ext_single fun x => by
      obtain ⟨a, b, d, rfl⟩ : ∃ a b d : G, x = ![a, b, d] :=
        ⟨x 0, x 1, x 2, by funext j; fin_cases j <;> rfl⟩
      simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply]
      exact dprism2_boundary_vec h k a b d
  exact LinearMap.congr_fun key c

/-! ### Equivariance and null chains -/

/-- The double prism in dimension `0` commutes with left translation. -/
theorem dprism0_leftTranslate (h k g : G) (c : Chains G 0) :
    dprism0 h k (leftTranslate g 0 c) = leftTranslate g 2 (dprism0 h k c) := by
  have key : dprism0 h k ∘ₗ leftTranslate g 0 = leftTranslate g 2 ∘ₗ dprism0 h k :=
    lin_ext_single fun x => by
      obtain ⟨a, rfl⟩ : ∃ a : G, x = ![a] := ⟨x 0, by funext j; fin_cases j; rfl⟩
      simp only [LinearMap.comp_apply, leftTranslate_vec1, dprism0_vec,
        leftTranslate_vec3, mul_assoc]
  exact LinearMap.congr_fun key c

/-- The double prism in dimension `1` commutes with left translation. -/
theorem dprism1_leftTranslate (h k g : G) (c : Chains G 1) :
    dprism1 h k (leftTranslate g 1 c) = leftTranslate g 3 (dprism1 h k c) := by
  have key : dprism1 h k ∘ₗ leftTranslate g 1 = leftTranslate g 3 ∘ₗ dprism1 h k :=
    lin_ext_single fun x => by
      obtain ⟨a, b, rfl⟩ : ∃ a b : G, x = ![a, b] :=
        ⟨x 0, x 1, by funext j; fin_cases j <;> rfl⟩
      simp only [LinearMap.comp_apply, leftTranslate_vec2, dprism1_vec, map_sub, map_add,
        leftTranslate_vec4, mul_assoc]
  exact LinearMap.congr_fun key c

/-- The double prism in dimension `2` commutes with left translation. -/
theorem dprism2_leftTranslate (h k g : G) (c : Chains G 2) :
    dprism2 h k (leftTranslate g 2 c) = leftTranslate g 4 (dprism2 h k c) := by
  have key : dprism2 h k ∘ₗ leftTranslate g 2 = leftTranslate g 4 ∘ₗ dprism2 h k :=
    lin_ext_single fun x => by
      obtain ⟨a, b, d, rfl⟩ : ∃ a b d : G, x = ![a, b, d] :=
        ⟨x 0, x 1, x 2, by funext j; fin_cases j <;> rfl⟩
      simp only [LinearMap.comp_apply, leftTranslate_vec3, dprism2_vec, map_sub, map_add,
        leftTranslate_vec5, mul_assoc]
  exact LinearMap.congr_fun key c

/-- The double prism in dimension `0` maps null chains to null chains. -/
theorem dprism0_mem_null {Λ : Subgroup G} (h k : G) {c : Chains G 0}
    (hc : c ∈ NullChains Λ 0) : dprism0 h k c ∈ NullChains Λ 2 := by
  have hle : NullChains Λ 0 ≤ (NullChains Λ 2).comap (dprism0 h k) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨γ, x, rfl⟩
    have e := dprism0_leftTranslate h k γ.val (Finsupp.single x (1 : ℂ))
    rw [leftTranslate_single] at e
    rw [SetLike.mem_coe, Submodule.mem_comap, map_sub, e]
    exact leftTranslate_sub_mem_null γ _
  exact hle hc

/-- The double prism in dimension `1` maps null chains to null chains. -/
theorem dprism1_mem_null {Λ : Subgroup G} (h k : G) {c : Chains G 1}
    (hc : c ∈ NullChains Λ 1) : dprism1 h k c ∈ NullChains Λ 3 := by
  have hle : NullChains Λ 1 ≤ (NullChains Λ 3).comap (dprism1 h k) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨γ, x, rfl⟩
    have e := dprism1_leftTranslate h k γ.val (Finsupp.single x (1 : ℂ))
    rw [leftTranslate_single] at e
    rw [SetLike.mem_coe, Submodule.mem_comap, map_sub, e]
    exact leftTranslate_sub_mem_null γ _
  exact hle hc

/-- The double prism in dimension `2` maps null chains to null chains. -/
theorem dprism2_mem_null {Λ : Subgroup G} (h k : G) {c : Chains G 2}
    (hc : c ∈ NullChains Λ 2) : dprism2 h k c ∈ NullChains Λ 4 := by
  have hle : NullChains Λ 2 ≤ (NullChains Λ 4).comap (dprism2 h k) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨γ, x, rfl⟩
    have e := dprism2_leftTranslate h k γ.val (Finsupp.single x (1 : ℂ))
    rw [leftTranslate_single] at e
    rw [SetLike.mem_coe, Submodule.mem_comap, map_sub, e]
    exact leftTranslate_sub_mem_null γ _
  exact hle hc

end TernaryPeriodPolynomials.BoundaryDuality.L2DoublePrism
