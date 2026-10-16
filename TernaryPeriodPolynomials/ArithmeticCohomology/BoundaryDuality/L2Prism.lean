module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.ChainCalculus
public import Mathlib.Tactic.Module

@[expose] public section


/-!
# The prism operator on homogeneous chains

For a group `G` and an element `h : G`, the prism `P_h` sends a simplex `(x₀, …, x_k)` to the
alternating sum `Σ_i (-1)^i (x₀, …, x_i, x_i h, …, x_k h)` of the simplices that subdivide the
product of the simplex with an interval, the top face being `(x₀ h, …, x_k h)` and the bottom
face `(x₀, …, x_k)`. It is a chain homotopy between the identity and right translation `R_h` of
all vertices:

  `∂ P_h + P_h ∂ = R_h - id`,

where in dimension `0` the term `P_h ∂` is absent. This file works with the operators in
dimensions `0, 1, 2, 3` on explicit simplices (vertex tuples written as vector literals) and
proves:

* the boundary of a simplex with `2, 3, 4, 5` explicit vertices;
* translations of all vertices (on the left or on the right) commute with the boundary,
  and left translation by an element `γ` of a subgroup `Λ` changes a chain by a null chain
  (a finite combination of differences `γ x - x`);
* the boundary and right translation preserve null chains and chains which are boundaries modulo
  null chains;
* the homotopy identities in dimensions `0, 1, 2, 3`;
* the prism operators commute with left translation, hence preserve null chains.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.L2Prism

open TernaryPeriodPolynomials.TopVanishing
  (homogeneousBoundary homogeneousBoundary_single lin_ext_single)
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains (NullChains)
open TernaryPeriodPolynomials.BoundaryDuality.ChainCalculus
  (Chains BdryChains leftTranslate rightTranslate leftTranslate_single rightTranslate_single)

/-- The vertex tuple `(a)` as a function on `Fin (0 + 1)`. -/
abbrev tup1 {G : Type} (a : G) : Fin (0 + 1) → G := ![a]

/-- The vertex tuple `(a, b)` as a function on `Fin (1 + 1)`. -/
abbrev tup2 {G : Type} (a b : G) : Fin (1 + 1) → G := ![a, b]

/-- The vertex tuple `(a, b, c)` as a function on `Fin (2 + 1)`. -/
abbrev tup3 {G : Type} (a b c : G) : Fin (2 + 1) → G := ![a, b, c]

/-- The vertex tuple `(a, b, c, d)` as a function on `Fin (3 + 1)`. -/
abbrev tup4 {G : Type} (a b c d : G) : Fin (3 + 1) → G := ![a, b, c, d]

/-- The vertex tuple `(a, b, c, d, e)` as a function on `Fin (4 + 1)`. -/
abbrev tup5 {G : Type} (a b c d e : G) : Fin (4 + 1) → G := ![a, b, c, d, e]

variable {G : Type} [Group G]

/-! ### Translations and null chains -/

/-- Left translation by an element of `Λ` changes a chain by a null chain. -/
theorem leftTranslate_sub_mem_null {Λ : Subgroup G} {k : ℕ} (γ : Λ) (c : Chains G k) :
    leftTranslate γ.val k c - c ∈ NullChains Λ k := by
  induction c using Finsupp.induction_linear with
  | zero =>
    rw [map_zero, sub_zero]
    exact Submodule.zero_mem _
  | add c₁ c₂ h₁ h₂ =>
    have e : leftTranslate γ.val k (c₁ + c₂) - (c₁ + c₂) =
        (leftTranslate γ.val k c₁ - c₁) + (leftTranslate γ.val k c₂ - c₂) := by
      rw [map_add]
      abel
    rw [e]
    exact Submodule.add_mem _ h₁ h₂
  | single x a =>
    have e : leftTranslate γ.val k (Finsupp.single x a) - Finsupp.single x a =
        a • (Finsupp.single (fun i => γ.val * x i) (1 : ℂ) - Finsupp.single x (1 : ℂ)) := by
      simp only [leftTranslate_single, smul_sub, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨γ, x, rfl⟩)

/-- Left translation by an element of `Λ` preserves the null chains. -/
theorem leftTranslate_mem_null {Λ : Subgroup G} {k : ℕ} (γ : Λ) {c : Chains G k}
    (hc : c ∈ NullChains Λ k) : leftTranslate γ.val k c ∈ NullChains Λ k := by
  have h := Submodule.add_mem _ (leftTranslate_sub_mem_null γ c) hc
  rwa [sub_add_cancel] at h

/-- Null chains are boundaries modulo null chains. -/
theorem null_le_bdry (Λ : Subgroup G) (k : ℕ) : NullChains Λ k ≤ BdryChains Λ k := by
  unfold BdryChains
  exact le_sup_left

/-- The boundary commutes with left translation of all vertices. -/
theorem homogeneousBoundary_leftTranslate (g : G) (k : ℕ) (c : Chains G (k + 1)) :
    homogeneousBoundary (k + 1) (leftTranslate g (k + 1) c) =
      leftTranslate g k (homogeneousBoundary (k + 1) c) := by
  have key : homogeneousBoundary (k + 1) ∘ₗ leftTranslate g (k + 1) =
      leftTranslate g k ∘ₗ homogeneousBoundary (k + 1) :=
    lin_ext_single fun x => by
      have hi : ∀ i : Fin (k + 1 + 1), (fun j => g * x j) ∘ Fin.succAbove i =
          fun j => g * (x ∘ Fin.succAbove i) j := fun _ => rfl
      rw [LinearMap.comp_apply, LinearMap.comp_apply, leftTranslate_single,
        homogeneousBoundary_single, homogeneousBoundary_single, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, leftTranslate_single, hi]
  exact LinearMap.congr_fun key c

/-- The boundary commutes with right translation of all vertices. -/
theorem homogeneousBoundary_rightTranslate (h : G) (k : ℕ) (c : Chains G (k + 1)) :
    homogeneousBoundary (k + 1) (rightTranslate h (k + 1) c) =
      rightTranslate h k (homogeneousBoundary (k + 1) c) := by
  have key : homogeneousBoundary (k + 1) ∘ₗ rightTranslate h (k + 1) =
      rightTranslate h k ∘ₗ homogeneousBoundary (k + 1) :=
    lin_ext_single fun x => by
      have hi : ∀ i : Fin (k + 1 + 1), (fun j => x j * h) ∘ Fin.succAbove i =
          fun j => (x ∘ Fin.succAbove i) j * h := fun _ => rfl
      rw [LinearMap.comp_apply, LinearMap.comp_apply, rightTranslate_single,
        homogeneousBoundary_single, homogeneousBoundary_single, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, rightTranslate_single, hi]
  exact LinearMap.congr_fun key c

/-- The boundary of a null chain is null. -/
theorem homogeneousBoundary_mem_null {Λ : Subgroup G} {k : ℕ} {c : Chains G (k + 1)}
    (hc : c ∈ NullChains Λ (k + 1)) : homogeneousBoundary (k + 1) c ∈ NullChains Λ k := by
  have hle : NullChains Λ (k + 1) ≤ (NullChains Λ k).comap (homogeneousBoundary (k + 1)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨γ, x, rfl⟩
    have e := homogeneousBoundary_leftTranslate γ.val k (Finsupp.single x (1 : ℂ))
    rw [leftTranslate_single] at e
    rw [SetLike.mem_coe, Submodule.mem_comap, map_sub, e]
    exact leftTranslate_sub_mem_null γ _
  exact hle hc

/-- Right translation of all vertices preserves the null chains. -/
theorem rightTranslate_mem_null {Λ : Subgroup G} (h : G) {k : ℕ} {c : Chains G k}
    (hc : c ∈ NullChains Λ k) : rightTranslate h k c ∈ NullChains Λ k := by
  have hle : NullChains Λ k ≤ (NullChains Λ k).comap (rightTranslate h k) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨γ, x, rfl⟩
    have e : rightTranslate h k (Finsupp.single (fun i => γ.val * x i) (1 : ℂ) -
        Finsupp.single x (1 : ℂ)) =
        Finsupp.single (fun i => γ.val * (x i * h)) (1 : ℂ) -
          Finsupp.single (fun i => x i * h) (1 : ℂ) := by
      rw [map_sub, rightTranslate_single, rightTranslate_single]
      simp only [mul_assoc]
    rw [SetLike.mem_coe, Submodule.mem_comap, e]
    exact Submodule.subset_span ⟨γ, fun i => x i * h, rfl⟩
  exact hle hc

/-- Right translation of all vertices preserves the boundaries modulo null chains. -/
theorem rightTranslate_mem_bdry {Λ : Subgroup G} (h : G) {k : ℕ} {c : Chains G k}
    (hc : c ∈ BdryChains Λ k) : rightTranslate h k c ∈ BdryChains Λ k := by
  have hc' : c ∈ NullChains Λ k ⊔ LinearMap.range (homogeneousBoundary (G := G) (k + 1)) := hc
  obtain ⟨a, ha, b, ⟨d, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hc'
  rw [map_add, ← homogeneousBoundary_rightTranslate]
  unfold BdryChains
  exact Submodule.add_mem_sup (rightTranslate_mem_null h ha) ⟨rightTranslate h (k + 1) d, rfl⟩

/-! ### Boundaries of explicit simplices -/

omit [Group G] in
/-- The boundary of the edge `(a, b)` is `(b) - (a)`. -/
theorem homogeneousBoundary_vec2 (a b : G) :
    homogeneousBoundary 1 (Finsupp.single (tup2 a b) (1 : ℂ) : Chains G 1) =
      (Finsupp.single (tup1 b) (1 : ℂ) : Chains G 0) - Finsupp.single (tup1 a) (1 : ℂ) := by
  have h0 : (tup2 a b) ∘ Fin.succAbove (0 : Fin 2) = (tup1 b) := by
    funext j; fin_cases j; rfl
  have h1 : (tup2 a b) ∘ Fin.succAbove (1 : Fin 2) = (tup1 a) := by
    funext j; fin_cases j; rfl
  have v0 : ((0 : Fin 2) : ℕ) = 0 := rfl
  have v1 : ((1 : Fin 2) : ℕ) = 1 := rfl
  rw [homogeneousBoundary_single, Fin.sum_univ_two]
  simp only [h0, h1, v0, v1]
  module

omit [Group G] in
/-- The boundary of the triangle `(a, b, c)` is `(b, c) - (a, c) + (a, b)`. -/
theorem homogeneousBoundary_vec3 (a b c : G) :
    homogeneousBoundary 2 (Finsupp.single (tup3 a b c) (1 : ℂ) : Chains G 2) =
      (Finsupp.single (tup2 b c) (1 : ℂ) : Chains G 1) - Finsupp.single (tup2 a c) (1 : ℂ) +
        Finsupp.single (tup2 a b) (1 : ℂ) := by
  have h0 : (tup3 a b c) ∘ Fin.succAbove (0 : Fin 3) = (tup2 b c) := by
    funext j; fin_cases j <;> rfl
  have h1 : (tup3 a b c) ∘ Fin.succAbove (1 : Fin 3) = (tup2 a c) := by
    funext j; fin_cases j <;> rfl
  have h2 : (tup3 a b c) ∘ Fin.succAbove (2 : Fin 3) = (tup2 a b) := by
    funext j; fin_cases j <;> rfl
  have v0 : ((0 : Fin 3) : ℕ) = 0 := rfl
  have v1 : ((1 : Fin 3) : ℕ) = 1 := rfl
  have v2 : ((2 : Fin 3) : ℕ) = 2 := rfl
  rw [homogeneousBoundary_single, Fin.sum_univ_three]
  simp only [h0, h1, h2, v0, v1, v2]
  module

omit [Group G] in
/-- The boundary of the tetrahedron `(a, b, c, d)`. -/
theorem homogeneousBoundary_vec4 (a b c d : G) :
    homogeneousBoundary 3 (Finsupp.single (tup4 a b c d) (1 : ℂ) : Chains G 3) =
      (Finsupp.single (tup3 b c d) (1 : ℂ) : Chains G 2) - Finsupp.single (tup3 a c d) (1 : ℂ) +
        Finsupp.single (tup3 a b d) (1 : ℂ) - Finsupp.single (tup3 a b c) (1 : ℂ) := by
  have h0 : (tup4 a b c d) ∘ Fin.succAbove (0 : Fin 4) = (tup3 b c d) := by
    funext j; fin_cases j <;> rfl
  have h1 : (tup4 a b c d) ∘ Fin.succAbove (1 : Fin 4) = (tup3 a c d) := by
    funext j; fin_cases j <;> rfl
  have h2 : (tup4 a b c d) ∘ Fin.succAbove (2 : Fin 4) = (tup3 a b d) := by
    funext j; fin_cases j <;> rfl
  have h3 : (tup4 a b c d) ∘ Fin.succAbove (3 : Fin 4) = (tup3 a b c) := by
    funext j; fin_cases j <;> rfl
  have v0 : ((0 : Fin 4) : ℕ) = 0 := rfl
  have v1 : ((1 : Fin 4) : ℕ) = 1 := rfl
  have v2 : ((2 : Fin 4) : ℕ) = 2 := rfl
  have v3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  rw [homogeneousBoundary_single, Fin.sum_univ_four]
  simp only [h0, h1, h2, h3, v0, v1, v2, v3]
  module

omit [Group G] in
/-- The boundary of the four-simplex `(a, b, c, d, e)`. -/
theorem homogeneousBoundary_vec5 (a b c d e : G) :
    homogeneousBoundary 4 (Finsupp.single (tup5 a b c d e) (1 : ℂ) : Chains G 4) =
      (Finsupp.single (tup4 b c d e) (1 : ℂ) : Chains G 3) -
        Finsupp.single (tup4 a c d e) (1 : ℂ) + Finsupp.single (tup4 a b d e) (1 : ℂ) -
          Finsupp.single (tup4 a b c e) (1 : ℂ) + Finsupp.single (tup4 a b c d) (1 : ℂ) := by
  have h0 : (tup5 a b c d e) ∘ Fin.succAbove (0 : Fin 5) = (tup4 b c d e) := by
    funext j; fin_cases j <;> rfl
  have h1 : (tup5 a b c d e) ∘ Fin.succAbove (1 : Fin 5) = (tup4 a c d e) := by
    funext j; fin_cases j <;> rfl
  have h2 : (tup5 a b c d e) ∘ Fin.succAbove (2 : Fin 5) = (tup4 a b d e) := by
    funext j; fin_cases j <;> rfl
  have h3 : (tup5 a b c d e) ∘ Fin.succAbove (3 : Fin 5) = (tup4 a b c e) := by
    funext j; fin_cases j <;> rfl
  have h4 : (tup5 a b c d e) ∘ Fin.succAbove (4 : Fin 5) = (tup4 a b c d) := by
    funext j; fin_cases j <;> rfl
  have v0 : ((0 : Fin 5) : ℕ) = 0 := rfl
  have v1 : ((1 : Fin 5) : ℕ) = 1 := rfl
  have v2 : ((2 : Fin 5) : ℕ) = 2 := rfl
  have v3 : ((3 : Fin 5) : ℕ) = 3 := rfl
  have v4 : ((4 : Fin 5) : ℕ) = 4 := rfl
  rw [homogeneousBoundary_single, Fin.sum_univ_five]
  simp only [h0, h1, h2, h3, h4, v0, v1, v2, v3, v4]
  module

/-! ### Translations of explicit simplices -/

/-- Left translation of the vertex chain `(a)`. -/
theorem leftTranslate_vec1 (g a : G) :
    leftTranslate g 0 (Finsupp.single (tup1 a) (1 : ℂ)) =
      Finsupp.single (tup1 (g * a)) (1 : ℂ) := by
  rw [leftTranslate_single]
  refine congrArg (fun y => Finsupp.single y (1 : ℂ)) ?_
  funext i
  fin_cases i; rfl

/-- Left translation of the edge `(a, b)`. -/
theorem leftTranslate_vec2 (g a b : G) :
    leftTranslate g 1 (Finsupp.single (tup2 a b) (1 : ℂ)) =
      Finsupp.single (tup2 (g * a) (g * b)) (1 : ℂ) := by
  rw [leftTranslate_single]
  refine congrArg (fun y => Finsupp.single y (1 : ℂ)) ?_
  funext i
  fin_cases i <;> rfl

/-- Left translation of the triangle `(a, b, c)`. -/
theorem leftTranslate_vec3 (g a b c : G) :
    leftTranslate g 2 (Finsupp.single (tup3 a b c) (1 : ℂ)) =
      Finsupp.single (tup3 (g * a) (g * b) (g * c)) (1 : ℂ) := by
  rw [leftTranslate_single]
  refine congrArg (fun y => Finsupp.single y (1 : ℂ)) ?_
  funext i
  fin_cases i <;> rfl

/-- Left translation of the tetrahedron `(a, b, c, d)`. -/
theorem leftTranslate_vec4 (g a b c d : G) :
    leftTranslate g 3 (Finsupp.single (tup4 a b c d) (1 : ℂ)) =
      Finsupp.single (tup4 (g * a) (g * b) (g * c) (g * d)) (1 : ℂ) := by
  rw [leftTranslate_single]
  refine congrArg (fun y => Finsupp.single y (1 : ℂ)) ?_
  funext i
  fin_cases i <;> rfl

/-- Left translation of the four-simplex `(a, b, c, d, e)`. -/
theorem leftTranslate_vec5 (g a b c d e : G) :
    leftTranslate g 4 (Finsupp.single (tup5 a b c d e) (1 : ℂ)) =
      Finsupp.single (tup5 (g * a) (g * b) (g * c) (g * d) (g * e)) (1 : ℂ) := by
  rw [leftTranslate_single]
  refine congrArg (fun y => Finsupp.single y (1 : ℂ)) ?_
  funext i
  fin_cases i <;> rfl

/-- Right translation of the vertex chain `(a)`. -/
theorem rightTranslate_vec1 (h a : G) :
    rightTranslate h 0 (Finsupp.single (tup1 a) (1 : ℂ)) =
      Finsupp.single (tup1 (a * h)) (1 : ℂ) := by
  rw [rightTranslate_single]
  refine congrArg (fun y => Finsupp.single y (1 : ℂ)) ?_
  funext i
  fin_cases i; rfl

/-- Right translation of the edge `(a, b)`. -/
theorem rightTranslate_vec2 (h a b : G) :
    rightTranslate h 1 (Finsupp.single (tup2 a b) (1 : ℂ)) =
      Finsupp.single (tup2 (a * h) (b * h)) (1 : ℂ) := by
  rw [rightTranslate_single]
  refine congrArg (fun y => Finsupp.single y (1 : ℂ)) ?_
  funext i
  fin_cases i <;> rfl

/-- Right translation of the triangle `(a, b, c)`. -/
theorem rightTranslate_vec3 (h a b c : G) :
    rightTranslate h 2 (Finsupp.single (tup3 a b c) (1 : ℂ)) =
      Finsupp.single (tup3 (a * h) (b * h) (c * h)) (1 : ℂ) := by
  rw [rightTranslate_single]
  refine congrArg (fun y => Finsupp.single y (1 : ℂ)) ?_
  funext i
  fin_cases i <;> rfl

/-- Right translation of the tetrahedron `(a, b, c, d)`. -/
theorem rightTranslate_vec4 (h a b c d : G) :
    rightTranslate h 3 (Finsupp.single (tup4 a b c d) (1 : ℂ)) =
      Finsupp.single (tup4 (a * h) (b * h) (c * h) (d * h)) (1 : ℂ) := by
  rw [rightTranslate_single]
  refine congrArg (fun y => Finsupp.single y (1 : ℂ)) ?_
  funext i
  fin_cases i <;> rfl

/-! ### The prism operators -/

/-- The prism in dimension `0`: `P_h (x₀) = (x₀, x₀ h)`. -/
def prism0 (h : G) : Chains G 0 →ₗ[ℂ] Chains G 1 :=
  Finsupp.linearCombination ℂ fun (x : Fin (0 + 1) → G) =>
    Finsupp.single (tup2 (x 0) (x 0 * h)) (1 : ℂ)

/-- The prism in dimension `1`:
`P_h (x₀, x₁) = (x₀, x₀ h, x₁ h) - (x₀, x₁, x₁ h)`. -/
def prism1 (h : G) : Chains G 1 →ₗ[ℂ] Chains G 2 :=
  Finsupp.linearCombination ℂ fun (x : Fin (1 + 1) → G) =>
    Finsupp.single (tup3 (x 0) (x 0 * h) (x 1 * h)) (1 : ℂ) -
      Finsupp.single (tup3 (x 0) (x 1) (x 1 * h)) (1 : ℂ)

/-- The prism in dimension `2`:
`P_h (x₀, x₁, x₂) = (x₀, x₀ h, x₁ h, x₂ h) - (x₀, x₁, x₁ h, x₂ h) + (x₀, x₁, x₂, x₂ h)`. -/
def prism2 (h : G) : Chains G 2 →ₗ[ℂ] Chains G 3 :=
  Finsupp.linearCombination ℂ fun (x : Fin (2 + 1) → G) =>
    Finsupp.single (tup4 (x 0) (x 0 * h) (x 1 * h) (x 2 * h)) (1 : ℂ) -
      Finsupp.single (tup4 (x 0) (x 1) (x 1 * h) (x 2 * h)) (1 : ℂ) +
        Finsupp.single (tup4 (x 0) (x 1) (x 2) (x 2 * h)) (1 : ℂ)

/-- The prism in dimension `3`:
`P_h (x₀, …, x₃) = (x₀, x₀ h, x₁ h, x₂ h, x₃ h) - (x₀, x₁, x₁ h, x₂ h, x₃ h)
  + (x₀, x₁, x₂, x₂ h, x₃ h) - (x₀, x₁, x₂, x₃, x₃ h)`. -/
def prism3 (h : G) : Chains G 3 →ₗ[ℂ] Chains G 4 :=
  Finsupp.linearCombination ℂ fun (x : Fin (3 + 1) → G) =>
    Finsupp.single (tup5 (x 0) (x 0 * h) (x 1 * h) (x 2 * h) (x 3 * h)) (1 : ℂ) -
      Finsupp.single (tup5 (x 0) (x 1) (x 1 * h) (x 2 * h) (x 3 * h)) (1 : ℂ) +
        Finsupp.single (tup5 (x 0) (x 1) (x 2) (x 2 * h) (x 3 * h)) (1 : ℂ) -
          Finsupp.single (tup5 (x 0) (x 1) (x 2) (x 3) (x 3 * h)) (1 : ℂ)

/-- The prism in dimension `0` on a basis chain. -/
theorem prism0_single (h : G) (x : Fin (0 + 1) → G) :
    prism0 h (Finsupp.single x (1 : ℂ)) = Finsupp.single (tup2 (x 0) (x 0 * h)) (1 : ℂ) := by
  unfold prism0
  rw [Finsupp.linearCombination_single, one_smul]

/-- The prism in dimension `1` on a basis chain. -/
theorem prism1_single (h : G) (x : Fin (1 + 1) → G) :
    prism1 h (Finsupp.single x (1 : ℂ)) =
      Finsupp.single (tup3 (x 0) (x 0 * h) (x 1 * h)) (1 : ℂ) -
        Finsupp.single (tup3 (x 0) (x 1) (x 1 * h)) (1 : ℂ) := by
  unfold prism1
  rw [Finsupp.linearCombination_single, one_smul]

/-- The prism in dimension `2` on a basis chain. -/
theorem prism2_single (h : G) (x : Fin (2 + 1) → G) :
    prism2 h (Finsupp.single x (1 : ℂ)) =
      Finsupp.single (tup4 (x 0) (x 0 * h) (x 1 * h) (x 2 * h)) (1 : ℂ) -
        Finsupp.single (tup4 (x 0) (x 1) (x 1 * h) (x 2 * h)) (1 : ℂ) +
          Finsupp.single (tup4 (x 0) (x 1) (x 2) (x 2 * h)) (1 : ℂ) := by
  unfold prism2
  rw [Finsupp.linearCombination_single, one_smul]

/-- The prism in dimension `3` on a basis chain. -/
theorem prism3_single (h : G) (x : Fin (3 + 1) → G) :
    prism3 h (Finsupp.single x (1 : ℂ)) =
      Finsupp.single (tup5 (x 0) (x 0 * h) (x 1 * h) (x 2 * h) (x 3 * h)) (1 : ℂ) -
        Finsupp.single (tup5 (x 0) (x 1) (x 1 * h) (x 2 * h) (x 3 * h)) (1 : ℂ) +
          Finsupp.single (tup5 (x 0) (x 1) (x 2) (x 2 * h) (x 3 * h)) (1 : ℂ) -
            Finsupp.single (tup5 (x 0) (x 1) (x 2) (x 3) (x 3 * h)) (1 : ℂ) := by
  unfold prism3
  rw [Finsupp.linearCombination_single, one_smul]

/-- The prism of a vertex `(a)` is the edge `(a, a h)`. -/
theorem prism0_vec (h a : G) :
    prism0 h (Finsupp.single (tup1 a) (1 : ℂ)) = Finsupp.single (tup2 a (a * h)) (1 : ℂ) :=
  prism0_single h (tup1 a)

/-- The prism of an edge `(a, b)`. -/
theorem prism1_vec (h a b : G) :
    prism1 h (Finsupp.single (tup2 a b) (1 : ℂ)) =
      Finsupp.single (tup3 a (a * h) (b * h)) (1 : ℂ) - Finsupp.single (tup3 a b (b * h)) (1 : ℂ) :=
  prism1_single h (tup2 a b)

/-- The prism of a triangle `(a, b, c)`. -/
theorem prism2_vec (h a b c : G) :
    prism2 h (Finsupp.single (tup3 a b c) (1 : ℂ)) =
      Finsupp.single (tup4 a (a * h) (b * h) (c * h)) (1 : ℂ) -
        Finsupp.single (tup4 a b (b * h) (c * h)) (1 : ℂ) +
          Finsupp.single (tup4 a b c (c * h)) (1 : ℂ) :=
  prism2_single h (tup3 a b c)

/-- The prism of a tetrahedron `(a, b, c, d)`. -/
theorem prism3_vec (h a b c d : G) :
    prism3 h (Finsupp.single (tup4 a b c d) (1 : ℂ)) =
      Finsupp.single (tup5 a (a * h) (b * h) (c * h) (d * h)) (1 : ℂ) -
        Finsupp.single (tup5 a b (b * h) (c * h) (d * h)) (1 : ℂ) +
          Finsupp.single (tup5 a b c (c * h) (d * h)) (1 : ℂ) -
            Finsupp.single (tup5 a b c d (d * h)) (1 : ℂ) :=
  prism3_single h (tup4 a b c d)

/-! ### The homotopy identities -/

/-- Homotopy identity in dimension `0` on a vertex `(a)`. -/
theorem prism0_homotopy_vec (h a : G) :
    homogeneousBoundary 1 (prism0 h (Finsupp.single (tup1 a) (1 : ℂ))) =
      rightTranslate h 0 (Finsupp.single (tup1 a) (1 : ℂ)) - Finsupp.single (tup1 a) (1 : ℂ) := by
  rw [prism0_vec, rightTranslate_vec1]
  exact homogeneousBoundary_vec2 a (a * h)

/-- Homotopy identity in dimension `1` on an edge `(a, b)`. -/
theorem prism1_homotopy_vec (h a b : G) :
    homogeneousBoundary 2 (prism1 h (Finsupp.single (tup2 a b) (1 : ℂ))) +
        prism0 h (homogeneousBoundary 1 (Finsupp.single (tup2 a b) (1 : ℂ))) =
      rightTranslate h 1 (Finsupp.single (tup2 a b) (1 : ℂ)) -
        Finsupp.single (tup2 a b) (1 : ℂ) := by
  rw [prism1_vec, map_sub, homogeneousBoundary_vec3 a (a * h) (b * h),
    homogeneousBoundary_vec3 a b (b * h), homogeneousBoundary_vec2 a b, map_sub,
    prism0_vec h b, prism0_vec h a, rightTranslate_vec2]
  module

/-- Homotopy identity in dimension `2` on a triangle `(a, b, c)`. -/
theorem prism2_homotopy_vec (h a b c : G) :
    homogeneousBoundary 3 (prism2 h (Finsupp.single (tup3 a b c) (1 : ℂ))) +
        prism1 h (homogeneousBoundary 2 (Finsupp.single (tup3 a b c) (1 : ℂ))) =
      rightTranslate h 2 (Finsupp.single (tup3 a b c) (1 : ℂ)) -
        Finsupp.single (tup3 a b c) (1 : ℂ) := by
  rw [prism2_vec, map_add, map_sub, homogeneousBoundary_vec4 a (a * h) (b * h) (c * h),
    homogeneousBoundary_vec4 a b (b * h) (c * h), homogeneousBoundary_vec4 a b c (c * h),
    homogeneousBoundary_vec3 a b c, map_add, map_sub, prism1_vec h b c, prism1_vec h a c,
    prism1_vec h a b, rightTranslate_vec3]
  module

/-- Homotopy identity in dimension `3` on a tetrahedron `(a, b, c, d)`. -/
theorem prism3_homotopy_vec (h a b c d : G) :
    homogeneousBoundary 4 (prism3 h (Finsupp.single (tup4 a b c d) (1 : ℂ))) +
        prism2 h (homogeneousBoundary 3 (Finsupp.single (tup4 a b c d) (1 : ℂ))) =
      rightTranslate h 3 (Finsupp.single (tup4 a b c d) (1 : ℂ)) -
        Finsupp.single (tup4 a b c d) (1 : ℂ) := by
  rw [prism3_vec, map_sub, map_add, map_sub, homogeneousBoundary_vec5 a (a * h) (b * h) (c * h)
      (d * h), homogeneousBoundary_vec5 a b (b * h) (c * h) (d * h),
    homogeneousBoundary_vec5 a b c (c * h) (d * h), homogeneousBoundary_vec5 a b c d (d * h),
    homogeneousBoundary_vec4 a b c d, map_sub, map_add, map_sub, prism2_vec h b c d,
    prism2_vec h a c d, prism2_vec h a b d, prism2_vec h a b c, rightTranslate_vec4]
  module

/-- Homotopy identity in dimension `0`: `∂ P_h = R_h - id` on vertex chains. -/
theorem prism0_homotopy (h : G) (c : Chains G 0) :
    homogeneousBoundary 1 (prism0 h c) = rightTranslate h 0 c - c := by
  have key : (homogeneousBoundary 1 ∘ₗ prism0 h : Chains G 0 →ₗ[ℂ] Chains G 0) =
      rightTranslate h 0 - LinearMap.id :=
    lin_ext_single fun x => by
      obtain ⟨a, rfl⟩ : ∃ a : G, x = (tup1 a) := ⟨x 0, by funext j; fin_cases j; rfl⟩
      exact prism0_homotopy_vec h a
  exact LinearMap.congr_fun key c

/-- Homotopy identity in dimension `1`: `∂ P_h + P_h ∂ = R_h - id` on edge chains. -/
theorem prism1_homotopy (h : G) (c : Chains G 1) :
    homogeneousBoundary 2 (prism1 h c) + prism0 h (homogeneousBoundary 1 c) =
      rightTranslate h 1 c - c := by
  have key : (homogeneousBoundary 2 ∘ₗ prism1 h + prism0 h ∘ₗ homogeneousBoundary 1 :
      Chains G 1 →ₗ[ℂ] Chains G 1) = rightTranslate h 1 - LinearMap.id :=
    lin_ext_single fun x => by
      obtain ⟨a, b, rfl⟩ : ∃ a b : G, x = (tup2 a b) :=
        ⟨x 0, x 1, by funext j; fin_cases j <;> rfl⟩
      exact prism1_homotopy_vec h a b
  exact LinearMap.congr_fun key c

/-- Homotopy identity in dimension `2`: `∂ P_h + P_h ∂ = R_h - id` on triangle chains. -/
theorem prism2_homotopy (h : G) (c : Chains G 2) :
    homogeneousBoundary 3 (prism2 h c) + prism1 h (homogeneousBoundary 2 c) =
      rightTranslate h 2 c - c := by
  have key : (homogeneousBoundary 3 ∘ₗ prism2 h + prism1 h ∘ₗ homogeneousBoundary 2 :
      Chains G 2 →ₗ[ℂ] Chains G 2) = rightTranslate h 2 - LinearMap.id :=
    lin_ext_single fun x => by
      obtain ⟨a, b, c, rfl⟩ : ∃ a b c : G, x = (tup3 a b c) :=
        ⟨x 0, x 1, x 2, by funext j; fin_cases j <;> rfl⟩
      exact prism2_homotopy_vec h a b c
  exact LinearMap.congr_fun key c

/-- Homotopy identity in dimension `3`: `∂ P_h + P_h ∂ = R_h - id` on tetrahedron chains. -/
theorem prism3_homotopy (h : G) (c : Chains G 3) :
    homogeneousBoundary 4 (prism3 h c) + prism2 h (homogeneousBoundary 3 c) =
      rightTranslate h 3 c - c := by
  have key : (homogeneousBoundary 4 ∘ₗ prism3 h + prism2 h ∘ₗ homogeneousBoundary 3 :
      Chains G 3 →ₗ[ℂ] Chains G 3) = rightTranslate h 3 - LinearMap.id :=
    lin_ext_single fun x => by
      obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : G, x = (tup4 a b c d) :=
        ⟨x 0, x 1, x 2, x 3, by funext j; fin_cases j <;> rfl⟩
      exact prism3_homotopy_vec h a b c d
  exact LinearMap.congr_fun key c

/-! ### Equivariance and null chains -/

/-- The prism in dimension `0` commutes with left translation. -/
theorem prism0_leftTranslate (h g : G) (c : Chains G 0) :
    prism0 h (leftTranslate g 0 c) = leftTranslate g 1 (prism0 h c) := by
  have key : prism0 h ∘ₗ leftTranslate g 0 = leftTranslate g 1 ∘ₗ prism0 h :=
    lin_ext_single fun x => by
      obtain ⟨a, rfl⟩ : ∃ a : G, x = (tup1 a) := ⟨x 0, by funext j; fin_cases j; rfl⟩
      simp only [LinearMap.comp_apply, leftTranslate_vec1, prism0_vec, leftTranslate_vec2,
        mul_assoc]
  exact LinearMap.congr_fun key c

/-- The prism in dimension `1` commutes with left translation. -/
theorem prism1_leftTranslate (h g : G) (c : Chains G 1) :
    prism1 h (leftTranslate g 1 c) = leftTranslate g 2 (prism1 h c) := by
  have key : prism1 h ∘ₗ leftTranslate g 1 = leftTranslate g 2 ∘ₗ prism1 h :=
    lin_ext_single fun x => by
      obtain ⟨a, b, rfl⟩ : ∃ a b : G, x = (tup2 a b) :=
        ⟨x 0, x 1, by funext j; fin_cases j <;> rfl⟩
      simp only [LinearMap.comp_apply, leftTranslate_vec2, prism1_vec, map_sub,
        leftTranslate_vec3, mul_assoc]
  exact LinearMap.congr_fun key c

/-- The prism in dimension `2` commutes with left translation. -/
theorem prism2_leftTranslate (h g : G) (c : Chains G 2) :
    prism2 h (leftTranslate g 2 c) = leftTranslate g 3 (prism2 h c) := by
  have key : prism2 h ∘ₗ leftTranslate g 2 = leftTranslate g 3 ∘ₗ prism2 h :=
    lin_ext_single fun x => by
      obtain ⟨a, b, c, rfl⟩ : ∃ a b c : G, x = (tup3 a b c) :=
        ⟨x 0, x 1, x 2, by funext j; fin_cases j <;> rfl⟩
      simp only [LinearMap.comp_apply, leftTranslate_vec3, prism2_vec, map_sub, map_add,
        leftTranslate_vec4, mul_assoc]
  exact LinearMap.congr_fun key c

/-- The prism in dimension `3` commutes with left translation. -/
theorem prism3_leftTranslate (h g : G) (c : Chains G 3) :
    prism3 h (leftTranslate g 3 c) = leftTranslate g 4 (prism3 h c) := by
  have key : prism3 h ∘ₗ leftTranslate g 3 = leftTranslate g 4 ∘ₗ prism3 h :=
    lin_ext_single fun x => by
      obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : G, x = (tup4 a b c d) :=
        ⟨x 0, x 1, x 2, x 3, by funext j; fin_cases j <;> rfl⟩
      simp only [LinearMap.comp_apply, leftTranslate_vec4, prism3_vec, map_sub, map_add,
        leftTranslate_vec5, mul_assoc]
  exact LinearMap.congr_fun key c

/-- The prism in dimension `0` maps null chains to null chains. -/
theorem prism0_mem_null {Λ : Subgroup G} (h : G) {c : Chains G 0}
    (hc : c ∈ NullChains Λ 0) : prism0 h c ∈ NullChains Λ 1 := by
  have hle : NullChains Λ 0 ≤ (NullChains Λ 1).comap (prism0 h) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨γ, x, rfl⟩
    have e := prism0_leftTranslate h γ.val (Finsupp.single x (1 : ℂ))
    rw [leftTranslate_single] at e
    rw [SetLike.mem_coe, Submodule.mem_comap, map_sub, e]
    exact leftTranslate_sub_mem_null γ _
  exact hle hc

/-- The prism in dimension `1` maps null chains to null chains. -/
theorem prism1_mem_null {Λ : Subgroup G} (h : G) {c : Chains G 1}
    (hc : c ∈ NullChains Λ 1) : prism1 h c ∈ NullChains Λ 2 := by
  have hle : NullChains Λ 1 ≤ (NullChains Λ 2).comap (prism1 h) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨γ, x, rfl⟩
    have e := prism1_leftTranslate h γ.val (Finsupp.single x (1 : ℂ))
    rw [leftTranslate_single] at e
    rw [SetLike.mem_coe, Submodule.mem_comap, map_sub, e]
    exact leftTranslate_sub_mem_null γ _
  exact hle hc

/-- The prism in dimension `2` maps null chains to null chains. -/
theorem prism2_mem_null {Λ : Subgroup G} (h : G) {c : Chains G 2}
    (hc : c ∈ NullChains Λ 2) : prism2 h c ∈ NullChains Λ 3 := by
  have hle : NullChains Λ 2 ≤ (NullChains Λ 3).comap (prism2 h) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨γ, x, rfl⟩
    have e := prism2_leftTranslate h γ.val (Finsupp.single x (1 : ℂ))
    rw [leftTranslate_single] at e
    rw [SetLike.mem_coe, Submodule.mem_comap, map_sub, e]
    exact leftTranslate_sub_mem_null γ _
  exact hle hc

/-- The prism in dimension `3` maps null chains to null chains. -/
theorem prism3_mem_null {Λ : Subgroup G} (h : G) {c : Chains G 3}
    (hc : c ∈ NullChains Λ 3) : prism3 h c ∈ NullChains Λ 4 := by
  have hle : NullChains Λ 3 ≤ (NullChains Λ 4).comap (prism3 h) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨γ, x, rfl⟩
    have e := prism3_leftTranslate h γ.val (Finsupp.single x (1 : ℂ))
    rw [leftTranslate_single] at e
    rw [SetLike.mem_coe, Submodule.mem_comap, map_sub, e]
    exact leftTranslate_sub_mem_null γ _
  exact hle hc

end TernaryPeriodPolynomials.BoundaryDuality.L2Prism
