module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.ChainCalculus
public import TernaryPeriodPolynomials.ArithmeticCohomology.TopVanishing.Homogeneous

@[expose] public section


/-!
# Torus two-chains modulo a subgroup

Let `G` be a group and `Λ ≤ G` a subgroup. Homogeneous chains have boundary
`∂(x₀, …, x_k) = Σ (-1)^i (…, x̂_i, …)`. For `p, q, r ∈ G` write `[p|q] = (1, p, pq)` and
`[p|q|r] = (1, p, pq, pqr)`. Modulo the span of the differences `γ·x - x` (`γ ∈ Λ`), the boundary
of a bar three-simplex with `p ∈ Λ` is
`∂[p|q|r] ≡ [q|r] - [pq|r] + [p|qr] - [p|q]`, since its first face `(p, pq, pqr)` is the left
translate by `p` of `(1, q, qr)`.

For commuting `u, v` the torus two-chain is `σ(u, v) = [u|v] - [v|u]`. We prove, for elements of
`Λ` that commute pairwise:
* `σ(v, u) = -σ(u, v)` and `σ(u, u) = 0`;
* `∂σ(u, v)` is a null chain, so `σ(u, v)` is a cycle modulo `Λ`;
* `σ(u, vw) - σ(u, v) - σ(u, w)` is the boundary of `[u|v|w] - [v|u|w] + [v|w|u]` modulo null
  chains, and `σ(u, 1)` is the boundary of `-[u|1|1] - [1|1|u]` modulo null chains;
* hence `σ(u, vⁿ) ≡ n σ(u, v)` and `σ(uⁿ, v) ≡ n σ(u, v)` modulo boundaries, for integers `n`;
* the determinant formula `σ(aᵖbᵍ, aʳbˢ) ≡ (ps - qr) σ(a, b)` modulo boundaries.

The congruences are also expressed as identities between classes in the quotient of the two-chains
by the boundaries modulo `Λ`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.L2Torus

open TernaryPeriodPolynomials.TopVanishing
  (homogeneousBoundary homogeneousBoundary_single)
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains (NullChains)
open TernaryPeriodPolynomials.BoundaryDuality.ChainCalculus (Chains BdryChains)

variable {G : Type} [Group G]

section Faces

omit [Group G] in
/-- The boundary of a two-simplex given by its three vertices. -/
theorem boundary_two_vec (a b c : G) :
    homogeneousBoundary 2 (Finsupp.single ![a, b, c] (1 : ℂ)) =
      Finsupp.single ![b, c] (1 : ℂ) - Finsupp.single ![a, c] (1 : ℂ) +
        Finsupp.single ![a, b] (1 : ℂ) := by
  have h0 : (![a, b, c] : Fin 3 → G) ∘ Fin.succAbove (0 : Fin 3) = ![b, c] := by
    funext j; fin_cases j <;> rfl
  have h1 : (![a, b, c] : Fin 3 → G) ∘ Fin.succAbove (1 : Fin 3) = ![a, c] := by
    funext j; fin_cases j <;> rfl
  have h2 : (![a, b, c] : Fin 3 → G) ∘ Fin.succAbove (2 : Fin 3) = ![a, b] := by
    funext j; fin_cases j <;> rfl
  have v0 : ((0 : Fin 3) : ℕ) = 0 := rfl
  have v1 : ((1 : Fin 3) : ℕ) = 1 := rfl
  have v2 : ((2 : Fin 3) : ℕ) = 2 := rfl
  rw [homogeneousBoundary_single, Fin.sum_univ_three]
  simp only [h0, h1, h2, v0, v1, v2]
  module

omit [Group G] in
/-- The boundary of a three-simplex given by its four vertices. -/
theorem boundary_three_vec (a b c d : G) :
    homogeneousBoundary 3 (Finsupp.single ![a, b, c, d] (1 : ℂ)) =
      Finsupp.single ![b, c, d] (1 : ℂ) - Finsupp.single ![a, c, d] (1 : ℂ) +
        Finsupp.single ![a, b, d] (1 : ℂ) - Finsupp.single ![a, b, c] (1 : ℂ) := by
  have h0 : (![a, b, c, d] : Fin 4 → G) ∘ Fin.succAbove (0 : Fin 4) = ![b, c, d] := by
    funext j; fin_cases j <;> rfl
  have h1 : (![a, b, c, d] : Fin 4 → G) ∘ Fin.succAbove (1 : Fin 4) = ![a, c, d] := by
    funext j; fin_cases j <;> rfl
  have h2 : (![a, b, c, d] : Fin 4 → G) ∘ Fin.succAbove (2 : Fin 4) = ![a, b, d] := by
    funext j; fin_cases j <;> rfl
  have h3 : (![a, b, c, d] : Fin 4 → G) ∘ Fin.succAbove (3 : Fin 4) = ![a, b, c] := by
    funext j; fin_cases j <;> rfl
  have v0 : ((0 : Fin 4) : ℕ) = 0 := rfl
  have v1 : ((1 : Fin 4) : ℕ) = 1 := rfl
  have v2 : ((2 : Fin 4) : ℕ) = 2 := rfl
  have v3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  rw [homogeneousBoundary_single, Fin.sum_univ_four]
  simp only [h0, h1, h2, h3, v0, v1, v2, v3]
  module

end Faces

section Bar

/-- The bar two-simplex `[p|q] = (1, p, pq)`. -/
def bar2 (p q : G) : Chains G 2 := Finsupp.single ![1, p, p * q] (1 : ℂ)

/-- The bar three-simplex `[p|q|r] = (1, p, pq, pqr)`. -/
def bar3 (p q r : G) : Chains G 3 := Finsupp.single ![1, p, p * q, p * q * r] (1 : ℂ)

/-- The boundary of `[p|q]`. -/
theorem boundary_bar2 (p q : G) :
    homogeneousBoundary 2 (bar2 p q) =
      Finsupp.single ![p, p * q] (1 : ℂ) - Finsupp.single ![1, p * q] (1 : ℂ) +
        Finsupp.single ![1, p] (1 : ℂ) :=
  boundary_two_vec 1 p (p * q)

/-- The boundary of `[p|q|r]`. -/
theorem boundary_bar3 (p q r : G) :
    homogeneousBoundary 3 (bar3 p q r) =
      Finsupp.single ![p, p * q, p * q * r] (1 : ℂ) -
        Finsupp.single ![1, p * q, p * q * r] (1 : ℂ) +
        Finsupp.single ![1, p, p * q * r] (1 : ℂ) - Finsupp.single ![1, p, p * q] (1 : ℂ) :=
  boundary_three_vec 1 p (p * q) (p * q * r)

/-- A chain that is a single simplex minus its left translate by an element of `Λ` is null. -/
theorem null_of_translate {Λ : Subgroup G} {p : G} (hp : p ∈ Λ) {k : ℕ}
    (x y : Fin (k + 1) → G) (hy : ∀ i, y i = p * x i) :
    Finsupp.single y (1 : ℂ) - Finsupp.single x (1 : ℂ) ∈ NullChains Λ k := by
  have h : y = fun i => p * x i := funext hy
  subst h
  exact Submodule.subset_span ⟨⟨p, hp⟩, x, rfl⟩

/-- Null chains of one-simplices: the vertices `(c, d)` are the left translate by `p ∈ Λ` of
`(a, b)`. -/
theorem null_vec2 {Λ : Subgroup G} {p : G} (hp : p ∈ Λ) (a b c d : G) (hc : c = p * a)
    (hd : d = p * b) :
    Finsupp.single ![c, d] (1 : ℂ) - Finsupp.single ![a, b] (1 : ℂ) ∈ NullChains Λ 1 := by
  refine null_of_translate hp ![a, b] ![c, d] ?_
  intro i
  fin_cases i
  · exact hc
  · exact hd

/-- Null chains of two-simplices: the vertices `(a', b', c')` are the left translate by `p ∈ Λ`
of `(a, b, c)`. -/
theorem null_vec3 {Λ : Subgroup G} {p : G} (hp : p ∈ Λ) (a b c a' b' c' : G)
    (ha : a' = p * a) (hb : b' = p * b) (hc : c' = p * c) :
    Finsupp.single ![a', b', c'] (1 : ℂ) - Finsupp.single ![a, b, c] (1 : ℂ) ∈
      NullChains Λ 2 := by
  refine null_of_translate hp ![a, b, c] ![a', b', c'] ?_
  intro i
  fin_cases i
  · exact ha
  · exact hb
  · exact hc

/-- Modulo null chains, the boundary of `[p|q|r]` for `p ∈ Λ` is
`[q|r] - [pq|r] + [p|qr] - [p|q]`. -/
theorem boundary_bar3_sub_mem_null {Λ : Subgroup G} {p : G} (hp : p ∈ Λ) (q r : G) :
    homogeneousBoundary 3 (bar3 p q r) -
      (bar2 q r - bar2 (p * q) r + bar2 p (q * r) - bar2 p q) ∈ NullChains Λ 2 := by
  have hn := null_vec3 hp 1 q (q * r) p (p * q) (p * q * r) (mul_one p).symm rfl
    (mul_assoc p q r)
  have e : homogeneousBoundary 3 (bar3 p q r) -
      (bar2 q r - bar2 (p * q) r + bar2 p (q * r) - bar2 p q) =
      Finsupp.single ![p, p * q, p * q * r] (1 : ℂ) - Finsupp.single ![1, q, q * r] (1 : ℂ) := by
    unfold bar2
    rw [boundary_bar3, ← mul_assoc p q r]
    abel
  rw [e]
  exact hn

/-- A two-chain whose difference with the boundary of a three-chain is null is a boundary modulo
null chains. -/
theorem mem_bdry_of_boundary_sub {Λ : Subgroup G} {x : Chains G 2} (c : Chains G 3)
    (h : homogeneousBoundary 3 c - x ∈ NullChains Λ 2) : x ∈ BdryChains Λ 2 := by
  refine Submodule.mem_sup.mpr ⟨-(homogeneousBoundary 3 c - x), neg_mem h,
    homogeneousBoundary 3 c, LinearMap.mem_range.mpr ⟨c, rfl⟩, ?_⟩
  abel

/-- The face expansion `[q|r] - [pq|r] + [p|qr] - [p|q]` of `∂[p|q|r]` lies in the boundaries
modulo null chains, for `p ∈ Λ`. -/
theorem face_mem_bdry {Λ : Subgroup G} {p : G} (hp : p ∈ Λ) (q r : G) :
    bar2 q r - bar2 (p * q) r + bar2 p (q * r) - bar2 p q ∈ BdryChains Λ 2 :=
  mem_bdry_of_boundary_sub (bar3 p q r) (boundary_bar3_sub_mem_null hp q r)

end Bar

section Torus

/-- The torus two-chain `σ(u, v) = [u|v] - [v|u]`. -/
def sigma (u v : G) : Chains G 2 := bar2 u v - bar2 v u

/-- The torus chain is antisymmetric. -/
theorem sigma_comm (u v : G) : sigma v u = -sigma u v := by
  unfold sigma
  abel

/-- The torus chain of an element with itself vanishes. -/
theorem sigma_self (u : G) : sigma u u = 0 := by
  unfold sigma
  exact sub_self _

/-- The torus chain of two commuting elements of `Λ` is a cycle modulo null chains. -/
theorem boundary_sigma_mem_null {Λ : Subgroup G} {u v : G} (hu : u ∈ Λ) (hv : v ∈ Λ)
    (huv : Commute u v) : homogeneousBoundary 2 (sigma u v) ∈ NullChains Λ 1 := by
  have hA := null_vec2 hu 1 v u (u * v) (mul_one u).symm rfl
  have hB := null_vec2 hv 1 u v (u * v) (mul_one v).symm huv.eq
  have e : homogeneousBoundary 2 (sigma u v) =
      (Finsupp.single ![u, u * v] (1 : ℂ) - Finsupp.single ![1, v] (1 : ℂ)) -
        (Finsupp.single ![v, u * v] (1 : ℂ) - Finsupp.single ![1, u] (1 : ℂ)) := by
    unfold sigma
    rw [map_sub, boundary_bar2 u v, boundary_bar2 v u, ← huv.eq]
    abel
  rw [e]
  exact sub_mem hA hB

/-- The boundary of `[u|v|w] - [v|u|w] + [v|w|u]` equals `σ(u, vw) - σ(u, v) - σ(u, w)` modulo
null chains, when `u` commutes with `v` and `w` and `u, v ∈ Λ`. -/
theorem torus_three_chain_sub_mem_null {Λ : Subgroup G} {u v w : G} (hu : u ∈ Λ) (hv : v ∈ Λ)
    (huv : Commute u v) (huw : Commute u w) :
    homogeneousBoundary 3 (bar3 u v w - bar3 v u w + bar3 v w u) -
      (sigma u (v * w) - sigma u v - sigma u w) ∈ NullChains Λ 2 := by
  have h1 := boundary_bar3_sub_mem_null hu v w
  have h2 := boundary_bar3_sub_mem_null hv u w
  have h3 := boundary_bar3_sub_mem_null hv w u
  have e : homogeneousBoundary 3 (bar3 u v w - bar3 v u w + bar3 v w u) -
      (sigma u (v * w) - sigma u v - sigma u w) =
      (homogeneousBoundary 3 (bar3 u v w) -
          (bar2 v w - bar2 (u * v) w + bar2 u (v * w) - bar2 u v)) -
        (homogeneousBoundary 3 (bar3 v u w) -
          (bar2 u w - bar2 (v * u) w + bar2 v (u * w) - bar2 v u)) +
        (homogeneousBoundary 3 (bar3 v w u) -
          (bar2 w u - bar2 (v * w) u + bar2 v (w * u) - bar2 v w)) := by
    unfold sigma
    rw [map_add, map_sub, ← huv.eq, ← huw.eq]
    abel
  rw [e]
  exact add_mem (sub_mem h1 h2) h3

/-- Additivity of the torus chain in the second variable, modulo boundaries. -/
theorem sigma_mul_right_mem_bdry {Λ : Subgroup G} {u v w : G} (hu : u ∈ Λ) (hv : v ∈ Λ)
    (huv : Commute u v) (huw : Commute u w) :
    sigma u (v * w) - sigma u v - sigma u w ∈ BdryChains Λ 2 :=
  mem_bdry_of_boundary_sub _ (torus_three_chain_sub_mem_null hu hv huv huw)

/-- The boundary of `-[u|1|1] - [1|1|u]` equals `σ(u, 1)` modulo null chains. -/
theorem torus_one_chain_sub_mem_null {Λ : Subgroup G} {u : G} (hu : u ∈ Λ) :
    homogeneousBoundary 3 (-(bar3 u 1 1 + bar3 1 1 u)) - sigma u 1 ∈ NullChains Λ 2 := by
  have h1 := boundary_bar3_sub_mem_null hu (1 : G) 1
  have h2 := boundary_bar3_sub_mem_null Λ.one_mem (1 : G) u
  have e : homogeneousBoundary 3 (-(bar3 u 1 1 + bar3 1 1 u)) - sigma u 1 =
      -(homogeneousBoundary 3 (bar3 u 1 1) -
          (bar2 1 1 - bar2 (u * 1) 1 + bar2 u (1 * 1) - bar2 u 1)) -
        (homogeneousBoundary 3 (bar3 1 1 u) -
          (bar2 1 u - bar2 (1 * 1) u + bar2 1 (1 * u) - bar2 1 1)) := by
    unfold sigma
    rw [map_neg, map_add]
    simp only [mul_one, one_mul]
    abel
  rw [e]
  exact sub_mem (neg_mem h1) h2

/-- The torus chain `σ(u, 1)` is a boundary modulo null chains. -/
theorem sigma_one_mem_bdry {Λ : Subgroup G} {u : G} (hu : u ∈ Λ) :
    sigma u 1 ∈ BdryChains Λ 2 :=
  mem_bdry_of_boundary_sub _ (torus_one_chain_sub_mem_null hu)

end Torus

section Classes

/-- The class of a torus chain in the two-chains modulo boundaries. -/
def sigmaClass (Λ : Subgroup G) (u v : G) : Chains G 2 ⧸ BdryChains Λ 2 :=
  (BdryChains Λ 2).mkQ (sigma u v)

/-- A two-chain is a boundary modulo null chains iff its class is zero. -/
theorem mem_bdry_iff_mkQ_eq_zero (Λ : Subgroup G) (x : Chains G 2) :
    x ∈ BdryChains Λ 2 ↔ (BdryChains Λ 2).mkQ x = 0 := by
  rw [← LinearMap.mem_ker, Submodule.ker_mkQ]

/-- Two two-chains have the same class iff their difference is a boundary modulo null chains. -/
theorem sub_mem_bdry_iff (Λ : Subgroup G) (x y : Chains G 2) :
    x - y ∈ BdryChains Λ 2 ↔ (BdryChains Λ 2).mkQ x = (BdryChains Λ 2).mkQ y := by
  rw [mem_bdry_iff_mkQ_eq_zero, map_sub, sub_eq_zero]

/-- The class of the torus chain is antisymmetric. -/
theorem sigmaClass_comm (Λ : Subgroup G) (u v : G) :
    sigmaClass Λ v u = -sigmaClass Λ u v := by
  unfold sigmaClass
  rw [sigma_comm u v, map_neg]

/-- The class of `σ(u, u)` is zero. -/
theorem sigmaClass_self (Λ : Subgroup G) (u : G) : sigmaClass Λ u u = 0 := by
  unfold sigmaClass
  rw [sigma_self u, map_zero]

/-- The class of `σ(u, 1)` is zero. -/
theorem sigmaClass_one_right {Λ : Subgroup G} {u : G} (hu : u ∈ Λ) :
    sigmaClass Λ u 1 = 0 :=
  (mem_bdry_iff_mkQ_eq_zero Λ _).mp (sigma_one_mem_bdry hu)

/-- Additivity of the class of the torus chain in the second variable. -/
theorem sigmaClass_add_right {Λ : Subgroup G} {u v w : G} (hu : u ∈ Λ) (hv : v ∈ Λ)
    (huv : Commute u v) (huw : Commute u w) :
    sigmaClass Λ u (v * w) = sigmaClass Λ u v + sigmaClass Λ u w := by
  have h : sigma u (v * w) - (sigma u v + sigma u w) ∈ BdryChains Λ 2 := by
    rw [← sub_sub]
    exact sigma_mul_right_mem_bdry hu hv huv huw
  have h' := (sub_mem_bdry_iff Λ _ _).mp h
  rw [map_add] at h'
  exact h'

/-- Additivity of the class of the torus chain in the first variable. -/
theorem sigmaClass_add_left {Λ : Subgroup G} {u v w : G} (hw : w ∈ Λ) (hu : u ∈ Λ)
    (huw : Commute u w) (hvw : Commute v w) :
    sigmaClass Λ (u * v) w = sigmaClass Λ u w + sigmaClass Λ v w := by
  rw [sigmaClass_comm Λ w (u * v), sigmaClass_add_right hw hu huw.symm hvw.symm, neg_add,
    sigmaClass_comm Λ w u, sigmaClass_comm Λ w v]

/-- The upward step of the integer-power formula in the second variable. -/
theorem sigmaClass_zpow_succ {Λ : Subgroup G} {u v : G} (hu : u ∈ Λ) (hv : v ∈ Λ)
    (huv : Commute u v) (n : ℤ) (ih : sigmaClass Λ u (v ^ n) = n • sigmaClass Λ u v) :
    sigmaClass Λ u (v ^ (n + 1)) = (n + 1) • sigmaClass Λ u v := by
  rw [zpow_add_one, sigmaClass_add_right hu (zpow_mem hv n) (huv.zpow_right n) huv, ih,
    add_smul, one_smul]

/-- The downward step of the integer-power formula in the second variable. -/
theorem sigmaClass_zpow_pred {Λ : Subgroup G} {u v : G} (hu : u ∈ Λ) (hv : v ∈ Λ)
    (huv : Commute u v) (n : ℤ) (ih : sigmaClass Λ u (v ^ n) = n • sigmaClass Λ u v) :
    sigmaClass Λ u (v ^ (n - 1)) = (n - 1) • sigmaClass Λ u v := by
  have hmul : v ^ (n - 1) * v = v ^ n := by
    rw [← zpow_add_one, sub_add_cancel]
  have h1 := sigmaClass_add_right hu (zpow_mem hv (n - 1)) (huv.zpow_right (n - 1)) huv
  rw [hmul, ih] at h1
  rw [sub_smul, one_smul]
  exact eq_sub_of_add_eq h1.symm

/-- The class of `σ(u, vⁿ)` is `n` times the class of `σ(u, v)`. -/
theorem sigmaClass_zpow_right {Λ : Subgroup G} {u v : G} (hu : u ∈ Λ) (hv : v ∈ Λ)
    (huv : Commute u v) (n : ℤ) : sigmaClass Λ u (v ^ n) = n • sigmaClass Λ u v := by
  refine Int.induction_on n ?_ ?_ ?_
  · show sigmaClass Λ u (v ^ (0 : ℤ)) = (0 : ℤ) • sigmaClass Λ u v
    rw [zpow_zero, zero_smul]
    exact sigmaClass_one_right hu
  · intro i ih
    exact sigmaClass_zpow_succ hu hv huv (i : ℤ) ih
  · intro i ih
    exact sigmaClass_zpow_pred hu hv huv (-(i : ℤ)) ih

/-- The class of `σ(uⁿ, v)` is `n` times the class of `σ(u, v)`. -/
theorem sigmaClass_zpow_left {Λ : Subgroup G} {u v : G} (hu : u ∈ Λ) (hv : v ∈ Λ)
    (huv : Commute u v) (n : ℤ) : sigmaClass Λ (u ^ n) v = n • sigmaClass Λ u v := by
  rw [sigmaClass_comm Λ v (u ^ n), sigmaClass_zpow_right hv hu huv.symm n,
    sigmaClass_comm Λ u v, smul_neg, neg_neg]

/-- The determinant formula for the classes of torus chains of two words in commuting elements
`a, b ∈ Λ`: `σ(aᵖbᵍ, aʳbˢ) = (ps - qr) σ(a, b)`. -/
theorem sigmaClass_word {Λ : Subgroup G} {a b : G} (ha : a ∈ Λ) (hb : b ∈ Λ)
    (hab : Commute a b) (p q r s : ℤ) :
    sigmaClass Λ (a ^ p * b ^ q) (a ^ r * b ^ s) = (p * s - q * r) • sigmaClass Λ a b := by
  have cAA : ∀ m n : ℤ, Commute (a ^ m) (a ^ n) := fun m n => (Commute.refl a).zpow_zpow m n
  have cAB : ∀ m n : ℤ, Commute (a ^ m) (b ^ n) := fun m n => hab.zpow_zpow m n
  have cBA : ∀ m n : ℤ, Commute (b ^ m) (a ^ n) := fun m n => hab.symm.zpow_zpow m n
  have cBB : ∀ m n : ℤ, Commute (b ^ m) (b ^ n) := fun m n => (Commute.refl b).zpow_zpow m n
  have step1 : sigmaClass Λ (a ^ p * b ^ q) (a ^ r * b ^ s) =
      sigmaClass Λ (a ^ p) (a ^ r * b ^ s) + sigmaClass Λ (b ^ q) (a ^ r * b ^ s) :=
    sigmaClass_add_left (mul_mem (zpow_mem ha r) (zpow_mem hb s)) (zpow_mem ha p)
      ((cAA p r).mul_right (cAB p s)) ((cBA q r).mul_right (cBB q s))
  have step2 : sigmaClass Λ (a ^ p) (a ^ r * b ^ s) =
      sigmaClass Λ (a ^ p) (a ^ r) + sigmaClass Λ (a ^ p) (b ^ s) :=
    sigmaClass_add_right (zpow_mem ha p) (zpow_mem ha r) (cAA p r) (cAB p s)
  have step3 : sigmaClass Λ (b ^ q) (a ^ r * b ^ s) =
      sigmaClass Λ (b ^ q) (a ^ r) + sigmaClass Λ (b ^ q) (b ^ s) :=
    sigmaClass_add_right (zpow_mem hb q) (zpow_mem ha r) (cBA q r) (cBB q s)
  have t1 : sigmaClass Λ (a ^ p) (a ^ r) = 0 := by
    rw [sigmaClass_zpow_left ha (zpow_mem ha r) ((Commute.refl a).zpow_right r) p,
      sigmaClass_zpow_right ha ha (Commute.refl a) r, sigmaClass_self Λ a]
    simp only [smul_zero]
  have t2 : sigmaClass Λ (a ^ p) (b ^ s) = (p * s) • sigmaClass Λ a b := by
    rw [sigmaClass_zpow_left ha (zpow_mem hb s) (hab.zpow_right s) p,
      sigmaClass_zpow_right ha hb hab s, smul_smul]
  have t3 : sigmaClass Λ (b ^ q) (a ^ r) = -((q * r) • sigmaClass Λ a b) := by
    rw [sigmaClass_zpow_left hb (zpow_mem ha r) (hab.symm.zpow_right r) q,
      sigmaClass_zpow_right hb ha hab.symm r, sigmaClass_comm Λ a b, smul_neg, smul_neg,
      smul_smul]
  have t4 : sigmaClass Λ (b ^ q) (b ^ s) = 0 := by
    rw [sigmaClass_zpow_left hb (zpow_mem hb s) ((Commute.refl b).zpow_right s) q,
      sigmaClass_zpow_right hb hb (Commute.refl b) s, sigmaClass_self Λ b]
    simp only [smul_zero]
  rw [step1, step2, step3, t1, t2, t3, t4, sub_smul, sub_eq_add_neg, zero_add, add_zero]

end Classes

section Memberships

/-- Additivity of the torus chain in the first variable, modulo boundaries. -/
theorem sigma_mul_left_mem_bdry {Λ : Subgroup G} {u v w : G} (hw : w ∈ Λ) (hu : u ∈ Λ)
    (huw : Commute u w) (hvw : Commute v w) :
    sigma (u * v) w - sigma u w - sigma v w ∈ BdryChains Λ 2 := by
  rw [sub_sub, sub_mem_bdry_iff, map_add]
  exact sigmaClass_add_left hw hu huw hvw

/-- `σ(u, vⁿ) - n σ(u, v)` is a boundary modulo null chains. -/
theorem sigma_zpow_right_mem_bdry {Λ : Subgroup G} {u v : G} (hu : u ∈ Λ) (hv : v ∈ Λ)
    (huv : Commute u v) (n : ℤ) :
    sigma u (v ^ n) - n • sigma u v ∈ BdryChains Λ 2 := by
  rw [sub_mem_bdry_iff, map_zsmul]
  exact sigmaClass_zpow_right hu hv huv n

/-- `σ(uⁿ, v) - n σ(u, v)` is a boundary modulo null chains. -/
theorem sigma_zpow_left_mem_bdry {Λ : Subgroup G} {u v : G} (hu : u ∈ Λ) (hv : v ∈ Λ)
    (huv : Commute u v) (n : ℤ) :
    sigma (u ^ n) v - n • sigma u v ∈ BdryChains Λ 2 := by
  rw [sub_mem_bdry_iff, map_zsmul]
  exact sigmaClass_zpow_left hu hv huv n

/-- **The determinant formula.** For commuting `a, b ∈ Λ` and integers `p, q, r, s`, the torus
chain `σ(aᵖbᵍ, aʳbˢ)` equals `(ps - qr) σ(a, b)` modulo boundaries. -/
theorem sigma_word_mem_bdry {Λ : Subgroup G} {a b : G} (ha : a ∈ Λ) (hb : b ∈ Λ)
    (hab : Commute a b) (p q r s : ℤ) :
    sigma (a ^ p * b ^ q) (a ^ r * b ^ s) - (p * s - q * r) • sigma a b ∈
      BdryChains Λ 2 := by
  rw [sub_mem_bdry_iff, map_zsmul]
  exact sigmaClass_word ha hb hab p q r s

end Memberships

end TernaryPeriodPolynomials.BoundaryDuality.L2Torus
