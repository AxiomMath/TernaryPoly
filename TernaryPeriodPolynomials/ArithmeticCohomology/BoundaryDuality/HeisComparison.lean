module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.L2Assembly
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Abel

@[expose] public section


/-!
# The orientation comparisons at the three complete flags

Let `X = I + E₀₁`, `Y = I + E₁₂` and `Z = I + E₀₂`. These span the integral Heisenberg group `H` of
matrices `[[1, a, c], [0, 1, b], [0, 0, 1]]`, in which `XY = YXZ` and `Z` is central. At the base
complete flag `e₀` the group `H` lies in the stabilizer of the plane `P₀`. The cusp cycle of the
line `L₀` is `P_Y σ_Q - ρ_Y` with `σ_Q = σ(X, Z)`, and the cusp cycle of the plane `P₀` is
`P_X σ_P - ρ_X` with `σ_P = σ(Z, Y)`.

The corrections `ρ` are determined only up to boundaries modulo the lattice. Since
`Y⁻¹XY = XZ` and `Y⁻¹ZY = Z`, the torus relation shows that `ρ'_Y = -[Z|X|Z]` has the required
boundary; likewise `X⁻¹ZX = Z` and `X⁻¹YX = YZ⁻¹` give `ρ'_X = -[Z|YZ⁻¹|Z]`. As `H³` of the
lattices vanishes, every invariant three-cocycle takes the same value on `ρ` and on `ρ'`.

For an `H`-invariant three-cocycle `κ`, normalizing the vertices of an explicit chain by left
translation to first vertex `1` reduces the comparison to an identity between values `κ(1, a, b, c)`
with Heisenberg coordinates. The chain `(P_Y σ_Q - ρ'_Y) - (P_X σ_P - ρ'_X)` is, modulo left
translation by `H`, the boundary of the four-chain
`-(1, Z, YZ, XY, XYZ) + (1, Z, XZ, XY, XYZ) + (1, Y, YZ, XY, XYZ) - (1, X, XZ, XY, XYZ)`.
Since `κ` is a cocycle it vanishes on this boundary, so `κ(C_{L₀}(T)) = κ(C_{P₀}(T₀))`.

At `e₂` the stabilizer is the image of `H` under `(a, b, c) ↦ [[1, b, 0], [0, 1, 0], [3a, 3c, 1]]`,
with the same group law, the line lattice `⟨X, Z⟩` with Levi element `Y`, and the plane lattice
`⟨Y, Z⟩` with Levi element `X`. The plane torus chain is `σ(Y, Z) = -σ(Z, Y)`, so the same
four-chain gives `κ(C_{L₁}(T₀)) = -κ(C_{P₁}(L'))`. At `e₁` the stabilizer is the image of
`(a, b, c) ↦ [[1, c, a], [0, 1, 0], [0, 3b, 1]]`, a Heisenberg group with the commutator relation
`XY = YXZ³`. The corrections are sums of three bar chains (`Z³` is reached in three steps), and a
four-chain with coefficients `±1/2` gives `κ(C_{L₀}(L)) = -κ(C_{P₁}(T'))`. These are the three
hypotheses of `traceData_of_comparisons`, which gives the boundary trace `isBoundaryTrace_L2`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein

namespace TernaryPeriodPolynomials.BoundaryDuality.HeisComparison

open TernaryPeriodPolynomials.Duality (differentialThreeRaw)
open TernaryPeriodPolynomials.TopVanishing (homogeneousBoundary)
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains
  (NullChains levelStabilizer)
open TernaryPeriodPolynomials.BoundaryDuality.ChainCalculus (Chains)
open TernaryPeriodPolynomials.BoundaryDuality.ChainDuality (mem_bdryChains_iff)
open TernaryPeriodPolynomials.BoundaryDuality.LowVanishing
  (TopVanishingThree mem_bdryChains_of_cycle)
open TernaryPeriodPolynomials.BoundaryDuality.ChiHom
  (IsLevi rho rho_spec conjugate)
open TernaryPeriodPolynomials.BoundaryDuality.L2Prism (prism2 prism2_vec)
open TernaryPeriodPolynomials.BoundaryDuality.L2Torus
  (sigma bar2 bar3 sigma_comm sigma_self torus_three_chain_sub_mem_null)
open TernaryPeriodPolynomials.BoundaryDuality.L2Matrices
open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly
  (latL0 latP0 latL1 latP1 cycleT cycleT₀P cycleL cycleT' cycleT₀L cycleL' isLevi_T isLevi_T₀_P₀
    isLevi_L isLevi_T' isLevi_T₀_L₁ isLevi_L' conjugate_sigma Comparison traceData_of_comparisons
    isBoundaryTrace_of_comparisons)

/-! ### Heisenberg coordinates and embeddings -/

/-- Heisenberg coordinates `(a, b, c)`. -/
abbrev HeisCoord : Type := ℤ × ℤ × ℤ

/-- The product of Heisenberg coordinates:
`(a, b, c)(a', b', c') = (a + a', b + b', c + c' + a b')`. -/
def heisMul (p q : HeisCoord) : HeisCoord :=
  (p.1 + q.1, p.2.1 + q.2.1, p.2.2 + q.2.2 + p.1 * q.2.1)

/-- The product of coordinates with commutator three:
`(a, b, c)(a', b', c') = (a + a', b + b', c + c' + 3 a b')`. -/
def heisMul3 (p q : HeisCoord) : HeisCoord :=
  (p.1 + q.1, p.2.1 + q.2.1, p.2.2 + q.2.2 + 3 * (p.1 * q.2.1))

/-- Verification of a small closed identity between Heisenberg coordinates. -/
local macro "hdec" : tactic => `(tactic| first | decide | rfl | norm_num [heisMul, heisMul3])

/-- Entrywise verification of an identity between explicit `3 × 3` matrices. -/
local macro "heis_entries" : tactic =>
  `(tactic| (ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring))

/-- The value `κ(1, φ p, φ q, φ r)` of a cochain on a tetrahedron with first vertex `1`. -/
def embVal (φ : HeisCoord → RationalGL3) (κ : (Fin 4 → RationalGL3) → ℂ) (p q r : HeisCoord) : ℂ :=
  κ ![1, φ p, φ q, φ r]

/-- Multiplication in an embedding, with a stated product. -/
theorem emb_mul_eq (φ : HeisCoord → RationalGL3) (mul : HeisCoord → HeisCoord → HeisCoord)
    (hφ : ∀ p q, φ p * φ q = φ (mul p q)) {p q r : HeisCoord} (e : mul p q = r) :
    φ p * φ q = φ r := by
  rw [hφ, e]

/-- Conjugation in an embedding, from a relation `q p = p s` of coordinates. -/
theorem emb_conj (φ : HeisCoord → RationalGL3) (mul : HeisCoord → HeisCoord → HeisCoord)
    (hφ : ∀ p q, φ p * φ q = φ (mul p q)) {p q s : HeisCoord} (e : mul q p = mul p s) :
    (φ p)⁻¹ * φ q * φ p = φ s := by
  rw [mul_assoc, inv_mul_eq_iff_eq_mul, hφ, hφ, e]

/-- Elements of an embedding whose coordinate products agree commute. -/
theorem emb_commute (φ : HeisCoord → RationalGL3) (mul : HeisCoord → HeisCoord → HeisCoord)
    (hφ : ∀ p q, φ p * φ q = φ (mul p q)) {p q : HeisCoord} (e : mul p q = mul q p) :
    Commute (φ p) (φ q) := by
  show φ p * φ q = φ q * φ p
  rw [hφ, hφ, e]

/-- Left translation by an element of an invariance group normalizes the first vertex. -/
theorem emb_face (φ : HeisCoord → RationalGL3) (mul : HeisCoord → HeisCoord → HeisCoord)
    (hφ : ∀ p q, φ p * φ q = φ (mul p q)) {Λ : Subgroup RationalGL3}
    {κ : (Fin 4 → RationalGL3) → ℂ} (hκ : ∀ (γ : Λ) x, κ (fun i => γ.val * x i) = κ x)
    (p1 p2 p3 p4 q2 q3 q4 : HeisCoord) (hp1 : φ p1 ∈ Λ) (e2 : mul p1 q2 = p2)
    (e3 : mul p1 q3 = p3) (e4 : mul p1 q4 = p4) :
    κ ![φ p1, φ p2, φ p3, φ p4] = embVal φ κ q2 q3 q4 := by
  have hinv : (φ p1)⁻¹ ∈ Λ := Λ.inv_mem hp1
  have h := hκ ⟨(φ p1)⁻¹, hinv⟩ ![φ p1, φ p2, φ p3, φ p4]
  have hv : (fun i => ((⟨(φ p1)⁻¹, hinv⟩ : Λ) : RationalGL3) *
      ![φ p1, φ p2, φ p3, φ p4] i) = ![1, φ q2, φ q3, φ q4] := by
    funext i
    fin_cases i
    · exact inv_mul_cancel (φ p1)
    · show (φ p1)⁻¹ * φ p2 = φ q2
      rw [inv_mul_eq_iff_eq_mul, hφ, e2]
    · show (φ p1)⁻¹ * φ p3 = φ q3
      rw [inv_mul_eq_iff_eq_mul, hφ, e3]
    · show (φ p1)⁻¹ * φ p4 = φ q4
      rw [inv_mul_eq_iff_eq_mul, hφ, e4]
  exact h.symm.trans (congrArg κ hv)

/-- The cocycle condition on the four-simplex `(1, φ p₁, φ p₂, φ p₃, φ p₄)`, with the face
`(φ p₁, φ p₂, φ p₃, φ p₄)` normalized to first vertex `1`. -/
theorem emb_cocycle (φ : HeisCoord → RationalGL3) (mul : HeisCoord → HeisCoord → HeisCoord)
    (hφ : ∀ p q, φ p * φ q = φ (mul p q)) {Λ : Subgroup RationalGL3}
    {κ : (Fin 4 → RationalGL3) → ℂ} (hκ : ∀ (γ : Λ) x, κ (fun i => γ.val * x i) = κ x)
    (closed : ∀ x, differentialThreeRaw κ x = 0)
    (p1 p2 p3 p4 q2 q3 q4 : HeisCoord) (hp1 : φ p1 ∈ Λ) (e2 : mul p1 q2 = p2)
    (e3 : mul p1 q3 = p3) (e4 : mul p1 q4 = p4) :
    embVal φ κ q2 q3 q4 - embVal φ κ p2 p3 p4 + embVal φ κ p1 p3 p4 - embVal φ κ p1 p2 p4 +
      embVal φ κ p1 p2 p3 = 0 := by
  have h : κ ![φ p1, φ p2, φ p3, φ p4] - κ ![1, φ p2, φ p3, φ p4] +
      κ ![1, φ p1, φ p3, φ p4] - κ ![1, φ p1, φ p2, φ p4] +
        κ ![1, φ p1, φ p2, φ p3] = 0 :=
    by
      exact closed ![1, φ p1, φ p2, φ p3, φ p4]
  rw [emb_face φ mul hφ hκ p1 p2 p3 p4 q2 q3 q4 hp1 e2 e3 e4] at h
  exact h

/-- The value of a scalar cochain on the prism of a torus chain. -/
theorem ev_prism2_sigma {G : Type} [Group G] (κ : (Fin 4 → G) → ℂ) (u v h : G) :
    Finsupp.linearCombination ℂ κ (prism2 h (sigma u v)) =
      κ ![1, 1 * h, u * h, u * v * h] - κ ![1, u, u * h, u * v * h] +
          κ ![1, u, u * v, u * v * h] -
        (κ ![1, 1 * h, v * h, v * u * h] - κ ![1, v, v * h, v * u * h] +
          κ ![1, v, v * u, v * u * h]) := by
  simp only [sigma, bar2, map_sub, prism2_vec, map_add, Finsupp.linearCombination_single,
    one_smul]

/-- The value of a scalar cochain on the prism of a torus chain in an embedding, with the products
of the coordinates given. -/
theorem ev_prism2_sigma_emb (φ : HeisCoord → RationalGL3)
    (mul : HeisCoord → HeisCoord → HeisCoord) (hφ : ∀ p q, φ p * φ q = φ (mul p q))
    (κ : (Fin 4 → RationalGL3) → ℂ)
    (u v h uh vh uv vu uvh vuh : HeisCoord) (e1 : mul u h = uh) (e2 : mul v h = vh)
    (e3 : mul u v = uv) (e4 : mul v u = vu) (e5 : mul uv h = uvh) (e6 : mul vu h = vuh) :
    Finsupp.linearCombination ℂ κ (prism2 (φ h) (sigma (φ u) (φ v))) =
      embVal φ κ h uh uvh - embVal φ κ u uh uvh + embVal φ κ u uv uvh -
        (embVal φ κ h vh vuh - embVal φ κ v vh vuh + embVal φ κ v vu vuh) := by
  rw [ev_prism2_sigma]
  simp only [one_mul, hφ, e1, e2, e3, e4, e5, e6, embVal]

/-- The value of a scalar cochain on a bar chain in an embedding, with the products of the
coordinates given. -/
theorem ev_bar3_emb (φ : HeisCoord → RationalGL3) (mul : HeisCoord → HeisCoord → HeisCoord)
    (hφ : ∀ p q, φ p * φ q = φ (mul p q)) (κ : (Fin 4 → RationalGL3) → ℂ)
    (u v w uv uvw : HeisCoord) (e1 : mul u v = uv) (e2 : mul uv w = uvw) :
    Finsupp.linearCombination ℂ κ (bar3 (φ u) (φ v) (φ w)) = embVal φ κ u uv uvw := by
  simp only [bar3, Finsupp.linearCombination_single, one_smul, hφ, e1, e2, embVal]

/-! ### The corrections `ρ'` -/

/-- A cocycle takes the same value on the chosen correction `ρ_m` and on any other correction
`ρ'` with `m⁻¹σm - σ - ∂ρ'` null modulo `U`, when `H³(U) = 0`. -/
theorem ev_rho_eq {G : Type} [Group G] {Λ U : Subgroup G} {σ : Chains G 2} {m : G}
    (hm : IsLevi Λ U σ m) (hU : TopVanishingThree U) (ρ' : Chains G 3)
    (hρ' : conjugate m 2 σ - σ - homogeneousBoundary 3 ρ' ∈ NullChains U 2)
    (κ : (Fin 4 → G) → ℂ) (hκ : ∀ (γ : U) x, κ (fun i => γ.val * x i) = κ x)
    (closed : ∀ x, differentialThreeRaw κ x = 0) :
    Finsupp.linearCombination ℂ κ (rho σ hm) = Finsupp.linearCombination ℂ κ ρ' := by
  have hcyc : homogeneousBoundary 3 (rho σ hm - ρ') ∈ NullChains U 2 := by
    have e : homogeneousBoundary 3 (rho σ hm - ρ') =
        (conjugate m 2 σ - σ - homogeneousBoundary 3 ρ') -
          (conjugate m 2 σ - σ - homogeneousBoundary 3 (rho σ hm)) := by
      rw [map_sub]
      abel
    rw [e]
    exact sub_mem hρ' (rho_spec σ hm)
  have hb := (mem_bdryChains_iff U _).mp (mem_bdryChains_of_cycle hU hcyc) κ hκ closed
  rw [map_sub, sub_eq_zero] at hb
  exact hb

/-- The torus relation `∂[z|x|z] ≡ σ(z, xz) - σ(z, x)` modulo null chains, for commuting
`z, x ∈ Λ`. -/
theorem torus_key {G : Type} [Group G] {Λ : Subgroup G} {z x : G} (hz : z ∈ Λ) (hx : x ∈ Λ)
    (hzx : Commute z x) :
    homogeneousBoundary 3 (bar3 z x z) - (sigma z (x * z) - sigma z x) ∈ NullChains Λ 2 := by
  have h := torus_three_chain_sub_mem_null hz hx hzx (Commute.refl z)
  rwa [sub_add_cancel, sigma_self, sub_zero] at h

/-! ### The core identities -/

/-- **The Heisenberg identity** (law `c + c' + a b'`). For an embedding `φ` of the Heisenberg
coordinates, and a three-cocycle invariant under a group containing its image,
`κ(P_Y σ(X, Z)) + κ[Z|X|Z] = κ(P_X σ(Z, Y)) + κ[Z|YZ⁻¹|Z]`. -/
theorem core_e₀ (φ : HeisCoord → RationalGL3) (hφ : ∀ p q, φ p * φ q = φ (heisMul p q))
    {Λ : Subgroup RationalGL3} {κ : (Fin 4 → RationalGL3) → ℂ}
    (hκ : ∀ (γ : Λ) x, κ (fun i => γ.val * x i) = κ x) (hmem : ∀ p, φ p ∈ Λ)
    (closed : ∀ x, differentialThreeRaw κ x = 0) :
    Finsupp.linearCombination ℂ κ
        (prism2 (φ (0, 1, 0)) (sigma (φ (1, 0, 0)) (φ (0, 0, 1)))) +
      Finsupp.linearCombination ℂ κ (bar3 (φ (0, 0, 1)) (φ (1, 0, 0)) (φ (0, 0, 1))) =
    Finsupp.linearCombination ℂ κ
        (prism2 (φ (1, 0, 0)) (sigma (φ (0, 0, 1)) (φ (0, 1, 0)))) +
      Finsupp.linearCombination ℂ κ (bar3 (φ (0, 0, 1)) (φ (0, 1, -1)) (φ (0, 0, 1))) := by
  have q1 := ev_prism2_sigma_emb φ heisMul hφ κ
    (1, 0, 0) (0, 0, 1) (0, 1, 0)
    (1, 1, 1) (0, 1, 1) (1, 0, 1) (1, 0, 1) (1, 1, 2) (1, 1, 2)
    (by hdec) (by hdec) (by hdec) (by hdec) (by hdec) (by hdec)
  have q2 := ev_prism2_sigma_emb φ heisMul hφ κ
    (0, 0, 1) (0, 1, 0) (1, 0, 0)
    (1, 0, 1) (1, 1, 0) (0, 1, 1) (0, 1, 1) (1, 1, 1) (1, 1, 1)
    (by hdec) (by hdec) (by hdec) (by hdec) (by hdec) (by hdec)
  have b1 := ev_bar3_emb φ heisMul hφ κ (0, 0, 1) (1, 0, 0) (0, 0, 1) (1, 0, 1) (1, 0, 2)
    (by hdec) (by hdec)
  have b2 := ev_bar3_emb φ heisMul hφ κ (0, 0, 1) (0, 1, -1) (0, 0, 1) (0, 1, 0) (0, 1, 1)
    (by hdec) (by hdec)
  have c1 := emb_cocycle φ heisMul hφ hκ closed
    (0, 0, 1) (0, 1, 1) (1, 1, 1) (1, 1, 2)
    (0, 1, 0) (1, 1, 0) (1, 1, 1)
    (hmem _) (by hdec) (by hdec) (by hdec)
  have c2 := emb_cocycle φ heisMul hφ hκ closed
    (0, 0, 1) (1, 0, 1) (1, 1, 1) (1, 1, 2)
    (1, 0, 0) (1, 1, 0) (1, 1, 1)
    (hmem _) (by hdec) (by hdec) (by hdec)
  have c3 := emb_cocycle φ heisMul hφ hκ closed
    (0, 1, 0) (0, 1, 1) (1, 1, 1) (1, 1, 2)
    (0, 0, 1) (1, 0, 1) (1, 0, 2)
    (hmem _) (by hdec) (by hdec) (by hdec)
  have c4 := emb_cocycle φ heisMul hφ hκ closed
    (1, 0, 0) (1, 0, 1) (1, 1, 1) (1, 1, 2)
    (0, 0, 1) (0, 1, 0) (0, 1, 1)
    (hmem _) (by hdec) (by hdec) (by hdec)
  linear_combination q1 + b1 - q2 - b2 + (-1 : ℂ) * c1 + (1 : ℂ) * c2 + (1 : ℂ) * c3 + (-1 : ℂ) * c4

/-- **The identity with commutator three** (law `c + c' + 3 a b'`). For an embedding `φ` and a
three-cocycle invariant under a group containing its image, with `Y` the generator of the
second coordinate, `x_k = X Z^k` and `v_k = Y Z^(k-3)`:
`κ(P_Y σ(Z, X)) - Σ κ[Z|x_k|Z] + κ(P_X σ(Z, Y)) + Σ κ[Z|v_k|Z] = 0`. -/
theorem core_e₁ (φ : HeisCoord → RationalGL3) (hφ : ∀ p q, φ p * φ q = φ (heisMul3 p q))
    {Λ : Subgroup RationalGL3} {κ : (Fin 4 → RationalGL3) → ℂ}
    (hκ : ∀ (γ : Λ) x, κ (fun i => γ.val * x i) = κ x) (hmem : ∀ p, φ p ∈ Λ)
    (closed : ∀ x, differentialThreeRaw κ x = 0) :
    Finsupp.linearCombination ℂ κ
        (prism2 (φ (0, 1, 0)) (sigma (φ (0, 0, 1)) (φ (1, 0, 0)))) -
      (Finsupp.linearCombination ℂ κ (bar3 (φ (0, 0, 1)) (φ (1, 0, 0)) (φ (0, 0, 1))) +
        Finsupp.linearCombination ℂ κ (bar3 (φ (0, 0, 1)) (φ (1, 0, 1)) (φ (0, 0, 1))) +
        Finsupp.linearCombination ℂ κ (bar3 (φ (0, 0, 1)) (φ (1, 0, 2)) (φ (0, 0, 1)))) +
      Finsupp.linearCombination ℂ κ
        (prism2 (φ (1, 0, 0)) (sigma (φ (0, 0, 1)) (φ (0, 1, 0)))) +
      (Finsupp.linearCombination ℂ κ (bar3 (φ (0, 0, 1)) (φ (0, 1, -3)) (φ (0, 0, 1))) +
        Finsupp.linearCombination ℂ κ (bar3 (φ (0, 0, 1)) (φ (0, 1, -2)) (φ (0, 0, 1))) +
        Finsupp.linearCombination ℂ κ (bar3 (φ (0, 0, 1)) (φ (0, 1, -1)) (φ (0, 0, 1)))) = 0 := by
  have q1 := ev_prism2_sigma_emb φ heisMul3 hφ κ
    (0, 0, 1) (1, 0, 0) (0, 1, 0)
    (0, 1, 1) (1, 1, 3) (1, 0, 1) (1, 0, 1) (1, 1, 4) (1, 1, 4)
    (by hdec) (by hdec) (by hdec) (by hdec) (by hdec) (by hdec)
  have q2 := ev_prism2_sigma_emb φ heisMul3 hφ κ
    (0, 0, 1) (0, 1, 0) (1, 0, 0)
    (1, 0, 1) (1, 1, 0) (0, 1, 1) (0, 1, 1) (1, 1, 1) (1, 1, 1)
    (by hdec) (by hdec) (by hdec) (by hdec) (by hdec) (by hdec)
  have b0 := ev_bar3_emb φ heisMul3 hφ κ (0, 0, 1) (1, 0, 0) (0, 0, 1) (1, 0, 1) (1, 0, 2)
    (by hdec) (by hdec)
  have b1 := ev_bar3_emb φ heisMul3 hφ κ (0, 0, 1) (1, 0, 1) (0, 0, 1) (1, 0, 2) (1, 0, 3)
    (by hdec) (by hdec)
  have b2 := ev_bar3_emb φ heisMul3 hφ κ (0, 0, 1) (1, 0, 2) (0, 0, 1) (1, 0, 3) (1, 0, 4)
    (by hdec) (by hdec)
  have d0 := ev_bar3_emb φ heisMul3 hφ κ (0, 0, 1) (0, 1, -3) (0, 0, 1) (0, 1, -2) (0, 1, -1)
    (by hdec) (by hdec)
  have d1 := ev_bar3_emb φ heisMul3 hφ κ (0, 0, 1) (0, 1, -2) (0, 0, 1) (0, 1, -1) (0, 1, 0)
    (by hdec) (by hdec)
  have d2 := ev_bar3_emb φ heisMul3 hφ κ (0, 0, 1) (0, 1, -1) (0, 0, 1) (0, 1, 0) (0, 1, 1)
    (by hdec) (by hdec)
  have c1 := emb_cocycle φ heisMul3 hφ hκ closed
    (0, 0, 1) (0, 1, -2) (0, 1, -1) (0, 1, 0)
    (0, 1, -3) (0, 1, -2) (0, 1, -1)
    (hmem _) (by hdec) (by hdec) (by hdec)
  have c2 := emb_cocycle φ heisMul3 hφ hκ closed
    (0, 0, 1) (0, 1, -1) (0, 1, 0) (0, 1, 1)
    (0, 1, -2) (0, 1, -1) (0, 1, 0)
    (hmem _) (by hdec) (by hdec) (by hdec)
  have c3 := emb_cocycle φ heisMul3 hφ hκ closed
    (0, 0, 1) (0, 1, 1) (1, 1, 1) (1, 1, 2)
    (0, 1, 0) (1, 1, 0) (1, 1, 1)
    (hmem _) (by hdec) (by hdec) (by hdec)
  have c4 := emb_cocycle φ heisMul3 hφ hκ closed
    (0, 0, 1) (0, 1, 1) (1, 1, 1) (1, 1, 3)
    (0, 1, 0) (1, 1, 0) (1, 1, 2)
    (hmem _) (by hdec) (by hdec) (by hdec)
  have c5 := emb_cocycle φ heisMul3 hφ hκ closed
    (0, 0, 1) (0, 1, 1) (1, 1, 2) (1, 1, 4)
    (0, 1, 0) (1, 1, 1) (1, 1, 3)
    (hmem _) (by hdec) (by hdec) (by hdec)
  have c6 := emb_cocycle φ heisMul3 hφ hκ closed
    (0, 0, 1) (0, 1, 1) (1, 1, 3) (1, 1, 4)
    (0, 1, 0) (1, 1, 2) (1, 1, 3)
    (hmem _) (by hdec) (by hdec) (by hdec)
  have c7 := emb_cocycle φ heisMul3 hφ hκ closed
    (0, 0, 1) (1, 0, 1) (1, 0, 2) (1, 0, 3)
    (1, 0, 0) (1, 0, 1) (1, 0, 2)
    (hmem _) (by hdec) (by hdec) (by hdec)
  have c8 := emb_cocycle φ heisMul3 hφ hκ closed
    (0, 0, 1) (1, 0, 1) (1, 1, 1) (1, 1, 2)
    (1, 0, 0) (1, 1, 0) (1, 1, 1)
    (hmem _) (by hdec) (by hdec) (by hdec)
  have c9 := emb_cocycle φ heisMul3 hφ hκ closed
    (0, 0, 1) (1, 0, 1) (1, 1, 1) (1, 1, 3)
    (1, 0, 0) (1, 1, 0) (1, 1, 2)
    (hmem _) (by hdec) (by hdec) (by hdec)
  have c10 := emb_cocycle φ heisMul3 hφ hκ closed
    (0, 0, 1) (1, 0, 1) (1, 1, 2) (1, 1, 4)
    (1, 0, 0) (1, 1, 1) (1, 1, 3)
    (hmem _) (by hdec) (by hdec) (by hdec)
  have c11 := emb_cocycle φ heisMul3 hφ hκ closed
    (0, 0, 1) (1, 0, 1) (1, 1, 3) (1, 1, 4)
    (1, 0, 0) (1, 1, 2) (1, 1, 3)
    (hmem _) (by hdec) (by hdec) (by hdec)
  have c12 := emb_cocycle φ heisMul3 hφ hκ closed
    (0, 0, 1) (1, 0, 2) (1, 0, 3) (1, 0, 4)
    (1, 0, 1) (1, 0, 2) (1, 0, 3)
    (hmem _) (by hdec) (by hdec) (by hdec)
  have c13 := emb_cocycle φ heisMul3 hφ hκ closed
    (0, 1, 0) (0, 1, 1) (1, 1, 1) (1, 1, 2)
    (0, 0, 1) (1, 0, 1) (1, 0, 2)
    (hmem _) (by hdec) (by hdec) (by hdec)
  have c14 := emb_cocycle φ heisMul3 hφ hκ closed
    (0, 1, 0) (0, 1, 1) (1, 1, 1) (1, 1, 3)
    (0, 0, 1) (1, 0, 1) (1, 0, 3)
    (hmem _) (by hdec) (by hdec) (by hdec)
  have c15 := emb_cocycle φ heisMul3 hφ hκ closed
    (0, 1, 0) (0, 1, 1) (1, 1, 2) (1, 1, 4)
    (0, 0, 1) (1, 0, 2) (1, 0, 4)
    (hmem _) (by hdec) (by hdec) (by hdec)
  have c16 := emb_cocycle φ heisMul3 hφ hκ closed
    (0, 1, 0) (0, 1, 1) (1, 1, 3) (1, 1, 4)
    (0, 0, 1) (1, 0, 3) (1, 0, 4)
    (hmem _) (by hdec) (by hdec) (by hdec)
  have c17 := emb_cocycle φ heisMul3 hφ hκ closed
    (0, 1, 0) (1, 1, 0) (1, 1, 1) (1, 1, 2)
    (1, 0, 0) (1, 0, 1) (1, 0, 2)
    (hmem _) (by hdec) (by hdec) (by hdec)
  have c18 := emb_cocycle φ heisMul3 hφ hκ closed
    (0, 1, 0) (1, 1, 2) (1, 1, 3) (1, 1, 4)
    (1, 0, 2) (1, 0, 3) (1, 0, 4)
    (hmem _) (by hdec) (by hdec) (by hdec)
  have c19 := emb_cocycle φ heisMul3 hφ hκ closed
    (1, 0, 0) (1, 0, 1) (1, 1, 1) (1, 1, 2)
    (0, 0, 1) (0, 1, -2) (0, 1, -1)
    (hmem _) (by hdec) (by hdec) (by hdec)
  have c20 := emb_cocycle φ heisMul3 hφ hκ closed
    (1, 0, 0) (1, 0, 1) (1, 1, 1) (1, 1, 3)
    (0, 0, 1) (0, 1, -2) (0, 1, 0)
    (hmem _) (by hdec) (by hdec) (by hdec)
  have c21 := emb_cocycle φ heisMul3 hφ hκ closed
    (1, 0, 0) (1, 0, 1) (1, 1, 2) (1, 1, 4)
    (0, 0, 1) (0, 1, -1) (0, 1, 1)
    (hmem _) (by hdec) (by hdec) (by hdec)
  have c22 := emb_cocycle φ heisMul3 hφ hκ closed
    (1, 0, 0) (1, 0, 1) (1, 1, 3) (1, 1, 4)
    (0, 0, 1) (0, 1, 0) (0, 1, 1)
    (hmem _) (by hdec) (by hdec) (by hdec)
  have c23 := emb_cocycle φ heisMul3 hφ hκ closed
    (1, 0, 0) (1, 1, 0) (1, 1, 1) (1, 1, 2)
    (0, 1, -3) (0, 1, -2) (0, 1, -1)
    (hmem _) (by hdec) (by hdec) (by hdec)
  have c24 := emb_cocycle φ heisMul3 hφ hκ closed
    (1, 0, 0) (1, 1, 2) (1, 1, 3) (1, 1, 4)
    (0, 1, -1) (0, 1, 0) (0, 1, 1)
    (hmem _) (by hdec) (by hdec) (by hdec)
  linear_combination q1 - b0 - b1 - b2 + q2 + d0 + d1 + d2 +
    (1 / 2 : ℂ) * c1 +
    (1 / 2 : ℂ) * c2 +
    (1 / 2 : ℂ) * c3 +
    (1 / 2 : ℂ) * c4 +
    (1 / 2 : ℂ) * c5 +
    (1 / 2 : ℂ) * c6 +
    (-1 / 2 : ℂ) * c7 +
    (-1 / 2 : ℂ) * c8 +
    (-1 / 2 : ℂ) * c9 +
    (-1 / 2 : ℂ) * c10 +
    (-1 / 2 : ℂ) * c11 +
    (-1 / 2 : ℂ) * c12 +
    (-1 / 2 : ℂ) * c13 +
    (-1 / 2 : ℂ) * c14 +
    (-1 / 2 : ℂ) * c15 +
    (-1 / 2 : ℂ) * c16 +
    (1 / 2 : ℂ) * c17 +
    (-1 / 2 : ℂ) * c18 +
    (1 / 2 : ℂ) * c19 +
    (1 / 2 : ℂ) * c20 +
    (1 / 2 : ℂ) * c21 +
    (1 / 2 : ℂ) * c22 +
    (-1 / 2 : ℂ) * c23 +
    (1 / 2 : ℂ) * c24

/-! ### The complete flag `e₀` -/

/-- The Heisenberg matrix with coordinates `p`, as an element of `GL₃(ℤ)`. -/
def heisInt (p : HeisCoord) : IntegralGL3 :=
  mkInt !![1, p.1, p.2.2; 0, 1, p.2.1; 0, 0, 1]
    !![1, -p.1, p.1 * p.2.1 - p.2.2; 0, 1, -p.2.1; 0, 0, 1]
    (by heis_entries) (by heis_entries)

/-- The matrix of `heisInt p`. -/
theorem heisInt_val (p : HeisCoord) :
    (heisInt p).val = !![1, p.1, p.2.2; 0, 1, p.2.1; 0, 0, 1] := rfl

/-- Multiplication of Heisenberg matrices in `GL₃(ℤ)`. -/
theorem heisInt_mul (p q : HeisCoord) : heisInt p * heisInt q = heisInt (heisMul p q) := by
  apply Units.ext
  simp only [Units.val_mul, heisInt_val, heisMul]
  heis_entries

/-- The Heisenberg matrix with coordinates `p`, as an element of `GL₃(ℚ)`. -/
def heisQ (p : HeisCoord) : RationalGL3 := embedZ (heisInt p)

/-- Multiplication of Heisenberg matrices in `GL₃(ℚ)`. -/
theorem heisQ_mul (p q : HeisCoord) : heisQ p * heisQ q = heisQ (heisMul p q) := by
  show embedZ (heisInt p) * embedZ (heisInt q) = embedZ (heisInt (heisMul p q))
  rw [← map_mul, heisInt_mul]

/-- The lattice element `I + x E₀₁ + y E₀₂` has coordinates `(x, 0, y)`. -/
theorem uL0_eq_heisQ (x y : ℤ) : uL0 x y = heisQ (x, 0, y) := by
  show embedZ (zuL0 x y) = embedZ (heisInt (x, 0, y))
  refine congrArg embedZ (Units.ext ?_)
  rfl

/-- The lattice element `I + x E₀₂ + y E₁₂` has coordinates `(0, y, x)`. -/
theorem uP0_eq_heisQ (x y : ℤ) : uP0 x y = heisQ (0, y, x) := by
  show embedZ (zuP0 x y) = embedZ (heisInt (0, y, x))
  refine congrArg embedZ (Units.ext ?_)
  rfl

/-- The element `T = I + E₁₂` has coordinates `(0, 1, 0)`. -/
theorem T_eq_heisQ : T = heisQ (0, 1, 0) := by
  show embedZ zT = embedZ (heisInt (0, 1, 0))
  refine congrArg embedZ (Units.ext ?_)
  rfl

/-- The element `T₀ = I + E₀₁` has coordinates `(1, 0, 0)`. -/
theorem T₀_eq_heisQ : T₀ = heisQ (1, 0, 0) := by
  show embedZ zT₀ = embedZ (heisInt (1, 0, 0))
  refine congrArg embedZ (Units.ext ?_)
  rfl

/-- Heisenberg matrices lie in the arithmetic level. -/
theorem heisQ_mem_level (p : HeisCoord) : heisQ p ∈ rationalLevel :=
  embedZ_mem_rationalLevel (heisInt p) 0 0 (by simp [heisInt_val]) (by simp [heisInt_val])
    (by simp [heisInt_val])

/-- Heisenberg matrices stabilize the plane `P₀` in the level. -/
theorem heisQ_mem_P₀ (p : HeisCoord) : heisQ p ∈ levelStabilizer P₀ :=
  mem_levelStabilizer_one (H := parabolic .plane) (heisQ_mem_level p)
    (mem_planeParabolic (heisInt p) (by simp [heisInt_val]) (by simp [heisInt_val]))

/-- The lattice of `L₀` lies in the stabilizer of `P₀`. -/
theorem latL0_le_P₀ : latL0.sub ≤ levelStabilizer P₀ := by
  rintro _ ⟨t, rfl⟩
  have h := heisQ_mem_P₀ ((Multiplicative.toAdd t).1, 0, (Multiplicative.toAdd t).2)
  rw [← uL0_eq_heisQ] at h
  exact h

/-- The lattice of `P₀` lies in the stabilizer of `P₀`. -/
theorem latP0_le_P₀ : latP0.sub ≤ levelStabilizer P₀ := by
  rintro _ ⟨t, rfl⟩
  have h := heisQ_mem_P₀ (0, (Multiplicative.toAdd t).2, (Multiplicative.toAdd t).1)
  rw [← uP0_eq_heisQ] at h
  exact h

/-- Heisenberg matrices `(x, 0, y)` lie in the lattice of `L₀`. -/
theorem heisQ_mem_latL0 (x y : ℤ) : heisQ (x, 0, y) ∈ latL0.sub := by
  rw [← uL0_eq_heisQ]
  exact latL0.u_mem x y

/-- Heisenberg matrices `(0, y, x)` lie in the lattice of `P₀`. -/
theorem heisQ_mem_latP0 (x y : ℤ) : heisQ (0, y, x) ∈ latP0.sub := by
  rw [← uP0_eq_heisQ]
  exact latP0.u_mem x y

/-- The correction `ρ'_Y = -[Z|X|Z]` for the line `L₀` and `m = T`. -/
def rhoQ : Chains RationalGL3 3 :=
  -bar3 (heisQ (0, 0, 1)) (heisQ (1, 0, 0)) (heisQ (0, 0, 1))

/-- The correction `ρ'_X = -[Z|YZ⁻¹|Z]` for the plane `P₀` and `m = T₀`. -/
def rhoP : Chains RationalGL3 3 :=
  -bar3 (heisQ (0, 0, 1)) (heisQ (0, 1, -1)) (heisQ (0, 0, 1))

/-- The torus chain of the lattice of `L₀` is `σ(X, Z)`. -/
theorem sigmaQ_eq : latL0.σ = sigma (heisQ (1, 0, 0)) (heisQ (0, 0, 1)) := by
  show sigma (uL0 1 0) (uL0 0 1) = _
  rw [uL0_eq_heisQ, uL0_eq_heisQ]

/-- The torus chain of the lattice of `P₀` is `σ(Z, Y)`. -/
theorem sigmaP_eq : latP0.σ = sigma (heisQ (0, 0, 1)) (heisQ (0, 1, 0)) := by
  show sigma (uP0 1 0) (uP0 0 1) = _
  rw [uP0_eq_heisQ, uP0_eq_heisQ]

/-- Conjugation of `σ(X, Z)` by `T = Y`: `σ(XZ, Z)`. -/
theorem conj_sigmaQ : conjugate T 2 latL0.σ = sigma (heisQ (1, 0, 1)) (heisQ (0, 0, 1)) := by
  rw [sigmaQ_eq, conjugate_sigma, T_eq_heisQ,
    emb_conj heisQ heisMul heisQ_mul (p := (0, 1, 0)) (q := (1, 0, 0)) (s := (1, 0, 1))
      (by hdec),
    emb_conj heisQ heisMul heisQ_mul (p := (0, 1, 0)) (q := (0, 0, 1)) (s := (0, 0, 1))
      (by hdec)]

/-- Conjugation of `σ(Z, Y)` by `T₀ = X`: `σ(Z, YZ⁻¹)`. -/
theorem conj_sigmaP : conjugate T₀ 2 latP0.σ = sigma (heisQ (0, 0, 1)) (heisQ (0, 1, -1)) := by
  rw [sigmaP_eq, conjugate_sigma, T₀_eq_heisQ,
    emb_conj heisQ heisMul heisQ_mul (p := (1, 0, 0)) (q := (0, 0, 1)) (s := (0, 0, 1))
      (by hdec),
    emb_conj heisQ heisMul heisQ_mul (p := (1, 0, 0)) (q := (0, 1, 0)) (s := (0, 1, -1))
      (by hdec)]

/-- `ρ'_Y` is a correction for `T` at the lattice of `L₀`. -/
theorem rhoQ_mem :
    conjugate T 2 latL0.σ - latL0.σ - homogeneousBoundary 3 rhoQ ∈ NullChains latL0.sub 2 := by
  have key := torus_key (heisQ_mem_latL0 0 1) (heisQ_mem_latL0 1 0)
    (emb_commute heisQ heisMul heisQ_mul (p := (0, 0, 1)) (q := (1, 0, 0)) (by hdec))
  rw [emb_mul_eq heisQ heisMul heisQ_mul (p := (1, 0, 0)) (q := (0, 0, 1)) (r := (1, 0, 1))
    (by hdec)] at key
  rw [conj_sigmaQ, sigmaQ_eq, rhoQ, map_neg,
    sigma_comm (heisQ (0, 0, 1)) (heisQ (1, 0, 1)),
    sigma_comm (heisQ (0, 0, 1)) (heisQ (1, 0, 0))]
  convert key using 1
  abel

/-- `ρ'_X` is a correction for `T₀` at the lattice of `P₀`. -/
theorem rhoP_mem :
    conjugate T₀ 2 latP0.σ - latP0.σ - homogeneousBoundary 3 rhoP ∈ NullChains latP0.sub 2 := by
  have key := torus_key (heisQ_mem_latP0 1 0) (heisQ_mem_latP0 (-1) 1)
    (emb_commute heisQ heisMul heisQ_mul (p := (0, 0, 1)) (q := (0, 1, -1)) (by hdec))
  rw [emb_mul_eq heisQ heisMul heisQ_mul (p := (0, 1, -1)) (q := (0, 0, 1)) (r := (0, 1, 0))
    (by hdec)] at key
  rw [conj_sigmaP, sigmaP_eq, rhoP, map_neg]
  convert key using 1
  abel

/-- The cusp cycle of `T` at `L₀` is `P_T σ_Q - ρ_T`. -/
theorem cycleT_eq : cycleT = prism2 T latL0.σ - rho latL0.σ isLevi_T := rfl

/-- The cusp cycle of `T₀` at `P₀` is `P_{T₀} σ_P - ρ_{T₀}`. -/
theorem cycleT₀P_eq : cycleT₀P = prism2 T₀ latP0.σ - rho latP0.σ isLevi_T₀_P₀ := rfl

/-- **The orientation comparison at the complete flag `e₀`.** For every three-cocycle invariant
under the stabilizer of `P₀` in the level, `κ(C_{L₀}(T)) = κ(C_{P₀}(T₀))`. -/
theorem comparison_e₀ : Comparison (levelStabilizer P₀) cycleT cycleT₀P 1 := by
  intro κ hκ closed
  have hQ := ev_rho_eq isLevi_T latL0.topVanishingThree rhoQ rhoQ_mem κ
    (fun γ x => hκ ⟨γ.val, latL0_le_P₀ γ.property⟩ x) closed
  have hP := ev_rho_eq isLevi_T₀_P₀ latP0.topVanishingThree rhoP rhoP_mem κ
    (fun γ x => hκ ⟨γ.val, latP0_le_P₀ γ.property⟩ x) closed
  have core := core_e₀ heisQ heisQ_mul hκ heisQ_mem_P₀ closed
  rw [cycleT_eq, cycleT₀P_eq, map_sub, map_sub, hQ, hP, rhoQ, rhoP, sigmaQ_eq, sigmaP_eq,
    T_eq_heisQ, T₀_eq_heisQ]
  simp only [map_neg]
  linear_combination core

/-! ### The complete flag `e₂` -/

/-- The matrix `[[1, b, 0], [0, 1, 0], [3a, 3c, 1]]` of the stabilizer of `e₂`, as an element of
`GL₃(ℤ)`. -/
def heis2Int (p : HeisCoord) : IntegralGL3 :=
  mkInt !![1, p.2.1, 0; 0, 1, 0; 3 * p.1, 3 * p.2.2, 1]
    !![1, -p.2.1, 0; 0, 1, 0; -(3 * p.1), 3 * (p.1 * p.2.1) - 3 * p.2.2, 1]
    (by heis_entries) (by heis_entries)

/-- The matrix of `heis2Int p`. -/
theorem heis2Int_val (p : HeisCoord) :
    (heis2Int p).val = !![1, p.2.1, 0; 0, 1, 0; 3 * p.1, 3 * p.2.2, 1] := rfl

/-- Multiplication in `GL₃(ℤ)` with the law `c + c' + a b'`. -/
theorem heis2Int_mul (p q : HeisCoord) : heis2Int p * heis2Int q = heis2Int (heisMul p q) := by
  apply Units.ext
  simp only [Units.val_mul, heis2Int_val, heisMul]
  heis_entries

/-- The element of the stabilizer of `e₂` with coordinates `p`, in `GL₃(ℚ)`. -/
def heis2Q (p : HeisCoord) : RationalGL3 := embedZ (heis2Int p)

/-- Multiplication of the matrices `heis2Q`. -/
theorem heis2Q_mul (p q : HeisCoord) : heis2Q p * heis2Q q = heis2Q (heisMul p q) := by
  show embedZ (heis2Int p) * embedZ (heis2Int q) = embedZ (heis2Int (heisMul p q))
  rw [← map_mul, heis2Int_mul]

/-- The lattice element `I + 3x E₂₀ + 3y E₂₁` has coordinates `(x, 0, y)`. -/
theorem uL1_eq_heis2Q (x y : ℤ) : uL1 x y = heis2Q (x, 0, y) := by
  show embedZ (zuL1 x y) = embedZ (heis2Int (x, 0, y))
  refine congrArg embedZ (Units.ext ?_)
  rfl

/-- The lattice element `I + x E₀₁ + 3y E₂₁` has coordinates `(0, x, y)`. -/
theorem uP1_eq_heis2Q (x y : ℤ) : uP1 x y = heis2Q (0, x, y) := by
  show embedZ (zuP1 x y) = embedZ (heis2Int (0, x, y))
  refine congrArg embedZ (Units.ext ?_)
  rfl

/-- The element `T₀ = I + E₀₁` has coordinates `(0, 1, 0)` at `e₂`. -/
theorem T₀_eq_heis2Q : T₀ = heis2Q (0, 1, 0) := by
  show embedZ zT₀ = embedZ (heis2Int (0, 1, 0))
  refine congrArg embedZ (Units.ext ?_)
  rfl

/-- The element `L' = I + 3E₂₀` has coordinates `(1, 0, 0)` at `e₂`. -/
theorem L'_eq_heis2Q : L' = heis2Q (1, 0, 0) := by
  show embedZ zL' = embedZ (heis2Int (1, 0, 0))
  refine congrArg embedZ (Units.ext ?_)
  rfl

/-- The matrices `heis2Q` lie in the arithmetic level. -/
theorem heis2Q_mem_level (p : HeisCoord) : heis2Q p ∈ rationalLevel :=
  embedZ_mem_rationalLevel (heis2Int p) p.1 p.2.2 (by simp [heis2Int_val])
    (by simp [heis2Int_val]) (by simp [heis2Int_val])

/-- The matrices `heis2Q` stabilize the plane `P₁` in the level. -/
theorem heis2Q_mem_P₁ (p : HeisCoord) : heis2Q p ∈ levelStabilizer P₁ :=
  mem_levelStabilizer_plane (zg := heis2Int p) (zr := zw₁) (heis2Q_mem_level p)
    (by
      simp only [Units.val_mul, zw₁_inv_val, heis2Int_val, zw₁_val]
      simp [Matrix.mul_apply, Fin.sum_univ_three])
    (by
      simp only [Units.val_mul, zw₁_inv_val, heis2Int_val, zw₁_val]
      simp [Matrix.mul_apply, Fin.sum_univ_three])

/-- The lattice of `L₁` lies in the stabilizer of `P₁`. -/
theorem latL1_le_P₁ : latL1.sub ≤ levelStabilizer P₁ := by
  rintro _ ⟨t, rfl⟩
  have h := heis2Q_mem_P₁ ((Multiplicative.toAdd t).1, 0, (Multiplicative.toAdd t).2)
  rw [← uL1_eq_heis2Q] at h
  exact h

/-- The lattice of `P₁` lies in the stabilizer of `P₁`. -/
theorem latP1_le_P₁ : latP1.sub ≤ levelStabilizer P₁ := by
  rintro _ ⟨t, rfl⟩
  have h := heis2Q_mem_P₁ (0, (Multiplicative.toAdd t).1, (Multiplicative.toAdd t).2)
  rw [← uP1_eq_heis2Q] at h
  exact h

/-- Matrices `heis2Q (x, 0, y)` lie in the lattice of `L₁`. -/
theorem heis2Q_mem_latL1 (x y : ℤ) : heis2Q (x, 0, y) ∈ latL1.sub := by
  rw [← uL1_eq_heis2Q]
  exact latL1.u_mem x y

/-- Matrices `heis2Q (0, x, y)` lie in the lattice of `P₁`. -/
theorem heis2Q_mem_latP1 (x y : ℤ) : heis2Q (0, x, y) ∈ latP1.sub := by
  rw [← uP1_eq_heis2Q]
  exact latP1.u_mem x y

/-- The correction `-[Z|X|Z]` for the line `L₁` and `m = T₀`. -/
def rhoL1 : Chains RationalGL3 3 :=
  -bar3 (heis2Q (0, 0, 1)) (heis2Q (1, 0, 0)) (heis2Q (0, 0, 1))

/-- The correction `[Z|YZ⁻¹|Z]` for the plane `P₁` and `m = L'`. -/
def rhoP1 : Chains RationalGL3 3 :=
  bar3 (heis2Q (0, 0, 1)) (heis2Q (0, 1, -1)) (heis2Q (0, 0, 1))

/-- The torus chain of the lattice of `L₁` is `σ(X, Z)`. -/
theorem sigmaL1_eq : latL1.σ = sigma (heis2Q (1, 0, 0)) (heis2Q (0, 0, 1)) := by
  show sigma (uL1 1 0) (uL1 0 1) = _
  rw [uL1_eq_heis2Q, uL1_eq_heis2Q]

/-- The torus chain of the lattice of `P₁` at `e₂` is `σ(Y, Z)`. -/
theorem sigmaP1_eq : latP1.σ = sigma (heis2Q (0, 1, 0)) (heis2Q (0, 0, 1)) := by
  show sigma (uP1 1 0) (uP1 0 1) = _
  rw [uP1_eq_heis2Q, uP1_eq_heis2Q]

/-- Conjugation of `σ(X, Z)` by `T₀ = Y`: `σ(XZ, Z)`. -/
theorem conj_sigmaL1 : conjugate T₀ 2 latL1.σ = sigma (heis2Q (1, 0, 1)) (heis2Q (0, 0, 1)) := by
  rw [sigmaL1_eq, conjugate_sigma, T₀_eq_heis2Q,
    emb_conj heis2Q heisMul heis2Q_mul (p := (0, 1, 0)) (q := (1, 0, 0)) (s := (1, 0, 1))
      (by hdec),
    emb_conj heis2Q heisMul heis2Q_mul (p := (0, 1, 0)) (q := (0, 0, 1)) (s := (0, 0, 1))
      (by hdec)]

/-- Conjugation of `σ(Y, Z)` by `L' = X`: `σ(YZ⁻¹, Z)`. -/
theorem conj_sigmaP1 : conjugate L' 2 latP1.σ = sigma (heis2Q (0, 1, -1)) (heis2Q (0, 0, 1)) := by
  rw [sigmaP1_eq, conjugate_sigma, L'_eq_heis2Q,
    emb_conj heis2Q heisMul heis2Q_mul (p := (1, 0, 0)) (q := (0, 1, 0)) (s := (0, 1, -1))
      (by hdec),
    emb_conj heis2Q heisMul heis2Q_mul (p := (1, 0, 0)) (q := (0, 0, 1)) (s := (0, 0, 1))
      (by hdec)]

/-- `-[Z|X|Z]` is a correction for `T₀` at the lattice of `L₁`. -/
theorem rhoL1_mem :
    conjugate T₀ 2 latL1.σ - latL1.σ - homogeneousBoundary 3 rhoL1 ∈ NullChains latL1.sub 2 := by
  have key := torus_key (heis2Q_mem_latL1 0 1) (heis2Q_mem_latL1 1 0)
    (emb_commute heis2Q heisMul heis2Q_mul (p := (0, 0, 1)) (q := (1, 0, 0)) (by hdec))
  rw [emb_mul_eq heis2Q heisMul heis2Q_mul (p := (1, 0, 0)) (q := (0, 0, 1)) (r := (1, 0, 1))
    (by hdec)] at key
  rw [conj_sigmaL1, sigmaL1_eq, rhoL1, map_neg,
    sigma_comm (heis2Q (0, 0, 1)) (heis2Q (1, 0, 1)),
    sigma_comm (heis2Q (0, 0, 1)) (heis2Q (1, 0, 0))]
  convert key using 1
  abel

/-- `[Z|YZ⁻¹|Z]` is a correction for `L'` at the lattice of `P₁`. -/
theorem rhoP1_mem :
    conjugate L' 2 latP1.σ - latP1.σ - homogeneousBoundary 3 rhoP1 ∈ NullChains latP1.sub 2 := by
  have key := torus_key (heis2Q_mem_latP1 0 1) (heis2Q_mem_latP1 1 (-1))
    (emb_commute heis2Q heisMul heis2Q_mul (p := (0, 0, 1)) (q := (0, 1, -1)) (by hdec))
  rw [emb_mul_eq heis2Q heisMul heis2Q_mul (p := (0, 1, -1)) (q := (0, 0, 1)) (r := (0, 1, 0))
    (by hdec)] at key
  rw [conj_sigmaP1, sigmaP1_eq, rhoP1,
    sigma_comm (heis2Q (0, 0, 1)) (heis2Q (0, 1, -1)),
    sigma_comm (heis2Q (0, 0, 1)) (heis2Q (0, 1, 0))]
  have key' := neg_mem key
  convert key' using 1
  abel

/-- The cusp cycle of `T₀` at `L₁` is `P_{T₀} σ_Q - ρ_{T₀}`. -/
theorem cycleT₀L_eq : cycleT₀L = prism2 T₀ latL1.σ - rho latL1.σ isLevi_T₀_L₁ := rfl

/-- The cusp cycle of `L'` at `P₁` is `P_{L'} σ_P - ρ_{L'}`. -/
theorem cycleL'_eq : cycleL' = prism2 L' latP1.σ - rho latP1.σ isLevi_L' := rfl

/-- **The orientation comparison at the complete flag `e₂`.** For every three-cocycle invariant
under the stabilizer of `P₁` in the level, `κ(C_{L₁}(T₀)) = -κ(C_{P₁}(L'))`. -/
theorem comparison_e₂ : Comparison (levelStabilizer P₁) cycleT₀L cycleL' (-1) := by
  intro κ hκ closed
  have hQ := ev_rho_eq isLevi_T₀_L₁ latL1.topVanishingThree rhoL1 rhoL1_mem κ
    (fun γ x => hκ ⟨γ.val, latL1_le_P₁ γ.property⟩ x) closed
  have hP := ev_rho_eq isLevi_L' latP1.topVanishingThree rhoP1 rhoP1_mem κ
    (fun γ x => hκ ⟨γ.val, latP1_le_P₁ γ.property⟩ x) closed
  have core := core_e₀ heis2Q heis2Q_mul hκ heis2Q_mem_P₁ closed
  rw [cycleT₀L_eq, cycleL'_eq, map_sub, map_sub, hQ, hP, rhoL1, rhoP1, sigmaL1_eq, sigmaP1_eq,
    T₀_eq_heis2Q, L'_eq_heis2Q, sigma_comm (heis2Q (0, 0, 1)) (heis2Q (0, 1, 0))]
  simp only [map_neg]
  linear_combination core

/-! ### The complete flag `e₁` -/

/-- The matrix `[[1, c, a], [0, 1, 0], [0, 3b, 1]]` of the stabilizer of `e₁`, as an element of
`GL₃(ℤ)`. -/
def heis3Int (p : HeisCoord) : IntegralGL3 :=
  mkInt !![1, p.2.2, p.1; 0, 1, 0; 0, 3 * p.2.1, 1]
    !![1, 3 * (p.1 * p.2.1) - p.2.2, -p.1; 0, 1, 0; 0, -(3 * p.2.1), 1]
    (by heis_entries) (by heis_entries)

/-- The matrix of `heis3Int p`. -/
theorem heis3Int_val (p : HeisCoord) :
    (heis3Int p).val = !![1, p.2.2, p.1; 0, 1, 0; 0, 3 * p.2.1, 1] := rfl

/-- Multiplication in `GL₃(ℤ)` with the law `c + c' + 3 a b'`. -/
theorem heis3Int_mul (p q : HeisCoord) : heis3Int p * heis3Int q = heis3Int (heisMul3 p q) := by
  apply Units.ext
  simp only [Units.val_mul, heis3Int_val, heisMul3]
  heis_entries

/-- The element of the stabilizer of `e₁` with coordinates `p`, in `GL₃(ℚ)`. -/
def heis3Q (p : HeisCoord) : RationalGL3 := embedZ (heis3Int p)

/-- Multiplication of the matrices `heis3Q`. -/
theorem heis3Q_mul (p q : HeisCoord) : heis3Q p * heis3Q q = heis3Q (heisMul3 p q) := by
  show embedZ (heis3Int p) * embedZ (heis3Int q) = embedZ (heis3Int (heisMul3 p q))
  rw [← map_mul, heis3Int_mul]

/-- The lattice element `I + x E₀₁ + y E₀₂` has coordinates `(y, 0, x)` at `e₁`. -/
theorem uL0_eq_heis3Q (x y : ℤ) : uL0 x y = heis3Q (y, 0, x) := by
  show embedZ (zuL0 x y) = embedZ (heis3Int (y, 0, x))
  refine congrArg embedZ (Units.ext ?_)
  rfl

/-- The lattice element `I + x E₀₁ + 3y E₂₁` has coordinates `(0, y, x)` at `e₁`. -/
theorem uP1_eq_heis3Q (x y : ℤ) : uP1 x y = heis3Q (0, y, x) := by
  show embedZ (zuP1 x y) = embedZ (heis3Int (0, y, x))
  refine congrArg embedZ (Units.ext ?_)
  rfl

/-- The element `L = I + 3E₂₁` has coordinates `(0, 1, 0)` at `e₁`. -/
theorem L_eq_heis3Q : L = heis3Q (0, 1, 0) := by
  show embedZ zL = embedZ (heis3Int (0, 1, 0))
  refine congrArg embedZ (Units.ext ?_)
  rfl

/-- The element `T' = I + E₀₂` has coordinates `(1, 0, 0)` at `e₁`. -/
theorem T'_eq_heis3Q : T' = heis3Q (1, 0, 0) := by
  show embedZ zT' = embedZ (heis3Int (1, 0, 0))
  refine congrArg embedZ (Units.ext ?_)
  rfl

/-- The matrices `heis3Q` lie in the arithmetic level. -/
theorem heis3Q_mem_level (p : HeisCoord) : heis3Q p ∈ rationalLevel :=
  embedZ_mem_rationalLevel (heis3Int p) 0 p.2.1 (by simp [heis3Int_val])
    (by simp [heis3Int_val]) (by simp [heis3Int_val])

/-- The matrices `heis3Q` stabilize the plane `P₁` in the level. -/
theorem heis3Q_mem_P₁ (p : HeisCoord) : heis3Q p ∈ levelStabilizer P₁ :=
  mem_levelStabilizer_plane (zg := heis3Int p) (zr := zw₁) (heis3Q_mem_level p)
    (by
      simp only [Units.val_mul, zw₁_inv_val, heis3Int_val, zw₁_val]
      simp [Matrix.mul_apply, Fin.sum_univ_three])
    (by
      simp only [Units.val_mul, zw₁_inv_val, heis3Int_val, zw₁_val]
      simp [Matrix.mul_apply, Fin.sum_univ_three])

/-- The lattice of `L₀` lies in the stabilizer of `P₁`. -/
theorem latL0_le_P₁ : latL0.sub ≤ levelStabilizer P₁ := by
  rintro _ ⟨t, rfl⟩
  have h := heis3Q_mem_P₁ ((Multiplicative.toAdd t).2, 0, (Multiplicative.toAdd t).1)
  rw [← uL0_eq_heis3Q] at h
  exact h

/-- Matrices `heis3Q (y, 0, x)` lie in the lattice of `L₀`. -/
theorem heis3Q_mem_latL0 (x y : ℤ) : heis3Q (y, 0, x) ∈ latL0.sub := by
  rw [← uL0_eq_heis3Q]
  exact latL0.u_mem x y

/-- Matrices `heis3Q (0, y, x)` lie in the lattice of `P₁`. -/
theorem heis3Q_mem_latP1 (x y : ℤ) : heis3Q (0, y, x) ∈ latP1.sub := by
  rw [← uP1_eq_heis3Q]
  exact latP1.u_mem x y

/-- The correction `Σ_{k<3} [Z|XZᵏ|Z]` for the line `L₀` and `m = L`. -/
def rhoL3 : Chains RationalGL3 3 :=
  bar3 (heis3Q (0, 0, 1)) (heis3Q (1, 0, 0)) (heis3Q (0, 0, 1)) +
    bar3 (heis3Q (0, 0, 1)) (heis3Q (1, 0, 1)) (heis3Q (0, 0, 1)) +
    bar3 (heis3Q (0, 0, 1)) (heis3Q (1, 0, 2)) (heis3Q (0, 0, 1))

/-- The correction `-Σ_{k<3} [Z|v_k|Z]`, `v_k = Y Z^{k-3}`, for the plane `P₁` and `m = T'`. -/
def rhoT3 : Chains RationalGL3 3 :=
  -(bar3 (heis3Q (0, 0, 1)) (heis3Q (0, 1, -3)) (heis3Q (0, 0, 1)) +
    bar3 (heis3Q (0, 0, 1)) (heis3Q (0, 1, -2)) (heis3Q (0, 0, 1)) +
    bar3 (heis3Q (0, 0, 1)) (heis3Q (0, 1, -1)) (heis3Q (0, 0, 1)))

/-- The torus chain of the lattice of `L₀` at `e₁` is `σ(Z, X)`. -/
theorem sigmaL0_eq3 : latL0.σ = sigma (heis3Q (0, 0, 1)) (heis3Q (1, 0, 0)) := by
  show sigma (uL0 1 0) (uL0 0 1) = _
  rw [uL0_eq_heis3Q, uL0_eq_heis3Q]

/-- The torus chain of the lattice of `P₁` at `e₁` is `σ(Z, Y)`. -/
theorem sigmaP1_eq3 : latP1.σ = sigma (heis3Q (0, 0, 1)) (heis3Q (0, 1, 0)) := by
  show sigma (uP1 1 0) (uP1 0 1) = _
  rw [uP1_eq_heis3Q, uP1_eq_heis3Q]

/-- Conjugation of `σ(Z, X)` by `L = Y`: `σ(Z, XZ³)`. -/
theorem conj_sigmaL0_3 :
    conjugate L 2 latL0.σ = sigma (heis3Q (0, 0, 1)) (heis3Q (1, 0, 3)) := by
  rw [sigmaL0_eq3, conjugate_sigma, L_eq_heis3Q,
    emb_conj heis3Q heisMul3 heis3Q_mul (p := (0, 1, 0)) (q := (0, 0, 1)) (s := (0, 0, 1))
      (by hdec),
    emb_conj heis3Q heisMul3 heis3Q_mul (p := (0, 1, 0)) (q := (1, 0, 0)) (s := (1, 0, 3))
      (by hdec)]

/-- Conjugation of `σ(Z, Y)` by `T' = X`: `σ(Z, YZ⁻³)`. -/
theorem conj_sigmaP1_3 :
    conjugate T' 2 latP1.σ = sigma (heis3Q (0, 0, 1)) (heis3Q (0, 1, -3)) := by
  rw [sigmaP1_eq3, conjugate_sigma, T'_eq_heis3Q,
    emb_conj heis3Q heisMul3 heis3Q_mul (p := (1, 0, 0)) (q := (0, 0, 1)) (s := (0, 0, 1))
      (by hdec),
    emb_conj heis3Q heisMul3 heis3Q_mul (p := (1, 0, 0)) (q := (0, 1, 0)) (s := (0, 1, -3))
      (by hdec)]

/-- `Σ_{k<3} [Z|XZᵏ|Z]` is a correction for `L` at the lattice of `L₀`. -/
theorem rhoL3_mem :
    conjugate L 2 latL0.σ - latL0.σ - homogeneousBoundary 3 rhoL3 ∈ NullChains latL0.sub 2 := by
  have hz := heis3Q_mem_latL0 1 0
  have k0 := torus_key hz (heis3Q_mem_latL0 0 1)
    (emb_commute heis3Q heisMul3 heis3Q_mul (p := (0, 0, 1)) (q := (1, 0, 0)) (by hdec))
  have k1 := torus_key hz (heis3Q_mem_latL0 1 1)
    (emb_commute heis3Q heisMul3 heis3Q_mul (p := (0, 0, 1)) (q := (1, 0, 1)) (by hdec))
  have k2 := torus_key hz (heis3Q_mem_latL0 2 1)
    (emb_commute heis3Q heisMul3 heis3Q_mul (p := (0, 0, 1)) (q := (1, 0, 2)) (by hdec))
  rw [emb_mul_eq heis3Q heisMul3 heis3Q_mul (p := (1, 0, 0)) (q := (0, 0, 1)) (r := (1, 0, 1))
    (by hdec)] at k0
  rw [emb_mul_eq heis3Q heisMul3 heis3Q_mul (p := (1, 0, 1)) (q := (0, 0, 1)) (r := (1, 0, 2))
    (by hdec)] at k1
  rw [emb_mul_eq heis3Q heisMul3 heis3Q_mul (p := (1, 0, 2)) (q := (0, 0, 1)) (r := (1, 0, 3))
    (by hdec)] at k2
  rw [conj_sigmaL0_3, sigmaL0_eq3, rhoL3, map_add, map_add]
  have key := neg_mem (add_mem (add_mem k0 k1) k2)
  convert key using 1
  abel

/-- `-Σ_{k<3} [Z|v_k|Z]` is a correction for `T'` at the lattice of `P₁`. -/
theorem rhoT3_mem :
    conjugate T' 2 latP1.σ - latP1.σ - homogeneousBoundary 3 rhoT3 ∈ NullChains latP1.sub 2 := by
  have hz := heis3Q_mem_latP1 1 0
  have k0 := torus_key hz (heis3Q_mem_latP1 (-3) 1)
    (emb_commute heis3Q heisMul3 heis3Q_mul (p := (0, 0, 1)) (q := (0, 1, -3)) (by hdec))
  have k1 := torus_key hz (heis3Q_mem_latP1 (-2) 1)
    (emb_commute heis3Q heisMul3 heis3Q_mul (p := (0, 0, 1)) (q := (0, 1, -2)) (by hdec))
  have k2 := torus_key hz (heis3Q_mem_latP1 (-1) 1)
    (emb_commute heis3Q heisMul3 heis3Q_mul (p := (0, 0, 1)) (q := (0, 1, -1)) (by hdec))
  rw [emb_mul_eq heis3Q heisMul3 heis3Q_mul (p := (0, 1, -3)) (q := (0, 0, 1)) (r := (0, 1, -2))
    (by hdec)] at k0
  rw [emb_mul_eq heis3Q heisMul3 heis3Q_mul (p := (0, 1, -2)) (q := (0, 0, 1)) (r := (0, 1, -1))
    (by hdec)] at k1
  rw [emb_mul_eq heis3Q heisMul3 heis3Q_mul (p := (0, 1, -1)) (q := (0, 0, 1)) (r := (0, 1, 0))
    (by hdec)] at k2
  rw [conj_sigmaP1_3, sigmaP1_eq3, rhoT3, map_neg, map_add, map_add]
  have key := add_mem (add_mem k0 k1) k2
  convert key using 1
  abel

/-- The cusp cycle of `L` at `L₀` is `P_L σ_Q - ρ_L`. -/
theorem cycleL_eq : cycleL = prism2 L latL0.σ - rho latL0.σ isLevi_L := rfl

/-- The cusp cycle of `T'` at `P₁` is `P_{T'} σ_P - ρ_{T'}`. -/
theorem cycleT'_eq : cycleT' = prism2 T' latP1.σ - rho latP1.σ isLevi_T' := rfl

/-- **The orientation comparison at the complete flag `e₁`.** For every three-cocycle invariant
under the stabilizer of `P₁` in the level, `κ(C_{L₀}(L)) = -κ(C_{P₁}(T'))`. -/
theorem comparison_e₁ : Comparison (levelStabilizer P₁) cycleL cycleT' (-1) := by
  intro κ hκ closed
  have hQ := ev_rho_eq isLevi_L latL0.topVanishingThree rhoL3 rhoL3_mem κ
    (fun γ x => hκ ⟨γ.val, latL0_le_P₁ γ.property⟩ x) closed
  have hP := ev_rho_eq isLevi_T' latP1.topVanishingThree rhoT3 rhoT3_mem κ
    (fun γ x => hκ ⟨γ.val, latP1_le_P₁ γ.property⟩ x) closed
  have core := core_e₁ heis3Q heis3Q_mul hκ heis3Q_mem_P₁ closed
  rw [cycleL_eq, cycleT'_eq, map_sub, map_sub, hQ, hP, rhoL3, rhoT3, sigmaL0_eq3, sigmaP1_eq3,
    L_eq_heis3Q, T'_eq_heis3Q]
  simp only [map_add, map_neg]
  linear_combination core

/-! ### The boundary trace -/

/-- **The boundary trace of the level-three Eisenstein setting**, from the three orientation
comparisons with signs `(1, -1, -1)`. -/
theorem isBoundaryTrace_L2 : TraceReduction.IsBoundaryTrace
    (traceData_of_comparisons 1 (-1) (-1) (by norm_num) comparison_e₀ comparison_e₁
      comparison_e₂).trace.toAddMonoidHom :=
  isBoundaryTrace_of_comparisons 1 (-1) (-1) (by norm_num) comparison_e₀ comparison_e₁
    comparison_e₂

end TernaryPeriodPolynomials.BoundaryDuality.HeisComparison
