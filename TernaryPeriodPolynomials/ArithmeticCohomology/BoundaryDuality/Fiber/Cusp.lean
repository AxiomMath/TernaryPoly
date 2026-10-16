module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Fiber.Cochains

@[expose] public section


/-!
# Pairing invariant two-cocycles with the torus cycle and the cusp cycles

Let `U ≤ G` be a subgroup and `σ` a two-chain which is a cycle modulo `U`.
* A `U`-invariant scalar two-cocycle vanishes on the boundaries modulo `U`
  (`pair_bdry_eq_zero`), so it pairs equally with two chains which agree modulo boundaries.
* **Levi invariance**: if `k⁻¹` is a Levi element for `σ` (it normalizes `U` and its conjugation
  fixes `σ` modulo boundaries), then `⟨k^* θ, σ⟩ = ⟨θ, σ⟩` for every `U`-invariant two-cocycle
  `θ` (`pair_spull2`): left translation by `k` is right translation of the conjugated chain, and
  right translation is homotopic to the identity through the prism.
* **The cusp cycle without its correction**: for a `U`-invariant scalar two-cochain `λ`,
  `⟨dλ, C(m)⟩ = ⟨m^* λ − λ, m⁻¹ σ m⟩` (`pair_cusp`), where `C(m) = P_m σ − ρ_m` is the cusp
  cycle of a Levi element `m`: the prism gives `∂ P_m σ = m · (m⁻¹ σ m) − σ − P_m ∂σ`, and the
  correction satisfies `∂ ρ_m ≡ m⁻¹ σ m − σ` modulo `U`. The chosen correction disappears.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.FiberCusp

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.TopVanishing (homogeneousBoundary)
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains
open TernaryPeriodPolynomials.BoundaryDuality.ChainCalculus
open TernaryPeriodPolynomials.BoundaryDuality.ChiHom
open TernaryPeriodPolynomials.BoundaryDuality.FiberCochains

variable {G : Type} [Group G]

/-- A `U`-invariant scalar two-cocycle vanishes on the boundaries modulo `U`. -/
theorem pair_bdry_eq_zero {U : Subgroup G} {θ : (Fin 3 → G) → ℂ}
    (hθ : ∀ (γ : U) x, θ (fun i => γ.val * x i) = θ x)
    (closed : ∀ x, differentialTwoRaw θ x = 0) {c : Chains G 2} (hc : c ∈ BdryChains U 2) :
    Finsupp.linearCombination ℂ θ c = 0 := by
  obtain ⟨n, hn, d, hd, rfl⟩ := Submodule.mem_sup.mp hc
  obtain ⟨e, rfl⟩ := LinearMap.mem_range.mp hd
  rw [map_add, eval_null θ hθ hn, zero_add, ← eval_differentialTwo]
  have zero : differentialTwoRaw θ = 0 := funext closed
  rw [zero]
  simp

/-- Two-chains which agree modulo boundaries modulo `U` pair equally with every `U`-invariant
two-cocycle. -/
theorem pair_eq_of_sub_mem_bdry {U : Subgroup G} {θ : (Fin 3 → G) → ℂ}
    (hθ : ∀ (γ : U) x, θ (fun i => γ.val * x i) = θ x)
    (closed : ∀ x, differentialTwoRaw θ x = 0) {c c' : Chains G 2}
    (h : c - c' ∈ BdryChains U 2) :
    Finsupp.linearCombination ℂ θ c = Finsupp.linearCombination ℂ θ c' := by
  have h0 := pair_bdry_eq_zero hθ closed h
  rw [map_sub, sub_eq_zero] at h0
  exact h0

/-- Pairing with a left translate is pairing the translated cochain. -/
theorem pair_leftTranslate (g : G) {d : ℕ} (f : (Fin (d + 1) → G) → ℂ) (c : Chains G d) :
    Finsupp.linearCombination ℂ f (leftTranslate g d c) =
      Finsupp.linearCombination ℂ (fun x => f (fun i => g * x i)) c := by
  rw [leftTranslate, Finsupp.lmapDomain_apply, Finsupp.linearCombination_mapDomain]
  rfl

/-- Conjugation by the identity is the identity. -/
theorem conjugate_one' {d : ℕ} (c : Chains G d) : conjugate (1 : G) d c = c := by
  rw [conjugate, Finsupp.lmapDomain_apply]
  have e : (fun (x : Fin (d + 1) → G) (i : Fin (d + 1)) => (1 : G)⁻¹ * x i * 1) = id := by
    funext x i
    simp
  rw [e, Finsupp.mapDomain_id]

/-- **Levi invariance of the pairing with the torus cycle.** If `k⁻¹` is a Levi element for `σ`,
every `U`-invariant scalar two-cocycle `θ` satisfies `⟨k^* θ, σ⟩ = ⟨θ, σ⟩`. -/
theorem pair_spull2 (D : PrismData G) {Λ U : Subgroup G} {σ : Chains G 2}
    (hσ : homogeneousBoundary 2 σ ∈ NullChains U 1) {k : G} (hk : IsLevi Λ U σ k⁻¹)
    {θ : (Fin 3 → G) → ℂ} (hθ : ∀ (γ : U) x, θ (fun i => γ.val * x i) = θ x)
    (closed : ∀ x, differentialTwoRaw θ x = 0) :
    Finsupp.linearCombination ℂ (spull2 k θ) σ = Finsupp.linearCombination ℂ θ σ := by
  have hleft : leftTranslate k 2 σ = rightTranslate k 2 (conjugate k⁻¹ 2 σ) := by
    rw [rightTranslate_eq, conjugate_conjugate, inv_mul_cancel, conjugate_one']
  have hP := D.prism_two k (conjugate k⁻¹ 2 σ)
  have hR : rightTranslate k 2 (conjugate k⁻¹ 2 σ) =
      conjugate k⁻¹ 2 σ + homogeneousBoundary 3 (D.P2 k (conjugate k⁻¹ 2 σ)) +
        D.P1 k (homogeneousBoundary 2 (conjugate k⁻¹ 2 σ)) := by
    rw [← eq_sub_iff_add_eq.mp hP]
    abel
  have hbc : homogeneousBoundary 2 (conjugate k⁻¹ 2 σ) ∈ NullChains U 1 := by
    rw [boundary_conjugate]
    exact conjugate_mem_null hk.2.1 hσ
  have h1 : Finsupp.linearCombination ℂ θ
      (homogeneousBoundary 3 (D.P2 k (conjugate k⁻¹ 2 σ))) = 0 := by
    rw [← eval_differentialTwo]
    have zero : differentialTwoRaw θ = 0 := funext closed
    rw [zero]
    simp
  have h2 : Finsupp.linearCombination ℂ θ
      (D.P1 k (homogeneousBoundary 2 (conjugate k⁻¹ 2 σ))) = 0 :=
    eval_null θ hθ (D.P1_null U k _ hbc)
  rw [spull2_eq_fun]
  refine (pair_leftTranslate k θ σ).symm.trans ?_
  rw [hleft, hR, map_add, map_add, h1, h2, add_zero, add_zero]
  exact pair_eq_of_sub_mem_bdry hθ closed hk.2.2

/-- **The cusp cycle without its correction.** For a `U`-invariant scalar two-cochain `λ`,
`⟨dλ, C(m)⟩ = ⟨m^* λ − λ, m⁻¹ σ m⟩`. -/
theorem pair_cusp (D : PrismData G) {Λ U : Subgroup G} {σ : Chains G 2}
    (hσ : homogeneousBoundary 2 σ ∈ NullChains U 1) {m : G} (hm : IsLevi Λ U σ m)
    {θ : (Fin 3 → G) → ℂ} (hθ : ∀ (γ : U) x, θ (fun i => γ.val * x i) = θ x) :
    Finsupp.linearCombination ℂ (differentialTwoRaw θ) (cusp D σ hm) =
      Finsupp.linearCombination ℂ (spull2 m θ - θ) (conjugate m 2 σ) := by
  have hP := D.prism_two m σ
  have hP' : homogeneousBoundary 3 (D.P2 m σ) =
      leftTranslate m 2 (conjugate m 2 σ) - σ - D.P1 m (homogeneousBoundary 2 σ) := by
    rw [← rightTranslate_eq]
    exact eq_sub_of_add_eq hP
  have key : homogeneousBoundary 3 (cusp D σ hm) =
      (leftTranslate m 2 (conjugate m 2 σ) - conjugate m 2 σ) +
        (conjugate m 2 σ - σ - homogeneousBoundary 3 (rho σ hm)) -
        D.P1 m (homogeneousBoundary 2 σ) := by
    rw [cusp, map_sub, hP']
    abel
  have e1 : Finsupp.linearCombination ℂ θ
      (conjugate m 2 σ - σ - homogeneousBoundary 3 (rho σ hm)) = 0 :=
    eval_null θ hθ (rho_spec σ hm)
  have e2 : Finsupp.linearCombination ℂ θ (D.P1 m (homogeneousBoundary 2 σ)) = 0 :=
    eval_null θ hθ (D.P1_null U m _ hσ)
  have e3 : Finsupp.linearCombination ℂ θ (leftTranslate m 2 (conjugate m 2 σ)) =
      Finsupp.linearCombination ℂ (spull2 m θ) (conjugate m 2 σ) := by
    rw [pair_leftTranslate, spull2_eq_fun]
  rw [eval_differentialTwo, key]
  calc Finsupp.linearCombination ℂ θ
        ((leftTranslate m 2 (conjugate m 2 σ) - conjugate m 2 σ) +
          (conjugate m 2 σ - σ - homogeneousBoundary 3 (rho σ hm)) -
          D.P1 m (homogeneousBoundary 2 σ))
      = Finsupp.linearCombination ℂ θ (leftTranslate m 2 (conjugate m 2 σ) - conjugate m 2 σ) +
          Finsupp.linearCombination ℂ θ
            (conjugate m 2 σ - σ - homogeneousBoundary 3 (rho σ hm)) -
          Finsupp.linearCombination ℂ θ (D.P1 m (homogeneousBoundary 2 σ)) := by
        rw [map_sub (Finsupp.linearCombination ℂ θ)
          ((leftTranslate m 2 (conjugate m 2 σ) - conjugate m 2 σ) +
            (conjugate m 2 σ - σ - homogeneousBoundary 3 (rho σ hm)))
          (D.P1 m (homogeneousBoundary 2 σ)), map_add]
    _ = Finsupp.linearCombination ℂ θ (leftTranslate m 2 (conjugate m 2 σ)) -
          Finsupp.linearCombination ℂ θ (conjugate m 2 σ) := by
        rw [e1, e2, add_zero, sub_zero, map_sub]
    _ = Finsupp.linearCombination ℂ (spull2 m θ - θ) (conjugate m 2 σ) := by
        rw [e3, pair_sub]

end TernaryPeriodPolynomials.BoundaryDuality.FiberCusp
