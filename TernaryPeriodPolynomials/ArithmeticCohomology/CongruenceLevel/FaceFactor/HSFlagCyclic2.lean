module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.HSFlagCyclic

@[expose] public section


/-!
# `exists_flag_primitive_explicit`: the explicit primitive on the flag group of a cusp stabilizer `⟨σ⟩`

Formalized by Claude Sonnet 5.5.

Let `z` be a relative two-cocycle with `z(s a, s b) = 0`, `z(inl r, s l) = 0` (`exists_normal_form_mixed`), `σ ∈ L` of infinite order generating the cusp stabilizer
`M = ⟨σ⟩`, `B = rightHom⁻¹ M` the flag group, and Wang data `φ ∈ Z¹(N, W)`, `ε ∈ W` with `c̃(σ) = (σ - 1) φ + dε` (`c̃(σ) = splitEdgeCycle σ z`).
Then `z|_B` is the coboundary of
`w (inl r · s(σ^k)) = φ(r) - inl(r) · S_k(ε)`,   `S_k(ε) = ε + T ε + ⋯ + T^{k-1} ε` (`T = ρ(s σ)`; for `k < 0` the inverse recursion, `cycSum`),
that is `flagPrimitive φ χ` with `χ(σ^k) = -S_k(ε)`.
-/

open TernaryPeriodPolynomials.SphericalDetection.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

variable {N E L : Type} [Group N] [Group E] [Group L] {extension : GroupExtension N E L}
  (splitting : extension.Splitting) (W : Rep ℂ E)

theorem oneBoundaryCycle_add (x y : W) :
    oneBoundaryCycle (Rep.res extension.inl W) (x + y) =
      oneBoundaryCycle (Rep.res extension.inl W) x + oneBoundaryCycle (Rep.res extension.inl W) y := by
  apply groupCohomology.cocycles₁_ext
  intro r
  have hadd : ∀ (p q : groupCohomology.cocycles₁ (Rep.res extension.inl W)) (t : N), (p + q) t = p t + q t :=
    fun _ _ _ => rfl
  rw [hadd, oneBoundaryCycle_apply, oneBoundaryCycle_apply, oneBoundaryCycle_apply]
  change W.ρ (extension.inl r) (x + y) - (x + y) = (W.ρ (extension.inl r) x - x) + (W.ρ (extension.inl r) y - y)
  rw [map_add]
  abel

theorem oneBoundaryCycle_neg (x : W) :
    oneBoundaryCycle (Rep.res extension.inl W) (-x) = -oneBoundaryCycle (Rep.res extension.inl W) x := by
  apply groupCohomology.cocycles₁_ext
  intro r
  have hneg : ∀ (p : groupCohomology.cocycles₁ (Rep.res extension.inl W)) (t : N), (-p) t = -p t :=
    fun _ _ => rfl
  rw [hneg, oneBoundaryCycle_apply, oneBoundaryCycle_apply]
  change W.ρ (extension.inl r) (-x) - -x = -(W.ρ (extension.inl r) x - x)
  rw [map_neg]
  abel

theorem oneBoundaryCycle_zero' :
    oneBoundaryCycle (Rep.res extension.inl W) (0 : W) = 0 := by
  apply groupCohomology.cocycles₁_ext
  intro r
  simp only [oneBoundaryCycle_apply, map_zero, sub_self]
  rfl

/-- The Levi action carries the boundary of `x` to the boundary of `ρ(s a) x`. -/
theorem splitRadicalCocycleAction_boundary (a : L) (x : W) :
    splitRadicalCocycleAction splitting W a (oneBoundaryCycle (Rep.res extension.inl W) x) =
      oneBoundaryCycle (Rep.res extension.inl W) (W.ρ (splitting a) x) := by
  apply groupCohomology.cocycles₁_ext
  intro r
  rw [splitRadicalCocycleAction_apply, oneBoundaryCycle_apply, oneBoundaryCycle_apply]
  change W.ρ (splitting a) (W.ρ (extension.inl (splitRadicalInput splitting a r)) x - x) =
    W.ρ (extension.inl r) (W.ρ (splitting a) x) - W.ρ (splitting a) x
  rw [map_sub, ← Module.End.mul_apply, ← map_mul, ← splitRadicalInput_commute, map_mul, Module.End.mul_apply]

/-- **M3b(ii): the explicit primitive on the flag group of a cyclic cusp stabilizer.** -/
theorem exists_flag_primitive_explicit (z : relativeTwoCocycles extension.inl W)
    (hU : ∀ a b : L, z.val (splitting a, splitting b) = 0)
    (hmix : ∀ (r : N) (l : L), z.val (extension.inl r, splitting l) = 0) (σ : L) (hσ : ∀ k : ℤ, σ ^ k = 1 → k = 0)
    (φ : groupCohomology.cocycles₁ (Rep.res extension.inl W)) (ε : W)
    (hσc : splitEdgeCycle splitting W σ z =
      splitRadicalCocycleAction splitting W σ φ - φ + oneBoundaryCycle (Rep.res extension.inl W) ε) :
    ∃ χ : L → W, (∀ k : ℤ, χ (σ ^ k) = cycW splitting W σ (-ε) k) ∧
      ∀ e₁ e₂ : E, extension.rightHom e₁ ∈ Subgroup.zpowers σ → extension.rightHom e₂ ∈ Subgroup.zpowers σ →
        z.val (e₁, e₂) = W.ρ e₁ (flagPrimitive splitting W φ χ e₂) - flagPrimitive splitting W φ χ (e₁ * e₂) +
          flagPrimitive splitting W φ χ e₁ := by
  classical
  let χ : L → W := fun a =>
    if h : ∃ k : ℤ, σ ^ k = a then cycW splitting W σ (-ε) (Classical.choose h) else 0
  have hχpow : ∀ k : ℤ, χ (σ ^ k) = cycW splitting W σ (-ε) k := by
    intro k
    have h : ∃ j : ℤ, σ ^ j = σ ^ k := ⟨k, rfl⟩
    simp only [χ, dite_eq_left h]
    have hspec := Classical.choose_spec h
    have hj : Classical.choose h = k := by
      have h1 : σ ^ (Classical.choose h - k) = 1 := by rw [zpow_sub, hspec, mul_inv_cancel]
      have := hσ _ h1
      omega
    rw [hj]
  have hχ : ∀ a ∈ Subgroup.zpowers σ, ∀ b ∈ Subgroup.zpowers σ,
      χ (a * b) = W.ρ (splitting a) (χ b) + χ a := by
    intro a ha b hb
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    rw [← zpow_add, hχpow, hχpow, hχpow, cycW_crossed]
  have hc : ∀ a ∈ Subgroup.zpowers σ, splitEdgeCycle splitting W a z =
      splitRadicalCocycleAction splitting W a φ - φ - oneBoundaryCycle (Rep.res extension.inl W) (χ a) := by
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    rw [hχpow]
    have hS : Function.Injective (splitRadicalCocycleAction splitting W σ) := by
      have hinv : ∀ x, splitRadicalCocycleAction splitting W σ⁻¹ (splitRadicalCocycleAction splitting W σ x) = x :=
        fun x => by rw [← splitRadicalCocycleAction_mul, inv_mul_cancel, splitRadicalCocycleAction_one]
      intro x y hxy
      rw [← hinv x, ← hinv y, hxy]
    have hcycle : ∀ j : ℤ, cycW splitting W σ (-ε) (j + 1) =
        -ε + W.ρ (splitting σ) (cycW splitting W σ (-ε) j) := fun j =>
      cycSum_succ (rho_s_inv_left splitting W σ) j
    have hone : cycW splitting W σ (-ε) 1 = -ε := by
      have := hcycle 0
      simpa [cycW, cycSum_zero] using this
    let Θ : ℤ → groupCohomology.cocycles₁ (Rep.res extension.inl W) := fun j =>
      splitRadicalCocycleAction splitting W (σ ^ j) φ - φ -
        oneBoundaryCycle (Rep.res extension.inl W) (cycW splitting W σ (-ε) j)
    have hmain := zpow_vanish (splitRadicalCocycleAction splitting W σ) hS
      (fun j => splitEdgeCycle splitting W (σ ^ j) z - Θ j) (by
        simp only [Θ, zpow_zero, splitEdgeCycle_one, splitRadicalCocycleAction_one, sub_self]
        have : cycW splitting W σ (-ε) 0 = 0 := cycSum_zero
        simp [this, oneBoundaryCycle_zero']) (by
        intro j
        have e1 : σ ^ (j + 1) = σ * σ ^ j := by rw [add_comm, zpow_add, zpow_one]
        simp only [Θ]
        rw [e1, splitEdgeCycle_mul_of_normal splitting W z hU σ (σ ^ j), splitRadicalCocycleAction_mul, hcycle,
          oneBoundaryCycle_add, map_sub, map_sub, map_sub, hσc, splitRadicalCocycleAction_boundary,
          oneBoundaryCycle_neg]
        abel) k
    simpa [Θ, sub_eq_zero] using hmain
  exact ⟨χ, hχpow, fun e₁ e₂ h₁ h₂ => flag_primitive_of_crossed splitting W z hU hmix _ φ χ hχ hc e₁ e₂ h₁ h₂⟩

/-- **`z|_B = dd₁ w` on the flag group `B = rightHom⁻¹⟨σ⟩`**, with `w` the explicit `flagPrimitive`. -/
theorem restriction_flag_boundary (z : relativeTwoCocycles extension.inl W)
    (hU : ∀ a b : L, z.val (splitting a, splitting b) = 0)
    (hmix : ∀ (r : N) (l : L), z.val (extension.inl r, splitting l) = 0) (σ : L) (hσ : ∀ k : ℤ, σ ^ k = 1 → k = 0)
    (φ : groupCohomology.cocycles₁ (Rep.res extension.inl W)) (ε : W)
    (hσc : splitEdgeCycle splitting W σ z =
      splitRadicalCocycleAction splitting W σ φ - φ + oneBoundaryCycle (Rep.res extension.inl W) ε)
    (B : Subgroup E) (hB : ∀ e, e ∈ B ↔ extension.rightHom e ∈ Subgroup.zpowers σ) :
    ∃ χ : L → W, (∀ k : ℤ, χ (σ ^ k) = cycW splitting W σ (-ε) k) ∧
      twoCocycleRestriction B.subtype W z.val =
        twoBoundaryCycle (Rep.res B.subtype W) (fun e : B => flagPrimitive splitting W φ χ e.1) := by
  obtain ⟨χ, hχ, hprim⟩ := exists_flag_primitive_explicit splitting W z hU hmix σ hσ φ ε hσc
  refine ⟨χ, hχ, ?_⟩
  apply Subtype.ext
  funext p
  exact hprim p.1.1 p.2.1 ((hB _).1 p.1.2) ((hB _).1 p.2.2)

/-- The explicit values: `w(inl r · s(σ^k)) = φ(r) + inl(r) · cycSum(-ε)(k)`, i.e. `φ(r) - inl(r) · (ε + Tε + ⋯ + T^{k-1}ε)`. -/
theorem flagPrimitive_zpow (φ : groupCohomology.cocycles₁ (Rep.res extension.inl W)) (χ : L → W) (σ : L) (ε : W)
    (hχ : ∀ k : ℤ, χ (σ ^ k) = cycW splitting W σ (-ε) k) (r : N) (k : ℤ) :
    flagPrimitive splitting W φ χ (extension.inl r * splitting (σ ^ k)) =
      φ r + W.ρ (extension.inl r) (cycW splitting W σ (-ε) k) := by
  rw [flagPrimitive_pair, hχ]

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
