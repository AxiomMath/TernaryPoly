module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Fiber.Formula

@[expose] public section


/-!
# The Kostant pairing of the fiber integration

For a lattice `U` with torus cycle `σ` (a cycle modulo `U`), the Kostant pairing of one-cochains
is `κ(f, g) = ⟨f ⌣ g, σ⟩`. It is bilinear (`kostantForm`), and on `U`-equivariant one-cocycles it
is invariant under pullback by an element `k` with `k⁻¹` a Levi element for `σ`
(`kostant_pull1`): `κ(k ⋆ f, k ⋆ g) = κ(f, g)`, the action of the Levi factor on `H²(U, ℂ) = ℂ`
being trivial. Equivalently `κ(f, k ⋆ g) = κ(k⁻¹ ⋆ f, g)` (`kostant_shift`).

The Levi cocycles `A(h) = h ⋆ ω_U − ω_U` of the fiber data are `U`-equivariant one-cocycles at
every element `h` of the stabilizer with `h⁻¹` a Levi element (`uCocycle_leviCocycle`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.FiberKostant

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.TopVanishing (homogeneousBoundary)
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains
open TernaryPeriodPolynomials.BoundaryDuality.ChainCalculus
open TernaryPeriodPolynomials.BoundaryDuality.ChiHom
open TernaryPeriodPolynomials.BoundaryDuality.FiberCochains
open TernaryPeriodPolynomials.BoundaryDuality.FiberCusp
open TernaryPeriodPolynomials.BoundaryDuality.FiberFormula

variable {G V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

section Bilinear

variable (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (σ : Chains G 2)

theorem kostant_add_left (f f' : (Fin 2 → G) → V) (g : (Fin 2 → G) → W) :
    kostant B σ (f + f') g = kostant B σ f g + kostant B σ f' g := by
  unfold kostant
  rw [cup11_add_left, pair_add]

theorem kostant_sub_left (f f' : (Fin 2 → G) → V) (g : (Fin 2 → G) → W) :
    kostant B σ (f - f') g = kostant B σ f g - kostant B σ f' g := by
  unfold kostant
  rw [cup11_sub_left, pair_sub]

theorem kostant_neg_left (f : (Fin 2 → G) → V) (g : (Fin 2 → G) → W) :
    kostant B σ (-f) g = -kostant B σ f g := by
  unfold kostant
  rw [cup11_neg_left, pair_neg]

theorem kostant_smul_left (c : ℂ) (f : (Fin 2 → G) → V) (g : (Fin 2 → G) → W) :
    kostant B σ (c • f) g = c * kostant B σ f g := by
  unfold kostant
  rw [cup11_smul_left, pair_smul]

theorem kostant_add_right (f : (Fin 2 → G) → V) (g g' : (Fin 2 → G) → W) :
    kostant B σ f (g + g') = kostant B σ f g + kostant B σ f g' := by
  unfold kostant
  rw [cup11_add_right, pair_add]

theorem kostant_neg_right (f : (Fin 2 → G) → V) (g : (Fin 2 → G) → W) :
    kostant B σ f (-g) = -kostant B σ f g := by
  unfold kostant
  rw [cup11_neg_right, pair_neg]

/-- The Kostant pairing as a bilinear form on one-cochains. -/
def kostantForm : ((Fin 2 → G) → V) →ₗ[ℂ] ((Fin 2 → G) → W) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (kostant B σ)
    (fun f f' g => kostant_add_left B σ f f' g)
    (fun c f g => by rw [kostant_smul_left, smul_eq_mul])
    (fun f g g' => kostant_add_right B σ f g g')
    (fun c f g => by
      unfold kostant
      rw [cup11_smul_right, pair_smul, smul_eq_mul])

theorem kostantForm_apply (f : (Fin 2 → G) → V) (g : (Fin 2 → G) → W) :
    kostantForm B σ f g = kostant B σ f g := rfl

theorem kostant_sum_left {ι : Type} (s : Finset ι) (f : ι → (Fin 2 → G) → V)
    (g : (Fin 2 → G) → W) :
    kostant B σ (∑ j ∈ s, f j) g = ∑ j ∈ s, kostant B σ (f j) g := by
  change kostantForm B σ (∑ j ∈ s, f j) g = ∑ j ∈ s, kostantForm B σ (f j) g
  rw [map_sum, LinearMap.sum_apply]

end Bilinear

section Invariance

variable [Group G]

/-- A `U`-equivariant one-cocycle. -/
def UCocycle (ρ : Representation ℂ G V) (U : Subgroup G) (f : (Fin 2 → G) → V) : Prop :=
  (∀ γ ∈ U, ∀ a b, f ![γ * a, γ * b] = ρ γ (f ![a, b])) ∧ ∀ x, differentialOneRaw f x = 0

theorem uCocycle_pull1 {ρ : Representation ℂ G V} {U : Subgroup G} {f : (Fin 2 → G) → V}
    (hf : UCocycle ρ U f) {h : G} (hn : ∀ u ∈ U, h * u * h⁻¹ ∈ U) :
    UCocycle ρ U (pull1 ρ h f) :=
  ⟨pull1_equivariant ρ hn hf.1, pull1_closed ρ h hf.2⟩

variable {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W} {B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ}
  {Λ U : Subgroup G} {σ : Chains G 2}

/-- An element whose inverse is a Levi element normalizes the lattice. -/
theorem conj_mem_of_isLevi_inv {k : G} (hk : IsLevi Λ U σ k⁻¹) :
    ∀ u ∈ U, k * u * k⁻¹ ∈ U := fun u hu => by simpa only [inv_inv] using hk.2.1 u hu

/-- A Levi element normalizes the lattice. -/
theorem inv_conj_mem_of_isLevi {k : G} (hk : IsLevi Λ U σ k) :
    ∀ u ∈ U, k⁻¹ * u * k⁻¹⁻¹ ∈ U := fun u hu => by simpa only [inv_inv] using hk.2.1 u hu

/-- **Levi invariance of the Kostant pairing** on `U`-equivariant one-cocycles. -/
theorem kostant_pull1 (D : PrismData G) (hσ : homogeneousBoundary 2 σ ∈ NullChains U 1)
    (hB : ∀ g ∈ Λ, ∀ v w, B (ρ g v) (ρ' g w) = B v w) (hUΛ : U ≤ Λ) {k : G}
    (hk : IsLevi Λ U σ k⁻¹) {f : (Fin 2 → G) → V} {g : (Fin 2 → G) → W}
    (hf : UCocycle ρ U f) (hg : UCocycle ρ' U g) :
    kostant B σ (pull1 ρ k f) (pull1 ρ' k g) = kostant B σ f g := by
  unfold kostant
  rw [← spull2_cup11 ρ ρ' B (fun v w => hB k⁻¹ hk.1 v w)]
  exact pair_spull2 D hσ hk
    (cup11_invariant B ρ ρ' (fun g' hg' => hB g' (hUΛ hg')) hf.1 hg.1) (cup11_closed B hf.2 hg.2)

/-- **Moving a pullback across the Kostant pairing**: `κ(f, k ⋆ g) = κ(k⁻¹ ⋆ f, g)`. -/
theorem kostant_shift (D : PrismData G) (hσ : homogeneousBoundary 2 σ ∈ NullChains U 1)
    (hB : ∀ g ∈ Λ, ∀ v w, B (ρ g v) (ρ' g w) = B v w) (hUΛ : U ≤ Λ) {k : G}
    (hk : IsLevi Λ U σ k) (hk' : IsLevi Λ U σ k⁻¹) {f : (Fin 2 → G) → V}
    {g : (Fin 2 → G) → W} (hf : UCocycle ρ U f) (hg : UCocycle ρ' U g) :
    kostant B σ f (pull1 ρ' k g) = kostant B σ (pull1 ρ k⁻¹ f) g := by
  have hf' : UCocycle ρ U (pull1 ρ k⁻¹ f) := uCocycle_pull1 hf (inv_conj_mem_of_isLevi hk)
  have h := kostant_pull1 D hσ hB hUΛ hk' hf' hg
  rw [pull1_pull1_inv] at h
  exact h

variable {ζ : (Fin 3 → G) → V} {η : (Fin 3 → G) → W} {ω ωU : (Fin 2 → G) → V}
  {θU : (Fin 2 → G) → W} {Λe : Subgroup G}

/-- The Levi cocycles of the fiber data are `U`-equivariant one-cocycles. -/
theorem uCocycle_leviCocycle (hF : FiberHyp ρ ρ' B Λ Λe U ζ η ω ωU θU) {h : G}
    (hh : IsLevi Λ U σ h⁻¹) :
    UCocycle ρ U (leviCocycle ρ ωU h) ∧ UCocycle ρ' U (leviCocycle ρ' θU h) := by
  have hhΛ : h ∈ Λ := by simpa only [inv_inv] using Λ.inv_mem hh.1
  have hn := conj_mem_of_isLevi_inv hh
  exact ⟨⟨leviCocycle_equivariant ρ hF.omegaU_eq hn,
      leviCocycle_closed ρ hF.omegaU_d (hF.zeta_eq h hhΛ)⟩,
    ⟨leviCocycle_equivariant ρ' hF.thetaU_eq hn,
      leviCocycle_closed ρ' hF.thetaU_d (hF.eta_eq h hhΛ)⟩⟩

/-- The cusp primitive `ω − ω_U` is a `U`-equivariant one-cocycle. -/
theorem uCocycle_cusp (hF : FiberHyp ρ ρ' B Λ Λe U ζ η ω ωU θU) : UCocycle ρ U (ω - ωU) := by
  refine ⟨fun γ hγ a b => ?_, fun x => ?_⟩
  · change ω ![γ * a, γ * b] - ωU ![γ * a, γ * b] = ρ γ (ω ![a, b] - ωU ![a, b])
    rw [hF.omega_eq γ (hF.le_edge hγ), hF.omegaU_eq γ hγ, map_sub]
  · show differentialOneRaw (ω - ωU) ![x 0, x 1, x 2] = 0
    rw [differentialOneRaw_sub, hF.omega_d, hF.omegaU_d, sub_self]

/-- At an element `m` of the edge stabilizer, `m ⋆ (ω − ω_U) = (ω − ω_U) − A(m)`. -/
theorem pull1_cusp (hF : FiberHyp ρ ρ' B Λ Λe U ζ η ω ωU θU) {m : G} (hm : m ∈ Λe) :
    pull1 ρ m (ω - ωU) = (ω - ωU) - leviCocycle ρ ωU m := by
  rw [pull1_sub, pull1_eq_self ρ (fun a b => hF.omega_eq m hm a b)]
  unfold leviCocycle
  abel

/-- `A(h) = −h ⋆ A(h⁻¹)`. -/
theorem leviCocycle_eq_neg_pull1_inv (ρ : Representation ℂ G V) (ω : (Fin 2 → G) → V) (h : G) :
    leviCocycle ρ ω h = -pull1 ρ h (leviCocycle ρ ω h⁻¹) := by
  have e := leviCocycle_inv ρ ω h⁻¹
  rwa [inv_inv] at e

end Invariance

end TernaryPeriodPolynomials.BoundaryDuality.FiberKostant
