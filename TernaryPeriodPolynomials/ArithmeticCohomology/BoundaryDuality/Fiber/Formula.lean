module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Fiber.Cusp

@[expose] public section


/-!
# Fiber integration of the local boundary value at a cusp

Let `Λ` be the stabilizer of a cusp in the homogeneous model with vertices in `G`, `Λe ≤ G` the
stabilizer of a complete flag above it, `U ≤ Λ ∩ Λe` a lattice with torus cycle `σ`, and
`B : V × W → ℂ` a pairing invariant under `Λ`. The data (`FiberHyp`) are a `Λ`-equivariant
two-cocycle `ζ` (the line class), a `Λe`-equivariant edge primitive `ω` (`dω = ζ`), a
`Λ`-equivariant two-cocycle `η` (the dual plane class), and `U`-equivariant primitives `ω_U`,
`θ_U` of `ζ` and `η` (the two classes restrict to zero on `U`: they lie in the part `E^{1,1}` of
the Hochschild–Serre filtration of `U ⋊ Λ/U`).

Choose a `Λ`-invariant primitive `K` of the four-cocycle `ζ ⌣ η` (it exists when `H⁴(Λ, ℂ) = 0`)
and a `U`-invariant primitive `ν` of the three-cocycle `K − ω_U ⌣ η` (it exists when
`H³(U, ℂ) = 0`) (`Primitives`, `exists_primitives`). The Levi data are
* the Levi cocycles `A(h) = h ⋆ ω_U − ω_U` and `A'(h) = h ⋆ θ_U − θ_U`, `U`-invariant
  one-cocycles which are right crossed homomorphisms in `h`;
* the Kostant pairing `κ(f, g) = ⟨f ⌣ g, σ⟩` of `U`-invariant one-cocycles;
* the fiber defect `ε(h) = h^* ν − ν − A(h) ⌣ θ_U`, a `U`-invariant two-cocycle, and its value
  `e(h) = ⟨ε(h), σ⟩`.

**Fiber integration** (`pair_cusp_eq`): for a Levi element `m ∈ Λe` (with `m⁻¹` Levi too) the
local value of the cusp cycle is

  `⟨ω ⌣ η − K, C(m)⟩ = −κ(m ⋆ (ω − ω_U), A'(m)) − e(m)`.

The defect is a twisted homomorphism: `e(h k) = e(h) + e(k) + κ(k ⋆ A(h), A'(k))`
(`defectValue_mul`), `e(1) = 0`, so for `f` of order `N`,
`N e(f) = −Σ_{j < N} κ(f ⋆ A(f^j), A'(f))` (`defectValue_torsion`). This is the vanishing of the
cup product in `H²` of the Levi quotient, and it determines `e` on products of torsion elements.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.FiberFormula

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.TopVanishing (homogeneousBoundary IsTopVanishing)
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains
open TernaryPeriodPolynomials.BoundaryDuality.ChainCalculus
open TernaryPeriodPolynomials.BoundaryDuality.LowVanishing
open TernaryPeriodPolynomials.BoundaryDuality.ChiHom
open TernaryPeriodPolynomials.BoundaryDuality.FiberCochains
open TernaryPeriodPolynomials.BoundaryDuality.FiberCusp

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

section Definitions

variable (ρ : Representation ℂ G V) (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (σ : Chains G 2)

/-- The Kostant pairing of one-cochains: `κ(f, g) = ⟨f ⌣ g, σ⟩`. -/
def kostant (f : (Fin 2 → G) → V) (g : (Fin 2 → G) → W) : ℂ :=
  Finsupp.linearCombination ℂ (cup11 B f g) σ

variable (ωU : (Fin 2 → G) → V) (θU : (Fin 2 → G) → W) (ν : (Fin 3 → G) → ℂ)

/-- The fiber defect `ε(h) = h^* ν − ν − A(h) ⌣ θ_U`. -/
def defect (h : G) : (Fin 3 → G) → ℂ :=
  spull2 h ν - ν - cup11 B (leviCocycle ρ ωU h) θU

/-- The value `e(h) = ⟨ε(h), σ⟩` of the fiber defect. -/
def defectValue (h : G) : ℂ :=
  Finsupp.linearCombination ℂ (defect ρ B ωU θU ν h) σ

/-- The `U`-invariant primitive `−(ω − ω_U) ⌣ θ_U − ν` of the edge three-cocycle `ω ⌣ η − K`. -/
def fiberPrimitive (ω : (Fin 2 → G) → V) : (Fin 3 → G) → ℂ :=
  -cup11 B (ω - ωU) θU - ν

end Definitions

/-- The local data at a cusp for the fiber integration: the stabilizers, the invariant pairing,
the line class `ζ` with its edge primitive `ω`, the dual plane class `η`, and the primitives
`ω_U`, `θ_U` of the restrictions of `ζ` and `η` to the lattice `U`. -/
structure FiberHyp (ρ : Representation ℂ G V) (ρ' : Representation ℂ G W)
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (Λ Λe U : Subgroup G) (ζ : (Fin 3 → G) → V)
    (η : (Fin 3 → G) → W) (ω ωU : (Fin 2 → G) → V) (θU : (Fin 2 → G) → W) : Prop where
  le : U ≤ Λ
  le_edge : U ≤ Λe
  invariant : ∀ g ∈ Λ, ∀ v w, B (ρ g v) (ρ' g w) = B v w
  zeta_eq : ∀ γ ∈ Λ, ∀ a b c, ζ ![γ * a, γ * b, γ * c] = ρ γ (ζ ![a, b, c])
  zeta_cocycle : IsCocycleTwo ζ
  eta_eq : ∀ γ ∈ Λ, ∀ a b c, η ![γ * a, γ * b, γ * c] = ρ' γ (η ![a, b, c])
  eta_cocycle : IsCocycleTwo η
  omega_eq : ∀ γ ∈ Λe, ∀ a b, ω ![γ * a, γ * b] = ρ γ (ω ![a, b])
  omega_d : ∀ a b c, differentialOneRaw ω ![a, b, c] = ζ ![a, b, c]
  omegaU_eq : ∀ γ ∈ U, ∀ a b, ωU ![γ * a, γ * b] = ρ γ (ωU ![a, b])
  omegaU_d : ∀ a b c, differentialOneRaw ωU ![a, b, c] = ζ ![a, b, c]
  thetaU_eq : ∀ γ ∈ U, ∀ a b, θU ![γ * a, γ * b] = ρ' γ (θU ![a, b])
  thetaU_d : ∀ a b c, differentialOneRaw θU ![a, b, c] = η ![a, b, c]

/-- The primitives used in the fiber integration: a `Λ`-invariant `K` with `dK = ζ ⌣ η` and a
`U`-invariant `ν` with `dν = K − ω_U ⌣ η`. -/
structure Primitives (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (Λ U : Subgroup G) (ζ : (Fin 3 → G) → V)
    (η : (Fin 3 → G) → W) (ωU : (Fin 2 → G) → V) (K : (Fin 4 → G) → ℂ)
    (ν : (Fin 3 → G) → ℂ) : Prop where
  K_inv : ∀ (γ : Λ) x, K (fun i => γ.val * x i) = K x
  K_d : ∀ x, differentialThreeRaw K x = cup22 B ζ η x
  nu_inv : ∀ (γ : U) x, ν (fun i => γ.val * x i) = ν x
  nu_d : ∀ x, differentialTwoRaw ν x = K x - cup12 B ωU η x

variable {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W} {B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ}
  {Λ Λe U : Subgroup G} {ζ : (Fin 3 → G) → V} {η : (Fin 3 → G) → W}
  {ω ωU : (Fin 2 → G) → V} {θU : (Fin 2 → G) → W}

/-- **Existence of the primitives** from `H⁴(Λ, ℂ) = 0` and `H³(U, ℂ) = 0`. -/
theorem exists_primitives (hF : FiberHyp ρ ρ' B Λ Λe U ζ η ω ωU θU) (hΛ : IsTopVanishing Λ)
    (hU : TopVanishingThree U) : ∃ K ν, Primitives B Λ U ζ η ωU K ν := by
  have hμ : ∀ (γ : Λ) x, cup22 B ζ η (fun i => γ.val * x i) = cup22 B ζ η x := by
    intro γ x
    change B (ζ ![γ.val * x 0, γ.val * x 1, γ.val * x 2])
        (η ![γ.val * x 2, γ.val * x 3, γ.val * x 4]) = B (ζ ![x 0, x 1, x 2]) (η ![x 2, x 3, x 4])
    rw [hF.zeta_eq γ.val γ.property, hF.eta_eq γ.val γ.property,
      hF.invariant γ.val γ.property]
  have hμc : ∀ x, differentialFourRaw (cup22 B ζ η) x = 0 := fun x =>
    differentialFourRaw_cupTwoTwo B id hF.zeta_cocycle hF.eta_cocycle x
  obtain ⟨K, hK, hdK⟩ := hΛ _ hμ hμc
  have hf : ∀ (γ : U) x, (K - cup12 B ωU η) (fun i => γ.val * x i) = (K - cup12 B ωU η) x := by
    intro γ x
    have e1 : K (fun i => γ.val * x i) = K x := hK ⟨γ.val, hF.le γ.property⟩ x
    have e2 : cup12 B ωU η (fun i => γ.val * x i) = cup12 B ωU η x := by
      change B (ωU ![γ.val * x 0, γ.val * x 1]) (η ![γ.val * x 1, γ.val * x 2, γ.val * x 3]) =
        B (ωU ![x 0, x 1]) (η ![x 1, x 2, x 3])
      rw [hF.omegaU_eq γ.val γ.property, hF.eta_eq γ.val (hF.le γ.property),
        hF.invariant γ.val (hF.le γ.property)]
    change K (fun i => γ.val * x i) - cup12 B ωU η (fun i => γ.val * x i) =
      K x - cup12 B ωU η x
    rw [e1, e2]
  have hfc : ∀ x, differentialThreeRaw (K - cup12 B ωU η) x = 0 := by
    intro x
    rw [differentialThreeRaw_sub', hdK, differentialThreeRaw_cup12 B ωU hF.eta_cocycle]
    change B (ζ ![x 0, x 1, x 2]) (η ![x 2, x 3, x 4]) -
      B (differentialOneRaw ωU ![x 0, x 1, x 2]) (η ![x 2, x 3, x 4]) = 0
    rw [hF.omegaU_d, sub_self]
  obtain ⟨ν, hν, hdν⟩ := hU _ hf hfc
  exact ⟨K, ν, { K_inv := hK, K_d := hdK, nu_inv := hν, nu_d := fun x => hdν x }⟩

section Defect

variable {K : (Fin 4 → G) → ℂ} {ν : (Fin 3 → G) → ℂ}

/-- The fiber defect at the identity vanishes. -/
theorem defect_one : defect ρ B ωU θU ν 1 = 0 := by
  funext x
  change ν ![1 * x 0, 1 * x 1, 1 * x 2] - ν x - cup11 B (leviCocycle ρ ωU 1) θU x = 0
  rw [leviCocycle_one, one_mul, one_mul, one_mul, vec3_eta]
  change ν x - ν x - B (0 : V) (θU ![x 1, x 2]) = 0
  rw [map_zero, LinearMap.zero_apply, sub_self, sub_zero]

/-- **The fiber defect is a twisted homomorphism** (cochain level):
`ε(h k) = ε(k) + k^* ε(h) + (k ⋆ A(h)) ⌣ A'(k)`. -/
theorem defect_mul {h k : G} (hk : ∀ v w, B (ρ k⁻¹ v) (ρ' k⁻¹ w) = B v w) :
    defect ρ B ωU θU ν (h * k) = defect ρ B ωU θU ν k + spull2 k (defect ρ B ωU θU ν h) +
      cup11 B (pull1 ρ k (leviCocycle ρ ωU h)) (leviCocycle ρ' θU k) := by
  have e3 : spull2 k (defect ρ B ωU θU ν h) = spull2 k (spull2 h ν) - spull2 k ν -
      cup11 B (pull1 ρ k (leviCocycle ρ ωU h)) (pull1 ρ' k θU) := by
    funext x
    change spull2 h ν ![k * x 0, k * x 1, k * x 2] - ν ![k * x 0, k * x 1, k * x 2] -
        B (leviCocycle ρ ωU h ![k * x 0, k * x 1]) (θU ![k * x 1, k * x 2]) =
      spull2 h ν ![k * x 0, k * x 1, k * x 2] - ν ![k * x 0, k * x 1, k * x 2] -
        B (ρ k⁻¹ (leviCocycle ρ ωU h ![k * x 0, k * x 1])) (ρ' k⁻¹ (θU ![k * x 1, k * x 2]))
    rw [hk]
  rw [e3]
  change spull2 (h * k) ν - ν - cup11 B (leviCocycle ρ ωU (h * k)) θU =
    (spull2 k ν - ν - cup11 B (leviCocycle ρ ωU k) θU) +
      (spull2 k (spull2 h ν) - spull2 k ν -
        cup11 B (pull1 ρ k (leviCocycle ρ ωU h)) (pull1 ρ' k θU)) +
      cup11 B (pull1 ρ k (leviCocycle ρ ωU h)) (pull1 ρ' k θU - θU)
  rw [spull2_mul, leviCocycle_mul, cup11_add_left, cup11_sub_right]
  abel

/-- The fiber defect is a two-cocycle. -/
theorem defect_closed (hF : FiberHyp ρ ρ' B Λ Λe U ζ η ω ωU θU)
    (hP : Primitives B Λ U ζ η ωU K ν) {h : G} (hh : h ∈ Λ) (x : Fin 4 → G) :
    differentialTwoRaw (defect ρ B ωU θU ν h) x = 0 := by
  have hA := leviCocycle_closed ρ hF.omegaU_d (hF.zeta_eq h hh)
  have hK : K ![h * x 0, h * x 1, h * x 2, h * x 3] = K x := by
    rw [vec4_mul]
    exact hP.K_inv ⟨h, hh⟩ x
  have hc : cup12 B ωU η ![h * x 0, h * x 1, h * x 2, h * x 3] =
      cup12 B (pull1 ρ h ωU) η x := by
    change B (ωU ![h * x 0, h * x 1]) (η ![h * x 1, h * x 2, h * x 3]) =
      B (ρ h⁻¹ (ωU ![h * x 0, h * x 1])) (η ![x 1, x 2, x 3])
    rw [hF.eta_eq h hh, ← hF.invariant h hh (ρ h⁻¹ _), rep_self_inv]
  have hd : cup12 B (leviCocycle ρ ωU h) (differentialOneRaw θU) x =
      cup12 B (pull1 ρ h ωU) η x - cup12 B ωU η x := by
    change B (pull1 ρ h ωU ![x 0, x 1] - ωU ![x 0, x 1]) (differentialOneRaw θU ![x 1, x 2, x 3]) =
      B (pull1 ρ h ωU ![x 0, x 1]) (η ![x 1, x 2, x 3]) - B (ωU ![x 0, x 1]) (η ![x 1, x 2, x 3])
    rw [hF.thetaU_d, map_sub, LinearMap.sub_apply]
  change differentialTwoRaw (spull2 h ν - ν - cup11 B (leviCocycle ρ ωU h) θU) x = 0
  rw [differentialTwoRaw_sub, differentialTwoRaw_sub, differentialTwoRaw_spull2, hP.nu_d,
    hP.nu_d, hK, hc, differentialTwoRaw_cup11_of_cocycle B hA, hd]
  ring

/-- The fiber defect is `U`-invariant at an element `h` with `h U h⁻¹ ⊆ U`. -/
theorem defect_invariant (hF : FiberHyp ρ ρ' B Λ Λe U ζ η ω ωU θU)
    (hP : Primitives B Λ U ζ η ωU K ν) {h : G} (hn : ∀ u ∈ U, h * u * h⁻¹ ∈ U) :
    ∀ (γ : U) x, defect ρ B ωU θU ν h (fun i => γ.val * x i) = defect ρ B ωU θU ν h x := by
  intro γ x
  have e : ∀ t, h * (γ.val * t) = h * γ.val * h⁻¹ * (h * t) := fun t => by group
  have h1 : spull2 h ν (fun i => γ.val * x i) = spull2 h ν x := by
    change ν ![h * (γ.val * x 0), h * (γ.val * x 1), h * (γ.val * x 2)] =
      ν ![h * x 0, h * x 1, h * x 2]
    rw [e (x 0), e (x 1), e (x 2)]
    exact inv3_apply hP.nu_inv (hn γ.val γ.property) _ _ _
  have h2 : ν (fun i => γ.val * x i) = ν x := hP.nu_inv γ x
  have h3 := cup11_invariant B ρ ρ' (fun g hg => hF.invariant g (hF.le hg))
    (leviCocycle_equivariant ρ hF.omegaU_eq hn) hF.thetaU_eq γ x
  change spull2 h ν (fun i => γ.val * x i) - ν (fun i => γ.val * x i) -
      cup11 B (leviCocycle ρ ωU h) θU (fun i => γ.val * x i) =
    spull2 h ν x - ν x - cup11 B (leviCocycle ρ ωU h) θU x
  rw [h1, h2, h3]

/-- The value of the fiber defect at the identity vanishes. -/
theorem defectValue_one (σ : Chains G 2) : defectValue ρ B σ ωU θU ν 1 = 0 := by
  unfold defectValue
  rw [defect_one, pair_zero]

/-- **The defect value is a twisted homomorphism**:
`e(h k) = e(h) + e(k) + κ(k ⋆ A(h), A'(k))`, for `h⁻¹`, `k⁻¹` Levi elements. -/
theorem defectValue_mul (hF : FiberHyp ρ ρ' B Λ Λe U ζ η ω ωU θU)
    (hP : Primitives B Λ U ζ η ωU K ν) (D : PrismData G) {σ : Chains G 2}
    (hσ : homogeneousBoundary 2 σ ∈ NullChains U 1) {h k : G} (hh : IsLevi Λ U σ h⁻¹)
    (hk : IsLevi Λ U σ k⁻¹) :
    defectValue ρ B σ ωU θU ν (h * k) = defectValue ρ B σ ωU θU ν h +
      defectValue ρ B σ ωU θU ν k +
        kostant B σ (pull1 ρ k (leviCocycle ρ ωU h)) (leviCocycle ρ' θU k) := by
  have hk1 : ∀ v w, B (ρ k⁻¹ v) (ρ' k⁻¹ w) = B v w := fun v w => hF.invariant k⁻¹ hk.1 v w
  have hhΛ : h ∈ Λ := by simpa only [inv_inv] using Λ.inv_mem hh.1
  have hn : ∀ u ∈ U, h * u * h⁻¹ ∈ U := fun u hu => by simpa only [inv_inv] using hh.2.1 u hu
  have hs := pair_spull2 D hσ hk (defect_invariant hF hP hn) (defect_closed hF hP hhΛ)
  change Finsupp.linearCombination ℂ (defect ρ B ωU θU ν (h * k)) σ =
    Finsupp.linearCombination ℂ (defect ρ B ωU θU ν h) σ +
      Finsupp.linearCombination ℂ (defect ρ B ωU θU ν k) σ +
        Finsupp.linearCombination ℂ (cup11 B (pull1 ρ k (leviCocycle ρ ωU h))
          (leviCocycle ρ' θU k)) σ
  rw [defect_mul hk1, pair_add, pair_add, hs]
  ring

/-- Iterating the twisted homomorphism along the powers of `f`. -/
theorem defectValue_pow (hF : FiberHyp ρ ρ' B Λ Λe U ζ η ω ωU θU)
    (hP : Primitives B Λ U ζ η ωU K ν) (D : PrismData G) {σ : Chains G 2}
    (hσ : homogeneousBoundary 2 σ ∈ NullChains U 1) {f : G} (hf : IsLevi Λ U σ f⁻¹) (j : ℕ) :
    defectValue ρ B σ ωU θU ν (f ^ j) = j * defectValue ρ B σ ωU θU ν f +
      ∑ i ∈ Finset.range j,
        kostant B σ (pull1 ρ f (leviCocycle ρ ωU (f ^ i))) (leviCocycle ρ' θU f) := by
  induction j with
  | zero =>
    rw [pow_zero, defectValue_one, Finset.sum_range_zero, Nat.cast_zero, zero_mul,
      add_zero]
  | succ j ih =>
    have hj : IsLevi Λ U σ (f ^ j)⁻¹ := by
      rw [← inv_pow]
      exact hf.pow j
    rw [pow_succ, defectValue_mul hF hP D hσ hj hf, ih, Finset.sum_range_succ]
    push_cast
    ring

/-- **The defect value at a torsion element**: if `f^N = 1` then
`N e(f) = −Σ_{j < N} κ(f ⋆ A(f^j), A'(f))`. -/
theorem defectValue_torsion (hF : FiberHyp ρ ρ' B Λ Λe U ζ η ω ωU θU)
    (hP : Primitives B Λ U ζ η ωU K ν) (D : PrismData G) {σ : Chains G 2}
    (hσ : homogeneousBoundary 2 σ ∈ NullChains U 1) {f : G} (hf : IsLevi Λ U σ f⁻¹) {N : ℕ}
    (hfN : f ^ N = 1) :
    (N : ℂ) * defectValue ρ B σ ωU θU ν f =
      -∑ i ∈ Finset.range N,
        kostant B σ (pull1 ρ f (leviCocycle ρ ωU (f ^ i))) (leviCocycle ρ' θU f) := by
  have h := defectValue_pow hF hP D hσ hf N
  rw [hfN, defectValue_one] at h
  linear_combination -h

/-- **Fiber integration of the local value at a cusp.** For a Levi element `m` of the edge
stabilizer (with `m⁻¹` Levi), `⟨ω ⌣ η − K, C(m)⟩ = −κ(m ⋆ (ω − ω_U), A'(m)) − e(m)`. -/
theorem pair_cusp_eq (hF : FiberHyp ρ ρ' B Λ Λe U ζ η ω ωU θU)
    (hP : Primitives B Λ U ζ η ωU K ν) (D : PrismData G) {σ : Chains G 2}
    (hσ : homogeneousBoundary 2 σ ∈ NullChains U 1) {m : G} (hm : IsLevi Λ U σ m)
    (hm' : IsLevi Λ U σ m⁻¹) (hme : m ∈ Λe) :
    Finsupp.linearCombination ℂ (cup12 B ω η - K) (cusp D σ hm) =
      -kostant B σ (pull1 ρ m (ω - ωU)) (leviCocycle ρ' θU m) -
        defectValue ρ B σ ωU θU ν m := by
  have hBU : ∀ g ∈ U, ∀ v w, B (ρ g v) (ρ' g w) = B v w := fun g hg => hF.invariant g (hF.le hg)
  have hc₀_closed : ∀ x, differentialOneRaw (ω - ωU) x = 0 := by
    intro x
    show differentialOneRaw (ω - ωU) ![x 0, x 1, x 2] = 0
    rw [differentialOneRaw_sub, hF.omega_d, hF.omegaU_d, sub_self]
  have hc₀_eq : ∀ γ ∈ U, ∀ a b, (ω - ωU) ![γ * a, γ * b] = ρ γ ((ω - ωU) ![a, b]) := by
    intro γ hγ a b
    change ω ![γ * a, γ * b] - ωU ![γ * a, γ * b] = ρ γ (ω ![a, b] - ωU ![a, b])
    rw [hF.omega_eq γ (hF.le_edge hγ), hF.omegaU_eq γ hγ, map_sub]
  -- the edge three-cocycle is the coboundary of the `U`-invariant `fiberPrimitive`
  have hdlam : cup12 B ω η - K = differentialTwoRaw (fiberPrimitive B ωU θU ν ω) := by
    funext x
    have h1 := differentialTwoRaw_cup11_of_cocycle B hc₀_closed θU x
    have h3 : cup12 B (ω - ωU) (differentialOneRaw θU) x = cup12 B ω η x - cup12 B ωU η x := by
      change B (ω ![x 0, x 1] - ωU ![x 0, x 1]) (differentialOneRaw θU ![x 1, x 2, x 3]) =
        B (ω ![x 0, x 1]) (η ![x 1, x 2, x 3]) - B (ωU ![x 0, x 1]) (η ![x 1, x 2, x 3])
      rw [hF.thetaU_d, map_sub, LinearMap.sub_apply]
    change cup12 B ω η x - K x = differentialTwoRaw (-cup11 B (ω - ωU) θU - ν) x
    rw [differentialTwoRaw_neg_sub, h1, h3, hP.nu_d]
    ring
  have hlam_inv : ∀ (γ : U) x, fiberPrimitive B ωU θU ν ω (fun i => γ.val * x i) =
      fiberPrimitive B ωU θU ν ω x := by
    intro γ x
    have e1 := cup11_invariant B ρ ρ' hBU hc₀_eq hF.thetaU_eq γ x
    have e2 := hP.nu_inv γ x
    change -cup11 B (ω - ωU) θU (fun i => γ.val * x i) - ν (fun i => γ.val * x i) =
      -cup11 B (ω - ωU) θU x - ν x
    rw [e1, e2]
  -- step 1: remove the correction of the cusp cycle
  rw [hdlam, pair_cusp D hσ hm hlam_inv]
  -- step 2: `m^* λ − λ = −(m ⋆ c₀) ⌣ A'(m) − ε(m)`
  have hm1 : ∀ v w, B (ρ m⁻¹ v) (ρ' m⁻¹ w) = B v w := fun v w => hF.invariant m⁻¹ hm'.1 v w
  have hω : pull1 ρ m ω = ω := pull1_eq_self ρ (fun a b => hF.omega_eq m hme a b)
  have e1 : spull2 m (fiberPrimitive B ωU θU ν ω) =
      -cup11 B (pull1 ρ m (ω - ωU)) (pull1 ρ' m θU) - spull2 m ν := by
    funext x
    change -B ((ω - ωU) ![m * x 0, m * x 1]) (θU ![m * x 1, m * x 2]) -
        ν ![m * x 0, m * x 1, m * x 2] =
      -B (ρ m⁻¹ ((ω - ωU) ![m * x 0, m * x 1])) (ρ' m⁻¹ (θU ![m * x 1, m * x 2])) -
        ν ![m * x 0, m * x 1, m * x 2]
    rw [hm1]
  have hstep : spull2 m (fiberPrimitive B ωU θU ν ω) - fiberPrimitive B ωU θU ν ω =
      -cup11 B (pull1 ρ m (ω - ωU)) (leviCocycle ρ' θU m) - defect ρ B ωU θU ν m := by
    rw [e1]
    unfold fiberPrimitive defect leviCocycle
    rw [pull1_sub, hω]
    simp only [cup11_sub_left, cup11_sub_right]
    abel
  rw [hstep]
  -- step 3: replace the conjugated torus cycle by the torus cycle
  have hn : ∀ u ∈ U, m * u * m⁻¹ ∈ U := fun u hu => by simpa only [inv_inv] using hm'.2.1 u hu
  have hP1 := pull1_equivariant ρ hn hc₀_eq
  have hP1c := pull1_closed ρ m hc₀_closed
  have hA'eq := leviCocycle_equivariant ρ' hF.thetaU_eq hn
  have hA'c := leviCocycle_closed ρ' hF.thetaU_d (hF.eta_eq m hm.1)
  have hinv1 := cup11_invariant B ρ ρ' hBU hP1 hA'eq
  have hcl1 := cup11_closed B hP1c hA'c
  have hinv2 := defect_invariant hF hP hn
  have hcl2 := defect_closed hF hP hm.1
  have hinv : ∀ (γ : U) x,
      (-cup11 B (pull1 ρ m (ω - ωU)) (leviCocycle ρ' θU m) - defect ρ B ωU θU ν m)
        (fun i => γ.val * x i) =
      (-cup11 B (pull1 ρ m (ω - ωU)) (leviCocycle ρ' θU m) - defect ρ B ωU θU ν m) x := by
    intro γ x
    change -cup11 B (pull1 ρ m (ω - ωU)) (leviCocycle ρ' θU m) (fun i => γ.val * x i) -
        defect ρ B ωU θU ν m (fun i => γ.val * x i) =
      -cup11 B (pull1 ρ m (ω - ωU)) (leviCocycle ρ' θU m) x - defect ρ B ωU θU ν m x
    rw [hinv1 γ x, hinv2 γ x]
  have hcl : ∀ x, differentialTwoRaw
      (-cup11 B (pull1 ρ m (ω - ωU)) (leviCocycle ρ' θU m) - defect ρ B ωU θU ν m) x = 0 := by
    intro x
    rw [differentialTwoRaw_neg_sub, hcl1, hcl2, neg_zero, sub_zero]
  rw [pair_eq_of_sub_mem_bdry hinv hcl hm.2.2, pair_sub, pair_neg]
  rfl

end Defect

end TernaryPeriodPolynomials.BoundaryDuality.FiberFormula
