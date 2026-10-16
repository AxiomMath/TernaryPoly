module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.ShuffleChain

@[expose] public section


/-!
# The fibre integration of a primitive: `μ σ = ⟨γ, Sh(ν; σ)⟩` is a primitive of `⟨dγ, Sh(ν; α, β)⟩`

Formalized by Claude Sonnet 5.5.

`T1`: for a 3-cochain `γ` of `G` vanishing on triples of `N`-letters (`Ge1`) with `dγ` vanishing on quadruples of which at least three are `N`-letters (`Ge2`), and assuming the
torus homotopies `∂m_α = ν^α - ν` (`hμ`), `μ β - μ(αβ) + μ α = ⟨dγ, Sh(ν; α, β)⟩` exactly.
`T2_cup22`, `T2_cup12`: for normal-form cochains `z`, `z'` (vanishing when the first letter is an `N`-letter, and `z(ll α, ll β) = 0`) only one placement survives.
-/

open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

open Finsupp in
/-- The bar boundary of `M`-chains of degree three (`M` abelian). -/
def torusBd3 (M : Type) [AddCommGroup M] : ((M × M × M) →₀ ℚ) →ₗ[ℚ] ((M × M) →₀ ℚ) :=
  linearCombination ℚ fun v => single (v.2.1, v.2.2) 1 - single (v.1 + v.2.1, v.2.2) 1 +
    single (v.1, v.2.1 + v.2.2) 1 - single (v.1, v.2.1) 1

open Finsupp in
/-- The torus cycle `ν = [e₁|e₂] - [e₂|e₁]`. -/
def nuChain {M : Type} [AddCommGroup M] (e₁ e₂ : M) : (M × M) →₀ ℚ := single (e₁, e₂) 1 - single (e₂, e₁) 1

namespace PairModel

variable {G M L : Type} [Group G] [AddCommGroup M] [Group L] (P : PairModel G M L)

/-- The 3-cochain vanishes on triples of `N`-letters (filtration `≥ 1`). -/
def Ge1 (γ : G → G → G → ℚ) : Prop := ∀ a b c : M, γ (P.nl a) (P.nl b) (P.nl c) = 0

/-- The 4-cochain vanishes on the quadruples with exactly one `L`-letter (it is in filtration `≥ 2`). -/
def ShapeOne (Γ : G → G → G → G → ℚ) : Prop := ∀ (σ : L) (a b c : M),
  Γ (P.ll σ) (P.nl a) (P.nl b) (P.nl c) = 0 ∧ Γ (P.nl a) (P.ll σ) (P.nl b) (P.nl c) = 0 ∧
    Γ (P.nl a) (P.nl b) (P.ll σ) (P.nl c) = 0 ∧ Γ (P.nl a) (P.nl b) (P.nl c) (P.ll σ) = 0

/-- A 4-cochain vanishing when the first or the third letter is an `N`-letter (e.g. `cup22 z z'` for `z(nl, ·) = z'(nl, ·) = 0`) is in `ShapeOne`. -/
theorem shapeOne_of_left_third (Γ : G → G → G → G → ℚ)
    (h : ∀ g₁ g₂ g₃ g₄ : G, (∃ v, g₁ = P.nl v) ∨ (∃ v, g₃ = P.nl v) → Γ g₁ g₂ g₃ g₄ = 0) : P.ShapeOne Γ :=
  fun _ a b _ => ⟨h _ _ _ _ (Or.inr ⟨b, rfl⟩), h _ _ _ _ (Or.inl ⟨a, rfl⟩), h _ _ _ _ (Or.inl ⟨a, rfl⟩),
    h _ _ _ _ (Or.inl ⟨a, rfl⟩)⟩

/-- `μ σ = ⟨γ, Sh(ν; σ)⟩`, `ν = [e₁|e₂] - [e₂|e₁]`. -/
def mu (γ : G → G → G → ℚ) (e₁ e₂ : M) (σ : L) : ℚ := P.sh1 γ e₁ e₂ σ - P.sh1 γ e₂ e₁ σ

/-- The pairing of a 3-cochain with `Sh(c; β)`, `c` a degree-two `M`-chain. -/
def chA (γ : G → G → G → ℚ) (β : L) : ((M × M) →₀ ℚ) →ₗ[ℚ] ℚ :=
  Finsupp.linearCombination ℚ fun v => P.sh1 γ v.1 v.2 β

/-- The pairing of a 4-cochain with `Sh(m; β)`, `m` a degree-three `M`-chain. -/
def chB (Γ : G → G → G → G → ℚ) (β : L) : ((M × M × M) →₀ ℚ) →ₗ[ℚ] ℚ :=
  Finsupp.linearCombination ℚ fun v => P.sh1' Γ v.1 v.2.1 v.2.2 β

/-- The pairing of a 3-cochain with the pure `N`-chain `m^β - m`. -/
def chZ (γ : G → G → G → ℚ) (β : L) : ((M × M × M) →₀ ℚ) →ₗ[ℚ] ℚ :=
  Finsupp.linearCombination ℚ fun v =>
    γ (P.nl (P.ψ β⁻¹ v.1)) (P.nl (P.ψ β⁻¹ v.2.1)) (P.nl (P.ψ β⁻¹ v.2.2)) - γ (P.nl v.1) (P.nl v.2.1) (P.nl v.2.2)

/-- **(C1) for arbitrary degree-three `M`-chains**: `⟨dγ, Sh(m; β)⟩ = -⟨γ, Sh(∂m; β)⟩ + ⟨γ, m^β - m⟩`. -/
theorem chB_dd (γ : G → G → G → ℚ) (β : L) (m : (M × M × M) →₀ ℚ) :
    P.chB (dd3T γ) β m = -(P.chA γ β (torusBd3 M m)) + P.chZ γ β m := by
  have h : P.chB (dd3T γ) β = -(P.chA γ β ∘ₗ torusBd3 M) + P.chZ γ β := by
    apply Finsupp.lhom_ext
    intro a b
    simp only [chB, chA, chZ, torusBd3, Finsupp.linearCombination_single, LinearMap.add_apply, LinearMap.neg_apply,
      LinearMap.comp_apply, map_smul, map_add, map_sub, smul_eq_mul]
    rw [P.C1_three γ a.1 a.2.1 a.2.2 β]
    ring
  rw [h]
  rfl

theorem chA_nu (γ : G → G → G → ℚ) (β : L) (a b : M) :
    P.chA γ β (nuChain a b) = P.sh1 γ a b β - P.sh1 γ b a β := by
  simp [chA, nuChain, Finsupp.linearCombination_single, map_sub]

theorem chB_zero (Γ : G → G → G → G → ℚ) (hΓ : P.ShapeOne Γ) (β : L) (m : (M × M × M) →₀ ℚ) : P.chB Γ β m = 0 := by
  have h : P.chB Γ β = 0 := by
    apply Finsupp.lhom_ext
    intro a b
    have t1 := (hΓ β (P.ψ β⁻¹ a.1) (P.ψ β⁻¹ a.2.1) (P.ψ β⁻¹ a.2.2)).1
    have t2 := (hΓ β a.1 (P.ψ β⁻¹ a.2.1) (P.ψ β⁻¹ a.2.2)).2.1
    have t3 := (hΓ β a.1 a.2.1 (P.ψ β⁻¹ a.2.2)).2.2.1
    have t4 := (hΓ β a.1 a.2.1 a.2.2).2.2.2
    have h0 : P.sh1' Γ a.1 a.2.1 a.2.2 β = 0 := by
      unfold sh1'
      rw [t1, t2, t3, t4]
      ring
    simp [chB, Finsupp.linearCombination_single, h0]
  rw [h]; rfl

theorem chZ_zero (γ : G → G → G → ℚ) (hγ : P.Ge1 γ) (β : L) (m : (M × M × M) →₀ ℚ) : P.chZ γ β m = 0 := by
  have h : P.chZ γ β = 0 := by
    apply Finsupp.lhom_ext
    intro a b
    simp [chZ, Finsupp.linearCombination_single, hγ (P.ψ β⁻¹ a.1) (P.ψ β⁻¹ a.2.1) (P.ψ β⁻¹ a.2.2), hγ a.1 a.2.1 a.2.2]
  rw [h]; rfl

/-- **(C0) dualised**: `⟨dα, Sh(ν; σ)⟩ = ⟨α, ν^σ - ν⟩` for every 2-cochain `α`. -/
theorem C0 (al : G → G → ℚ) (e₁ e₂ : M) (σ : L) :
    P.sh1 (dd2T al) e₁ e₂ σ - P.sh1 (dd2T al) e₂ e₁ σ =
      (al (P.nl (P.ψ σ⁻¹ e₁)) (P.nl (P.ψ σ⁻¹ e₂)) - al (P.nl (P.ψ σ⁻¹ e₂)) (P.nl (P.ψ σ⁻¹ e₁))) -
        (al (P.nl e₁) (P.nl e₂) - al (P.nl e₂) (P.nl e₁)) := by
  simp only [sh1, dd2T, nl_mul_nl, ll_mul_nl, nl_mul_ll]
  abel_nf

/-- **THEOREM T1.** -/
theorem T1 (γ : G → G → G → ℚ) (hγ : P.Ge1 γ) (hΓ : P.ShapeOne (dd3T γ)) (e₁ e₂ : M)
    (hμ : ∀ α : L, ∃ m : (M × M × M) →₀ ℚ,
      torusBd3 M m = nuChain (P.ψ α⁻¹ e₁) (P.ψ α⁻¹ e₂) - nuChain e₁ e₂) (α β : L) :
    P.mu γ e₁ e₂ β - P.mu γ e₁ e₂ (α * β) + P.mu γ e₁ e₂ α =
      P.sh2' (dd3T γ) e₁ e₂ α β - P.sh2' (dd3T γ) e₂ e₁ α β := by
  obtain ⟨m, hm⟩ := hμ α
  have h1 := P.chB_dd γ β m
  rw [P.chB_zero _ hΓ, P.chZ_zero γ hγ, hm, map_sub, P.chA_nu, P.chA_nu] at h1
  rw [P.C2 γ e₁ e₂ α β]
  unfold mu
  linarith

section Explicit

variable {V W' : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup W'] [Module ℚ W']
  (ρ' : Representation ℚ G W') (e : V →ₗ[ℚ] W' →ₗ[ℚ] ℚ)

/-- **T2 (cup22):** for normal-form cochains only the placement `[α | α·v₁ | β | (αβ)·v₂]` contributes, with sign `-1`. -/
theorem T2_cup22 (z : G → G → V) (z' : G → G → W') (hzN : ∀ v g, z (P.nl v) g = 0)
    (hU : ∀ α β, z (P.ll α) (P.ll β) = 0) (hzN' : ∀ v g, z' (P.nl v) g = 0) (v₁ v₂ : M) (α β : L) :
    P.sh2' (cup22 ρ' e z z') v₁ v₂ α β =
      -e (z (P.ll α) (P.nl (P.ψ α⁻¹ v₁))) (ρ' (P.pr v₁ α) (z' (P.ll β) (P.nl (P.ψ (α * β)⁻¹ v₂)))) := by
  unfold sh2' cup22
  simp [hU, hzN, hzN', ll_mul_nl]

/-- **T2 (cup12):** `⟨cup12 w z', Sh(v₁ v₂; σ)⟩ = -e(w v₁, v₁ · z'(σ, σ·v₂))`. -/
theorem T2_cup12 (w : G → V) (z' : G → G → W') (hzN' : ∀ v g, z' (P.nl v) g = 0) (v₁ v₂ : M) (σ : L) :
    P.sh1 (cup12 ρ' e w z') v₁ v₂ σ = -e (w (P.nl v₁)) (ρ' (P.nl v₁) (z' (P.ll σ) (P.nl (P.ψ σ⁻¹ v₂)))) := by
  unfold sh1 cup12
  simp [hzN']

end Explicit

end PairModel

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
