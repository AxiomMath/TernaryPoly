module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.CupProduct

@[expose] public section


/-!
# The Eilenberg-Zilber shuffle of the torus 2-cycle with the Levi letters, in functional form

Formalized by Claude Sonnet 5.5.

`PairModel G M L`: a group `G` with pair coordinates `pr a σ` (`a ∈ M`, `σ ∈ L`) multiplying as in `M ⋊ L` (`pr a σ * pr b τ = pr (a + ψ σ b) (σ τ)`).
`sh1 γ v₁ v₂ σ`, `sh1'`, `sh2'` are the pairings of a cochain with the shuffles `Sh([v₁|v₂]; σ)`, `Sh([v₁|v₂|v₃]; σ)`, `Sh([v₁|v₂]; α, β)` of the `M`-letters with
the `L`-letters; an `M`-letter placed after the `L`-prefix `P` is conjugated by `ψ P⁻¹`, and the sign is `(-1)^{#M-letters before each L-letter}`.
* `C1_three`: `⟨dγ, Sh(c; β)⟩ = -⟨γ, Sh(∂c; β)⟩ + ⟨γ, c^β - c⟩` for the `M`-chain `c = [v₁|v₂|v₃]`.
* `C2`: `⟨dγ, Sh(ν; α, β)⟩ = ⟨γ, Sh(ν^α; β)⟩ - ⟨γ, Sh(ν; αβ)⟩ + ⟨γ, Sh(ν; α)⟩` for `ν = [v₁|v₂] - [v₂|v₁]`.
Both are identities between finitely many evaluations of an arbitrary cochain, closed by `abel_nf` in the additive coordinates.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

/-- A group `G` with "pair coordinates" `pr a σ = a · σ` (`a ∈ M`, `σ ∈ L`) multiplying as in `M ⋊ L`: `pr a σ * pr b τ = pr (a + ψ σ b) (σ τ)`. -/
structure PairModel (G M L : Type) [Group G] [AddCommGroup M] [Group L] where
  ψ : L → M →+ M
  ψ_one : ∀ x, ψ 1 x = x
  ψ_mul : ∀ σ τ x, ψ (σ * τ) x = ψ σ (ψ τ x)
  pr : M → L → G
  pr_mul : ∀ a σ b τ, pr a σ * pr b τ = pr (a + ψ σ b) (σ * τ)

namespace PairModel

variable {G M L : Type} [Group G] [AddCommGroup M] [Group L] (P : PairModel G M L)

theorem ψ_ψ_inv (σ : L) (x : M) : P.ψ σ (P.ψ σ⁻¹ x) = x := by
  rw [← P.ψ_mul, mul_inv_cancel, P.ψ_one]

theorem ψ_inv_ψ (σ : L) (x : M) : P.ψ σ⁻¹ (P.ψ σ x) = x := by
  rw [← P.ψ_mul, inv_mul_cancel, P.ψ_one]

/-- The `N`-letter and the `L`-letter. -/
def nl (v : M) : G := P.pr v 1
def ll (σ : L) : G := P.pr 0 σ

/-- `Sh(v₁ v₂; σ)` paired with a 3-cochain `γ`. -/
def sh1 (γ : G → G → G → ℚ) (v₁ v₂ : M) (σ : L) : ℚ :=
  γ (P.ll σ) (P.nl (P.ψ σ⁻¹ v₁)) (P.nl (P.ψ σ⁻¹ v₂)) - γ (P.nl v₁) (P.ll σ) (P.nl (P.ψ σ⁻¹ v₂)) +
    γ (P.nl v₁) (P.nl v₂) (P.ll σ)

/-- `Sh(v₁ v₂ v₃; σ)` paired with a 4-cochain. -/
def sh1' (Γ : G → G → G → G → ℚ) (v₁ v₂ v₃ : M) (σ : L) : ℚ :=
  Γ (P.ll σ) (P.nl (P.ψ σ⁻¹ v₁)) (P.nl (P.ψ σ⁻¹ v₂)) (P.nl (P.ψ σ⁻¹ v₃)) -
    Γ (P.nl v₁) (P.ll σ) (P.nl (P.ψ σ⁻¹ v₂)) (P.nl (P.ψ σ⁻¹ v₃)) +
    Γ (P.nl v₁) (P.nl v₂) (P.ll σ) (P.nl (P.ψ σ⁻¹ v₃)) - Γ (P.nl v₁) (P.nl v₂) (P.nl v₃) (P.ll σ)

theorem nl_mul_nl (a b : M) : P.nl a * P.nl b = P.nl (a + b) := by
  simp [PairModel.nl, P.pr_mul, P.ψ_one]

theorem nl_mul_ll (a : M) (σ : L) : P.nl a * P.ll σ = P.pr a σ := by
  simp [PairModel.nl, PairModel.ll, P.pr_mul, P.ψ_one]

theorem ll_mul_ll (σ τ : L) : P.ll σ * P.ll τ = P.ll (σ * τ) := by
  simp [PairModel.ll, P.pr_mul]

theorem ll_mul_nl (σ : L) (v : M) : P.ll σ * P.nl (P.ψ σ⁻¹ v) = P.pr v σ := by
  simp [PairModel.nl, PairModel.ll, P.pr_mul, P.ψ_ψ_inv]

/-- **The chain-level identity (C1) for degree-three `N`-chains, dualised**:
`⟨dγ, Sh([v₁|v₂|v₃]; β)⟩ = -⟨γ, Sh(∂[v₁|v₂|v₃]; β)⟩ + ⟨γ, [β·v] - [v]⟩`. -/
theorem C1_three (γ : G → G → G → ℚ) (v₁ v₂ v₃ : M) (β : L) :
    P.sh1' (dd3T γ) v₁ v₂ v₃ β =
      -(P.sh1 γ v₂ v₃ β - P.sh1 γ (v₁ + v₂) v₃ β + P.sh1 γ v₁ (v₂ + v₃) β - P.sh1 γ v₁ v₂ β) +
        (γ (P.nl (P.ψ β⁻¹ v₁)) (P.nl (P.ψ β⁻¹ v₂)) (P.nl (P.ψ β⁻¹ v₃)) - γ (P.nl v₁) (P.nl v₂) (P.nl v₃)) := by
  simp only [sh1, sh1', dd3T, nl_mul_nl, ll_mul_nl, nl_mul_ll, map_add]
  abel

theorem ll_mul_nl' (σ : L) (x : M) : P.ll σ * P.nl x = P.pr (P.ψ σ x) σ := by
  simp [PairModel.nl, PairModel.ll, P.pr_mul]

/-- `Sh(v₁ v₂; α, β)` paired with a 4-cochain (the six placements of two `L`-letters among two `N`-letters). -/
def sh2' (Γ : G → G → G → G → ℚ) (v₁ v₂ : M) (α β : L) : ℚ :=
  Γ (P.ll α) (P.ll β) (P.nl (P.ψ (α * β)⁻¹ v₁)) (P.nl (P.ψ (α * β)⁻¹ v₂)) -
    Γ (P.ll α) (P.nl (P.ψ α⁻¹ v₁)) (P.ll β) (P.nl (P.ψ (α * β)⁻¹ v₂)) +
    Γ (P.ll α) (P.nl (P.ψ α⁻¹ v₁)) (P.nl (P.ψ α⁻¹ v₂)) (P.ll β) +
    Γ (P.nl v₁) (P.ll α) (P.ll β) (P.nl (P.ψ (α * β)⁻¹ v₂)) -
    Γ (P.nl v₁) (P.ll α) (P.nl (P.ψ α⁻¹ v₂)) (P.ll β) + Γ (P.nl v₁) (P.nl v₂) (P.ll α) (P.ll β)

/-- **(C2) dualised**: `⟨dγ, Sh(ν; α, β)⟩ = ⟨γ, Sh(ν^α; β)⟩ - ⟨γ, Sh(ν; αβ)⟩ + ⟨γ, Sh(ν; α)⟩`, `ν = [v₁|v₂] - [v₂|v₁]`. -/
theorem C2 (γ : G → G → G → ℚ) (v₁ v₂ : M) (α β : L) :
    P.sh2' (dd3T γ) v₁ v₂ α β - P.sh2' (dd3T γ) v₂ v₁ α β =
      (P.sh1 γ (P.ψ α⁻¹ v₁) (P.ψ α⁻¹ v₂) β - P.sh1 γ (P.ψ α⁻¹ v₂) (P.ψ α⁻¹ v₁) β) -
        (P.sh1 γ v₁ v₂ (α * β) - P.sh1 γ v₂ v₁ (α * β)) + (P.sh1 γ v₁ v₂ α - P.sh1 γ v₂ v₁ α) := by
  simp only [sh2', sh1, dd3T, nl_mul_nl, ll_mul_nl', nl_mul_ll, ll_mul_ll, mul_inv_rev, P.ψ_mul, P.ψ_ψ_inv]
  abel_nf

end PairModel

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
