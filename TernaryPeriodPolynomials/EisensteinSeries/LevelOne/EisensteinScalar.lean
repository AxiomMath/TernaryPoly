module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.BoundaryPeriod
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.ParabolicES

@[expose] public section


/-!
# The Eisenstein line of `H¹(GL₂(ℤ), Sym^{2r} ⊗ det^σ)` and the Hecke scalar on it

Let `betaGL r σ` be the boundary functional `[z] ↦ ℓ(z(T))` of `H¹(SL₂(ℤ), Sym^{2r})` composed with
the restriction from `GL₂(ℤ)`. It kills the Eichler–Shimura period image, is nonzero on `SL₂(ℤ)`, and
is a Hecke eigenfunctional with eigenvalue `q = p^(2r+1-σ) + p^(-σ)`. Combined with the dimension
count `ker_eq_range_period`, the period image is exactly its kernel (`ker_betaGL_eq_range_per`).
Consequently `T_p x - q x` is a period class for every class `x` (`arithmeticHecke_sub_mem_range`):
`T_p` acts on the quotient `H¹ / periodImage` (of dimension at most one) by the scalar `q`.
Every generalized eigenvector of some `T_{p₀}` with eigenvalue `≠ q p₀` is a period class
(`mem_range_per_of_mem_maxGenEigenspace`).

Original work by Claude Sonnet 5.5 and Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open scoped ModularForm MatrixGroups
open GeneralEisenstein
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.LevelOneHecke
open TernaryPeriodPolynomials.Spectral.LevelOneEichlerShimura
open TernaryPeriodPolynomials.Spectral.LevelOneESDimension
open TernaryPeriodPolynomials.Spectral.LevelOneHeckeH1
open TernaryPeriodPolynomials.Spectral.BoundaryFunctional
open TernaryPeriodPolynomials.Spectral.ParabolicES

namespace TernaryPeriodPolynomials.LevelOneEisenstein

/-- **The boundary functional on `H¹(GL₂(ℤ), Sym^d ⊗ det^σ)`**: restriction to `SL₂(ℤ)` followed
by `z ↦ ℓ(z(T))`. -/
def betaGL (d : ℕ) (σ : ℤ) : groupCohomology.H1 (arithmeticBinaryRep d σ) →ₗ[ℂ] ℂ :=
  beta d σ ∘ₗ restriction d σ σ

/-- **Hecke equivariance of `betaGL`**: `β ∘ T_p = q β`, `q = p^(d+1-σ) + p^(-σ)`. -/
theorem betaGL_arithmeticHecke (d : ℕ) (σ : ℤ) (p : Nat.Primes)
    (x : groupCohomology.H1 (arithmeticBinaryRep d σ)) :
    betaGL d σ (arithmeticHecke d σ p x) = q d σ p * betaGL d σ x := by
  simp only [betaGL, LinearMap.comp_apply]
  rw [restriction_arithmeticHecke, beta_modularHecke]

/-- **`betaGL` kills the period image.** -/
theorem betaGL_per (r : ℕ) (σ : ℤ) (f : CuspForm levelOne (-2 * hw r)) :
    betaGL (2 * r) σ (per r σ f) = 0 :=
  BoundaryPeriod.beta_restriction_levelOnePeriodMap (2 * r) σ σ (hw r) (weight_eq_r r)
    (even_two_mul r) (parityOf σ) (parityOf_sign σ) f

/-- **The period image is the kernel of the boundary functional**, for every twist. -/
theorem ker_betaGL_eq_range_per (r : ℕ) (positive : 0 < r) (σ : ℤ) :
    LinearMap.ker (betaGL (2 * r) σ) = LinearMap.range (per r σ) :=
  (ker_eq_range_period r positive σ (beta (2 * r) σ)
    (beta_ne_zero (2 * r) σ (by omega) (even_two_mul r))
    (fun f => BoundaryPeriod.beta_restriction_levelOnePeriodMap (2 * r) σ σ (hw r)
      (weight_eq_r r) (even_two_mul r) (parityOf σ) (parityOf_sign σ) f)
    (fun f => BoundaryPeriod.beta_restriction_levelOnePeriodMap (2 * r) (σ + 1) σ (hw r)
      (weight_eq_r r) (even_two_mul r) (parityOf (σ + 1)) (parityOf_sign (σ + 1)) f)).1

/-- `T_p` preserves the period image: `T_p (per f) = p^(-σ) per (T_p f)`. -/
theorem arithmeticHecke_per (r : ℕ) (σ : ℤ) (p : Nat.Primes) (f : CuspForm levelOne (-2 * hw r)) :
    arithmeticHecke (2 * r) σ p (per r σ f) =
      ((p.val : ℂ) ^ σ)⁻¹ • per r σ (levelOneHecke (-2 * hw r) p f) := by
  have h := levelOnePeriodMap_hecke (2 * r) σ p (hw r) (weight_eq_r r) (even_two_mul r)
    (parityOf σ) (parityOf_sign σ) f
  have hp : ((p.val : ℂ) ^ σ) ≠ 0 := zpow_ne_zero _ (by exact_mod_cast p.property.ne_zero)
  change per r σ (levelOneHecke (-2 * hw r) p f) =
    ((p.val : ℂ) ^ σ) • arithmeticHecke (2 * r) σ p (per r σ f) at h
  rw [h, smul_smul, inv_mul_cancel₀ hp, one_smul]

theorem arithmeticHecke_mem_range (r : ℕ) (σ : ℤ) (p : Nat.Primes)
    {x : groupCohomology.H1 (arithmeticBinaryRep (2 * r) σ)} (hx : x ∈ LinearMap.range (per r σ)) :
    arithmeticHecke (2 * r) σ p x ∈ LinearMap.range (per r σ) := by
  obtain ⟨f, rfl⟩ := hx
  rw [arithmeticHecke_per]
  exact Submodule.smul_mem _ _ ⟨_, rfl⟩

/-- **The Hecke scalar on `H¹ / periodImage`**: `T_p x - q x` is a period class for every `x`. -/
theorem arithmeticHecke_sub_mem_range (r : ℕ) (positive : 0 < r) (σ : ℤ) (p : Nat.Primes)
    (x : groupCohomology.H1 (arithmeticBinaryRep (2 * r) σ)) :
    arithmeticHecke (2 * r) σ p x - q (2 * r) σ p • x ∈ LinearMap.range (per r σ) := by
  rw [← ker_betaGL_eq_range_per r positive σ, LinearMap.mem_ker, map_sub, map_smul,
    betaGL_arithmeticHecke, smul_eq_mul, sub_self]

/-- **Generalized eigenvectors away from the Eisenstein eigenvalue are period classes**: if
`(T_{p₀} - μ)^k x = 0` for some `k` and `μ ≠ q`, then `x` is a period class. -/
theorem mem_range_per_of_mem_maxGenEigenspace (r : ℕ) (positive : 0 < r) (σ : ℤ)
    (p₀ : Nat.Primes) (μ : ℂ) (hμ : μ ≠ q (2 * r) σ p₀)
    {x : groupCohomology.H1 (arithmeticBinaryRep (2 * r) σ)}
    (hx : x ∈ (arithmeticHecke (2 * r) σ p₀).maxGenEigenspace μ) :
    x ∈ LinearMap.range (per r σ) := by
  rw [← ker_betaGL_eq_range_per r positive σ, LinearMap.mem_ker]
  exact functional_eq_zero_of_mem_maxGenEigenspace _ (betaGL (2 * r) σ) _ μ
    (betaGL_arithmeticHecke (2 * r) σ p₀) hμ hx

/-- **Multiplicity one in `H¹(GL₂(ℤ), Sym^{2r} ⊗ det^σ)` away from the Eisenstein eigenvalue**:
if `e p₀ ≠ q` for one `p₀ ≠ 3`, the joint generalized eigenspace of the `T_p`, `p ≠ 3`, with
eigenvalues `e` has dimension at most one. -/
theorem finrank_jointH1_le_one_of_ne (r : ℕ) (positive : 0 < r) (σ : ℤ) (e : Nat.Primes → ℂ)
    (p₀ : Nat.Primes) (hp₀ : p₀.val ≠ 3) (hne : e p₀ ≠ q (2 * r) σ p₀) :
    Module.finrank ℂ (jointH1 (2 * r) σ e) ≤ 1 :=
  finrank_jointH1_le_one r positive σ (betaGL (2 * r) σ) (ker_betaGL_eq_range_per r positive σ)
    e p₀ hp₀ (q (2 * r) σ p₀) (betaGL_arithmeticHecke (2 * r) σ p₀) hne

/-- The joint generalized eigenspaces of `H¹` are finite dimensional. -/
theorem jointH1_finiteDimensional (d : ℕ) (σ : ℤ) (e : Nat.Primes → ℂ) :
    FiniteDimensional ℂ (jointH1 d σ e) := by
  have := arithmeticH1_finiteDimensional d σ
  infer_instance

end TernaryPeriodPolynomials.LevelOneEisenstein
