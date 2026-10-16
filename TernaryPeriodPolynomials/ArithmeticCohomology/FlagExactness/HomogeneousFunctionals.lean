module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section


/-!
# Functionals on homogeneous polynomials are finite coefficient combinations

For a finite variable type `σ` and degree `n`, every complex linear functional on the
homogeneous polynomials of degree `n` is a finite linear combination of coefficient
functionals. This makes continuity and integrals of functionals of
polynomial-valued families reduce to their coefficients.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

namespace TernaryPeriodPolynomials.FlagExactness

variable {σ : Type} [Fintype σ] [DecidableEq σ]

/-- All exponent vectors of total degree `n`. -/
def degreeExponents (σ : Type) [Fintype σ] [DecidableEq σ] (n : ℕ) : Finset (σ →₀ ℕ) :=
  ((Finset.univ : Finset (σ → Fin (n + 1))).image
    (fun f => Finsupp.equivFunOnFinite.symm (fun i => (f i : ℕ)))).filter (fun d => d.degree = n)

theorem mem_degreeExponents {n : ℕ} {d : σ →₀ ℕ} (h : d.degree = n) : d ∈ degreeExponents σ n := by
  simp only [degreeExponents, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  refine ⟨⟨fun i => ⟨d i, ?_⟩, ?_⟩, h⟩
  · have hle : d i ≤ d.degree := by
      rw [Finsupp.degree_eq_sum]
      exact Finset.single_le_sum (fun j _ => Nat.zero_le (d j)) (Finset.mem_univ i)
    omega
  · ext i
    simp

/-- The coefficient vector of a homogeneous polynomial. -/
def homogeneousCoefficients (n : ℕ) :
    MvPolynomial.homogeneousSubmodule σ ℂ n →ₗ[ℂ] (degreeExponents σ n → ℂ) where
  toFun p := fun s => p.val.coeff s.val
  map_add' p q := by
    funext s
    simp
  map_smul' a p := by
    funext s
    simp

theorem homogeneousCoefficients_injective (n : ℕ) :
    Function.Injective (homogeneousCoefficients (σ := σ) n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro p hp
  apply Subtype.ext
  apply MvPolynomial.ext
  intro d
  have homogeneous : p.val.IsHomogeneous n := (MvPolynomial.mem_homogeneousSubmodule n p.val).mp p.property
  by_cases hd : d.degree = n
  · exact congrFun hp ⟨d, mem_degreeExponents hd⟩
  · rw [homogeneous.coeff_eq_zero hd]
    rfl

/-- Every functional is a finite combination of coefficients. -/
theorem homogeneous_functional_eq_sum (n : ℕ)
    (functional : MvPolynomial.homogeneousSubmodule σ ℂ n →ₗ[ℂ] ℂ) :
    ∃ weight : degreeExponents σ n → ℂ, ∀ p,
      functional p = ∑ s, p.val.coeff s.val * weight s := by
  obtain ⟨inverse, hinverse⟩ := LinearMap.exists_leftInverse_of_injective
    (homogeneousCoefficients (σ := σ) n)
    (LinearMap.ker_eq_bot.mpr (homogeneousCoefficients_injective n))
  refine ⟨fun s => (functional.comp inverse) (fun j => if s = j then 1 else 0), fun p => ?_⟩
  have hp : functional p = (functional.comp inverse) (homogeneousCoefficients n p) := by
    rw [LinearMap.comp_apply, ← LinearMap.comp_apply inverse, hinverse, LinearMap.id_apply]
  rw [hp, LinearMap.pi_apply_eq_sum_univ]
  rfl

end TernaryPeriodPolynomials.FlagExactness
