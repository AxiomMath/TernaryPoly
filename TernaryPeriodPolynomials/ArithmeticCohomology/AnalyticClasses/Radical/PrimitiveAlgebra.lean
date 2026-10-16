module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Radical.PrimitiveInterface

@[expose] public section


/-!
# The infinitesimal coboundaries of the real lower radical

The pairs `(D₀ B, D₁ A)` with `Dᵢ v = -Xᵢ ∂₂ v` produce, through `D₀ B - D₁ A`, every homogeneous
polynomial whose `X₂ⁿ`-coefficient vanishes: such a polynomial is `X₀ P + X₁ Q`, and `P`, `Q`
are `∂₂`-derivatives of homogeneous polynomials of degree `n`, obtained by integrating in `X₂`
monomial by monomial.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic MvPolynomial

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

/-- The Lie-algebra coboundary `(A, B) ↦ D₀ B - D₁ A` of the real lower radical. -/
def lieBoundary (n : ℕ) : HomogeneousPoly n × HomogeneousPoly n →ₗ[ℂ] HomogeneousPoly n :=
  lowerShear n 0 ∘ₗ LinearMap.snd ℂ _ _ - lowerShear n 1 ∘ₗ LinearMap.fst ℂ _ _

theorem lieBoundary_apply (A B : HomogeneousPoly n) :
    lieBoundary n (A, B) = lowerShear n 0 B - lowerShear n 1 A := rfl

/-- Multiplying the `X₂`-integral of a monomial by `Xᵢ` and differentiating in `X₂`. -/
theorem X_mul_pderiv_integral {i : Fin 3} (hi : i ≠ 2) {α : Fin 3 →₀ ℕ} (hα : 1 ≤ α i)
    (c : ℂ) :
    X i * pderiv 2 (monomial (α - Finsupp.single i 1 + Finsupp.single 2 1)
      (c / ((α 2 : ℂ) + 1))) = monomial α c := by
  rw [pderiv_monomial]
  have h2 : (α - Finsupp.single i 1 + Finsupp.single 2 1 : Fin 3 →₀ ℕ) 2 = α 2 + 1 := by
    simp [hi]
  have hsub : α - Finsupp.single i 1 + Finsupp.single 2 1 - Finsupp.single 2 1 =
      α - Finsupp.single i 1 := add_tsub_cancel_right _ _
  have hle : Finsupp.single i 1 ≤ α := by
    rw [Finsupp.single_le_iff]
    exact hα
  rw [h2, hsub, X, monomial_mul_monomial, one_mul, add_tsub_cancel_of_le hle]
  congr 1
  push_cast
  field_simp

theorem degree_integral {i : Fin 3} {α : Fin 3 →₀ ℕ} (hα : 1 ≤ α i) :
    (α - Finsupp.single i 1 + Finsupp.single 2 1).degree = α.degree := by
  have hle : Finsupp.single i 1 ≤ α := by
    rw [Finsupp.single_le_iff]
    exact hα
  have split : α.degree = (α - Finsupp.single i 1).degree + 1 := by
    conv_lhs => rw [← tsub_add_cancel_of_le hle]
    rw [map_add, Finsupp.degree_single]
  rw [map_add, Finsupp.degree_single, split]

/-- The image of the infinitesimal coboundaries in the polynomial ring. -/
def lieBoundaryImage (n : ℕ) : Submodule ℂ (MvPolynomial (Fin 3) ℂ) :=
  (LinearMap.range (lieBoundary n)).map (HomogeneousPoly n).subtype

theorem shear_zero_mem {α : Fin 3 →₀ ℕ} (hdeg : α.degree = n) (h0 : 1 ≤ α 0) (c : ℂ) :
    monomial α c ∈ lieBoundaryImage n := by
  set B : HomogeneousPoly n := ⟨monomial (α - Finsupp.single 0 1 + Finsupp.single 2 1)
    (-c / ((α 2 : ℂ) + 1)), (mem_homogeneousSubmodule n _).mpr (isHomogeneous_monomial _
      ((degree_integral h0).trans hdeg))⟩
  refine ⟨lieBoundary n (0, B), ⟨(0, B), rfl⟩, ?_⟩
  have value : ((lowerShear n 0 B : HomogeneousPoly n) : MvPolynomial (Fin 3) ℂ) =
      monomial α c := by
    have key := X_mul_pderiv_integral (i := 0) (by decide) h0 (-c)
    rw [lowerShear_val, Fin.castSucc_zero]
    change -(X 0 * pderiv 2 (monomial (α - Finsupp.single 0 1 + Finsupp.single 2 1)
      (-c / ((α 2 : ℂ) + 1)))) = _
    rw [key, map_neg, neg_neg]
  rw [lieBoundary_apply, map_zero, sub_zero]
  exact value

theorem shear_one_mem {α : Fin 3 →₀ ℕ} (hdeg : α.degree = n) (h1 : 1 ≤ α 1) (c : ℂ) :
    monomial α c ∈ lieBoundaryImage n := by
  set A : HomogeneousPoly n := ⟨monomial (α - Finsupp.single 1 1 + Finsupp.single 2 1)
    (c / ((α 2 : ℂ) + 1)), (mem_homogeneousSubmodule n _).mpr (isHomogeneous_monomial _
      ((degree_integral h1).trans hdeg))⟩
  refine ⟨lieBoundary n (A, 0), ⟨(A, 0), rfl⟩, ?_⟩
  have value : ((lowerShear n 1 A : HomogeneousPoly n) : MvPolynomial (Fin 3) ℂ) =
      -monomial α c := by
    rw [lowerShear_val, Fin.castSucc_one]
    exact congrArg Neg.neg (X_mul_pderiv_integral (by decide) h1 c)
  rw [lieBoundary_apply, map_zero, zero_sub]
  change -((lowerShear n 1 A : HomogeneousPoly n) : MvPolynomial (Fin 3) ℂ) = _
  rw [value, neg_neg]

/-- A homogeneous monomial other than `X₂ⁿ` is an infinitesimal coboundary. -/
theorem monomial_mem_lieBoundaryImage {α : Fin 3 →₀ ℕ} (hdeg : α.degree = n)
    (hne : α ≠ Finsupp.single 2 n) (c : ℂ) : monomial α c ∈ lieBoundaryImage n := by
  by_cases h0 : 1 ≤ α 0
  · exact shear_zero_mem hdeg h0 c
  by_cases h1 : 1 ≤ α 1
  · exact shear_one_mem hdeg h1 c
  exfalso
  apply hne
  have a0 : α 0 = 0 := by omega
  have a1 : α 1 = 0 := by omega
  have a2 : α 2 = n := by
    rw [← hdeg, Finsupp.degree_eq_sum, Fin.sum_univ_three, a0, a1]
    simp
  ext k
  fin_cases k <;> simp [a0, a1, a2]

/-- **The infinitesimal coboundaries of the real lower radical are the kernel of the
coinvariant functional.** -/
theorem exists_lieBoundary_eq (ω : HomogeneousPoly n) (hω : topCoefficient n ω = 0) :
    ∃ p : HomogeneousPoly n × HomogeneousPoly n, lieBoundary n p = ω := by
  have homogeneous : ω.val.IsHomogeneous n := (mem_homogeneousSubmodule n _).mp ω.property
  have mem : ω.val ∈ lieBoundaryImage n := by
    rw [ω.val.as_sum]
    refine Submodule.sum_mem _ fun α hα => ?_
    have hdeg : α.degree = n := by
      rw [Finsupp.degree_eq_weight_one]
      exact homogeneous (mem_support_iff.mp hα)
    refine monomial_mem_lieBoundaryImage hdeg ?_ _
    rintro rfl
    exact mem_support_iff.mp hα hω
  obtain ⟨v, ⟨p, rfl⟩, hv⟩ := mem
  exact ⟨p, Subtype.ext hv⟩

end TernaryPeriodPolynomials.AnalyticClasses
