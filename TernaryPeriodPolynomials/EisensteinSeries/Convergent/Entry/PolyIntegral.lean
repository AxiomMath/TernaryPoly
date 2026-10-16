module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs.Coefficients
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.ENNReal
public import Mathlib.Topology.Order.AtTopBotIxx

@[expose] public section


/-!
# Componentwise integrals of homogeneous polynomials

`HomogeneousPoly n` carries no norm in the library; its elements are determined by their coefficients on the
degree-`n` monomials (`ofCoeffs`, `eq_ofCoeffs`).  The componentwise integral `polyInt` of a family of
homogeneous polynomials, with `coeff_polyInt`, and its compatibility with linear endomorphisms
(`linear_polyInt`, e.g. the coefficient action `ρ(g)`), avoid choosing a norm.

Formalized by Claude Sonnet 5.5.
-/

open MeasureTheory MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

open GeneralEisenstein

/-- The monomials of degree `n` in three variables. -/
def degMonomials (n : ℕ) : Finset (Fin 3 →₀ ℕ) := Finset.finsuppAntidiag Finset.univ n

theorem mem_degMonomials {n : ℕ} {d : Fin 3 →₀ ℕ} : d ∈ degMonomials n ↔ d.degree = n := by
  rw [degMonomials, Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]
  simp

/-- The homogeneous polynomial of degree `n` with prescribed coefficients on the degree-`n` monomials. -/
def ofCoeffs (n : ℕ) (f : (Fin 3 →₀ ℕ) → ℂ) : HomogeneousPoly n :=
  ⟨∑ d ∈ degMonomials n, MvPolynomial.monomial d (f d), by
    rw [MvPolynomial.mem_homogeneousSubmodule]
    exact MvPolynomial.IsHomogeneous.sum _ _ _ fun d hd =>
      MvPolynomial.isHomogeneous_monomial _ (mem_degMonomials.mp hd)⟩

theorem coeff_ofCoeffs (n : ℕ) (f : (Fin 3 →₀ ℕ) → ℂ) (κ : Fin 3 →₀ ℕ) :
    ((ofCoeffs n f : HomogeneousPoly n) : Poly).coeff κ = if κ.degree = n then f κ else 0 := by
  simp only [ofCoeffs, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  by_cases h : κ.degree = n
  · rw [ite_eq_left h, Finset.sum_eq_single κ]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hκ
      exact absurd (mem_degMonomials.mpr h) hκ
  · rw [ite_eq_right h]
    refine Finset.sum_eq_zero fun d hd => ?_
    have : d ≠ κ := fun e => h (e ▸ mem_degMonomials.mp hd)
    simp [this]

theorem eq_ofCoeffs (n : ℕ) (P : HomogeneousPoly n) :
    P = ofCoeffs n (fun d => (P : Poly).coeff d) := by
  apply Subtype.ext
  ext κ
  rw [coeff_ofCoeffs]
  by_cases h : κ.degree = n
  · rw [ite_eq_left h]
  · rw [ite_eq_right h]
    exact ((MvPolynomial.mem_homogeneousSubmodule n _).mp P.2).coeff_eq_zero h

/-- The coordinate monomial. -/
def polyBasis (n : ℕ) (ν : Fin 3 →₀ ℕ) : HomogeneousPoly n := ofCoeffs n (fun d => if d = ν then 1 else 0)

theorem eq_sum_polyBasis (n : ℕ) (P : HomogeneousPoly n) :
    P = ∑ ν ∈ degMonomials n, (P : Poly).coeff ν • polyBasis n ν := by
  apply Subtype.ext
  ext κ
  simp only [Submodule.coe_sum, Submodule.coe_smul, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul,
    polyBasis, coeff_ofCoeffs, smul_eq_mul]
  by_cases h : κ.degree = n
  · rw [Finset.sum_eq_single κ]
    · simp [h]
    · intro b _ hb
      simp [h, Ne.symm hb]
    · intro hκ
      exact absurd (mem_degMonomials.mpr h) hκ
  · have : ∀ ν ∈ degMonomials n, ν ≠ κ := fun ν hν e => h (e ▸ mem_degMonomials.mp hν)
    rw [Finset.sum_eq_zero fun ν hν => by simp [Ne.symm (this ν hν)]]
    exact ((MvPolynomial.mem_homogeneousSubmodule n _).mp P.2).coeff_eq_zero h

theorem coeff_linear (n : ℕ) (Λ : HomogeneousPoly n →ₗ[ℂ] HomogeneousPoly n) (P : HomogeneousPoly n)
    (κ : Fin 3 →₀ ℕ) :
    ((Λ P : HomogeneousPoly n) : Poly).coeff κ =
      ∑ ν ∈ degMonomials n, (P : Poly).coeff ν * ((Λ (polyBasis n ν) : HomogeneousPoly n) : Poly).coeff κ := by
  conv_lhs => rw [eq_sum_polyBasis n P]
  simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_smul, smul_eq_mul]

/-- The componentwise integral of a family of homogeneous polynomials. -/
def polyInt {X : Type*} [MeasurableSpace X] (n : ℕ) (f : X → HomogeneousPoly n) (μ : Measure X) :
    HomogeneousPoly n :=
  ofCoeffs n (fun κ => ∫ x, ((f x : HomogeneousPoly n) : Poly).coeff κ ∂μ)

theorem coeff_polyInt {X : Type*} [MeasurableSpace X] (n : ℕ) (f : X → HomogeneousPoly n) (μ : Measure X)
    (κ : Fin 3 →₀ ℕ) :
    ((polyInt n f μ : HomogeneousPoly n) : Poly).coeff κ = ∫ x, ((f x : HomogeneousPoly n) : Poly).coeff κ ∂μ := by
  rw [polyInt, coeff_ofCoeffs]
  by_cases h : κ.degree = n
  · rw [ite_eq_left h]
  · rw [ite_eq_right h]
    have : ∀ x, ((f x : HomogeneousPoly n) : Poly).coeff κ = 0 := fun x =>
      ((MvPolynomial.mem_homogeneousSubmodule n _).mp (f x).2).coeff_eq_zero h
    simp [this]

theorem linear_polyInt {X : Type*} [MeasurableSpace X] (n : ℕ) (f : X → HomogeneousPoly n) (μ : Measure X)
    (hf : ∀ κ, Integrable (fun x => ((f x : HomogeneousPoly n) : Poly).coeff κ) μ)
    (Λ : HomogeneousPoly n →ₗ[ℂ] HomogeneousPoly n) (κ : Fin 3 →₀ ℕ) :
    ((Λ (polyInt n f μ) : HomogeneousPoly n) : Poly).coeff κ =
      ∫ x, ((Λ (f x) : HomogeneousPoly n) : Poly).coeff κ ∂μ := by
  rw [coeff_linear]
  simp only [coeff_polyInt, coeff_linear n Λ (f _) κ]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun ν _ => ?_
    rw [integral_mul_const]
  · intro ν _
    exact (hf ν).mul_const _

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
