module

public import TernaryPeriodPolynomials.ModularForm.HeckeEndomorphism.Basic
public import TernaryPeriodPolynomials.ModularForm.Hecke.CommuteCoefficients

@[expose] public section


noncomputable section
open UpperHalfPlane Complex
open scoped MatrixGroups
namespace TernaryPoly.BinaryCuspHeckeEndomorphism
open BinaryCuspPeriod BinaryCuspHecke

/-- Actual convergent q-expansions detect full-level cusp forms. -/
theorem coefficients_injective (d : ℕ) : Function.Injective (coefficients (d := d)) := by
  intro f g h
  apply DFunLike.ext
  intro z
  apply (hasSum_coefficients f z).unique
  simpa only [h] using hasSum_coefficients g z

/-- The Fourier coefficients of the genuine cusp endomorphism are exactly the proved transformed sequence. -/
theorem coefficients_T (d p : ℕ) [Fact p.Prime] (f : Forms d) (n : ℕ) :
    coefficients (T d p f) n = transformedCoefficients f p n := by
  have hperiod : (1 : ℝ) ∈ (𝒮ℒ).strictPeriods := by simp
  have he := ModularFormClass.qExpansion_coeff_unique (f := T d p f) (by norm_num : (0 : ℝ) < 1)
    hperiod (c := transformedCoefficients f p) (fun z => by
      simpa only [T_apply,smul_eq_mul,q] using hasSum_primeOperator f p (Fact.out : p.Prime).pos z) n
  exact he.symm

/-- Function-valued coefficient identity for composing actual cusp endomorphisms. -/
theorem coefficients_T_function (d p : ℕ) [Fact p.Prime] (f : Forms d) :
    coefficients (T d p f) = coefficientOperator d p (coefficients f) := by
  funext n
  exact coefficients_T d p f n

end TernaryPoly.BinaryCuspHeckeEndomorphism
