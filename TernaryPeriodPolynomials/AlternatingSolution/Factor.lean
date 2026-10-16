module

public import TernaryPeriodPolynomials.AlternatingSolution.NormalDescent
public import TernaryPeriodPolynomials.PeriodPolynomial.Lift.Factors
public import TernaryPeriodPolynomials.AlternatingSolution.FactorQuotient

@[expose] public section

open MvPolynomial
noncomputable section
namespace TernaryPoly

/-- Every odd alternating differential Todd-kernel element has the full nine-plane factor. -/
theorem binaryLiftNineFactor_dvd_of_todd_derivative {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hc : C f = f) (hs : S f = -f)
    (hJ : pderiv 0 (alternatingTodd f) = 0) : binaryLiftNineFactor ∣ f := by
  apply alternating_normal_induction (fun p => binaryLiftNineFactor ∣ p) (dvd_zero _) ?_ ?_
    hf hodd hc hs hJ
  · intro q hq l hl
    exact binaryLiftNineFactor_dvd_quotient hq l hl
  · intro l g hl hg
    exact dvd_add hl (dvd_mul_of_dvd_right hg _)

/-- The actual norm forces both whole Todd vanishing and the full nine-plane divisor. -/
theorem alternating_norm_todd_and_factor {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hc : C f = f) (hs : S f = -f)
    (hn : N f = 0) : alternatingTodd f = 0 ∧ binaryLiftNineFactor ∣ f :=
  ⟨alternatingTodd_eq_zero hf hodd hc hs hn,
    binaryLiftNineFactor_dvd_of_todd_derivative hf hodd hc hs
      (pderiv_zero_alternatingTodd hc hs hn)⟩

/-- The actual odd alternating norm solution has a symmetric even-degree factor and whole Todd zero. -/
theorem alternating_norm_factorization {f : TernaryPolynomial} {n : ℕ}
    (hf : f.IsHomogeneous n) (hodd : Odd n) (hc : C f = f) (hs : S f = -f)
    (hn : N f = 0) :
    alternatingTodd f = 0 ∧ ∃ (m : ℕ) (H : TernaryPolynomial),
      f = binaryLiftNineFactor*H ∧ H.IsHomogeneous (2*m) ∧ C H = H ∧ S H = H := by
  obtain ⟨hj, hd⟩ := alternating_norm_todd_and_factor hf hodd hc hs hn
  exact ⟨hj, alternating_factor_symmetric_even_quotient hf hodd hc hs hd⟩

end TernaryPoly
