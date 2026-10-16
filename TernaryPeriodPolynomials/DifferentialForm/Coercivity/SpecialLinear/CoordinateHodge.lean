module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.LowDegreeAction

@[expose] public section


/-! Coordinate transport for the actual Hodge operator. -/
noncomputable section
namespace TernaryPoly.SL3PolynomialCoercivity
open MvPolynomial

theorem coordinatePolynomial_add {ι : Type*} [Fintype ι] (e : ι → Exponent)
    (x y : ι → ℝ) : coordinatePolynomial e (x+y) = coordinatePolynomial e x + coordinatePolynomial e y := by
  simp [coordinatePolynomial, add_smul, Finset.sum_add_distrib]

theorem coordinatePolynomial_smul {ι : Type*} [Fintype ι] (e : ι → Exponent)
    (r : ℝ) (x : ι → ℝ) : coordinatePolynomial e (r • x) = r • coordinatePolynomial e x := by
  simp [coordinatePolynomial, Finset.smul_sum, smul_smul]

theorem coordinatePolynomial_homogeneous {ι : Type*} [Fintype ι] (e : ι → Exponent)
    {n : ℕ} (he : ∀ i, (e i).degree = n) (x : ι → ℝ) :
    (coordinatePolynomial e x).IsHomogeneous n := by
  unfold coordinatePolynomial
  apply IsHomogeneous.sum
  intro i hi
  exact (homogeneousSubmodule (Fin 3) ℝ n).smul_mem (x i) (isHomogeneous_monomial 1 (he i))

theorem lowExponent1_degree (i : Fin 3) : (lowExponent1 i).degree = 1 := by
  fin_cases i <;> simp [lowExponent1, tripleExponent]

theorem lowExponent2_degree (i : Fin 6) : (lowExponent2 i).degree = 2 := by
  fin_cases i <;> simp [lowExponent2, tripleExponent]

theorem lowExponent3_degree (i : Fin 10) : (lowExponent3 i).degree = 3 := by
  fin_cases i <;> simp [lowExponent3, tripleExponent]

theorem toTen_add (a b : TwoCoordinates) : toTen (a+b) = toTen a + toTen b := by
  funext i
  fin_cases i <;> rfl

theorem toTen_map (f : Poly → Poly) (a : TwoCoordinates) :
    toTen (fun i j => f (a i j)) = fun i => f (toTen a i) := by
  funext i
  fin_cases i <;> rfl

def tenHodgeAction (n : ℕ) (u : TenCoordinates) : TenCoordinates :=
  (2 * (n : ℝ) * (n+3) / 3) • u +
    (1/2 : ℝ) • (∑ k : Fin 3, tenCoefficientAction k (tenCoefficientAction k u)) +
    (1/2 : ℝ) • (∑ k : Fin 3, tenCompactAction k (tenCoefficientAction k u))

theorem toTen_algebraicHodgeTwo {n : ℕ} (u : TenCoordinates)
    (hu : ∀ i, (u i).IsHomogeneous n) :
    toTen (algebraicHodgeTwo (fromTen u)) = tenHodgeAction n u := by
  have hs : algebraicHodgeTwo (fromTen u) =
      (fun i j => fullCoefficientCasimir (fromTen u i j) - compactCoefficientCasimir (fromTen u i j)) +
        hodgeCross (fromTen u) := by
    funext i j
    exact algebraicHodgeTwo_split _ i j
  rw [hs, toTen_add, toTen_map (fun p => fullCoefficientCasimir p - compactCoefficientCasimir p) (fromTen u), toTen_fromTen, hodgeCross_toTen]
  funext i
  simp only [Pi.add_apply, fullCoefficientCasimir_homogeneous (hu i),
    compactCoefficientCasimir_eq_sum, tenHodgeAction, Pi.smul_apply, Finset.sum_apply,
    tenCoefficientAction]
  module

end TernaryPoly.SL3PolynomialCoercivity
