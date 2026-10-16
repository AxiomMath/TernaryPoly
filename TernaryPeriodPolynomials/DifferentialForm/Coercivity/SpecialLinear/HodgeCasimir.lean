module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.ExteriorCasimir
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.Commutators

@[expose] public section


/-! The concrete mixed compact action in the algebraic Hodge operator. -/
noncomputable section
namespace TernaryPoly.SL3PolynomialCoercivity
open MvPolynomial

def coefficientLift (A : Mat) (a : TwoCoordinates) : TwoCoordinates := fun i j => infinitesimal A (a i j)

def tenCoefficientAction (k : Fin 3) (u : TenCoordinates) : TenCoordinates :=
  fun i => infinitesimal (skewFrame k) (u i)

def hodgeCross (a : TwoCoordinates) : TwoCoordinates := fun i j =>
  ∑ l : Fin 5, tangentWeight l •
    (infinitesimal (tangentFrame i * tangentFrame l - tangentFrame l * tangentFrame i) (a l j) -
      infinitesimal (tangentFrame j * tangentFrame l - tangentFrame l * tangentFrame j) (a l i))

theorem coefficientLift_alternating (A : Mat) (a : TwoCoordinates) (ha : IsAlternatingTwo a) :
    IsAlternatingTwo (coefficientLift A a) := by
  intro i j
  simp only [coefficientLift, ha i j, map_neg]

theorem hodgeCross_alternating (a : TwoCoordinates) : IsAlternatingTwo (hodgeCross a) := by
  intro i j
  simp [hodgeCross, neg_sub, ← Finset.sum_neg_distrib, ← smul_neg]

theorem coefficientLift_fromTen (k : Fin 3) (u : TenCoordinates) :
    coefficientLift (skewFrame k) (fromTen u) = fromTen (tenCoefficientAction k u) := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [coefficientLift, fromTen, tenCoefficientAction]

theorem algebraicHodgeTwo_split (a : TwoCoordinates) (i j : Fin 5) :
    algebraicHodgeTwo a i j = fullCoefficientCasimir (a i j) - compactCoefficientCasimir (a i j) +
      hodgeCross a i j := by
  simp only [algebraicHodgeTwo_expansion, fullCoefficientCasimir, add_sub_cancel_right,
    hodgeCross, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  module


theorem hodgeCross_toTen_0 (u : TenCoordinates) :
    toTen (hodgeCross (fromTen u)) 0 =
      (1/2 : ℝ) • (∑ k : Fin 3, tenCompactAction k (tenCoefficientAction k u)) 0 := by
  simp [toTen, hodgeCross, fromTen, tenCompactAction, tenCoefficientAction,
    infinitesimal_tangent_commutator, tangentWeight, tangentCommutatorCoordinates,
    Fin.sum_univ_succ]
  module

theorem hodgeCross_toTen_1 (u : TenCoordinates) :
    toTen (hodgeCross (fromTen u)) 1 =
      (1/2 : ℝ) • (∑ k : Fin 3, tenCompactAction k (tenCoefficientAction k u)) 1 := by
  simp [toTen, hodgeCross, fromTen, tenCompactAction, tenCoefficientAction,
    infinitesimal_tangent_commutator, tangentWeight, tangentCommutatorCoordinates,
    Fin.sum_univ_succ]
  module

theorem hodgeCross_toTen_2 (u : TenCoordinates) :
    toTen (hodgeCross (fromTen u)) 2 =
      (1/2 : ℝ) • (∑ k : Fin 3, tenCompactAction k (tenCoefficientAction k u)) 2 := by
  simp [toTen, hodgeCross, fromTen, tenCompactAction, tenCoefficientAction,
    infinitesimal_tangent_commutator, tangentWeight, tangentCommutatorCoordinates,
    Fin.sum_univ_succ]
  module

theorem hodgeCross_toTen_3 (u : TenCoordinates) :
    toTen (hodgeCross (fromTen u)) 3 =
      (1/2 : ℝ) • (∑ k : Fin 3, tenCompactAction k (tenCoefficientAction k u)) 3 := by
  simp [toTen, hodgeCross, fromTen, tenCompactAction, tenCoefficientAction,
    infinitesimal_tangent_commutator, tangentWeight, tangentCommutatorCoordinates,
    Fin.sum_univ_succ]
  module

theorem hodgeCross_toTen_4 (u : TenCoordinates) :
    toTen (hodgeCross (fromTen u)) 4 =
      (1/2 : ℝ) • (∑ k : Fin 3, tenCompactAction k (tenCoefficientAction k u)) 4 := by
  simp [toTen, hodgeCross, fromTen, tenCompactAction, tenCoefficientAction,
    infinitesimal_tangent_commutator, tangentWeight, tangentCommutatorCoordinates,
    Fin.sum_univ_succ]
  module

theorem hodgeCross_toTen_5 (u : TenCoordinates) :
    toTen (hodgeCross (fromTen u)) 5 =
      (1/2 : ℝ) • (∑ k : Fin 3, tenCompactAction k (tenCoefficientAction k u)) 5 := by
  simp [toTen, hodgeCross, fromTen, tenCompactAction, tenCoefficientAction,
    infinitesimal_tangent_commutator, tangentWeight, tangentCommutatorCoordinates,
    Fin.sum_univ_succ]
  module

theorem hodgeCross_toTen_6 (u : TenCoordinates) :
    toTen (hodgeCross (fromTen u)) 6 =
      (1/2 : ℝ) • (∑ k : Fin 3, tenCompactAction k (tenCoefficientAction k u)) 6 := by
  simp [toTen, hodgeCross, fromTen, tenCompactAction, tenCoefficientAction,
    infinitesimal_tangent_commutator, tangentWeight, tangentCommutatorCoordinates,
    Fin.sum_univ_succ]
  module

theorem hodgeCross_toTen_7 (u : TenCoordinates) :
    toTen (hodgeCross (fromTen u)) 7 =
      (1/2 : ℝ) • (∑ k : Fin 3, tenCompactAction k (tenCoefficientAction k u)) 7 := by
  simp [toTen, hodgeCross, fromTen, tenCompactAction, tenCoefficientAction,
    infinitesimal_tangent_commutator, tangentWeight, tangentCommutatorCoordinates,
    Fin.sum_univ_succ]
  module

theorem hodgeCross_toTen_8 (u : TenCoordinates) :
    toTen (hodgeCross (fromTen u)) 8 =
      (1/2 : ℝ) • (∑ k : Fin 3, tenCompactAction k (tenCoefficientAction k u)) 8 := by
  simp [toTen, hodgeCross, fromTen, tenCompactAction, tenCoefficientAction,
    infinitesimal_tangent_commutator, tangentWeight, tangentCommutatorCoordinates,
    Fin.sum_univ_succ]
  module

theorem hodgeCross_toTen_9 (u : TenCoordinates) :
    toTen (hodgeCross (fromTen u)) 9 =
      (1/2 : ℝ) • (∑ k : Fin 3, tenCompactAction k (tenCoefficientAction k u)) 9 := by
  simp [toTen, hodgeCross, fromTen, tenCompactAction, tenCoefficientAction,
    infinitesimal_tangent_commutator, tangentWeight, tangentCommutatorCoordinates,
    Fin.sum_univ_succ]
  module

theorem hodgeCross_toTen (u : TenCoordinates) :
    toTen (hodgeCross (fromTen u)) =
      (1/2 : ℝ) • ∑ k : Fin 3, tenCompactAction k (tenCoefficientAction k u) := by
  funext i
  fin_cases i
  · exact hodgeCross_toTen_0 u
  · exact hodgeCross_toTen_1 u
  · exact hodgeCross_toTen_2 u
  · exact hodgeCross_toTen_3 u
  · exact hodgeCross_toTen_4 u
  · exact hodgeCross_toTen_5 u
  · exact hodgeCross_toTen_6 u
  · exact hodgeCross_toTen_7 u
  · exact hodgeCross_toTen_8 u
  · exact hodgeCross_toTen_9 u

theorem tenPairing_smul_left (r : ℝ) (u v : TenCoordinates) :
    tenPairing (r • u) v = r * tenPairing u v := by
  simp [tenPairing, Finset.mul_sum, mul_left_comm]

theorem tenPairing_add_left (u v w : TenCoordinates) :
    tenPairing (u + v) w = tenPairing u w + tenPairing v w := by
  simp [tenPairing, mul_add, Finset.sum_add_distrib]

theorem tenPairing_symmetric (u v : TenCoordinates) : tenPairing u v = tenPairing v u := by
  simp only [tenPairing, factorialPairing_symmetric]

theorem toTen_coefficientLift (k : Fin 3) (a : TwoCoordinates) :
    toTen (coefficientLift (skewFrame k) a) = tenCoefficientAction k (toTen a) := by
  funext i
  fin_cases i <;> rfl

theorem hodgeCross_energy (a : TwoCoordinates) (ha : IsAlternatingTwo a) :
    twoPairing (hodgeCross a) a = -(1/2 : ℝ) * ∑ k : Fin 3,
      twoPairing (coefficientLift (skewFrame k) a) (compactExteriorAction k a) := by
  rw [← fromTen_toTen a ha]
  rw [twoPairing_toTen _ _ (hodgeCross_alternating _) (fromTen_alternating _),
    hodgeCross_toTen, toTen_fromTen, tenPairing_smul_left]
  simp only [Fin.sum_univ_succ, tenPairing_add_left, tenCompactAction_skew_adjoint,
    coefficientLift_fromTen, ← fromTen_tenCompactAction, twoPairing_fromTen]
  have hz : tenPairing 0 (toTen a) = 0 := by simp [tenPairing]
  simp only [Fin.sum_univ_zero, hz]
  ring

theorem twoPairing_smul_left (r : ℝ) (a b : TwoCoordinates) :
    twoPairing (r • a) b = r * twoPairing a b := by
  simp [twoPairing, Finset.mul_sum, mul_left_comm]

theorem twoPairing_sub_left (a b c : TwoCoordinates) :
    twoPairing (a-b) c = twoPairing a c - twoPairing b c := by
  simp [twoPairing, mul_sub, Finset.sum_sub_distrib]

theorem twoPairing_sum_left {ι : Type*} [Fintype ι] (f : ι → TwoCoordinates)
    (a : TwoCoordinates) : twoPairing (∑ i, f i) a = ∑ i, twoPairing (f i) a := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp [twoPairing]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, twoPairing_add_left, ih]

end TernaryPoly.SL3PolynomialCoercivity
