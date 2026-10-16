module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.Basic

@[expose] public section


/-! Ten independent exterior coordinates for the five-dimensional tangent frame. -/
noncomputable section
namespace TernaryPoly.SL3PolynomialCoercivity

abbrev TenCoordinates := Fin 10 → Poly

def toTen (a : TwoCoordinates) : TenCoordinates :=
  ![a 0 1, a 0 2, a 0 3, a 0 4, a 1 2, a 1 3, a 1 4, a 2 3, a 2 4, a 3 4]

def fromTen (u : TenCoordinates) : TwoCoordinates := ![
  ![0, u 0, u 1, u 2, u 3],
  ![-u 0, 0, u 4, u 5, u 6],
  ![-u 1, -u 4, 0, u 7, u 8],
  ![-u 2, -u 5, -u 7, 0, u 9],
  ![-u 3, -u 6, -u 8, -u 9, 0]]

theorem alternatingTwo_diagonal (a : TwoCoordinates) (ha : IsAlternatingTwo a) (i : Fin 5) :
    a i i = 0 := by
  have h : (2 : ℝ) • a i i = 0 := by
    simpa only [two_smul] using (eq_neg_iff_add_eq_zero.mp (ha i i))
  exact (smul_eq_zero.mp h).resolve_left (by norm_num)

theorem fromTen_alternating (u : TenCoordinates) : IsAlternatingTwo (fromTen u) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [fromTen]

@[simp] theorem toTen_fromTen (u : TenCoordinates) : toTen (fromTen u) = u := by
  funext i
  fin_cases i <;> rfl

theorem fromTen_toTen (a : TwoCoordinates) (ha : IsAlternatingTwo a) : fromTen (toTen a) = a := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [fromTen, toTen, alternatingTwo_diagonal a ha,
      ha 1 0, ha 2 0, ha 3 0, ha 4 0, ha 2 1, ha 3 1, ha 4 1, ha 3 2, ha 4 2, ha 4 3]

def tenWeight : Fin 10 → ℝ := ![1/12, 1/4, 1/4, 1/4, 1/12, 1/12, 1/12, 1/4, 1/4, 1/4]

def tenPairing (u v : TenCoordinates) : ℝ :=
  ∑ i : Fin 10, tenWeight i * factorialPairing (u i) (v i)

theorem twoPairing_fromTen (u v : TenCoordinates) :
    twoPairing (fromTen u) (fromTen v) = tenPairing u v := by
  simp [twoPairing, tenPairing, tenWeight, tangentWeight, fromTen, Fin.sum_univ_succ]
  ring

theorem twoPairing_toTen (a b : TwoCoordinates) (ha : IsAlternatingTwo a)
    (hb : IsAlternatingTwo b) : twoPairing a b = tenPairing (toTen a) (toTen b) := by
  rw [← twoPairing_fromTen, fromTen_toTen a ha, fromTen_toTen b hb]

end TernaryPoly.SL3PolynomialCoercivity
