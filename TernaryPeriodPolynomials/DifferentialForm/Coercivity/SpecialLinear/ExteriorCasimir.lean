module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.CoefficientCasimir
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.ExteriorCoordinates

@[expose] public section

/-! Concrete compact coadjoint action and its exterior Casimir upper bound. -/
noncomputable section
namespace TernaryPoly.SL3PolynomialCoercivity

def compactTangentCoefficient (k : Fin 3) (i j : Fin 5) : ℝ :=
  tangentWeight j * Matrix.trace (tangentFrame j *
    (skewFrame k * tangentFrame i - tangentFrame i * skewFrame k))

def compactTangentMatrix : Fin 3 → Matrix (Fin 5) (Fin 5) ℝ := ![
  !![0, 0, -2, 0, 0; 0, 0, 0, 0, 0; 2, 0, 0, 0, 0; 0, 0, 0, 0, -1; 0, 0, 0, 1, 0],
  !![0, 0, 0, -1, 0; 0, 0, 0, -3, 0; 0, 0, 0, 0, -1; 1, 1, 0, 0, 0; 0, 0, 1, 0, 0],
  !![0, 0, 0, 0, 1; 0, 0, 0, 0, -3; 0, 0, 0, -1, 0; 0, 0, 1, 0, 0; -1, 1, 0, 0, 0]]

theorem compactTangentCoefficient_eq (k : Fin 3) (i j : Fin 5) :
    compactTangentCoefficient k i j = compactTangentMatrix k i j := by
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [compactTangentCoefficient, compactTangentMatrix, tangentWeight,
      tangentFrame, skewFrame, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The actual coadjoint action on both exterior slots. -/
def compactExteriorAction (k : Fin 3) (a : TwoCoordinates) : TwoCoordinates := fun i j =>
  -(∑ l : Fin 5, compactTangentCoefficient k i l • a l j) -
    ∑ l : Fin 5, compactTangentCoefficient k j l • a i l

def tenCompactAction (k : Fin 3) (u : TenCoordinates) : TenCoordinates := ![
  ![(-2 : ℝ) • u 4,
    0,
    u 3 + (2 : ℝ) • u 7,
    (-u 2) + (2 : ℝ) • u 8,
    (2 : ℝ) • u 0,
    u 6,
    (-u 5),
    (-2 : ℝ) • u 2 + u 8,
    (-2 : ℝ) • u 3 + (-u 7),
    0],
  ![(3 : ℝ) • u 2 + (-u 5),
    u 3 + (-u 7),
    (-u 0),
    (-u 1) + u 9,
    u 6 + (-3 : ℝ) • u 7,
    u 0,
    (-u 4) + (3 : ℝ) • u 9,
    u 1 + u 4 + (-u 9),
    0,
    (-u 3) + (-u 6) + u 7],
  ![(3 : ℝ) • u 3 + u 6,
    u 2 + u 8,
    (-u 1) + u 9,
    (-u 0),
    u 5 + (-3 : ℝ) • u 8,
    (-u 4) + (-3 : ℝ) • u 9,
    (-u 0),
    0,
    (-u 1) + u 4 + u 9,
    (-u 2) + u 5 + (-u 8)]] k

theorem compactExteriorAction_alternating (k : Fin 3) (a : TwoCoordinates)
    (ha : IsAlternatingTwo a) : IsAlternatingTwo (compactExteriorAction k a) := by
  intro i j
  have h1 : (∑ l : Fin 5, compactTangentCoefficient k j l • a l i) =
      -(∑ l : Fin 5, compactTangentCoefficient k j l • a i l) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    rw [ha l i, smul_neg]
  have h2 : (∑ l : Fin 5, compactTangentCoefficient k i l • a j l) =
      -(∑ l : Fin 5, compactTangentCoefficient k i l • a l j) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    rw [ha j l, smul_neg]
  simp only [compactExteriorAction]
  conv_rhs => rw [h1, h2]
  abel

theorem compactExteriorAction_toTen_0 (u : TenCoordinates) :
    toTen (compactExteriorAction 0 (fromTen u)) = tenCompactAction 0 u := by
  funext i
  fin_cases i <;>
    simp [toTen, compactExteriorAction, compactTangentCoefficient_eq, compactTangentMatrix,
      fromTen, tenCompactAction, Fin.sum_univ_succ] <;> module


theorem compactExteriorAction_toTen_1 (u : TenCoordinates) :
    toTen (compactExteriorAction 1 (fromTen u)) = tenCompactAction 1 u := by
  funext i
  fin_cases i <;>
    simp [toTen, compactExteriorAction, compactTangentCoefficient_eq, compactTangentMatrix,
      fromTen, tenCompactAction, Fin.sum_univ_succ] <;> module


theorem compactExteriorAction_toTen_2 (u : TenCoordinates) :
    toTen (compactExteriorAction 2 (fromTen u)) = tenCompactAction 2 u := by
  funext i
  fin_cases i <;>
    simp [toTen, compactExteriorAction, compactTangentCoefficient_eq, compactTangentMatrix,
      fromTen, tenCompactAction, Fin.sum_univ_succ] <;> module

theorem compactExteriorAction_toTen (k : Fin 3) (u : TenCoordinates) :
    toTen (compactExteriorAction k (fromTen u)) = tenCompactAction k u := by
  fin_cases k
  · exact compactExteriorAction_toTen_0 u
  · exact compactExteriorAction_toTen_1 u
  · exact compactExteriorAction_toTen_2 u

theorem fromTen_tenCompactAction (k : Fin 3) (u : TenCoordinates) :
    fromTen (tenCompactAction k u) = compactExteriorAction k (fromTen u) := by
  rw [← compactExteriorAction_toTen, fromTen_toTen _
    (compactExteriorAction_alternating k _ (fromTen_alternating u))]

theorem tenCompactAction_skew_adjoint (k : Fin 3) (u v : TenCoordinates) :
    tenPairing (tenCompactAction k u) v = -tenPairing u (tenCompactAction k v) := by
  fin_cases k <;>
    simp [tenPairing, tenWeight, tenCompactAction, Fin.sum_univ_succ] <;> ring

theorem compactExteriorAction_skew_adjoint (k : Fin 3) (a b : TwoCoordinates)
    (ha : IsAlternatingTwo a) (hb : IsAlternatingTwo b) :
    twoPairing (compactExteriorAction k a) b = -twoPairing a (compactExteriorAction k b) := by
  rw [← fromTen_toTen a ha, ← fromTen_toTen b hb, ← fromTen_tenCompactAction,
    ← fromTen_tenCompactAction, twoPairing_fromTen, twoPairing_fromTen]
  exact tenCompactAction_skew_adjoint k _ _

def tenCompactEnergy (u : TenCoordinates) : ℝ :=
  (1/2 : ℝ) * ∑ k : Fin 3, tenPairing (tenCompactAction k u) (tenCompactAction k u)

def exteriorGapForms (u : TenCoordinates) : Fin 3 → Poly := ![
  u 1 + (1/2 : ℝ) • u 9,
  u 2 + u 5 + u 8,
  u 3 - u 6 - u 7]

/-- Explicit three-square certificate for the exterior compact Casimir upper bound. -/
theorem tenCompactEnergy_gap (u : TenCoordinates) :
    6 * tenPairing u u - tenCompactEnergy u =
      factorialPairing (exteriorGapForms u 0) (exteriorGapForms u 0) +
      (1/4 : ℝ) * factorialPairing (exteriorGapForms u 1) (exteriorGapForms u 1) +
      (1/4 : ℝ) * factorialPairing (exteriorGapForms u 2) (exteriorGapForms u 2) := by
  simp [tenPairing, tenWeight, tenCompactAction, tenCompactEnergy, exteriorGapForms,
    Fin.sum_univ_succ]
  simp only [factorialPairing_symmetric]
  ring

theorem tenCompactEnergy_upper (u : TenCoordinates) : tenCompactEnergy u ≤ 6 * tenPairing u u := by
  have h := tenCompactEnergy_gap u
  have h0 := factorialPairing_self_nonneg (exteriorGapForms u 0)
  have h1 := factorialPairing_self_nonneg (exteriorGapForms u 1)
  have h2 := factorialPairing_self_nonneg (exteriorGapForms u 2)
  linarith

theorem compactExteriorAction_energy_upper (a : TwoCoordinates) (ha : IsAlternatingTwo a) :
    (∑ k : Fin 3, twoPairing (compactExteriorAction k a) (compactExteriorAction k a)) ≤
      12 * twoPairing a a := by
  have h := tenCompactEnergy_upper (toTen a)
  rw [← fromTen_toTen a ha]
  simp_rw [← fromTen_tenCompactAction, twoPairing_fromTen]
  unfold tenCompactEnergy at h
  linarith

end TernaryPoly.SL3PolynomialCoercivity
