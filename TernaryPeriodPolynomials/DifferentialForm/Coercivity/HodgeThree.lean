module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.HodgeFour

@[expose] public section



/-! Degree-three algebraic Hodge operator and its energy identity, mirroring
`algebraicHodgeTwo`/`algebraicHodgeTwo_energy`/`algebraicHodgeTwo_nonneg`
(`TernaryPoly.SL3PolynomialCoercivityHodge`/`...HodgeMetric`) one degree up. Built purely from the
two already-proven adjoint pairs `exteriorTwo`/`contractionThree` (original authors) and
`exteriorThree`/`contractionFour` (mine, `HodgeFour.lean`). This isolates the remaining hard
analytic gap for clause `k = 2`'s piece B to exactly one fact: `algebraicHodgeThree`'s own
coercivity (all `n > 0`), the degree-three analogue of `homogeneousHodgeTwo_coercive`
(`TernaryPoly.SL3PolynomialCoercivityPositive`). -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity

/-- `exteriorThree` carries `IsAlternatingThree` to `IsAlternatingFour`, mirroring
`exteriorTwo_alternating` one degree up. -/
theorem exteriorThree_alternating (a : ThreeCoordinates) (ha : IsAlternatingThree a) :
    IsAlternatingFour (exteriorThree a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j k l
    have h1 : a j i l = -a i j l := by rw [ha.1 i j l]; ring
    have h2 : a j i k = -a i j k := by rw [ha.1 i j k]; ring
    simp only [exteriorThree, h1, h2, map_neg]
    abel
  · intro i j k l
    have h1 : a j k l = -a k j l := by rw [ha.1 k j l]; ring
    have h2 : a i k l = -a k i l := by rw [ha.1 k i l]; ring
    have h3 : a i j k = a k i j := ha.2 i j k
    simp only [exteriorThree, h1, h2, h3, map_neg]
    abel
  · intro i j k l
    have h1 : a j k l = a l j k := ha.2 j k l
    have h2 : a i k l = a l i k := ha.2 i k l
    have h3 : a i j l = a l i j := ha.2 i j l
    simp only [exteriorThree, h1, h2, h3]
    abel

theorem threePairing_symmetric (a b : ThreeCoordinates) : threePairing a b = threePairing b a := by
  simp only [threePairing, factorialPairing_symmetric]

theorem threePairing_add_left (a b c : ThreeCoordinates) :
    threePairing (a + b) c = threePairing a c + threePairing b c := by
  simp [threePairing, mul_add, Finset.sum_add_distrib]

theorem fourPairing_add_left (a b c : FourCoordinates) :
    fourPairing (a + b) c = fourPairing a c + fourPairing b c := by
  simp [fourPairing, mul_add, Finset.sum_add_distrib]

theorem fourPairing_self_nonneg (a : FourCoordinates) : 0 ≤ fourPairing a a := by
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 24)
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
    Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun l _ =>
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (tangentWeight_pos i).le
        (tangentWeight_pos j).le) (tangentWeight_pos k).le) (tangentWeight_pos l).le)
        (factorialPairing_self_nonneg (a i j k l))))))

/-- `T T* + T* T` in exterior degree three, mirroring `algebraicHodgeTwo` one degree up. -/
def algebraicHodgeThree (a : ThreeCoordinates) : ThreeCoordinates :=
  exteriorTwo (contractionThree a) + contractionFour (exteriorThree a)

/-- The algebraic Hodge energy at degree three includes both adjacent exterior degrees,
mirroring `algebraicHodgeTwo_energy` one degree up. -/
theorem algebraicHodgeThree_energy (a : ThreeCoordinates) (ha : IsAlternatingThree a) :
    threePairing (algebraicHodgeThree a) a =
      twoPairing (contractionThree a) (contractionThree a) +
        fourPairing (exteriorThree a) (exteriorThree a) := by
  rw [algebraicHodgeThree, threePairing_add_left,
    exteriorTwo_contractionThree_adjoint _ _ ha, threePairing_symmetric]
  rw [← exteriorThree_contractionFour_adjoint _ _ (exteriorThree_alternating a ha)]

theorem algebraicHodgeThree_nonneg (a : ThreeCoordinates) (ha : IsAlternatingThree a) :
    0 ≤ threePairing (algebraicHodgeThree a) a := by
  rw [algebraicHodgeThree_energy a ha]
  exact add_nonneg (twoPairing_self_nonneg _) (fourPairing_self_nonneg _)

end TernaryPeriodPolynomials.Argument.Coercivity
