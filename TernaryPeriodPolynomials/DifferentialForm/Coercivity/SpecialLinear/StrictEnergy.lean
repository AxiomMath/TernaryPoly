module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.Compactness

@[expose] public section

/-! Strict Hodge energy follows from injectivity of the actual algebraic operator. -/
noncomputable section
namespace TernaryPoly.SL3PolynomialCoercivity

theorem onePairing_self_eq_zero (a : OneCoordinates) : onePairing a a = 0 ↔ a = 0 := by
  constructor
  · intro ha
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) =>
      mul_nonneg (tangentWeight_pos i).le (factorialPairing_self_nonneg (a i)))).mp ha
    funext i
    exact (factorialPairing_self_eq_zero _).mp ((mul_eq_zero.mp (hz i (Finset.mem_univ i))).resolve_left
      (ne_of_gt (tangentWeight_pos i)))
  · rintro rfl
    simp [onePairing]

theorem threePairing_self_eq_zero (a : ThreeCoordinates) : threePairing a a = 0 ↔ a = 0 := by
  constructor
  · intro ha
    have hn (i j k : Fin 5) : 0 ≤ tangentWeight i * tangentWeight j * tangentWeight k *
        factorialPairing (a i j k) (a i j k) :=
      mul_nonneg (mul_nonneg (mul_nonneg (tangentWeight_pos i).le (tangentWeight_pos j).le)
        (tangentWeight_pos k).le) (factorialPairing_self_nonneg _)
    have hs : (∑ i : Fin 5, ∑ j : Fin 5, ∑ k : Fin 5,
        tangentWeight i * tangentWeight j * tangentWeight k * factorialPairing (a i j k) (a i j k)) = 0 := by
      unfold threePairing at ha
      linarith
    have hrow := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
      Finset.sum_nonneg (fun k _ => hn i j k)))).mp hs
    funext i j k
    have hs2 := hrow i (Finset.mem_univ i)
    have hz2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Finset.sum_nonneg
      (fun k _ => hn i j k))).mp hs2
    have hz3 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hn i j k)).mp (hz2 j (Finset.mem_univ j))
    exact (factorialPairing_self_eq_zero _).mp ((mul_eq_zero.mp (hz3 k (Finset.mem_univ k))).resolve_left
      (ne_of_gt (mul_pos (mul_pos (tangentWeight_pos i) (tangentWeight_pos j)) (tangentWeight_pos k))))
  · rintro rfl
    simp [threePairing]

theorem algebraicHodgeTwo_eq_zero_of_energy_zero (a : TwoCoordinates)
    (ha : IsAlternatingTwo a) (hz : twoPairing (algebraicHodgeTwo a) a = 0) :
    algebraicHodgeTwo a = 0 := by
  rw [algebraicHodgeTwo_energy a ha] at hz
  have h1 := onePairing_self_nonneg (contractionTwo a)
  have h3 := threePairing_self_nonneg (exteriorTwo a)
  have hz1 := (onePairing_self_eq_zero (contractionTwo a)).mp (by linarith)
  have hz3 := (threePairing_self_eq_zero (exteriorTwo a)).mp (by linarith)
  rw [algebraicHodgeTwo, hz1, hz3]
  funext i j
  simp [exteriorOne, contractionThree]

theorem homogeneousHodgeTwo_coercive_of_kernel {n : ℕ}
    (hinj : ∀ a : homogeneousTwoForms n, algebraicHodgeTwo a.val = 0 → a = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : homogeneousTwoForms n,
      c * twoPairing a.val a.val ≤ twoPairing (homogeneousHodgeTwo n a).val a.val := by
  let : InnerProductSpace.Core ℝ (homogeneousTwoForms n) := homogeneousTwoInnerCore n
  let : NormedAddCommGroup (homogeneousTwoForms n) := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  let : InnerProductSpace ℝ (homogeneousTwoForms n) := InnerProductSpace.ofCore (homogeneousTwoInnerCore n).toCore
  apply finite_inner_coercivity (homogeneousHodgeTwo n)
  intro a ha
  change 0 < twoPairing (algebraicHodgeTwo a.val) a.val
  apply lt_of_le_of_ne (algebraicHodgeTwo_nonneg a.val a.property.1)
  intro hz
  exact ha (hinj a (algebraicHodgeTwo_eq_zero_of_energy_zero a.val a.property.1 hz.symm))

end TernaryPoly.SL3PolynomialCoercivity
