module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.DegreeOne.Algebra
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.DegreeOne.Coercive
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.ExteriorCasimir
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.Commutators
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.CoefficientCasimir
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.StrictEnergy

@[expose] public section



/-! # The `n ≥ 2` Casimir + Young's-inequality coercivity bound, exterior degree one

Mirrors `TernaryPoly.SL3PolynomialCoercivity.algebraicHodgeTwo_high_degree`
(`TernaryPeriodPolynomials/DifferentialForm/Coercivity/SpecialLinear/HighDegree.lean`) one exterior degree down. Unlike
degree two, the exterior-compact-Casimir energy is an *exact identity* here
(`exteriorEnergyOne_eq`) rather than an inequality (no three-square certificate is needed,
since there is only one slot to act on), so the whole `n ≥ 2` bound goes through with plain
Young's-inequality algebra (`onePairing_young` / `mixedEnergyOne_young`, mirroring
`twoPairing_young` / `mixedEnergy_young`), giving the closed form
`((2*n-3)*(n+3)/12) * onePairing a a ≤ onePairing (algebraicHodgeOne a) a`
for `a` homogeneous of degree `n ≥ 2`. (The bound is `-1/3` at `n = 1`, which is why `n = 1`
is handled separately in `Coercive.lean` via `exteriorOne_injective_of_isHomogeneous_one`.) -/

noncomputable section
open TernaryPoly.SL3PolynomialCoercivity MvPolynomial

namespace TernaryPeriodPolynomials.Argument.CoercivityOne

/-! ## `onePairing` linearity helpers not already in `Algebra.lean` -/

theorem onePairing_smul_left (r : ℝ) (a b : OneCoordinates) :
    onePairing (r • a) b = r * onePairing a b := by
  simp [onePairing, Finset.mul_sum, mul_left_comm]

theorem onePairing_sub_left (a b c : OneCoordinates) :
    onePairing (a - b) c = onePairing a c - onePairing b c := by
  simp [onePairing, mul_sub, Finset.sum_sub_distrib]

theorem onePairing_sum_left {ι : Type*} [Fintype ι] (f : ι → OneCoordinates)
    (a : OneCoordinates) : onePairing (∑ i, f i) a = ∑ i, onePairing (f i) a := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp [onePairing]
  | insert x s hx ih => simp only [Finset.sum_insert hx, onePairing_add_left, ih]

/-! ## The Hodge-Casimir splitting in degree one -/

/-- One-slot lift of a matrix's infinitesimal action on `OneCoordinates`. -/
def coefficientLiftOne (A : Mat) (a : OneCoordinates) : OneCoordinates :=
  fun i => infinitesimal A (a i)

/-- The cross term of the degree-one Hodge splitting; the one-slot analogue of `hodgeCross`. -/
def hodgeCrossOne (a : OneCoordinates) : OneCoordinates := fun i =>
  ∑ k : Fin 5, tangentWeight k •
    infinitesimal (tangentFrame i * tangentFrame k - tangentFrame k * tangentFrame i) (a k)

theorem algebraicHodgeOne_split (a : OneCoordinates) (i : Fin 5) :
    algebraicHodgeOne a i =
      fullCoefficientCasimir (a i) - compactCoefficientCasimir (a i) + hodgeCrossOne a i := by
  simp only [algebraicHodgeOne_expansion, fullCoefficientCasimir, add_sub_cancel_right,
    hodgeCrossOne, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  module

/-! ## The one-slot exterior compact action -/

/-- The one-slot analogue of `compactExteriorAction`: the compact-Lie-algebra action on the
single exterior slot of `OneCoordinates`. -/
def compactOneAction (k : Fin 3) (a : OneCoordinates) : OneCoordinates := fun i =>
  -(∑ l : Fin 5, compactTangentCoefficient k i l • a l)

theorem compactTangentCoefficient_skew (k : Fin 3) (i l : Fin 5) :
    tangentWeight i * compactTangentCoefficient k i l +
      tangentWeight l * compactTangentCoefficient k l i = 0 := by
  fin_cases k <;> fin_cases i <;> fin_cases l <;>
    norm_num [compactTangentCoefficient_eq, compactTangentMatrix, tangentWeight]

theorem compactOneAction_skew_adjoint (k : Fin 3) (a b : OneCoordinates) :
    onePairing (compactOneAction k a) b = -onePairing a (compactOneAction k b) := by
  have hL : onePairing (compactOneAction k a) b =
      -∑ i : Fin 5, ∑ l : Fin 5,
        (tangentWeight i * compactTangentCoefficient k i l) * factorialPairing (a l) (b i) := by
    simp only [onePairing, compactOneAction, map_neg, LinearMap.neg_apply, map_sum,
      LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, mul_neg,
      Finset.sum_neg_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro l _
    ring
  have hR0 : onePairing a (compactOneAction k b) =
      -∑ l : Fin 5, ∑ i : Fin 5,
        (tangentWeight l * compactTangentCoefficient k l i) * factorialPairing (a l) (b i) := by
    simp only [onePairing, compactOneAction, map_neg, map_sum, map_smul, smul_eq_mul, mul_neg,
      Finset.sum_neg_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl; intro l _
    apply Finset.sum_congr rfl; intro i _
    ring
  have hR : onePairing a (compactOneAction k b) =
      -∑ i : Fin 5, ∑ l : Fin 5,
        (tangentWeight l * compactTangentCoefficient k l i) * factorialPairing (a l) (b i) := by
    rw [hR0, Finset.sum_comm]
  have hsum : (∑ i : Fin 5, ∑ l : Fin 5,
      (tangentWeight i * compactTangentCoefficient k i l) * factorialPairing (a l) (b i)) +
      (∑ i : Fin 5, ∑ l : Fin 5,
      (tangentWeight l * compactTangentCoefficient k l i) * factorialPairing (a l) (b i)) = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro l _
    rw [← add_mul, compactTangentCoefficient_skew k i l, zero_mul]
  rw [hL, hR]
  linarith [hsum]

/-! ## The commutator/matrix bridge and the Hodge-cross identity -/

/-- Bridges the commutator-coordinate presentation of `hodgeCrossOne` (via
`tangentCommutatorCoordinates`) and the matrix presentation of `compactOneAction` (via
`compactTangentMatrix`): numerically exact for all `75` cases. -/
theorem tangentCommutatorCoordinates_bridge (i j : Fin 5) (k : Fin 3) :
    tangentWeight j * tangentCommutatorCoordinates i j k =
      -(1/2 : ℝ) * compactTangentMatrix k i j := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [tangentWeight, tangentCommutatorCoordinates, compactTangentMatrix]

theorem hodgeCrossOne_eq_compactOneAction (a : OneCoordinates) :
    hodgeCrossOne a =
      (1/2 : ℝ) • ∑ k : Fin 3, compactOneAction k (coefficientLiftOne (skewFrame k) a) := by
  funext i
  have hL : hodgeCrossOne a i =
      ∑ k : Fin 3, ∑ j : Fin 5,
        (-(1/2 : ℝ) * compactTangentMatrix k i j) • infinitesimal (skewFrame k) (a j) := by
    simp only [hodgeCrossOne, infinitesimal_tangent_commutator, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    rw [tangentCommutatorCoordinates_bridge i j k]
  have hR : ((1/2 : ℝ) • ∑ k : Fin 3,
      compactOneAction k (coefficientLiftOne (skewFrame k) a)) i =
      ∑ k : Fin 3, ∑ j : Fin 5,
        (-(1/2 : ℝ) * compactTangentMatrix k i j) • infinitesimal (skewFrame k) (a j) := by
    simp only [Pi.smul_apply, Finset.sum_apply, compactOneAction, coefficientLiftOne,
      compactTangentCoefficient_eq, Finset.smul_sum, smul_neg, smul_smul, neg_mul,
      neg_smul, ← Finset.sum_neg_distrib]
  rw [hL, hR]

def mixedEnergyOne (a : OneCoordinates) : ℝ :=
  ∑ k : Fin 3, onePairing (coefficientLiftOne (skewFrame k) a) (compactOneAction k a)

theorem hodgeCrossOne_energy (a : OneCoordinates) :
    onePairing (hodgeCrossOne a) a = -(1/2 : ℝ) * mixedEnergyOne a := by
  rw [hodgeCrossOne_eq_compactOneAction, onePairing_smul_left, onePairing_sum_left]
  have hterm : ∀ k : Fin 3,
      onePairing (compactOneAction k (coefficientLiftOne (skewFrame k) a)) a =
        -onePairing (coefficientLiftOne (skewFrame k) a) (compactOneAction k a) :=
    fun k => compactOneAction_skew_adjoint k (coefficientLiftOne (skewFrame k) a) a
  rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_neg_distrib]
  simp only [mixedEnergyOne]
  ring

/-! ## Energies -/

def compactCoefficientLiftOne (a : OneCoordinates) : OneCoordinates :=
  fun i => compactCoefficientCasimir (a i)

def coefficientEnergyOne (a : OneCoordinates) : ℝ :=
  ∑ k : Fin 3,
    onePairing (coefficientLiftOne (skewFrame k) a) (coefficientLiftOne (skewFrame k) a)

def exteriorEnergyOne (a : OneCoordinates) : ℝ :=
  ∑ k : Fin 3, onePairing (compactOneAction k a) (compactOneAction k a)

theorem compactCoefficientLiftOne_energy (a : OneCoordinates) :
    onePairing (compactCoefficientLiftOne a) a = (1/2 : ℝ) * coefficientEnergyOne a := by
  simp only [onePairing, compactCoefficientLiftOne, compactCoefficientCasimir_energy,
    coefficientEnergyOne, coefficientLiftOne, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem coefficientEnergyOne_upper {n : ℕ} (a : OneCoordinates)
    (ha : ∀ i, (a i).IsHomogeneous n) :
    coefficientEnergyOne a ≤ ((n : ℝ) * (n + 1)) * onePairing a a := by
  have h : onePairing (compactCoefficientLiftOne a) a ≤
      ((n : ℝ) * (n + 1) / 2) * onePairing a a := by
    simp only [onePairing, compactCoefficientLiftOne]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hp := mul_le_mul_of_nonneg_left (compactCoefficientCasimir_upper (ha i))
      (tangentWeight_pos i).le
    nlinarith
  rw [compactCoefficientLiftOne_energy] at h
  linarith

/-! ## The exact exterior-compact-Casimir identity -/

theorem onePairing_matrix_action (k : Fin 3) (a b : OneCoordinates) :
    onePairing (compactOneAction k a) (compactOneAction k b) =
      ∑ i : Fin 5, ∑ l : Fin 5, ∑ m : Fin 5,
        tangentWeight i * (compactTangentMatrix k i l * compactTangentMatrix k i m) *
          factorialPairing (a l) (b m) := by
  simp only [onePairing, compactOneAction, map_neg, LinearMap.neg_apply, map_sum,
    LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, neg_neg,
    compactTangentCoefficient_eq, Finset.mul_sum, mul_neg, Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro m _
  ring

theorem compactTangentMatrix_weighted_sum (l m : Fin 5) :
    (∑ k : Fin 3, ∑ i : Fin 5,
      tangentWeight i * (compactTangentMatrix k i l * compactTangentMatrix k i m)) =
      if l = m then 6 * tangentWeight l else 0 := by
  fin_cases l <;> fin_cases m <;>
    simp [compactTangentMatrix, tangentWeight, Fin.sum_univ_three, Fin.sum_univ_five] <;>
    norm_num [compactTangentMatrix, tangentWeight]

theorem exteriorEnergyOne_eq (a : OneCoordinates) : exteriorEnergyOne a = 6 * onePairing a a := by
  have hsum : exteriorEnergyOne a =
      ∑ l : Fin 5, ∑ m : Fin 5,
        (∑ k : Fin 3, ∑ i : Fin 5,
          tangentWeight i * (compactTangentMatrix k i l * compactTangentMatrix k i m)) *
            factorialPairing (a l) (a m) := by
    simp only [exteriorEnergyOne, onePairing_matrix_action, Finset.sum_mul]
    calc ∑ k : Fin 3, ∑ i : Fin 5, ∑ l : Fin 5, ∑ m : Fin 5,
          tangentWeight i * (compactTangentMatrix k i l * compactTangentMatrix k i m) *
            factorialPairing (a l) (a m)
        = ∑ k : Fin 3, ∑ l : Fin 5, ∑ i : Fin 5, ∑ m : Fin 5,
          tangentWeight i * (compactTangentMatrix k i l * compactTangentMatrix k i m) *
            factorialPairing (a l) (a m) :=
          Finset.sum_congr rfl (fun k _ => Finset.sum_comm)
      _ = ∑ l : Fin 5, ∑ k : Fin 3, ∑ i : Fin 5, ∑ m : Fin 5,
          tangentWeight i * (compactTangentMatrix k i l * compactTangentMatrix k i m) *
            factorialPairing (a l) (a m) :=
          Finset.sum_comm
      _ = ∑ l : Fin 5, ∑ k : Fin 3, ∑ m : Fin 5, ∑ i : Fin 5,
          tangentWeight i * (compactTangentMatrix k i l * compactTangentMatrix k i m) *
            factorialPairing (a l) (a m) :=
          Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ => Finset.sum_comm))
      _ = ∑ l : Fin 5, ∑ m : Fin 5, ∑ k : Fin 3, ∑ i : Fin 5,
          tangentWeight i * (compactTangentMatrix k i l * compactTangentMatrix k i m) *
            factorialPairing (a l) (a m) :=
          Finset.sum_congr rfl (fun l _ => Finset.sum_comm)
  rw [hsum]
  simp only [compactTangentMatrix_weighted_sum, ite_mul, zero_mul]
  have hcollapse : ∀ l : Fin 5, (∑ m : Fin 5,
      (if l = m then 6 * tangentWeight l * factorialPairing (a l) (a m) else 0)) =
      6 * tangentWeight l * factorialPairing (a l) (a l) := by
    intro l
    rw [Finset.sum_ite_eq]
    simp
  rw [Finset.sum_congr rfl (fun l _ => hcollapse l)]
  rw [onePairing, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

/-! ## Homogeneous-degree energy decomposition and the final Young's-inequality bound -/

theorem algebraicHodgeOne_homogeneous_energy {n : ℕ} (a : OneCoordinates)
    (hn : ∀ i, (a i).IsHomogeneous n) :
    onePairing (algebraicHodgeOne a) a =
      (2 * (n : ℝ) * (n + 3) / 3) * onePairing a a -
        (1/2 : ℝ) * coefficientEnergyOne a - (1/2 : ℝ) * mixedEnergyOne a := by
  have he : algebraicHodgeOne a =
      (2 * (n : ℝ) * (n + 3) / 3) • a - compactCoefficientLiftOne a + hodgeCrossOne a := by
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, compactCoefficientLiftOne]
    rw [algebraicHodgeOne_split a i, fullCoefficientCasimir_homogeneous (hn i)]
  rw [he, onePairing_add_left, onePairing_sub_left, onePairing_smul_left,
    compactCoefficientLiftOne_energy, hodgeCrossOne_energy a]
  ring

theorem onePairing_young (a b : OneCoordinates) (r s : ℝ) :
    0 ≤ r ^ 2 * onePairing a a + s ^ 2 * onePairing b b - 2 * r * s * onePairing a b := by
  have hp := onePairing_self_nonneg (r • a - s • b)
  have h1 : onePairing (r • a - s • b) (r • a - s • b) =
      r ^ 2 * onePairing a a + s ^ 2 * onePairing b b - 2 * r * s * onePairing a b := by
    rw [onePairing_sub_left, onePairing_smul_left, onePairing_smul_left,
      onePairing_symmetric a (r • a - s • b), onePairing_symmetric b (r • a - s • b),
      onePairing_sub_left, onePairing_sub_left,
      onePairing_smul_left, onePairing_smul_left, onePairing_smul_left, onePairing_smul_left]
    have hba : onePairing b a = onePairing a b := (onePairing_symmetric a b).symm
    rw [hba]
    ring
  linarith [h1 ▸ hp]

theorem mixedEnergyOne_young (a : OneCoordinates) (n : ℝ) :
    0 ≤ 9 * coefficientEnergyOne a + n ^ 2 * exteriorEnergyOne a - 6 * n * mixedEnergyOne a := by
  have h := Finset.sum_nonneg (s := (Finset.univ : Finset (Fin 3))) (fun k _ =>
    onePairing_young (coefficientLiftOne (skewFrame k) a) (compactOneAction k a) 3 n)
  have heq : (∑ k : Fin 3, ((3:ℝ) ^ 2 *
        onePairing (coefficientLiftOne (skewFrame k) a) (coefficientLiftOne (skewFrame k) a) +
      n ^ 2 * onePairing (compactOneAction k a) (compactOneAction k a) -
      2 * 3 * n * onePairing (coefficientLiftOne (skewFrame k) a) (compactOneAction k a))) =
      9 * coefficientEnergyOne a + n ^ 2 * exteriorEnergyOne a - 6 * n * mixedEnergyOne a := by
    simp only [coefficientEnergyOne, exteriorEnergyOne, mixedEnergyOne, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [heq] at h
  linarith

theorem algebraicHodgeOne_high_degree {n : ℕ} (hn : 2 ≤ n) (a : OneCoordinates)
    (hd : ∀ i, (a i).IsHomogeneous n) :
    ((2 * (n : ℝ) - 3) * ((n : ℝ) + 3) / 12) * onePairing a a ≤
      onePairing (algebraicHodgeOne a) a := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hR := coefficientEnergyOne_upper a hd
  have hS : exteriorEnergyOne a ≤ 6 * onePairing a a := (exteriorEnergyOne_eq a).le
  have hY := mixedEnergyOne_young a (n : ℝ)
  rw [algebraicHodgeOne_homogeneous_energy a hd]
  have hR' := mul_le_mul_of_nonneg_left hR (by linarith : (0:ℝ) ≤ 2 * (n:ℝ) - 3)
  have hS' := mul_le_mul_of_nonneg_left hS (sq_nonneg (n:ℝ))
  apply (mul_le_mul_iff_right₀ (show 0 < 6 * (n:ℝ) by positivity)).mp
  nlinarith

theorem homogeneousHodgeOne_high_degree {n : ℕ} (hn : 2 ≤ n) (a : homogeneousOneForms n) :
    ((2 * (n : ℝ) - 3) * ((n : ℝ) + 3) / 12) * onePairing a.val a.val ≤
      onePairing (homogeneousHodgeOne n a).val a.val :=
  algebraicHodgeOne_high_degree hn a.val a.property

theorem homogeneousHodgeOne_coercive_high_degree {n : ℕ} (hn : 2 ≤ n) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : homogeneousOneForms n,
      c * onePairing a.val a.val ≤ onePairing (homogeneousHodgeOne n a).val a.val := by
  refine ⟨(2 * (n : ℝ) - 3) * ((n : ℝ) + 3) / 12, ?_, homogeneousHodgeOne_high_degree hn⟩
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0 : ℝ) < 2 * (n:ℝ) - 3 := by linarith
  positivity

/-- Assembled coercivity of the degree-one algebraic Hodge operator at every positive
homogeneous degree: `n = 1` via `homogeneousHodgeOne_coercive_degree_one`
(`Coercive.lean`), `n ≥ 2` via `homogeneousHodgeOne_coercive_high_degree` above. -/
theorem homogeneousHodgeOne_coercive {n : ℕ} (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : homogeneousOneForms n,
      c * onePairing a.val a.val ≤ onePairing (homogeneousHodgeOne n a).val a.val := by
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · have : n = 1 := by omega
    subst this
    exact homogeneousHodgeOne_coercive_degree_one
  · exact homogeneousHodgeOne_coercive_high_degree h2

end TernaryPeriodPolynomials.Argument.CoercivityOne
