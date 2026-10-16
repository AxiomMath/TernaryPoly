module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Cancellation
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.DegreeOne.CancellationOne
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Three
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Four
public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.Cancellation
public import TernaryPeriodPolynomials.Polynomial.PositiveInnerVanishing
public import TernaryPeriodPolynomials.SymmetricSpace.All.TopBoundaryPolynomial

@[expose] public section



/-! Final assembly of Proposition C.1 (`TernaryPeriodPolynomials.Argument.Targets.PropC1`)
from the per-degree coercivity results, taking the exterior-degree-4 clause (`k = 3`) as a
hypothesis `h4`. The constant is the
minimum of the six per-degree constants; degrees `≥ 6` (`k ≥ 5`) are handled unconditionally
since `Core n m` is the zero module for `m ≥ 6` (any `≥ 6` vectors in the 5-dimensional
`Coordinates` are linearly dependent), generalizing `SixVanishing.lean`'s degree-6 case. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.PolynomialFormCoordinates TernaryPoly.PolynomialFormHilbert TernaryPoly.PolynomialCoefficientBundle
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpaceCovering TernaryPoly.SymmetricSpacePositive
open TernaryPoly.SymmetricSpaceRiemannian
open TernaryPoly.SmoothCoveringDeRham TernaryPoly.SmoothLocalDeRham Set MeasureTheory
open TernaryPoly.SymmetricSpaceAllTopBoundary TernaryPoly.CompactInteriorRelativeBoundary
open TernaryPoly.SymmetricSpaceBordifiedCohomology
open scoped SymmetricSpaceRiemannian Matrix.Norms.Elementwise

/-- Any `m ≥ 6` vectors in the 5-dimensional `Coordinates` are linearly dependent, generalizing
`not_linearIndependent_six`. -/
private theorem not_linearIndependent_of_ge_six {m : ℕ} (hm : 6 ≤ m) (v : Fin m → Coordinates) :
    ¬ LinearIndependent ℝ v := by
  intro hli
  have hcard := hli.fintype_card_le_finrank
  rw [finrank_coordinates, Fintype.card_fin] at hcard
  omega

/-- `FormValue n m` is trivial for `m ≥ 6`, generalizing `formValue_six_eq_zero`. -/
private theorem formValue_eq_zero_of_ge_six {m : ℕ} (hm : 6 ≤ m) (n : ℕ) (f : FormValue n m) :
    f = 0 :=
  ContinuousAlternatingMap.ext fun v =>
    AlternatingMap.map_linearDependent f.toAlternatingMap v (not_linearIndependent_of_ge_six hm v)

/-- Any `Form`-level `m`-form (`m ≥ 6`), on any domain `s`, is the zero form. -/
private theorem form_eq_zero_of_ge_six {m : ℕ} (hm : 6 ≤ m) (n : ℕ) {s : Set Coordinates}
    (w : Form (F := Coefficients n) s m) : w = 0 :=
  Form.ext fun x _ => formValue_eq_zero_of_ge_six hm n (w.val x)

/-- Any equivariant degree-`m` form (`m ≥ 6`) is zero. -/
private theorem equivariantForm_eq_zero_of_ge_six {m : ℕ} (hm : 6 ≤ m) (n : ℕ)
    (a : EquivariantForm (deckRepresentation n) univ m) : a = 0 :=
  Subtype.ext (form_eq_zero_of_ge_six hm n a.val)

/-- `Core n m` is the trivial module for `m ≥ 6`, generalizing `core_six_eq_zero`. -/
private theorem core_eq_zero_of_ge_six {m : ℕ} (hm : 6 ≤ m) (n : ℕ) (b : Core n m) : b = 0 :=
  Subtype.ext (equivariantForm_eq_zero_of_ge_six hm n b.val)

/-- The `k < 5` case of the universally quantified successor clause, from the five genuine
per-degree bounds via `interval_cases`.
-/
private theorem succ_clause_lt_five (n : ℕ) (c c1 c2 c3 c4 c5 : ℝ)
    (hcle1 : c ≤ c1) (hcle2 : c ≤ c2) (hcle3 : c ≤ c3) (hcle4 : c ≤ c4) (hcle5 : c ≤ c5)
    (h1 : ∀ a : Core n 1, c1 * ‖inclusion n 1 a‖ ^ 2 ≤
      ‖inclusion n 0 (compactAdjoint n 0 a)‖ ^ 2 +
        ‖inclusion n 2 (compactDifferential (deckRepresentation n) isOpen_univ 1 a)‖ ^ 2)
    (h2 : ∀ a : Core n 2, c2 * ‖inclusion n 2 a‖ ^ 2 ≤
      ‖inclusion n 1 (compactAdjoint n 1 a)‖ ^ 2 +
        ‖inclusion n 3 (compactDifferential (deckRepresentation n) isOpen_univ 2 a)‖ ^ 2)
    (h3 : ∀ a : Core n 3, c3 * ‖inclusion n 3 a‖ ^ 2 ≤
      ‖inclusion n 2 (compactAdjoint n 2 a)‖ ^ 2 +
        ‖inclusion n 4 (compactDifferential (deckRepresentation n) isOpen_univ 3 a)‖ ^ 2)
    (h4' : ∀ a : Core n 4, c4 * ‖inclusion n 4 a‖ ^ 2 ≤
      ‖inclusion n 3 (PolynomialFormCoordinates.compactAdjoint n 3 a)‖ ^ 2 +
        ‖inclusion n 5 (compactDifferential (deckRepresentation n) isOpen_univ 4 a)‖ ^ 2)
    (h5 : ∀ a : Core n 5, c5 * ‖inclusion n 5 a‖ ^ 2 ≤
      ‖inclusion n 4 (compactAdjoint n 4 a)‖ ^ 2 +
        ‖inclusion n 6 (compactDifferential (deckRepresentation n) isOpen_univ 5 a)‖ ^ 2) :
    ∀ (k : ℕ), k < 5 → ∀ (a : Core n (k + 1)), c * ‖inclusion n (k + 1) a‖ ^ 2 ≤
      ‖inclusion n k (PolynomialFormCoordinates.compactAdjoint n k a)‖ ^ 2 +
        ‖inclusion n (k + 2)
          (compactDifferential (deckRepresentation n) isOpen_univ (k + 1) a)‖ ^ 2 := by
  intro k hk
  interval_cases k
  · exact fun a => (mul_le_mul_of_nonneg_right hcle1 (sq_nonneg _)).trans (h1 a)
  · exact fun a => (mul_le_mul_of_nonneg_right hcle2 (sq_nonneg _)).trans (h2 a)
  · exact fun a => (mul_le_mul_of_nonneg_right hcle3 (sq_nonneg _)).trans (h3 a)
  · exact fun a => (mul_le_mul_of_nonneg_right hcle4 (sq_nonneg _)).trans (h4' a)
  · exact fun a => (mul_le_mul_of_nonneg_right hcle5 (sq_nonneg _)).trans (h5 a)

/-- The `k ≥ 5` case of the universally quantified successor clause: `Core n (k+1)` is trivial, so
the left side vanishes and the bound holds by nonnegativity of both summands on the right. -/
private theorem succ_clause_ge_five (n : ℕ) (c : ℝ) :
    ∀ (k : ℕ), k ≥ 5 → ∀ (a : Core n (k + 1)), c * ‖inclusion n (k + 1) a‖ ^ 2 ≤
      ‖inclusion n k (PolynomialFormCoordinates.compactAdjoint n k a)‖ ^ 2 +
        ‖inclusion n (k + 2)
          (compactDifferential (deckRepresentation n) isOpen_univ (k + 1) a)‖ ^ 2 := by
  intro k hk a
  have ha0 : a = 0 := core_eq_zero_of_ge_six (by omega) n a
  have hA : ‖inclusion n (k + 1) a‖ = 0 := by rw [ha0, map_zero, norm_zero]
  have hR1 : (0:ℝ) ≤ ‖inclusion n k (PolynomialFormCoordinates.compactAdjoint n k a)‖ ^ 2 :=
    sq_nonneg _
  have hR2 : (0:ℝ) ≤ ‖inclusion n (k + 2)
      (compactDifferential (deckRepresentation n) isOpen_univ (k + 1) a)‖ ^ 2 := sq_nonneg _
  calc c * ‖inclusion n (k + 1) a‖ ^ 2 = c * (0:ℝ) ^ 2 := by rw [hA]
    _ = 0 := by ring
    _ ≤ _ := add_nonneg hR1 hR2

/-- The universally quantified successor clause of Proposition C.1 (`k = 0..4` from the five
genuine per-degree bounds, `k ≥ 5` unconditionally since `Core n` vanishes there), taking the
already-extracted plain-real constants `c1..c5` and the common lower bound `c ≤ cI` as plain
arguments.
-/
private theorem forall_succ_clause (n : ℕ) (c c1 c2 c3 c4 c5 : ℝ)
    (hcle1 : c ≤ c1) (hcle2 : c ≤ c2) (hcle3 : c ≤ c3) (hcle4 : c ≤ c4) (hcle5 : c ≤ c5)
    (h1 : ∀ a : Core n 1, c1 * ‖inclusion n 1 a‖ ^ 2 ≤
      ‖inclusion n 0 (compactAdjoint n 0 a)‖ ^ 2 +
        ‖inclusion n 2 (compactDifferential (deckRepresentation n) isOpen_univ 1 a)‖ ^ 2)
    (h2 : ∀ a : Core n 2, c2 * ‖inclusion n 2 a‖ ^ 2 ≤
      ‖inclusion n 1 (compactAdjoint n 1 a)‖ ^ 2 +
        ‖inclusion n 3 (compactDifferential (deckRepresentation n) isOpen_univ 2 a)‖ ^ 2)
    (h3 : ∀ a : Core n 3, c3 * ‖inclusion n 3 a‖ ^ 2 ≤
      ‖inclusion n 2 (compactAdjoint n 2 a)‖ ^ 2 +
        ‖inclusion n 4 (compactDifferential (deckRepresentation n) isOpen_univ 3 a)‖ ^ 2)
    (h4' : ∀ a : Core n 4, c4 * ‖inclusion n 4 a‖ ^ 2 ≤
      ‖inclusion n 3 (PolynomialFormCoordinates.compactAdjoint n 3 a)‖ ^ 2 +
        ‖inclusion n 5 (compactDifferential (deckRepresentation n) isOpen_univ 4 a)‖ ^ 2)
    (h5 : ∀ a : Core n 5, c5 * ‖inclusion n 5 a‖ ^ 2 ≤
      ‖inclusion n 4 (compactAdjoint n 4 a)‖ ^ 2 +
        ‖inclusion n 6 (compactDifferential (deckRepresentation n) isOpen_univ 5 a)‖ ^ 2) :
    ∀ (k : ℕ) (a : Core n (k + 1)), c * ‖inclusion n (k + 1) a‖ ^ 2 ≤
      ‖inclusion n k (PolynomialFormCoordinates.compactAdjoint n k a)‖ ^ 2 +
        ‖inclusion n (k + 2)
          (compactDifferential (deckRepresentation n) isOpen_univ (k + 1) a)‖ ^ 2 :=
  fun k a =>
    if hk : k < 5 then
      succ_clause_lt_five n c c1 c2 c3 c4 c5 hcle1 hcle2 hcle3 hcle4 hcle5 h1 h2 h3 h4' h5 k hk a
    else
      succ_clause_ge_five n c k (by omega) a

/-- Final assembly of Proposition C.1, taking the exterior-degree-4 clause (`k = 3`) as a
hypothesis. The constant is the minimum of the six per-degree constants (degree 0, 1, 2, 3, the
hypothesis `h4` at degree 4, and degree 5); degrees `≥ 6` hold unconditionally since `Core n`
vanishes there. -/
theorem prop_C_1_of_degree_four (n : ℕ) (hn : 0 < n)
    (h4 : ∃ c > 0, ∀ a : Core n 4,
      c * ‖inclusion n 4 a‖ ^ 2 ≤
        ‖inclusion n 3 (PolynomialFormCoordinates.compactAdjoint n 3 a)‖ ^ 2 +
          ‖inclusion n 5 (compactDifferential (deckRepresentation n) isOpen_univ 4 a)‖ ^ 2) :
    (∃ c : ℝ, 0 < c ∧
      (∀ a : Core n 0, c * ‖inclusion n 0 a‖ ^ 2 ≤
        ‖inclusion n 1 (compactDifferential (deckRepresentation n) isOpen_univ 0 a)‖ ^ 2) ∧
      ∀ (k : ℕ) (a : Core n (k + 1)), c * ‖inclusion n (k + 1) a‖ ^ 2 ≤
        ‖inclusion n k (PolynomialFormCoordinates.compactAdjoint n k a)‖ ^ 2 +
          ‖inclusion n (k + 2)
            (compactDifferential (deckRepresentation n) isOpen_univ (k + 1) a)‖ ^ 2) ∧
    ∀ e : ℤ, compactForget interiorCover (polynomialCoefficients n e) 2 = 0 := by
  have e0 := norm_differential_energy_coercive_zero hn
  have e1 :=
    TernaryPeriodPolynomials.Argument.CoercivityOne.norm_differential_energy_coercive_one hn
  have e2 := TernaryPoly.PolynomialFormGeometricEnergy.norm_differential_energy_coercive hn
  have e3 := norm_differential_energy_coercive_three hn
  have e5 := norm_adjoint_differential_energy_coercive_four hn
  have hc0 : 0 < e0.choose := e0.choose_spec.1
  have hc1 : 0 < e1.choose := e1.choose_spec.1
  have hc2 : 0 < e2.choose := e2.choose_spec.1
  have hc3 : 0 < e3.choose := e3.choose_spec.1
  have hc4 : 0 < h4.choose := h4.choose_spec.1
  have hc5 : 0 < e5.choose := e5.choose_spec.1
  have h0 := e0.choose_spec.2
  have h1 := e1.choose_spec.2
  have h2 := e2.choose_spec.2
  have h3 := e3.choose_spec.2
  have h4' := h4.choose_spec.2
  have h5 := e5.choose_spec.2
  let c : ℝ := min e0.choose (min e1.choose (min e2.choose (min e3.choose (min h4.choose e5.choose))))
  have hc_def :
      c = min e0.choose (min e1.choose (min e2.choose (min e3.choose (min h4.choose e5.choose)))) :=
    rfl
  have hcpos : 0 < c := by
    rw [hc_def]
    exact lt_min hc0 (lt_min hc1 (lt_min hc2 (lt_min hc3 (lt_min hc4 hc5))))
  have hcle0 : c ≤ e0.choose := by rw [hc_def]; exact min_le_left _ _
  have hcle1 : c ≤ e1.choose := by rw [hc_def]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hcle2 : c ≤ e2.choose := by
    rw [hc_def]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcle3 : c ≤ e3.choose := by
    rw [hc_def]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _)))
  have hcle4 : c ≤ h4.choose := by
    rw [hc_def]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have hcle5 : c ≤ e5.choose := by
    rw [hc_def]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))
  refine ⟨⟨c, hcpos, fun a => (mul_le_mul_of_nonneg_right hcle0 (sq_nonneg _)).trans (h0 a),
    forall_succ_clause n c e1.choose e2.choose e3.choose h4.choose e5.choose
      hcle1 hcle2 hcle3 hcle4 hcle5 h1 h2 h3 h4' h5⟩, ?_⟩
  exact TernaryPoly.SymmetricSpaceAllTopBoundary.positivePolynomialInnerVanishing n hn

end TernaryPeriodPolynomials.Argument.Coercivity
