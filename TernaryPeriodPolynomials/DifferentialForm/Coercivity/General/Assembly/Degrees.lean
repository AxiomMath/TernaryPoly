module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Assembly.Pointwise
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.CoerciveTransport
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.DegreeOne.BasepointBridge
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.CoerciveTransportThree
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.CoerciveTransportDegreeFour
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.CoerciveTransportFour
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Adjoint
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.AdjointThree
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.AdjointFour
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Anticommutator
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.DegreeOne.AnticommutatorOne
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Anticommutator.Three
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Anticommutator.DegreeFour
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Anticommutator.FiveIdentity
public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.Coercive
public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.Adjoint

@[expose] public section


/-!
# The pointwise inputs in every degree

Formalized by Claude Sonnet 5.5.

Supplies the group-free pointwise facts of `Assembly/Pointwise.lean` for every degree.  Degrees
`0, ..., 5` come from the finished modules of `Revision/Proofs/Coercivity*` and
the original library; degrees `>= 6` are vacuous because a `6`-form on the
five-dimensional space of coordinates is zero.  The coercivity constants of the six degrees are
combined by taking their minimum, which depends only on `n`.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly TernaryPoly.PolynomialFormGeometricEnergy TernaryPoly.PolynomialFormConnection
open TernaryPoly.PolynomialCoefficientMetric TernaryPoly.PolynomialFormMetric
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.SymmetricSpacePositive
open scoped ContDiff Matrix.Norms.Elementwise

/-- A form of degree at least six on the five-dimensional space of coordinates is zero. -/
theorem formValue_eq_zero_of_ge_six {m : ℕ} (hm : 6 ≤ m) (n : ℕ) (f : FormValue n m) :
    f = 0 := by
  refine ContinuousAlternatingMap.ext fun v => ?_
  refine AlternatingMap.map_linearDependent f.toAlternatingMap v ?_
  intro hli
  have hcard := hli.fintype_card_le_finrank
  rw [finrank_coordinates, Fintype.card_fin] at hcard
  omega

/-! ### Adjointness of `S↑` and `S↓` -/

/-- Adjointness of `S↑` and `S↓` in every degree. -/
theorem symmetricAdjoint (n k : ℕ) : SymmetricAdjoint n k := by
  intro x hx a b
  rcases Nat.lt_or_ge k 5 with hk | hk
  · interval_cases k
    · exact TernaryPeriodPolynomials.Argument.Coercivity.symmetricExterior_zero_adjoint n x hx a b
    · exact symmetricExterior_one_adjoint n x hx a b
    · exact symmetricExterior_two_adjoint n x hx a b
    · exact TernaryPeriodPolynomials.Argument.Coercivity.symmetricExterior_three_adjoint n x hx a b
    · exact TernaryPeriodPolynomials.Argument.Coercivity.symmetricExterior_four_adjoint n x hx a b
  · have hb : b = 0 := formValue_eq_zero_of_ge_six (by omega) n b
    subst hb
    rw [symmetricContraction_zero]
    simp

/-! ### Pointwise coercivity -/

theorem positiveCoercive_zero {n : ℕ} (hn : 0 < n) : ∃ c : ℝ, 0 < c ∧ PositiveCoercive n 0 c := by
  obtain ⟨c, hc, h⟩ := TernaryPeriodPolynomials.Argument.CoercivityOne.symmetric_energy_coercive_one hn
  exact ⟨c, hc, fun x hx a => (h x hx a).trans_eq (add_comm _ _)⟩

theorem positiveCoercive_one {n : ℕ} (hn : 0 < n) : ∃ c : ℝ, 0 < c ∧ PositiveCoercive n 1 c := by
  obtain ⟨c, hc, h⟩ := symmetric_energy_coercive hn
  exact ⟨c, hc, fun x hx a => (h x hx a).trans_eq (add_comm _ _)⟩

theorem positiveCoercive_two {n : ℕ} (hn : 0 < n) : ∃ c : ℝ, 0 < c ∧ PositiveCoercive n 2 c := by
  obtain ⟨c, hc, h⟩ := TernaryPeriodPolynomials.Argument.Coercivity.symmetric_energy_coercive_three hn
  exact ⟨c, hc, h⟩

theorem positiveCoercive_three {n : ℕ} (hn : 0 < n) : ∃ c : ℝ, 0 < c ∧ PositiveCoercive n 3 c := by
  obtain ⟨c, hc, h⟩ :=
    TernaryPeriodPolynomials.Argument.Coercivity.symmetric_energy_coercive_degree_four hn
  exact ⟨c, hc, h⟩

theorem positiveCoercive_four {n : ℕ} (hn : 0 < n) : ∃ c : ℝ, 0 < c ∧ PositiveCoercive n 4 c := by
  obtain ⟨c, hc, h⟩ := TernaryPeriodPolynomials.Argument.Coercivity.symmetric_energy_coercive_four hn
  refine ⟨c, hc, fun x hx a => ?_⟩
  have h6 : formPairing n (4 + 1 + 1) x (symmetricExterior n (4 + 1) x a)
      (symmetricExterior n (4 + 1) x a) = 0 := by
    have h0 : symmetricExterior n (4 + 1) x a = 0 := formValue_eq_zero_of_ge_six (by norm_num) n _
    rw [h0, formPairing_zero_left]
  have h5 := h x hx a
  calc c * formPairing n (4 + 1) x a a
      ≤ formPairing n 4 x (symmetricContraction n 4 x a) (symmetricContraction n 4 x a) := h5
    _ = formPairing n (4 + 1 + 1) x (symmetricExterior n (4 + 1) x a)
          (symmetricExterior n (4 + 1) x a) +
        formPairing n 4 x (symmetricContraction n 4 x a) (symmetricContraction n 4 x a) := by
      rw [h6, zero_add]

/-- In degree at least six the coercivity inequality is trivial. -/
theorem positiveCoercive_of_ge_five {n k : ℕ} (hk : 5 ≤ k) (c : ℝ) : PositiveCoercive n k c := by
  intro x _ a
  have ha : a = 0 := formValue_eq_zero_of_ge_six (by omega) n a
  subst ha
  have h1 : symmetricExterior n (k + 1) x 0 = 0 := formValue_eq_zero_of_ge_six (by omega) n _
  rw [h1, symmetricContraction_zero]
  simp

theorem bottomCoercive_exists {n : ℕ} (hn : 0 < n) : ∃ c : ℝ, 0 < c ∧ BottomCoercive n c :=
  TernaryPeriodPolynomials.Argument.Coercivity.symmetric_energy_coercive_zero hn

/-- One constant makes all the pointwise coercivity inequalities hold, in every degree. -/
theorem exists_pointwise_constant {n : ℕ} (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ BottomCoercive n c ∧ ∀ k, PositiveCoercive n k c := by
  obtain ⟨c0, hc0, h0⟩ := bottomCoercive_exists hn
  obtain ⟨c1, hc1, h1⟩ := positiveCoercive_zero hn
  obtain ⟨c2, hc2, h2⟩ := positiveCoercive_one hn
  obtain ⟨c3, hc3, h3⟩ := positiveCoercive_two hn
  obtain ⟨c4, hc4, h4⟩ := positiveCoercive_three hn
  obtain ⟨c5, hc5, h5⟩ := positiveCoercive_four hn
  refine ⟨min c0 (min c1 (min c2 (min c3 (min c4 c5)))),
    lt_min hc0 (lt_min hc1 (lt_min hc2 (lt_min hc3 (lt_min hc4 hc5)))), ?_, ?_⟩
  · exact h0.mono (min_le_left _ _)
  · intro k
    rcases Nat.lt_or_ge k 5 with hk | hk
    · interval_cases k
      · exact h1.mono ((min_le_right _ _).trans (min_le_left _ _))
      · exact h2.mono ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
      · exact h3.mono ((min_le_right _ _).trans ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_left _ _))))
      · exact h4.mono ((min_le_right _ _).trans ((min_le_right _ _).trans
          ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
      · exact h5.mono ((min_le_right _ _).trans ((min_le_right _ _).trans
          ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
    · exact positiveCoercive_of_ge_five hk _

/-! ### The divergence identity -/

/-- The divergence identity follows from the anticommutator of `S↓` with `∇`. -/
theorem positiveDivergence_of_anticommutator {n k : ℕ}
    (h : ∀ (w : Coordinates → FormValue n (k + 1)) (x : Coordinates), x ∈ positiveCoordinates →
      DifferentiableAt ℝ w x →
        symmetricContraction n (k + 1) x (covariantExterior n (k + 1) w x) +
          covariantExterior n k (fun y => symmetricContraction n k y (w y)) x =
            symmetricDirectionalTrace n (k + 1) w x) :
    PositiveDivergence n k := by
  intro w hw x hx
  rw [weightedDivergence_energyCurrent n (k + 1) hw x hx,
    h w x hx (((hw x hx).contDiffAt (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp))]

/-- The divergence identity in every positive degree. -/
theorem positiveDivergence (n k : ℕ) : PositiveDivergence n k := by
  rcases Nat.lt_or_ge k 5 with hk | hk
  · interval_cases k
    · exact positiveDivergence_of_anticommutator
        (TernaryPeriodPolynomials.Argument.CoercivityOne.covariant_contraction_anticommutator_one n)
    · exact positiveDivergence_of_anticommutator (covariant_contraction_anticommutator_two n)
    · exact positiveDivergence_of_anticommutator
        (TernaryPeriodPolynomials.Argument.Coercivity.covariant_contraction_anticommutator_three n)
    · exact positiveDivergence_of_anticommutator
        (TernaryPeriodPolynomials.Argument.Coercivity.covariant_contraction_anticommutator_four n)
    · exact positiveDivergence_of_anticommutator
        (TernaryPeriodPolynomials.Argument.Coercivity.covariant_contraction_anticommutator_five n)
  · intro w hw x hx
    have h0 : w x = 0 := formValue_eq_zero_of_ge_six (by omega) n _
    rw [weightedDivergence_energyCurrent n (k + 1) hw x hx, h0]
    simp

/-- The divergence identity in degree zero. -/
theorem bottomDivergence (n : ℕ) : BottomDivergence n := by
  intro w hw x hx
  rw [weightedDivergence_energyCurrent n 0 hw x hx,
    ← TernaryPeriodPolynomials.Argument.Coercivity.covariant_contraction_anticommutator_zero
      n w x hx]

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
