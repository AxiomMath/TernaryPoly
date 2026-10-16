module

public import TernaryPeriodPolynomials.Polynomial.CoefficientBaseChange
public import TernaryPeriodPolynomials.SymmetricSolution.Factors
public import TernaryPeriodPolynomials.Building.BoundaryApartments

@[expose] public section


/-!
# `lem:sym-boundary-factors` over `ℂ`, and the vanishing of `J_f` at `Y = 0` and `Z = 3Y`

Paper:

* , `lem:sym-boundary-factors`: "A symmetric homogeneous solution `f` is divisible by
  `cPlus` (`= (x+y)(x+z)(y+z)`). In positive even degree it is divisible by `w cPlus`" (`w = x+y+z`).
  The rational statement is `Statements.PaperDeliverables.lemma_2_2` (the paper's translation-invariance
  argument is `TernaryPoly.symmetric_opposite_plane_zero`, `symmetric_total_plane_zero`); here it is
  carried to `ℂ` through the coefficient base change `proposition_6_1`
  (`symmetricSolution_baseChangeEquiv`: every complex symmetric solution is a `ℂ`-combination of
  rational ones), giving `lemma_2_2_complex` and, for the `SymmetricSolution f`,
  `sym_boundary_factors`.
* "`J_f(0,Z) = Z f(Z,-X,X) = 0` by the opposite-pair vanishing" and "For odd `d`,
  Lemma 2.2 gives `w ∣ f`. All three frames have sum `Z - 3Y`, so `J_f(Y,3Y) = 0`":
  `bernoulliObstruction_zero_Y` and `bernoulliObstruction_three_Y`, both derived from
  `sym_boundary_factors` (and not from the cocycle relations of the bridge).

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial TensorProduct TernaryPoly.Paper GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FiberModel.SymBoundaryFactors

abbrev cPlus (A : Type*) [CommRing A] : Ternary A := (X 0 + X 1) * (X 0 + X 2) * (X 1 + X 2)
abbrev wcPlus (A : Type*) [CommRing A] : Ternary A := (X 0 + X 1 + X 2) * ((X 0 + X 1) * (X 0 + X 2) * (X 1 + X 2))

theorem map_cPlus : map (algebraMap ℚ ℂ) (cPlus ℚ) = cPlus ℂ := by simp [cPlus]
theorem map_wcPlus : map (algebraMap ℚ ℂ) (wcPlus ℚ) = wcPlus ℂ := by simp [wcPlus]

/-- **Lemma 2.2 over `ℂ`.** -/
theorem lemma_2_2_complex {n : ℕ} {f : Ternary ℂ} (hf : f ∈ symmetricSolutionSpace ℂ n) :
    cPlus ℂ ∣ f ∧ (0 < n → Even n → wcPlus ℂ ∣ f) := by
  obtain ⟨t, ht⟩ := (symmetricSolution_baseChangeEquiv ℂ n).surjective ⟨f, hf⟩
  have key : ∀ t : ℂ ⊗[ℚ] symmetricSolutionSpace ℚ n,
      cPlus ℂ ∣ (symmetricSolution_baseChangeEquiv ℂ n t).val ∧
      (0 < n → Even n → wcPlus ℂ ∣ (symmetricSolution_baseChangeEquiv ℂ n t).val) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a g =>
      rw [symmetricSolution_baseChangeEquiv_tmul]
      obtain ⟨hh, hsol⟩ := (mem_solutionSpace n g.val).mp g.2.1
      have hs : bind₁ (![X 1, X 0, X 2] : Fin 3 → Ternary ℚ) g.val = g.val := by
        have := g.2.2
        simpa [sub_eq_zero] using this
      have h22 : cPlus ℚ ∣ g.val ∧ (0 < n → Even n → wcPlus ℚ ∣ g.val) :=
        ⟨TernaryPoly.homogeneous_symmetric_pair_sum_product_dvd ⟨hsol.1, hsol.2⟩ hs hh,
          fun _ he => TernaryPoly.homogeneous_symmetric_total_pair_sum_product_dvd
            ⟨hsol.1, hsol.2⟩ hs hh he⟩
      refine ⟨?_, fun hn he => ?_⟩
      · rw [smul_eq_C_mul]
        refine Dvd.dvd.mul_left ?_ _
        have := map_dvd (MvPolynomial.map (algebraMap ℚ ℂ)) h22.1
        rwa [map_cPlus] at this
      · rw [smul_eq_C_mul]
        refine Dvd.dvd.mul_left ?_ _
        have := map_dvd (MvPolynomial.map (algebraMap ℚ ℂ)) (h22.2 hn he)
        rwa [map_wcPlus] at this
    | add x y hx hy =>
      rw [map_add, Submodule.coe_add]
      exact ⟨dvd_add hx.1 hy.1, fun hn he => dvd_add (hx.2 hn he) (hy.2 hn he)⟩
  have := key t
  rw [ht] at this
  exact this


open TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers Homogeneous

/-- The `SymmetricSolution` gives membership in `symmetricSolutionSpace ℂ n`. -/
theorem mem_symmetricSolutionSpace {n : ℕ} (f : HomogeneousPoly n) (hf : SymmetricSolution f) :
    f.val ∈ symmetricSolutionSpace ℂ n := by
  have hh : f.val.IsHomogeneous n := (MvPolynomial.mem_homogeneousSubmodule n f.val).mp f.2
  have hp : (fun i => X (finRotate 3 i) : Fin 3 → Ternary ℂ) = ![X 1, X 2, X 0] := by
    funext i; fin_cases i <;> simp
  have hc := hf.1 (finRotate 3)
  rw [hp] at hc
  have hsw : (fun i => X (Equiv.swap (0 : Fin 3) 1 i) : Fin 3 → Ternary ℂ) = ![X 1, X 0, X 2] := by
    funext i; fin_cases i <;> simp [Equiv.swap_apply_def]
  have hs := hf.1 (Equiv.swap 0 1)
  rw [hsw] at hs
  refine Submodule.mem_inf.mpr ⟨(mem_solutionSpace n _).mpr ⟨hh, hc, hf.2⟩, ?_⟩
  rw [LinearMap.mem_ker]
  simp [hs]

/-- **`lem:sym-boundary-factors` for the revision's symmetric solutions over `ℂ`.** -/
theorem sym_boundary_factors {n : ℕ} (f : HomogeneousPoly n) (hf : SymmetricSolution f) :
    cPlus ℂ ∣ f.val ∧ (0 < n → Even n → wcPlus ℂ ∣ f.val) :=
  lemma_2_2_complex (mem_symmetricSolutionSpace f hf)

/-- Opposite-pair vanishing: `f(c, -a, a) = 0` (the factor `y + z`). -/
theorem opposite_vanishing {n : ℕ} (f : HomogeneousPoly n) (hf : SymmetricSolution f) (a c : ℂ) :
    eval ![c, -a, a] f.val = 0 := by
  obtain ⟨g, hg⟩ := (sym_boundary_factors f hf).1
  rw [hg]
  simp

/-- Total-plane vanishing in positive even degree: `f(x, y, -x-y) = 0` (the factor `w`). -/
theorem total_vanishing {n : ℕ} (hn : 0 < n) (hev : Even n) (f : HomogeneousPoly n)
    (hf : SymmetricSolution f) (x y : ℂ) : eval ![x, y, -(x + y)] f.val = 0 := by
  obtain ⟨g, hg⟩ := (sym_boundary_factors f hf).2 hn hev
  rw [hg]
  simp

/-- **`J_f(0, Z) = 0`** ("`J_f(0,Z) = Z f(Z,-X,X) = 0` by the opposite-pair
vanishing"), from `sym_boundary_factors`. -/
theorem bernoulliObstruction_zero_Y {n : ℕ} (f : HomogeneousPoly n) (hf : SymmetricSolution f)
    (first third : ℂ) : polynomialValue (bernoulliObstruction f) first 0 third = 0 := by
  have parameter_zero : eval ![first, (0 : ℂ), third] (X (1 : Fin 3)) = 0 := by simp
  have evaluated := bernoulliOperator_eval_parameter_zero n (X 1)
    (bind₁ ![X 2 - 2 * X 1, -X 0, X 0 - X 1] f.val)
    ![first, 0, third] parameter_zero
  unfold polynomialValue bernoulliObstruction
  simp only [map_sub, map_mul, eval_X, Matrix.cons_val_two, Matrix.cons_val_one,
    Matrix.cons_val_zero, Matrix.vecHead, Matrix.vecTail, zero_mul, sub_zero]
  rw [evaluated]
  change third * polynomialValue (bind₁ ![X 2 - 2 * X 1, -X 0, X 0 - X 1] f.val) first 0 third = 0
  rw [polynomialValue_bind]
  have coordinates : (fun index => polynomialValue
      (![X 2 - 2 * X 1, -X 0, X 0 - X 1] index) first 0 third) = ![third, -first, first] := by
    funext index
    fin_cases index <;> simp [polynomialValue]
  rw [coordinates]
  change third * eval ![third, -first, first] f.val = 0
  rw [opposite_vanishing f hf first third, mul_zero]


theorem frame_vanishing {n : ℕ} (hn : 0 < n) (hev : Even n) (f : HomogeneousPoly n)
    (hf : SymmetricSolution f) (first second : ℂ) :
    polynomialValue (bind₁ ![X 2 - 2 * X 1, -X 0, X 0 - X 1] f.val) first second (3 * second) = 0 ∧
    polynomialValue (bind₁ ![X 2 - X 0, X 0 - 2 * X 1, -X 1] f.val) first second (3 * second) = 0 ∧
    polynomialValue (bind₁ ![X 2 - 2 * X 1, X 1 - X 0, X 0 - 2 * X 1] f.val)
      first second (3 * second) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [polynomialValue_bind]
    have coordinates : (fun index => polynomialValue
        (![X 2 - 2 * X 1, -X 0, X 0 - X 1] index) first second (3 * second)) =
          ![second, -first, first - second] := by
      funext index
      fin_cases index <;> simp [polynomialValue]
      ring
    rw [coordinates]
    have h := total_vanishing hn hev f hf second (-first)
    have hs : first - second = -(second + -first) := by ring
    rw [hs]; exact h
  · rw [polynomialValue_bind]
    have coordinates : (fun index => polynomialValue
        (![X 2 - X 0, X 0 - 2 * X 1, -X 1] index) first second (3 * second)) =
          ![3 * second - first, first - 2 * second, -second] := by
      funext index
      fin_cases index <;> simp [polynomialValue]
    rw [coordinates]
    have h := total_vanishing hn hev f hf (3 * second - first) (first - 2 * second)
    have hs : -second = -((3 * second - first) + (first - 2 * second)) := by ring
    change eval ![3 * second - first, first - 2 * second, -second] f.val = 0
    rw [hs]; exact h
  · rw [polynomialValue_bind]
    have coordinates : (fun index => polynomialValue
        (![X 2 - 2 * X 1, X 1 - X 0, X 0 - 2 * X 1] index) first second (3 * second)) =
          ![second, second - first, first - 2 * second] := by
      funext index
      fin_cases index <;> simp [polynomialValue]
      ring
    rw [coordinates]
    have h := total_vanishing hn hev f hf second (second - first)
    have hs : first - 2 * second = -(second + (second - first)) := by ring
    change eval ![second, second - first, first - 2 * second] f.val = 0
    rw [hs]; exact h

/-- **`J_f(Y, 3Y) = 0` for even `n`** (odd `d = n + 1`;: "Lemma 2.2 gives `w ∣ f`.
All three frames have sum `Z - 3Y`, so `J_f(Y,3Y) = 0`"), from `sym_boundary_factors`. -/
theorem bernoulliObstruction_three_Y {n : ℕ} (hn : 0 < n) (hev : Even n) (f : HomogeneousPoly n)
    (hf : SymmetricSolution f) (first second : ℂ) :
    polynomialValue (bernoulliObstruction f) first second (3 * second) = 0 := by
  have first_operator := bernoulliOperator_eval_zero_of_line_zero n (X 1)
    (bind₁ ![X 2 - 2 * X 1, -X 0, X 0 - X 1] f.val) second (3 * second)
    (fun point => (frame_vanishing hn hev f hf point second).1) first
  have second_operator := bernoulliOperator_eval_zero_of_line_zero n (X 2)
    (bind₁ ![X 2 - 2 * X 1, -X 0, X 0 - X 1] f.val -
      bind₁ ![X 2 - X 0, X 0 - 2 * X 1, -X 1] f.val +
      bind₁ ![X 2 - 2 * X 1, X 1 - X 0, X 0 - 2 * X 1] f.val)
    second (3 * second) (by
      intro point
      obtain ⟨a, b, c⟩ := frame_vanishing hn hev f hf point second
      change eval ![point, second, 3 * second] _ = 0
      simp only [map_add, map_sub]
      change polynomialValue _ point second (3 * second) -
        polynomialValue _ point second (3 * second) +
        polynomialValue _ point second (3 * second) = 0
      rw [a, b, c]
      ring) first
  unfold bernoulliObstruction
  change eval ![first, second, 3 * second] _ = 0
  simp only [map_sub, map_mul, eval_X, Matrix.cons_val_two, Matrix.cons_val_one]
  change 3 * second * polynomialValue _ first second (3 * second) -
    second * polynomialValue _ first second (3 * second) = 0
  rw [first_operator, second_operator]
  ring

end TernaryPeriodPolynomials.Argument.FiberModel.SymBoundaryFactors
