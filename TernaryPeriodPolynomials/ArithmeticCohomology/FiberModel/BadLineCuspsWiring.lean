module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.BadLineCusps
public import TernaryPeriodPolynomials.Building.BoundaryApartments
public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.SymBoundaryFactors

@[expose] public section


/-!
# The literal cusp argument applied to the library's `J_f` (wiring for Proposition 4.2)

Proof of
`lem:bad-line-coordinate` and Proposition 4.2 (`thm:J-vanishes`).

`BadLineCusps` proves the paper's binary-quotient/cusp argument for any binary form `J` satisfying
the finite-group relations of the positive cocycle (`BadLineRelations`).  The library's proof of
`symmetric_obstruction_vanishes` (`TernaryPeriodPolynomials.Argument.Classification.Prop42`, through `PolynomialBoundaryBridge`) establishes the same
relations for `J_f = bernoulliObstruction f` inside its own model (`bernoulliObstruction_A_norm`,
`bernoulliObstruction_BA_relation`, `upperCuspCoordinate_reflection_relation`,
`bernoulliObstruction_upperCusp_all`, `bernoulliObstruction_goodBoundary`).  This file transports
those facts to the two-variable binary form `J_f(Y, Z)` and applies the literal argument:
for every symmetric solution `f` of positive degree `n`, with `d = n + 1`,

* `J_f` satisfies `BadLineRelations ℂ d J_f` (the relations of the paper);
* the upper cusp restriction vanishes (`J_f + A J_f = Q - T Q` for a degree-`d` form `Q`);
* detection: if the cocycle with values `J_f, 0, 0` on `A₀, B₀, R₀` is a coboundary `(1 - g) m` of
  a degree-`d` form `m`, then `J_f = 0`.

`J_f(Y,3Y) = 0` (even `n`, i.e. odd `d`) and `J_f(0,Z) = 0` are proved from `lem:sym-boundary-factors`
(`SymBoundaryFactors.bernoulliObstruction_three_Y`, `bernoulliObstruction_zero_Y`), not from the
bridge.  This does not replace or edit the proofs of `symmetric_obstruction_vanishes` and `line_restriction_eq_zero_of_good_vertices`; it shows that
the library's `J_f` satisfies exactly the hypotheses of the paper-literal argument.

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial GeneralEisenstein
open TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
open TernaryPeriodPolynomials.Argument.FiberModel
open TernaryPeriodPolynomials.Argument.FiberModel.BadLineCusps

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FiberModel.BadLineCuspsWiring

/-- The binary image of a ternary polynomial: `X₀ ↦ 0`, `X₁ ↦ Y`, `X₂ ↦ Z`. -/
def toBinary : MvPolynomial (Fin 3) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ := bind₁ ![0, X 0, X 1]

theorem eval_toBinary (P : MvPolynomial (Fin 3) ℂ) (y z : ℂ) :
    eval ![y, z] (toBinary P) = eval ![0, y, z] P := by
  unfold toBinary
  have := eval₂Hom_bind₁ (RingHom.id ℂ) ![y, z] ![0, X 0, X 1] P
  change eval ![y, z] _ = _ at this ⊢
  rw [this]
  have hc : (fun i => (eval₂Hom (RingHom.id ℂ) ![y, z])
      ((![0, X 0, X 1] : Fin 3 → MvPolynomial (Fin 2) ℂ) i)) = ![0, y, z] := by
    funext i; fin_cases i <;> simp
  rw [hc]; rfl

theorem toBinary_homog {d : ℕ} {P : MvPolynomial (Fin 3) ℂ} (hP : P.IsHomogeneous d) :
    (toBinary P).IsHomogeneous d := by
  have := hP.aeval (n := 1) (![0, X (0 : Fin 2), X 1] : Fin 3 → MvPolynomial (Fin 2) ℂ)
    (fun i => by
      fin_cases i
      · exact isHomogeneous_zero _ _ _
      · exact isHomogeneous_X ℂ _
      · exact isHomogeneous_X ℂ _)
  simpa [toBinary, one_mul] using this

private theorem funext_vec {Q R : MvPolynomial (Fin 2) ℂ}
    (h : ∀ y z : ℂ, eval ![y, z] Q = eval ![y, z] R) : Q = R := by
  apply MvPolynomial.funext
  intro v
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [hv]; exact h _ _

private theorem eval3_congr {u w : Fin 3 → ℂ} (h : u = w) (P : MvPolynomial (Fin 3) ℂ) :
    eval u P = eval w P := by rw [h]

theorem toBinary_A (P : MvPolynomial (Fin 3) ℂ) :
    toBinary (binarySubstitutionA P) = repG ℂ a0 (toBinary P) := by
  apply funext_vec
  intro y z
  rw [eval_toBinary, eval_repG_a0, eval_toBinary]
  change polynomialValue (binarySubstitutionA P) 0 y z = _
  unfold binarySubstitutionA
  rw [polynomialValue_bind]
  refine eval3_congr ?_ P
  funext i; fin_cases i <;> simp [polynomialValue]

theorem toBinary_B (P : MvPolynomial (Fin 3) ℂ) :
    toBinary (binarySubstitutionB P) = repG ℂ b0 (toBinary P) := by
  apply funext_vec
  intro y z
  rw [eval_toBinary, eval_repG_b0, eval_toBinary]
  change polynomialValue (binarySubstitutionB P) 0 y z = _
  unfold binarySubstitutionB
  rw [polynomialValue_bind]
  refine eval3_congr ?_ P
  funext i; fin_cases i <;> simp [polynomialValue]

theorem toBinary_R (P : MvPolynomial (Fin 3) ℂ) :
    toBinary (binarySubstitutionR P) = repG ℂ r0 (toBinary P) := by
  apply funext_vec
  intro y z
  rw [eval_toBinary, eval_repG_r0, eval_toBinary]
  change polynomialValue (binarySubstitutionR P) 0 y z = _
  unfold binarySubstitutionR
  rw [polynomialValue_bind]
  refine eval3_congr ?_ P
  funext i; fin_cases i <;> simp [polynomialValue]

theorem toBinary_T (P : MvPolynomial (Fin 3) ℂ) :
    toBinary (upperTranslationPolynomial P) = repG ℂ t0 (toBinary P) := by
  apply funext_vec
  intro y z
  rw [eval_toBinary, repG_t0, eval_shearY, eval_toBinary]
  change polynomialValue (upperTranslationPolynomial P) 0 y z = _
  unfold upperTranslationPolynomial
  rw [polynomialValue_bind]
  refine eval3_congr ?_ P
  funext i; fin_cases i <;> simp [polynomialValue]

/-- **The library's `J_f` satisfies the relations of the paper's binary-quotient argument** and
the two vanishing inputs `J_f(Y, 3Y) = 0`, `J_f(0, Z) = 0`. -/
theorem relations_of_symmetricSolution (n : ℕ) (hn : 0 < n) (f : HomogeneousPoly n)
    (hf : SymmetricSolution f) :
    BadLineRelations ℂ (n + 1) (toBinary (bernoulliObstruction f)) ∧
      (Even n → eval ![1, 3] (toBinary (bernoulliObstruction f)) = 0) ∧
      eval ![0, 1] (toBinary (bernoulliObstruction f)) = 0 := by
  have hF := polynomialEdgeFunctional_property hf
  have hreal := pathCocycle_realizes hF specialPaths_isPathFamily
  have cube3 := bernoulliObstruction_A_norm hn hF hreal
  have refl3 := bernoulliObstruction_BA_relation hn hF hreal
  have rt3 := upperCuspCoordinate_reflection_relation hn hF hreal
  rw [mixedBernoulliCoordinate_upperCusp hn hF hreal] at rt3
  refine ⟨⟨toBinary_homog (bernoulliObstruction_homogeneous f), ?_, ?_, ?_⟩, ?_, ?_⟩
  · have := congrArg toBinary cube3
    simpa only [map_add, map_zero, toBinary_A] using this
  · have := congrArg toBinary refl3
    simpa only [map_add, toBinary_A, toBinary_B] using this
  · have := congrArg toBinary rt3
    simp only [map_neg, map_add, toBinary_A, toBinary_R, toBinary_T] at this
    exact neg_eq_iff_eq_neg.mp (by simpa using this)
  · intro hev
    have h := SymBoundaryFactors.bernoulliObstruction_three_Y hn hev f hf 0 1
    rw [eval_toBinary]
    simpa [polynomialValue] using h
  · have h := SymBoundaryFactors.bernoulliObstruction_zero_Y f hf 0 1
    rw [eval_toBinary]
    simpa [polynomialValue] using h

/-- **Proposition 4.2, cusp-restriction and detection steps, literally**, for the
library's `J_f`: the upper cusp restriction vanishes in every parity, and if the cocycle with values
`J_f, 0, 0` is a coboundary then `J_f = 0`. -/
theorem prop_4_2_cusp_argument (n : ℕ) (hn : 0 < n) (f : HomogeneousPoly n)
    (hf : SymmetricSolution f) :
    BadLineRelations ℂ (n + 1) (toBinary (bernoulliObstruction f)) ∧
    (∃ Q : MvPolynomial (Fin 2) ℂ, Q.IsHomogeneous (n + 1) ∧
      toBinary (bernoulliObstruction f) + repG ℂ a0 (toBinary (bernoulliObstruction f)) =
        Q - repG ℂ t0 Q) ∧
    (∀ m : MvPolynomial (Fin 2) ℂ, m.IsHomogeneous (n + 1) →
      toBinary (bernoulliObstruction f) = m - repG ℂ a0 m → repG ℂ b0 m = m →
        repG ℂ r0 m = m → toBinary (bernoulliObstruction f) = 0) := by
  obtain ⟨hR, h3, h0⟩ := relations_of_symmetricSolution n hn f hf
  refine ⟨hR, hR.upper_cusp (fun hodd => h3 (by simpa [Nat.odd_add_one, Nat.not_odd_iff_even] using hodd)), ?_⟩
  intro m hm hJ hB hRm
  exact detection (by omega) hm hJ hB hRm h0

end TernaryPeriodPolynomials.Argument.FiberModel.BadLineCuspsWiring
