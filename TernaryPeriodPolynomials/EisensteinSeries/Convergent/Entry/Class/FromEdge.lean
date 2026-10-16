module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.SourceQuotient
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.RationalComparison

@[expose] public section


/-!
# Classes of sources that differ by an edge coboundary

`sourceToSummand_eq_of_edge`: two source cocycles whose difference is the coboundary `δB` of an edge cochain
`B(y₀, y₁)(g)` that is covariant under `GL₃(ℝ)`, invariant under the finite level and under the rational parabolic of
the side, have the same class in `StratumH2`.  The edge cochain evaluates, on rational flags, to a `1`-cochain of
`rationalLevel` (the flag independence is the rational parabolic invariance), whose coboundary is the difference of
the evaluated cocycles.

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

/-- **A source cocycle that differs from another by the coboundary of an edge cochain with the induced laws has the
same class.**  The laws of `B` are: covariance under `GL₃(ℝ)` (`hE2`), invariance under the finite level (`hE3`) and
under the rational parabolic of the side (`hE4`); they make `B` evaluate to a `1`-cochain of `rationalLevel` on the
rational flags, whose coboundary is the difference of the evaluated cocycles. -/
theorem sourceToSummand_eq_of_edge {n : ℕ} (D : InducingData n) (side : Side)
    (c c' : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly n)
    (hc : IsSourceCocycle D side c) (hc' : IsSourceCocycle D side c')
    (B : (Fin 2 → RealGL3) → AdelicGL → HomogeneousPoly n)
    (hE0 : ∀ y g, c y g - c' y g = B ![y 1, y 2] g - B ![y 0, y 2] g + B ![y 0, y 1] g)
    (hE2 : ∀ (h : RealGL3) y g, B (fun i => h * y i) g =
      realCoefficientComponent n D.chi h (B y (g * atInfinity h)))
    (hE3 : ∀ (k : finiteLevel) y g, B y (g * atFinite k.val) = B y g)
    (hE4 : ∀ p : RationalGL3, p ∈ parabolic side → ∀ y g, B y (rationalGroup p * g) = B y g) :
    SourceQuotient.sourceToSummand D side ⟨c, hc⟩ = SourceQuotient.sourceToSummand D side ⟨c', hc'⟩ := by
  set χ := D.chi with hχdef
  let rB : (Fin 2 → RationalGL3) → RationalGL3 → HomogeneousPoly n := fun v q =>
    B (fun i => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (v i)) (rationalGroup q⁻¹)
  have hind : ∀ v first second, first⁻¹ * second ∈ parabolic side → rB v first = rB v second := by
    intro v first second related
    have inverseRelated : (first⁻¹ * second)⁻¹ ∈ parabolic side := (parabolic side).inv_mem related
    have invariant := hE4 ((first⁻¹ * second)⁻¹) inverseRelated
      (fun i => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (v i)) (rationalGroup first⁻¹)
    have argEq : rationalGroup ((first⁻¹ * second)⁻¹) * rationalGroup first⁻¹ = rationalGroup second⁻¹ := by
      rw [← map_mul, _root_.mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel, mul_one]
    rw [argEq] at invariant
    exact invariant.symm
  have heq : ∀ (γ : rationalLevel) (v : Fin 2 → RationalGL3) (q : RationalGL3),
      rB (fun i => γ.val * v i) q =
        rationalCoefficientComponent n χ γ.val (rB v (γ.val⁻¹ * q)) := by
    intro γ v q
    have vEq : (fun i => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (γ.val * v i)) =
        fun i => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) γ.val *
          Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (v i) := funext fun i => map_mul _ _ _
    show B (fun i => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (γ.val * v i)) (rationalGroup q⁻¹) =
      realCoefficientComponent n χ (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) γ.val)
        (B (fun i => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (v i)) (rationalGroup (γ.val⁻¹ * q)⁻¹))
    rw [vEq, hE2]
    congr 1
    rw [_root_.mul_inv_rev, inv_inv, map_mul, Comparison.rationalGroup_split γ.val, ← mul_assoc]
    exact (hE3 ⟨rationalFinite γ.val, Comparison.rationalLevel_finiteLevel γ⟩ _ _).symm
  let b : cochains rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) side) 1 :=
    ⟨fun v flag => Quotient.liftOn' flag (rB v)
      (fun first second related => hind v first second (QuotientGroup.leftRel_apply.mp related)), by
      intro γ v
      funext flag
      induction flag using Quotient.inductionOn with
      | h q => exact heq γ v q⟩
  have hb : (boundaryMap rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) side) b) =
      SourceSpace.evaluatedSource D side ⟨c, hc⟩ - SourceSpace.evaluatedSource D side ⟨c', hc'⟩ := by
    apply Subtype.ext
    apply Subtype.ext
    funext v flag
    induction flag using Quotient.inductionOn with
    | h q =>
      have h1 := SourceSpace.evaluatedSource_realizes D side ⟨c, hc⟩ v q
      have h2 := SourceSpace.evaluatedSource_realizes D side ⟨c', hc'⟩ v q
      have pairEq : ∀ first second : RationalGL3,
          (fun i => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) ((![first, second] : Fin 2 → RationalGL3) i)) =
          ![Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) first,
            Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) second] := by
        intro first second
        funext i
        fin_cases i <;> rfl
      have hE := hE0 (fun i => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (v i)) (rationalGroup q⁻¹)
      change (rB ![v 1, v 2] q - rB ![v 0, v 2] q + rB ![v 0, v 1] q) = _
      simp only [rB, pairEq]
      change _ = (SourceSpace.evaluatedSource D side ⟨c, hc⟩).val.val v (QuotientGroup.mk q) -
        (SourceSpace.evaluatedSource D side ⟨c', hc'⟩).val.val v (QuotientGroup.mk q)
      rw [h1, h2, hE]
  apply Subtype.ext
  show classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) side)
      (SourceSpace.evaluatedSource D side ⟨c, hc⟩) =
    classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) side)
      (SourceSpace.evaluatedSource D side ⟨c', hc'⟩)
  rw [← sub_eq_zero, ← map_sub, ← hb]
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨b, rfl⟩

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
