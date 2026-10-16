module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.DerivativeEdge
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.LatticeComparisonAlgebra

@[expose] public section


/-!
# The corrected radical edge of the real good-line stabilizer and its derivative

Let `t` be a two-cochain of `LineGroup = ℝ² ⋊ SL₂^±(ℝ)` with values in scalar tests and let
`a : ℝ² → LineValues n` be a family of linear tests. For a Levi element `m` the corrected radical
edge is `g_m(Y) = t(m, e^{Y m}) - t(e^Y, m) - (m • a(Y m) - a(Y))`. If `t` restricted to the
radical is the coboundary of `a`, then `g_m` is a crossed homomorphism of the radical. If `t` is
regular along the radical and `a` is differentiable at `0`, the lower radical coordinate of the
derivative of `g_m` at `0` is `Ẽ(m) - (m ⋆ A - A)`, where `Ẽ` is the derivative edge and `A` is the
lower radical coordinate of the derivative of `a` at `0`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EdgeControl

variable {n : ℕ}

/-- The corrected radical edge `Y ↦ t(m, e^{Y m}) - t(e^Y, m) - (m • a(Y m) - a(Y))`. -/
def leviCorrectedEdge (t : LineGroup → LineGroup → LineValues n)
    (a : (Fin 2 → ℝ) → LineValues n) (m : unimodularLevi) (Y : Fin 2 → ℝ) : LineValues n :=
  radicalEdge t m Y - (lineLeviElement m • a (rowAction m Y) - a Y)

/-- The lower radical coordinate of the derivative at `0` of a family of linear tests. -/
def radicalDerivativeCoordinate (a : (Fin 2 → ℝ) → LineValues n) :
    BinaryAdelicGL → Binary.HomogeneousPoly (n + 1) :=
  fun h => lowerRadicalCoordinate n
    (fun i => lineVector (fun p => fderiv ℝ (fun Y => a Y p) 0 (Pi.single i 1)) h)

/-- One axis component of the derivative at `0` of a family of tests. -/
def radicalDerivativeComponent (a : (Fin 2 → ℝ) → LineValues n) (k : Fin 2) : LineValues n :=
  fun p => fderiv ℝ (fun Y => a Y p) 0 (Pi.single k 1)

theorem lineRadicalElement_add (Y Y' : Fin 2 → ℝ) :
    lineRadicalElement (Y + Y') = lineRadicalElement Y * lineRadicalElement Y' :=
  map_mul SemidirectProduct.inl (Multiplicative.ofAdd Y) (Multiplicative.ofAdd Y')

/-- The corrected radical edge is the corrected mixed edge function of a group cochain. -/
theorem leviCorrectedEdge_eq_correctedEdgeFunction (t : LineGroup → LineGroup → LineValues n)
    (a : (Fin 2 → ℝ) → LineValues n) (m : unimodularLevi) (Y : Fin 2 → ℝ) :
    leviCorrectedEdge t a m Y = correctedEdgeFunction t (fun q => a q.left.toAdd)
      (lineLeviElement m) (lineRadicalElement Y) := by
  unfold leviCorrectedEdge correctedEdgeFunction
  rw [lineLevi_conj_radical]
  rfl

/-- **The corrected radical edge is a crossed homomorphism of the radical** when `t` is the
coboundary of `a` on the radical. -/
theorem leviCorrectedEdge_add {t : LineGroup → LineGroup → LineValues n}
    (cocycle : IsTwoCocycle t) {a : (Fin 2 → ℝ) → LineValues n}
    (trivial : ∀ Y Y', t (lineRadicalElement Y) (lineRadicalElement Y') =
      lineRadicalElement Y • a Y' - a (Y + Y') + a Y) (m : unimodularLevi) (Y Y' : Fin 2 → ℝ) :
    leviCorrectedEdge t a m (Y + Y') =
      leviCorrectedEdge t a m Y + lineRadicalElement Y • leviCorrectedEdge t a m Y' := by
  simp only [leviCorrectedEdge_eq_correctedEdgeFunction, lineRadicalElement_add]
  apply correctedEdgeFunction_mul_of_pairs cocycle
  · rw [← lineRadicalElement_add]
    exact trivial Y Y'
  · rw [lineLevi_conj_radical, lineLevi_conj_radical, ← lineRadicalElement_add]
    exact trivial _ _

/-- The derivative components of the corrected radical edge. -/
theorem leviCorrectedEdge_component {t : LineGroup → LineGroup → LineValues n}
    (regular : EdgeRegular t) {a : (Fin 2 → ℝ) → LineValues n}
    (differentiable : ∀ p, DifferentiableAt ℝ (fun Y => a Y p) 0) (m : unimodularLevi)
    (i : Fin 2) (p : BinaryAdelicGL × (HomogeneousPoly n →ₗ[ℂ] ℂ)) :
    fderiv ℝ (fun Y => leviCorrectedEdge t a m Y p) 0 (Pi.single i 1) =
      edgeComponent t m i p - (∑ k, (((m : BinaryRealGL).val i k : ℝ) : ℂ) *
        (lineLeviElement m • radicalDerivativeComponent a k) p -
          fderiv ℝ (fun Y => a Y p) 0 (Pi.single i 1)) := by
  set φ : BinaryAdelicGL × (HomogeneousPoly n →ₗ[ℂ] ℂ) →
      BinaryAdelicGL × (HomogeneousPoly n →ₗ[ℂ] ℂ) :=
    fun q => (q.1 * atInfinity (pivotConjugate ((lineLeviElement m).right : BinaryRealGL)),
      q.2 ∘ₗ realCoefficientComponent n trivialCharacter (lineMatrix (lineLeviElement m)))
  have moved (F : LineValues n) : (lineLeviElement m • F) p = F (φ p) := rfl
  have edge : HasFDerivAt (fun Y => radicalEdge t m Y p) (radicalEdgeDerivative t m p) 0 :=
    (regular.edge_differentiable m p).hasFDerivAt
  have shifted : HasFDerivAt (fun Y => a (rowAction m Y) (φ p))
      ((fderiv ℝ (fun Y => a Y (φ p)) 0).comp (rowAction m)) 0 := by
    have outer : HasFDerivAt (fun Y => a Y (φ p)) (fderiv ℝ (fun Y => a Y (φ p)) 0)
        (rowAction m 0) := by
      rw [map_zero]
      exact (differentiable (φ p)).hasFDerivAt
    exact outer.comp (0 : Fin 2 → ℝ) (rowAction m).hasFDerivAt
  have whole : HasFDerivAt (fun Y => leviCorrectedEdge t a m Y p)
      (radicalEdgeDerivative t m p - ((fderiv ℝ (fun Y => a Y (φ p)) 0).comp (rowAction m) -
        fderiv ℝ (fun Y => a Y p) 0)) 0 :=
    edge.sub (shifted.sub (differentiable p).hasFDerivAt)
  rw [whole.fderiv]
  simp only [_root_.sub_apply, ContinuousLinearMap.comp_apply, rowAction_single, map_sum,
    map_smul, Complex.real_smul]
  rfl

/-- One axis component of the derivative of the corrected radical edge at `0`. -/
def correctedEdgeComponent (t : LineGroup → LineGroup → LineValues n)
    (a : (Fin 2 → ℝ) → LineValues n) (m : unimodularLevi) (i : Fin 2) : LineValues n :=
  fun p => fderiv ℝ (fun Y => leviCorrectedEdge t a m Y p) 0 (Pi.single i 1)

/-- **Derivative of the corrected radical edge.** -/
theorem leviCorrectedEdge_derivative {t : LineGroup → LineGroup → LineValues n}
    (regular : EdgeRegular t) {a : (Fin 2 → ℝ) → LineValues n} (linear : ∀ Y, LinearTests (a Y))
    (differentiable : ∀ p, DifferentiableAt ℝ (fun Y => a Y p) 0) (m : unimodularLevi)
    (h : BinaryAdelicGL) :
    lowerRadicalCoordinate n (fun i => lineVector
        (fun p => fderiv ℝ (fun Y => leviCorrectedEdge t a m Y p) 0 (Pi.single i 1)) h) =
      derivativeEdge t m h -
        (edgeAction m (radicalDerivativeCoordinate a) h - radicalDerivativeCoordinate a h) := by
  set h' := h * atInfinity (pivotConjugate (m : BinaryRealGL))
  set C := realCoefficientComponent n trivialCharacter (planeLevi (m : BinaryRealGL) 1)
  have derivativeLinear (k : Fin 2) : LinearTests (radicalDerivativeComponent a k) :=
    linearTests_fderiv linear differentiable (Pi.single k 1)
  change lowerRadicalCoordinate n (fun i => lineVector (correctedEdgeComponent t a m i) h) = _
  have vector (i : Fin 2) : lineVector (correctedEdgeComponent t a m i) h =
      lineVector (edgeComponent t m i) h -
        (∑ k, (((m : BinaryRealGL).val i k : ℝ) : ℂ) •
          C (lineVector (radicalDerivativeComponent a k) h') -
            lineVector (radicalDerivativeComponent a i) h) := by
    apply (homogeneousBasis n).ext_elem
    intro j
    rw [← Module.Basis.coord_apply, ← Module.Basis.coord_apply, coord_lineVector]
    change fderiv ℝ (fun Y => leviCorrectedEdge t a m Y _) 0 (Pi.single i 1) = _
    rw [leviCorrectedEdge_component regular differentiable m i, map_sub, map_sub, map_sum,
      coord_lineVector, coord_lineVector]
    simp_rw [lineLeviElement_smul_apply m (derivativeLinear _), map_smul, smul_eq_mul]
    rfl
  have pairs : (fun i => lineVector (correctedEdgeComponent t a m i) h) =
      (fun i => lineVector (edgeComponent t m i) h) -
        ((fun i => ∑ k, (((m : BinaryRealGL).val i k : ℝ) : ℂ) •
          C (lineVector (radicalDerivativeComponent a k) h')) -
            fun i => lineVector (radicalDerivativeComponent a i) h) := by
    funext i
    rw [vector]
    rfl
  rw [pairs, map_sub, map_sub, lowerRadicalCoordinate_levi]
  rfl

end TernaryPeriodPolynomials.AnalyticClasses
