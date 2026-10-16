module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.TransferOrthogonal
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.NormalCocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Eichler.RegularityNormal

@[expose] public section


/-!
# The derivative edge along the diagonal flow: the objects

The derivative edge `Ẽ` of the real good-line transfer of the Eichler normal form and the
transported twisted normal form `edgeNormal` are one-cocycles of `SL₂^±(ℝ)` for the same action,
and both vanish on orthogonal elements. By the Cartan decomposition they agree up to a constant as
soon as their derivatives along the diagonal flow `a(s) = diag(eˢ, e⁻ˢ)` agree up to that
constant. This file fixes the objects of that comparison: the diagonal flow, the analytic
hypotheses on the scalar form `F`, the pointwise edge section whose mixed derivative is the
integrand of `d/ds Ẽ(a(s))|₀`, and the velocity of `edgeNormal` along the flow.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

/-! ### The diagonal flow -/

/-- The matrix `diag(eˢ, e⁻ˢ)`. -/
def diagonalFlowMatrix (s : ℝ) : BinaryRealGL :=
  ⟨!![Real.exp s, 0; 0, Real.exp (-s)], !![Real.exp (-s), 0; 0, Real.exp s], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [← Real.exp_add], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [← Real.exp_add]⟩

theorem diagonalFlowMatrix_val (s : ℝ) :
    (diagonalFlowMatrix s).val = !![Real.exp s, 0; 0, Real.exp (-s)] := rfl

theorem det_diagonalFlowMatrix (s : ℝ) : (diagonalFlowMatrix s).val.det = 1 := by
  rw [diagonalFlowMatrix_val, Matrix.det_fin_two_of, mul_zero, sub_zero, ← Real.exp_add,
    add_neg_cancel, Real.exp_zero]

/-- **The diagonal flow** `a(s) = diag(eˢ, e⁻ˢ)` in `SL₂^±(ℝ)`. -/
def diagonalFlow (s : ℝ) : unimodularLevi :=
  ⟨diagonalFlowMatrix s, by
    change |(diagonalFlowMatrix s).val.det| = 1
    rw [det_diagonalFlowMatrix, abs_one]⟩

theorem diagonalFlow_add (s t : ℝ) : diagonalFlow (s + t) = diagonalFlow s * diagonalFlow t := by
  apply Subtype.ext
  apply Units.ext
  change !![Real.exp (s + t), 0; 0, Real.exp (-(s + t))] =
    !![Real.exp s, 0; 0, Real.exp (-s)] * !![Real.exp t, 0; 0, Real.exp (-t)]
  rw [Matrix.mul_fin_two]
  simp [Real.exp_add, mul_comm]

theorem diagonalFlow_zero : diagonalFlow 0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  change !![Real.exp 0, 0; 0, Real.exp (-0)] = 1
  rw [neg_zero, Real.exp_zero, Matrix.one_fin_two]

/-! ### Analytic hypotheses on the scalar form -/

/-- The analytic data of a scalar form `F h z` of weight `n + 3`: holomorphic in `z`, modular for
right translation by `SL₂(ℝ)`, invariant under positive scalars, and bounded on compact subsets of
the upper half plane uniformly in `h`. -/
structure EichlerData (n : ℕ) (F : BinaryAdelicGL → ℂ → ℂ) : Prop where
  holomorphic : ∀ h, DifferentiableOn ℂ (F h) {z : ℂ | 0 < z.im}
  modular : ∀ A : BinaryRealGL, A.val.det = 1 → ∀ h (z : UpperHalfPlane),
    F (h * atInfinity A) z = UpperHalfPlane.denom A z ^ (-((n : ℤ) + 3)) * F h (A • z : _)
  central : ∀ c : ℝˣ, 0 < c.val → ∀ h z,
    F (h * atInfinity (GeneralLinearGroup.scalar (Fin 2) c)) z = F h z
  bounded : ∀ K ⊆ {z : ℂ | 0 < z.im}, IsCompact K → ∃ C, ∀ h, ∀ w ∈ K, ‖F h w‖ ≤ C

/-! ### The pointwise edge section and its mixed derivative -/

/-- The integrand of the radical edge function `Y ↦ t(a(s), a(s)⁻¹ e^Y a(s)) - t(e^Y, a(s))` of the
real transfer `t` of `N`, along the axis `Y = r eᵢ`, at the good-line coordinate `u`. -/
def edgeSection (N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (u : ℝ × ℝ) (i : Fin 2) (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (s r : ℝ) : ℂ :=
  functional (relativeIntegrand N u (lineLeviElement (diagonalFlow s))
      (lineRadicalElement (r • Pi.single i 1) * lineLeviElement (diagonalFlow s)) h) -
    functional (relativeIntegrand N u (lineRadicalElement (r • Pi.single i 1))
      (lineRadicalElement (r • Pi.single i 1) * lineLeviElement (diagonalFlow s)) h)

/-- The mixed derivative `∂ₛ ∂ᵣ` at `(0, 0)` of the edge section. -/
def edgeMixed (N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (u : ℝ × ℝ) (i : Fin 2) (h : BinaryAdelicGL) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) : ℂ :=
  deriv (fun s => deriv (fun r => edgeSection N u i h functional s r) 0) 0

/-- The integrated mixed derivative, as scalar tests. -/
def edgeMixedIntegral (N : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (i : Fin 2) : LineValues n :=
  fun p => ∫ u, edgeMixed N u i p.1 p.2 ∂((volume : Measure ℝ).prod volume)

/-! ### The velocity of the transported twisted normal form -/

/-- The velocity of `edgeNormal F (a(s)) h` at `s = 0`: since `σ a(s) σ · i = e^{-2s} i`, it is
`Sw(-i F_h(i) P(i) + i · J ⋆ (F(i) P(i))(h))` with `P(z) = binaryPointPower (n + 1) z`. -/
def edgeNormalVelocity (n : ℕ) (F : BinaryAdelicGL → ℂ → ℂ) (h : BinaryAdelicGL) :
    Binary.HomogeneousPoly (n + 1) :=
  binarySwap n (-Complex.I • (F h Complex.I • binaryPointPower (n + 1) Complex.I) +
    Complex.I • binaryAmbientRepresentation n UpperHalfPlane.J
      (fun h' => F h' Complex.I • binaryPointPower (n + 1) Complex.I) h)

end TernaryPeriodPolynomials.AnalyticClasses
