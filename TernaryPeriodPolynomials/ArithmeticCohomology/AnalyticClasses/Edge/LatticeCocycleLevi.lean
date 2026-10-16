module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.LatticeCocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.StabilizerEdge

@[expose] public section


/-!
# The integral Levi action at the identity and the lattice edge cocycle

At the identity adelic point, the real Levi action `(m ⋆ X)(h) = det m · binaryCoefficient m
(X(h · σ m σ))` of an integral Levi element `γ ∈ GL₂(ℤ)` on a function `X` that is invariant
under `σ γ σ` at infinity is the action of `γ` on `Sym^{n+1}` without determinant twist: the
determinant cancels the twist `det⁻¹` of the plane Levi coefficient. Consequently, if the
primitive `a` of the radical restriction of a regular two-cocycle `t` is invariant under the
integral Levi at infinity, the lower radical coordinates of the lattice edge cocycles at the
identity are `3` times the derivative edge of `t`, up to a one-coboundary of `GL₂(ℤ)` acting on
`Sym^{n+1}` without determinant twist.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

/-! ### The determinant cancels the plane Levi twist -/

/-- **The determinant cancels the twist of the plane Levi coefficient.** -/
theorem det_smul_binaryCoefficient (m : BinaryRealGL) (P : Binary.HomogeneousPoly (n + 1)) :
    ((m.val.det : ℝ) : ℂ) • binaryCoefficient n m P =
      Binary.homogeneousAction (n + 1) 0 (GeneralLinearGroup.map (algebraMap ℝ ℂ) m) P := by
  have determinant : ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℝ ℂ) m) :
      ℂˣ) : ℂ) = ((m.val.det : ℝ) : ℂ) := by
    rw [GeneralLinearGroup.val_det_apply]
    change ((algebraMap ℝ ℂ).mapMatrix m.val).det = _
    rw [← RingHom.map_det]
    rfl
  have nonzero : ((m.val.det : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr ((Matrix.isUnit_iff_isUnit_det _).mp m.isUnit).ne_zero
  apply Subtype.ext
  simp only [binaryCoefficient, SetLike.val_smul, Binary.homogeneousAction_coe,
    Binary.action_apply, Binary.determinantCharacter, MonoidHom.coe_mk, OneHom.coe_mk,
    determinant, smul_smul, _root_.zpow_neg_one, zpow_zero]
  rw [mul_inv_cancel₀ nonzero]

theorem map_integralLevi (γ : GeneralLinearGroup (Fin 2) ℤ) :
    GeneralLinearGroup.map (algebraMap ℝ ℂ) ((integralLevi γ : unimodularLevi) : BinaryRealGL) =
      GeneralLinearGroup.map (Int.castRingHom ℂ) γ := by
  apply Units.ext
  funext i j
  simp [integralLevi, GeneralLinearGroup.map_apply]

/-- **The integral Levi action at the identity.** On a function invariant under `σ γ σ` at
infinity, the real Levi action of `γ` at the identity is the untwisted action of `γ` on
`Sym^{n+1}`. -/
theorem edgeAction_integralLevi_one_eq_homogeneousAction (γ : GeneralLinearGroup (Fin 2) ℤ)
    (X : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (invariant : X (atInfinity (pivotConjugate
      (GeneralLinearGroup.map (Int.castRingHom ℝ) γ))) = X 1) :
    edgeAction (integralLevi γ) X 1 =
      Binary.homogeneousAction (n + 1) 0 (GeneralLinearGroup.map (Int.castRingHom ℂ) γ) (X 1) := by
  unfold edgeAction
  rw [one_mul]
  change _ • binaryCoefficient n ((integralLevi γ : unimodularLevi) : BinaryRealGL)
    (X (atInfinity (pivotConjugate (GeneralLinearGroup.map (Int.castRingHom ℝ) γ)))) = _
  rw [invariant, det_smul_binaryCoefficient, map_integralLevi]

/-- **The integral Levi action at the identity**, through the arithmetic representation
`arithmeticBinaryRep (n + 1) 0`. -/
theorem edgeAction_integralLevi_one (γ : GeneralLinearGroup (Fin 2) ℤ)
    (X : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (invariant : X (atInfinity (pivotConjugate
      (GeneralLinearGroup.map (Int.castRingHom ℝ) γ))) = X 1) :
    edgeAction (integralLevi γ) X 1 = (arithmeticBinaryRep (n + 1) 0).ρ γ (X 1) :=
  edgeAction_integralLevi_one_eq_homogeneousAction γ X invariant

/-! ### The lattice edge cocycle at the identity -/

/-- The derivative coordinate of an invariant family of tests is invariant. -/
theorem radicalDerivativeCoordinate_invariant {a : (Fin 2 → ℝ) → LineValues n}
    (γ : GeneralLinearGroup (Fin 2) ℤ)
    (invariant : ∀ Y ℓ, a Y (atInfinity (pivotConjugate
      (GeneralLinearGroup.map (Int.castRingHom ℝ) γ)), ℓ) = a Y (1, ℓ)) :
    radicalDerivativeCoordinate a
        (atInfinity (pivotConjugate (GeneralLinearGroup.map (Int.castRingHom ℝ) γ))) =
      radicalDerivativeCoordinate a 1 := by
  unfold radicalDerivativeCoordinate lineVector
  simp_rw [invariant]

/-- **The lattice edge cocycles at the identity are `3` times the derivative edge, up to a
one-coboundary of `GL₂(ℤ)` acting on `Sym^{n+1}` without determinant twist**, when the primitive
`a` is invariant under the integral Levi at infinity. The action is that of
`arithmeticBinaryRep (n + 1) 0`. -/
theorem exists_lowerRadicalCocycleCoordinate_latticeEdgeCocycle
    {t : LineGroup → LineGroup → LineValues n} (cocycle : IsTwoCocycle t)
    (regular : EdgeRegular t) {a : (Fin 2 → ℝ) → LineValues n} (linear : ∀ Y, LinearTests (a Y))
    (differentiable : ∀ p, DifferentiableAt ℝ (fun Y => a Y p) 0)
    (trivial : ∀ Y Y', t (lineRadicalElement Y) (lineRadicalElement Y') =
      lineRadicalElement Y • a Y' - a (Y + Y') + a Y)
    (invariant : ∀ (γ : GeneralLinearGroup (Fin 2) ℤ) Y ℓ, a Y (atInfinity (pivotConjugate
      (GeneralLinearGroup.map (Int.castRingHom ℝ) γ)), ℓ) = a Y (1, ℓ)) :
    ∃ P0 : Binary.HomogeneousPoly (n + 1), ∀ γ : GeneralLinearGroup (Fin 2) ℤ,
      lowerRadicalCocycleCoordinate n (latticeEdgeCocycle cocycle regular.linear linear trivial
          γ 1) =
        (3 : ℂ) • derivativeEdge t (integralLevi γ) 1 -
          (Binary.homogeneousAction (n + 1) 0 (GeneralLinearGroup.map (Int.castRingHom ℂ) γ) P0 -
            P0) := by
  refine ⟨(3 : ℂ) • radicalDerivativeCoordinate a 1, fun γ => ?_⟩
  rw [lowerRadicalCocycleCoordinate_latticeEdgeCocycle cocycle regular linear differentiable,
    edgeAction_integralLevi_one_eq_homogeneousAction γ _
      (radicalDerivativeCoordinate_invariant γ (invariant γ)), map_smul, smul_sub, smul_sub]

end TernaryPeriodPolynomials.AnalyticClasses
