module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.CartanDecomposition
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.CocycleRigidity
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Eichler.BridgeCocycle

@[expose] public section


/-!
# Rigidity of the derivative edge

A one-cocycle `D` of `SL₂^±(ℝ)` for the action
`(m ⋆ F)(h) = det m · binaryCoefficient m (F(h · σ m σ))` that vanishes on orthogonal elements and
whose coordinates have derivative zero along the diagonal flow `a(s) = diag(eˢ, e⁻ˢ)` at `s = 0`
vanishes identically: it vanishes along the whole flow by one-parameter rigidity, and hence
everywhere by the Cartan decomposition `m = k₁ a(s) k₂`.

Applied to `Ẽ - c · edgeNormal F`, where `Ẽ` is the derivative edge of the real good-line transfer
of the Eichler normal form, this shows that `Ẽ = c · edgeNormal F` as soon as the velocities of the
two cocycles along the diagonal flow are proportional with factor `c`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

/-! ### Orthogonal elements fix `i` -/

/-- An orthogonal element of `SL₂^±(ℝ)` fixes `i`. -/
theorem IsOrthogonalLevi.smul_I {k : unimodularLevi} (hk : IsOrthogonalLevi k) :
    (k : BinaryRealGL) • UpperHalfPlane.I = UpperHalfPlane.I := by
  set g : BinaryRealGL := k.val
  have entry (i j : Fin 2) :
      (g.val.transpose * g.val) i j = (1 : Matrix (Fin 2) (Fin 2) ℝ) i j := by
    rw [show g.val.transpose * g.val = 1 from hk]
  have e00 := entry 0 0
  have e01 := entry 0 1
  have e11 := entry 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne, ne_eq, zero_ne_one, not_false_eq_true] at e00 e01 e11
  have unimodular : |g.val.det| = 1 := k.property
  rw [Matrix.det_fin_two] at unimodular
  rcases abs_eq (zero_le_one' ℝ) |>.mp unimodular with positive | negative
  · have det_pos : 0 < (Matrix.GeneralLinearGroup.det g).val := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, positive]
      exact one_pos
    apply (UpperHalfPlane.gl_smul_I_eq_I_iff_of_pos det_pos).mpr
    constructor <;>
      nlinarith [sq_nonneg (g.val 0 0 - g.val 1 1), sq_nonneg (g.val 0 1 + g.val 1 0)]
  · set g' : BinaryRealGL := g * UpperHalfPlane.J
    have entries : g'.val = !![-g.val 0 0, g.val 0 1; -g.val 1 0, g.val 1 1] := by
      change g.val * UpperHalfPlane.J.val = _
      rw [UpperHalfPlane.val_J, Matrix.eta_fin_two g.val, Matrix.mul_fin_two]
      simp
    have det_pos : 0 < (Matrix.GeneralLinearGroup.det g').val := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, entries, Matrix.det_fin_two_of]
      linarith
    have fixes : g' • UpperHalfPlane.I = UpperHalfPlane.I := by
      apply (UpperHalfPlane.gl_smul_I_eq_I_iff_of_pos det_pos).mpr
      rw [entries]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      constructor <;>
        nlinarith [sq_nonneg (g.val 0 0 + g.val 1 1), sq_nonneg (g.val 0 1 - g.val 1 0)]
    have square : UpperHalfPlane.J * UpperHalfPlane.J = 1 := by
      rw [← pow_two, UpperHalfPlane.J_sq]
    have recover : g = g' * UpperHalfPlane.J := by
      rw [mul_assoc, square, mul_one]
    rw [recover, mul_smul, binaryReflection_smul_I, fixes]

/-! ### The edge action -/

theorem edgeAction_one (F : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)) :
    edgeAction 1 F = F := by
  funext h
  have coefficient : binaryCoefficient n 1 = 1 := by
    unfold binaryCoefficient
    rw [map_one, map_one]
  unfold edgeAction
  rw [OneMemClass.coe_one, pivotConjugate_one, atInfinity_one, mul_one, Units.val_one,
    Matrix.det_one, coefficient, Complex.ofReal_one, one_smul, Module.End.one_apply]

theorem edgeAction_zero (m : unimodularLevi) :
    edgeAction m (0 : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)) = 0 := by
  funext h
  unfold edgeAction
  rw [Pi.zero_apply, map_zero, smul_zero, Pi.zero_apply]

theorem edgeAction_sub_smul (m : unimodularLevi) (c : ℂ)
    (F G : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)) :
    edgeAction m (F - c • G) = edgeAction m F - c • edgeAction m G := by
  funext h
  unfold edgeAction
  rw [Pi.sub_apply, Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, map_sub, map_smul, smul_sub,
    smul_comm c]

/-- The action `⋆` of `SL₂^±(ℝ)` read in the coordinates of the binary weight basis, as an action
of pointwise linear form. -/
def edgeCoordinateAction (n : ℕ) :
    PointwiseAction unimodularLevi BinaryAdelicGL (Fin (n + 2) → ℂ) where
  act g f h := (binaryWeightBasis (n + 1)).equivFun
    (edgeAction g (fun x => (binaryWeightBasis (n + 1)).equivFun.symm (f x)) h)
  act_one f := by
    funext h
    rw [edgeAction_one, LinearEquiv.apply_symm_apply]
  pointwise g := ⟨(LinearMap.toContinuousLinearMap ((binaryWeightBasis (n + 1)).equivFun.toLinearMap
      ∘ₗ ((((g : BinaryRealGL).val.det : ℝ) : ℂ) • binaryCoefficient n g) ∘ₗ
        (binaryWeightBasis (n + 1)).equivFun.symm.toLinearMap)).restrictScalars ℝ,
    fun x => x * atInfinity (pivotConjugate (g : BinaryRealGL)), fun _ _ => rfl⟩

/-! ### Rigidity -/

/-- **Rigidity of edge cocycles.** A one-cocycle for the edge action that vanishes on orthogonal
elements and whose coordinates are stationary along the diagonal flow at `s = 0` vanishes. -/
theorem edgeCocycle_eq_zero {D : unimodularLevi → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)}
    (cocycle : ∀ a b, D (a * b) = D a + edgeAction a (D b))
    (orthogonal : ∀ k, IsOrthogonalLevi k → D k = 0)
    (flow : ∀ h (j : Fin (n + 2)),
      HasDerivAt (fun s => (binaryWeightBasis (n + 1)).coord j (D (diagonalFlow s) h)) 0 0)
    (m : unimodularLevi) : D m = 0 := by
  set e := (binaryWeightBasis (n + 1)).equivFun
  set E : unimodularLevi → BinaryAdelicGL → (Fin (n + 2) → ℂ) := fun g x => e (D g x)
  have hE : IsActionCocycle (edgeCoordinateAction n) E := by
    intro a b
    funext x
    change e (D (a * b) x) = e (D a x) + e (edgeAction a (fun y => e.symm (e (D b y))) x)
    simp only [LinearEquiv.symm_apply_apply]
    rw [cocycle, Pi.add_apply, map_add]
  have stationary (x : BinaryAdelicGL) : HasDerivAt (fun s => E (diagonalFlow s) x) 0 0 := by
    apply hasDerivAt_pi.mpr
    intro j
    have := flow x j
    simp only [Module.Basis.coord_apply] at this
    exact this
  have along (s : ℝ) : D (diagonalFlow s) = 0 := by
    have vanish := hE.eq_zero_of_hasDerivAt diagonalFlow diagonalFlow_add diagonalFlow_zero
      stationary s
    funext x
    apply e.injective
    rw [Pi.zero_apply, map_zero]
    exact congrFun vanish x
  obtain ⟨k₁, k₂, s, h₁, h₂, rfl⟩ := cartan_decomposition m
  rw [cocycle, cocycle, orthogonal k₁ h₁, along, orthogonal k₂ h₂, edgeAction_zero,
    edgeAction_zero, add_zero, add_zero]

/-- **The derivative edge is a multiple of the edge normal form.** If the velocity of the
derivative edge `Ẽ` of the real good-line transfer of the Eichler normal form along the diagonal
flow is `c` times the velocity `V` of `edgeNormal F`, then `Ẽ = c · edgeNormal F`. -/
theorem derivativeEdge_eq_smul_edgeNormal {F : BinaryAdelicGL → ℂ → ℂ} (hF : EichlerData n F)
    (cocycle : IsTwoCocycle (lineTransferCochain (eichlerNormal n F)))
    (regular : EdgeRegular (lineTransferCochain (eichlerNormal n F)))
    (c : ℂ) (V : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (edgeVelocity : ∀ h (j : Fin (n + 2)), HasDerivAt (fun s => (binaryWeightBasis (n + 1)).coord j
      (derivativeEdge (lineTransferCochain (eichlerNormal n F)) (diagonalFlow s) h))
      ((binaryWeightBasis (n + 1)).coord j (c • V h)) 0)
    (normalVelocity : ∀ h (j : Fin (n + 2)), HasDerivAt (fun s =>
      (binaryWeightBasis (n + 1)).coord j (edgeNormal n F (diagonalFlow s) h))
      ((binaryWeightBasis (n + 1)).coord j (V h)) 0)
    (m : unimodularLevi) :
    derivativeEdge (lineTransferCochain (eichlerNormal n F)) m = c • edgeNormal n F m := by
  set t := lineTransferCochain (eichlerNormal n F)
  have zero := edgeCocycle_eq_zero (D := fun g => derivativeEdge t g - c • edgeNormal n F g)
    (fun a b => by
      rw [derivativeEdge_mul cocycle regular, edgeNormal_mul F hF.holomorphic hF.modular,
        edgeAction_sub_smul, smul_add]
      abel)
    (fun k hk => by
      rw [derivativeEdge_orthogonal (fun A hA => eichlerNormal_of_smul_I F A hA) hk,
        edgeNormal_of_smul_I F hk.smul_I, smul_zero, sub_zero])
    (fun h j => by
      have difference := (edgeVelocity h j).sub ((normalVelocity h j).const_mul c)
      rw [map_smul, smul_eq_mul, sub_self] at difference
      refine difference.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      simp only [Pi.sub_apply, Pi.smul_apply, map_sub, map_smul, smul_eq_mul])
    m
  exact sub_eq_zero.mp zero

end TernaryPeriodPolynomials.AnalyticClasses
