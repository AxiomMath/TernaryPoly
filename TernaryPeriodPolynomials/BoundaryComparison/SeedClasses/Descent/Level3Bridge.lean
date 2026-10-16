module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.ESSpan
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Period.Dimension
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Injective.Main
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.ReflectionLevel

@[expose] public section


/-!
# Level three, bridge I: `Γ₁(3)` as the subgroup `Gamma1 3` and the Eichler primitive

Paper: Lemma C.3
(`ar:lem:seed`), Eichler--Shimura at the level-three plane cusp.

The library's level-three development (`AxiomCodeLevelThree`) works with the group
`core = ⟨T, L⟩ ⊂ Γ₁'(3) ⊂ GL₂(ℤ)` and its own crossed cohomology. This module identifies
`core` with the subgroup `Gamma1 3 ⊆ SL₂(ℤ)` (`coreToLam`, onto), matches the coefficient
representation `coreRep (n+1) e` with `binRep (Gamma1 3) n` (`coreRep_eq_binRep`, any twist `e`
since the determinant is one), and shows that the library's primitive of
`f(z)(X₀ - zX₁)^{n+1} dz` is `(-1)^{n+1}` times the Eichler primitive `eichlerPoly`
(`primitive_eq_eichlerPoly`), so that the library's period cocycle is `(-1)^{n+1}` times the
cocycle `holCocycle`.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups Manifold ModularForm
open GeneralEisenstein Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

open TernaryPeriodPolynomials.LevelThree
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle
open TernaryPeriodPolynomials.LevelThree.GammaOneThree
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
  (binaryIntegralComplex binaryArithmeticLevel)

/-- The subgroup `Γ₁(3) ⊆ SL₂(ℤ)`. -/
abbrev Gam3 : Subgroup SL(2, ℤ) := CongruenceSubgroup.Gamma1 3

/-- The library's `Γ₁(3) = ⟨T, L⟩` as the subgroup `Gamma1 3`. -/
def coreToLam : core →* Gam3 := coreSL.codRestrict Gam3 coreSL_mem

theorem coreToLam_surjective : Function.Surjective coreToLam := fun γ => by
  obtain ⟨k, hk⟩ := exists_core_of_mem γ.1 γ.2
  exact ⟨k, Subtype.ext hk⟩

theorem homogeneousAction_twist (d : ℕ) (e e' : ℤ) (g : Binary.GL2)
    (hg : ((GeneralLinearGroup.det g : ℂˣ) : ℂ) = 1) (P : Binary.HomogeneousPoly d) :
    Binary.homogeneousAction d e g P = Binary.homogeneousAction d e' g P := by
  apply Subtype.ext
  rw [Binary.homogeneousAction_coe, Binary.homogeneousAction_coe, Binary.action_apply,
    Binary.action_apply]
  have h : ∀ t : ℤ, Binary.determinantCharacter t g = 1 := fun t => by
    change ((GeneralLinearGroup.det g : ℂˣ) : ℂ) ^ t = 1
    rw [hg, _root_.one_zpow]
  rw [h e, h e']

theorem coreRep_eq_binRep (n : ℕ) (e : ℤ) (k : core) :
    coreRep (n + 1) e k = (binRep Gam3 n).ρ (coreToLam k) := by
  apply LinearMap.ext
  intro P
  change Binary.homogeneousAction (n + 1) e (binaryIntegralComplex (k : binaryArithmeticLevel).val)
      P = Binary.homogeneousAction (n + 1) (-1)
        (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL (coreSL k))) P
  have hmat : GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL (coreSL k)) =
      binaryIntegralComplex (k : binaryArithmeticLevel).val := by
    apply Units.ext
    rfl
  rw [hmat]
  exact homogeneousAction_twist _ _ _ _ (ExactLevel.complex_det k) P

section Primitive

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodPrimitive
open UpperHalfPlane

/-- Evaluation of a binary homogeneous form at a point, as a linear functional. -/
def evFun (d : ℕ) (v : Fin 2 → ℂ) : Binary.HomogeneousPoly d →ₗ[ℂ] ℂ :=
  (MvPolynomial.aeval v).toLinearMap.comp (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ d).subtype

theorem evFun_apply (d : ℕ) (v : Fin 2 → ℂ) (P : Binary.HomogeneousPoly d) :
    evFun d v P = MvPolynomial.eval v (P : MvPolynomial (Fin 2) ℂ) := by
  simp [evFun]

/-- **The level-three primitive is `(-1)^m` times the Eichler primitive.** -/
theorem primitive_eq_eichlerPoly (n : ℕ) {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (G : ℕ → ℂ → ℂ) (hG0 : ∀ j, G j Complex.I = 0)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (G j) (f (ofComplex z) * z ^ j) z)
    {z : ℂ} (hz : 0 < z.im) :
    ((primitive (n + 1) f z : Binary.HomogeneousPoly (n + 1)) : MvPolynomial (Fin 2) ℂ) =
      C ((-1 : ℂ) ^ (n + 1)) * eichlerPoly n G z := by
  apply MvPolynomial.funext
  intro v
  have hopen : IsOpen {u : ℂ | 0 < u.im} := isOpen_upperHalfPlaneSet
  have hconn : IsPreconnected {u : ℂ | 0 < u.im} :=
    (convex_halfSpace_im_gt (0 : ℝ)).isPreconnected
  let F₁ : ℂ → ℂ := fun w => evFun (n + 1) v (primitive (n + 1) f w)
  let F₂ : ℂ → ℂ := fun w => (-1 : ℂ) ^ (n + 1) * MvPolynomial.eval v (eichlerPoly n G w)
  have h₁ : ∀ w, 0 < w.im → HasDerivAt F₁ (evFun (n + 1) v (pointForm (n + 1) f w)) w :=
    fun w hw => primitive_isPrimitive (n + 1) hf (evFun (n + 1) v) w hw
  have h₂ : ∀ w, 0 < w.im → HasDerivAt F₂
      ((-1 : ℂ) ^ (n + 1) * binaryIntegrand n (fun u => f (ofComplex u)) v w) w := fun w hw =>
    (eichlerPoly_hasDerivAt n (fun u => f (ofComplex u)) G hG v hw).const_mul _
  have hderiv : ∀ w, 0 < w.im →
      evFun (n + 1) v (pointForm (n + 1) f w) =
        (-1 : ℂ) ^ (n + 1) * binaryIntegrand n (fun u => f (ofComplex u)) v w := by
    intro w _
    have hs : ((-1 : ℂ)) ^ (n + 1) * (-1) ^ (n + 1) = 1 := by
      rw [← mul_pow]; norm_num
    rw [pointForm, map_smul, smul_eq_mul, evFun_apply]
    unfold binaryIntegrand
    rw [binaryPointPower]
    simp only [map_pow, map_sub, map_mul, eval_X, eval_C]
    rw [show (w * v 1 - v 0) = -(v 0 - w * v 1) by ring, neg_pow (v 0 - w * v 1) (n + 1)]
    linear_combination (-(f (ofComplex w) * (v 0 - w * v 1) ^ (n + 1))) * hs
  have heq : Set.EqOn F₁ F₂ {u : ℂ | 0 < u.im} := by
    refine hopen.eqOn_of_deriv_eq hconn
      (fun w hw => (h₁ w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => (h₂ w hw).differentiableAt.differentiableWithinAt) (fun w hw => ?_)
      (show (0 : ℝ) < Complex.I.im by simp) ?_
    · rw [(h₁ w hw).deriv, (h₂ w hw).deriv, hderiv w hw]
    · change evFun (n + 1) v (primitive (n + 1) f Complex.I) =
        (-1 : ℂ) ^ (n + 1) * MvPolynomial.eval v (eichlerPoly n G Complex.I)
      rw [primitive_basepoint, eichlerPoly_base n G hG0, map_zero, map_zero, mul_zero]
  have := heq hz
  change evFun (n + 1) v _ = _ at this
  rw [evFun_apply] at this
  rw [this, MvPolynomial.eval_mul, MvPolynomial.eval_C]

end Primitive

end TernaryPeriodPolynomials.Argument.SeedC3S4c
