module

public import TernaryPeriodPolynomials.ArithmeticGroup.GL3Congruence.Basic
public import TernaryPeriodPolynomials.ArithmeticGroup.GL3Congruence.Minkowski

@[expose] public section

/- These covers are the actual matrix-reduction kernels in the arithmetic groups. -/
open Matrix
noncomputable section
namespace TernaryPoly.IntegralGL3Congruence
open ModThreeGoodAction

/-- The level-three principal subgroup has no nonidentity finite-order element. -/
theorem principalThree_finiteOrder_eq_one (g : IntegralGL) (hg : g∈principalThree)
    (hfin : IsOfFinOrder g) : g=1 :=
  generalLinear_modThree_finiteOrder_eq_one g hg hfin

/-- In particular, the actual principal level-six subgroup is ordinarily torsion-free. -/
theorem principalSix_finiteOrder_eq_one (g : IntegralGL) (hg : g∈principalSix)
    (hfin : IsOfFinOrder g) : g=1 :=
  principalThree_finiteOrder_eq_one g (principalSix_le_three hg) hfin

/-- Ordinary torsion-freeness stated intrinsically in the principal subgroup. -/
theorem principalSix_subgroup_finiteOrder_eq_one (g : principalSix)
    (hfin : IsOfFinOrder g) : g=1 := by
  apply Subtype.ext
  exact principalSix_finiteOrder_eq_one g.val g.property
    (principalSix.subtype.isOfFinOrder hfin)

/-- The same explicit finite-index kernel inside the actual sum-covector fixer has no torsion. -/
theorem principalSixInK_finiteOrder_eq_one (g : K) (hg : g∈principalSixInK)
    (hfin : IsOfFinOrder g) : g=1 := by
  apply Subtype.ext
  exact principalSix_finiteOrder_eq_one g.val ((mem_principalSixInK g).mp hg)
    (K.subtype.isOfFinOrder hfin)

theorem principalSixInK_subgroup_finiteOrder_eq_one (g : principalSixInK)
    (hfin : IsOfFinOrder g) : g=1 := by
  apply Subtype.ext
  exact principalSixInK_finiteOrder_eq_one g.val g.property
    (principalSixInK.subtype.isOfFinOrder hfin)

/-- Restricting to the level-six subgroup removes every polynomial determinant twist. -/
theorem principalSix_action_eq_untwisted (e : ℤ) (g : IntegralGL) (hg : g∈principalSix) :
    PolynomialGLAction.action e (GeneralLinearGroup.map (Int.castRingHom ℚ) g)=
      PolynomialGLAction.untwisted (GeneralLinearGroup.map (Int.castRingHom ℚ) g) := by
  change PolynomialGLAction.determinantCharacter e
    (GeneralLinearGroup.map (Int.castRingHom ℚ) g) •
      PolynomialGLAction.untwisted (GeneralLinearGroup.map (Int.castRingHom ℚ) g) = _
  rw [principalSix_determinantCharacter e g hg,one_smul]

/-- All homogeneous integral twists restrict to the same action on the level-six subgroup. -/
theorem principalSix_integralAction_eq (n : ℕ) (e : ℤ) (g : IntegralGL)
    (hg : g∈principalSix) :
    PolynomialGLAction.integralAction n e g=PolynomialGLAction.integralAction n 0 g := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  change PolynomialGLAction.action e (GeneralLinearGroup.map (Int.castRingHom ℚ) g) f.val=
    PolynomialGLAction.action 0 (GeneralLinearGroup.map (Int.castRingHom ℚ) g) f.val
  rw [principalSix_action_eq_untwisted e g hg,principalSix_action_eq_untwisted 0 g hg]

/-- An explicit normal finite-index torsion-free subgroup of the actual integral general linear
 group, contained in the exact arithmetic subgroup and having determinant one. -/
theorem actual_IntegralGL_torsionfree_cover :
    ∃ Γ : Subgroup IntegralGL,Γ.Normal ∧ Γ.FiniteIndex ∧ Γ≤K ∧
      (∀ g : IntegralGL,g∈Γ → IsOfFinOrder g → g=1) ∧
      (∀ g : IntegralGL,g∈Γ → g.val.det=1) := by
  exact ⟨principalSix,inferInstance,inferInstance,principalSix_le_K,
    principalSix_finiteOrder_eq_one,principalSix_det_one⟩

/-- An explicit normal finite-index torsion-free subgroup of the actual mod-three sum-covector
 fixer. This is the algebraic cover prerequisite; no geometric freeness is asserted here. -/
theorem actual_K_torsionfree_cover :
    ∃ Γ : Subgroup K,Γ.Normal ∧ Γ.FiniteIndex ∧
      (∀ g : K,g∈Γ → IsOfFinOrder g → g=1) ∧
      (∀ g : K,g∈Γ → g.val.val.det=1) ∧
      (∀ (e : ℤ) (g : K),g∈Γ → PolynomialGLAction.determinantCharacter e
        (GeneralLinearGroup.map (Int.castRingHom ℚ) g.val)=1) := by
  refine ⟨principalSixInK,inferInstance,inferInstance,principalSixInK_finiteOrder_eq_one,?_,?_⟩
  · intro g hg
    exact principalSix_det_one g.val ((mem_principalSixInK g).mp hg)
  · intro e g hg
    exact principalSix_determinantCharacter e g.val ((mem_principalSixInK g).mp hg)

end TernaryPoly.IntegralGL3Congruence
