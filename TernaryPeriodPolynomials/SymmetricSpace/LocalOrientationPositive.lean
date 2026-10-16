module

public import TernaryPeriodPolynomials.SymmetricSpace.LocalOrientation
public import TernaryPeriodPolynomials.SymmetricSpace.MatrixIsotopy.Positive

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceLocalOrientation
open CategoryTheory HomologicalComplex SymmetricSpacePositive

/-- Every positive-determinant real matrix preserves the actual degree-five local generators. -/
theorem positive_actionLocalMap_generator (g : RealGL)
    (hg : 0 < (Matrix.GeneralLinearGroup.det g : ℝ)) (S : Space) :
    homologyMap (actionLocalMap g S) 5 (localGenerator S) = localGenerator (act g S) :=
  actionLocalMap_generator (RealMatrixIsotopy.positiveGLPath g hg) S

/-- Negating a three-dimensional matrix leaves its actual normalized congruence action unchanged. -/
@[simp] theorem act_neg (g : RealGL) (S : Space) : act (-g) S = act g S := by
  apply Subtype.ext
  simp [act, conjugate]

/-- Every invertible real three-dimensional matrix has an identical-action representative
of positive determinant. -/
theorem exists_positive_same_action (g : RealGL) :
    ∃ h : RealGL, 0 < (Matrix.GeneralLinearGroup.det h : ℝ) ∧ act h = act g := by
  by_cases hg : 0 < (Matrix.GeneralLinearGroup.det g : ℝ)
  · exact ⟨g,hg,rfl⟩
  · refine ⟨-g,?_,funext (act_neg g)⟩
    have hn : (Matrix.GeneralLinearGroup.det g : ℝ) ≠ 0 := Units.ne_zero _
    have hd : (Matrix.GeneralLinearGroup.det (-g) : ℝ) =
        -(Matrix.GeneralLinearGroup.det g : ℝ) := by
      change (-g.val).det = -g.val.det
      norm_num [Matrix.det_neg]
    rw [hd]
    exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hg) hn)

/-- Matrices with the same normalized congruence action give identical homeomorphisms. -/
theorem actionHomeomorph_eq_of_act_eq (g h : RealGL) (he : act g = act h) :
    actionHomeomorph g = actionHomeomorph h := by
  apply Homeomorph.ext
  intro S
  exact congrFun he S

/-- Preservation of the chosen actual local generators, expressed solely in terms of a map. -/
def PreservesLocalGenerators (f : C(Space,Space)) : Prop :=
  ∀ (hf : Function.Injective f) (S : Space),
    homologyMap (RationalRelativeSingular.relativeMap f {S}ᶜ {f S}ᶜ
      (fun _ hT => fun he => hT (hf he))) 5 (localGenerator S) = localGenerator (f S)

/-- Every real GL3 matrix preserves the genuine local generators on the actual form space. -/
theorem all_actionLocalMap_generator (g : RealGL) (S : Space) :
    homologyMap (actionLocalMap g S) 5 (localGenerator S) = localGenerator (act g S) := by
  obtain ⟨h,hh,he⟩ := exists_positive_same_action g
  have hf := actionHomeomorph_eq_of_act_eq h g he
  have H : PreservesLocalGenerators (actionHomeomorph h).toHomotopyEquiv.toFun := by
    intro hi T
    exact positive_actionLocalMap_generator h hh T
  rw [hf] at H
  exact H (actionHomeomorph g).injective S

end TernaryPoly.SymmetricSpaceLocalOrientation
