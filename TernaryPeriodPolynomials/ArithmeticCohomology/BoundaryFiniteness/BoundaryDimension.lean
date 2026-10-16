module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryFiniteness.ModularPresentation
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryFiniteness.ParabolicDuality

@[expose] public section


namespace TernaryPeriodPolynomials.BoundaryFiniteness.BoundaryDimension

open Matrix GeneralEisenstein

def toDeterminantKernel : SpecialLinearGroup (Fin 2) ℤ →*
    (GeneralLinearGroup.det : GeneralLinearGroup (Fin 2) ℤ →* ℤˣ).ker :=
  SpecialLinearGroup.toGL.codRestrict _ (fun g => SpecialLinearGroup.coeToGL_det g)

theorem toDeterminantKernel_bijective : Function.Bijective toDeterminantKernel := by
  constructor
  · intro x y equation
    apply SpecialLinearGroup.toGL_injective
    exact congrArg Subtype.val equation
  · intro matrix
    have determinant : matrix.val.val.det = 1 := congrArg Units.val matrix.property
    refine ⟨⟨matrix.val.val, determinant⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    rfl

noncomputable def determinantKernelEquiv : SpecialLinearGroup (Fin 2) ℤ ≃*
    (GeneralLinearGroup.det : GeneralLinearGroup (Fin 2) ℤ →* ℤˣ).ker :=
  MulEquiv.ofBijective toDeterminantKernel toDeterminantKernel_bijective

theorem binary_finitelyPresented : Group.IsFinitelyPresented (GeneralLinearGroup (Fin 2) ℤ) := by
  let := ModularPresentation.finitelyPresented
  let : Group.IsFinitelyPresented
      (GeneralLinearGroup.det : GeneralLinearGroup (Fin 2) ℤ →* ℤˣ).ker :=
    Group.IsFinitelyPresented.equiv determinantKernelEquiv
  exact PresentedExtensions.finitelyPresented GeneralLinearGroup.det GeneralLinearGroup.det_surjective

theorem boundary_finiteDimensional (degree : ℕ) (character : RankOneCharacter) :
    FiniteDimensional ℂ (BoundaryCoordinates degree character) := by
  let := binary_finitelyPresented
  exact ParabolicDuality.boundary_finiteDimensional degree character

end TernaryPeriodPolynomials.BoundaryFiniteness.BoundaryDimension
