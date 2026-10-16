module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cohomological.CocycleLift
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.FamilyParameterDerivatives

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem binaryCocycle_matrix_orbit_smooth (cusp : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → (BinaryDegreeMonomial (degree + 1) → cusp.smooth))
    (smooth : Smooth (fun input : Fin 2 → BinaryRealGL => fun monomial =>
      (cuspSmoothAction cusp (atInfinity (input 1)) (cocycle (input 0) monomial)).val))
    (monomial : BinaryDegreeMonomial (degree + 1)) :
    ContDiffOn ℝ ⊤
      (fun input : Matrix (Fin 2) (Fin 2) ℝ × (Fin 1 → Matrix (Fin 2) (Fin 2) ℝ) =>
        cusp.π (atInfinity (invertibleMatrix (input.2 0))) (cocycle (invertibleMatrix input.1) monomial).val)
      ({entries | entries.det ≠ 0} ×ˢ {entries | ∀ index, (entries index).det ≠ 0}) := by
  let tuple (input : Matrix (Fin 2) (Fin 2) ℝ × (Fin 1 → Matrix (Fin 2) (Fin 2) ℝ)) :
      Fin 2 → Matrix (Fin 2) (Fin 2) ℝ := ![input.1, input.2 0]
  have tuple_smooth : ContDiff ℝ ⊤ tuple := by
    apply contDiff_pi.mpr
    intro index
    fin_cases index
    · change ContDiff ℝ ⊤ (fun input : Matrix (Fin 2) (Fin 2) ℝ ×
        (Fin 1 → Matrix (Fin 2) (Fin 2) ℝ) => input.1)
      exact contDiff_fst
    · change ContDiff ℝ ⊤ (fun input : Matrix (Fin 2) (Fin 2) ℝ ×
        (Fin 1 → Matrix (Fin 2) (Fin 2) ℝ) => input.2 0)
      fun_prop
  have maps : Set.MapsTo tuple
      ({entries | entries.det ≠ 0} ×ˢ {entries | ∀ index, (entries index).det ≠ 0})
      {entries : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ | ∀ index, (entries index).det ≠ 0} := by
    intro input member index
    fin_cases index
    · exact member.1
    · exact member.2 0
  have coordinate_smooth := contDiffOn_pi.mp smooth monomial
  have composed := coordinate_smooth.comp tuple_smooth.contDiffOn maps
  simpa only [Function.comp_def, tuple, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    cuspSmoothAction_apply_val]
    using composed

theorem binaryCocycle_parameter_smooth (cusp : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → (BinaryDegreeMonomial (degree + 1) → cusp.smooth))
    (smooth : Smooth (fun input : Fin 2 → BinaryRealGL => fun monomial =>
      (cuspSmoothAction cusp (atInfinity (input 1)) (cocycle (input 0) monomial)).val))
    (monomial : BinaryDegreeMonomial (degree + 1)) :
    ContDiffOn ℝ ⊤ (fun entries : Matrix (Fin 2) (Fin 2) ℝ =>
      (cocycle (invertibleMatrix entries) monomial).val) {entries | entries.det ≠ 0} :=
  cusp_family_parameter_contDiffOn cusp (fun entries => cocycle (invertibleMatrix entries) monomial)
    (binaryCocycle_matrix_orbit_smooth cusp degree cocycle smooth monomial)

theorem binaryCocycle_parameter_fderiv_mem (cusp : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → (BinaryDegreeMonomial (degree + 1) → cusp.smooth))
    (smooth : Smooth (fun input : Fin 2 → BinaryRealGL => fun monomial =>
      (cuspSmoothAction cusp (atInfinity (input 1)) (cocycle (input 0) monomial)).val))
    (finite : ∃ level : Subgroup BinaryFiniteGL, IsOpen (level : Set BinaryFiniteGL) ∧
      IsCompact (level : Set BinaryFiniteGL) ∧ ∀ element : level, ∀ matrix monomial,
        cusp.π (atFinite element.val) (cocycle matrix monomial).val = (cocycle matrix monomial).val)
    (monomial : BinaryDegreeMonomial (degree + 1)) (direction : Matrix (Fin 2) (Fin 2) ℝ) :
    fderiv ℝ (fun entries : Matrix (Fin 2) (Fin 2) ℝ =>
      (cocycle (invertibleMatrix entries) monomial).val) 1 direction ∈ cusp.smooth := by
  obtain ⟨level, level_open, level_compact, fixed⟩ := finite
  exact cusp_family_parameter_fderiv_mem_smooth cusp
    (fun entries => cocycle (invertibleMatrix entries) monomial)
    (isOpen_ne.preimage continuous_id.matrix_det)
    (binaryCocycle_matrix_orbit_smooth cusp degree cocycle smooth monomial)
    level level_open level_compact (fun element entries => fixed element (invertibleMatrix entries) monomial)
    (by simp) direction

noncomputable def binaryCocycleInfinitesimal (cusp : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → (BinaryDegreeMonomial (degree + 1) → cusp.smooth))
    (smooth : Smooth (fun input : Fin 2 → BinaryRealGL => fun monomial =>
      (cuspSmoothAction cusp (atInfinity (input 1)) (cocycle (input 0) monomial)).val))
    (finite : ∃ level : Subgroup BinaryFiniteGL, IsOpen (level : Set BinaryFiniteGL) ∧
      IsCompact (level : Set BinaryFiniteGL) ∧ ∀ element : level, ∀ matrix monomial,
        cusp.π (atFinite element.val) (cocycle matrix monomial).val = (cocycle matrix monomial).val) :
    Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] (BinaryDegreeMonomial (degree + 1) → cusp.smooth) :=
  LinearMap.pi (fun monomial =>
    ((fderiv ℝ (fun entries : Matrix (Fin 2) (Fin 2) ℝ =>
      (cocycle (invertibleMatrix entries) monomial).val) 1).toLinearMap).codRestrict
      (cusp.smooth.restrictScalars ℝ) (binaryCocycle_parameter_fderiv_mem cusp degree cocycle smooth finite monomial))

theorem binaryCocycleInfinitesimal_val (cusp : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → (BinaryDegreeMonomial (degree + 1) → cusp.smooth))
    (smooth : Smooth (fun input : Fin 2 → BinaryRealGL => fun monomial =>
      (cuspSmoothAction cusp (atInfinity (input 1)) (cocycle (input 0) monomial)).val))
    (finite : ∃ level : Subgroup BinaryFiniteGL, IsOpen (level : Set BinaryFiniteGL) ∧
      IsCompact (level : Set BinaryFiniteGL) ∧ ∀ element : level, ∀ matrix monomial,
        cusp.π (atFinite element.val) (cocycle matrix monomial).val = (cocycle matrix monomial).val)
    (direction : Matrix (Fin 2) (Fin 2) ℝ) (monomial : BinaryDegreeMonomial (degree + 1)) :
    (binaryCocycleInfinitesimal cusp degree cocycle smooth finite direction monomial).val =
      fderiv ℝ (fun entries : Matrix (Fin 2) (Fin 2) ℝ =>
        (cocycle (invertibleMatrix entries) monomial).val) 1 direction := rfl

theorem binaryCocycle_one (cusp : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → (BinaryDegreeMonomial (degree + 1) → cusp.smooth))
    (identity : ∀ first second, cocycle (first * second) = cocycle first +
      binaryCohomologicalRepresentation cusp degree first (cocycle second)) : cocycle 1 = 0 := by
  have equality := identity 1 1
  simp only [one_mul, map_one, Module.End.one_apply] at equality
  apply add_left_cancel (a := cocycle 1)
  simpa only [add_zero] using equality.symm

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
