module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.AffineDerivatives

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def cuspAffineSmoothValues (cusp : CuspidalRepresentation) : Submodule ℂ cusp.H where
  carrier := {vector | ContDiffOn ℝ (↑(⊤ : ℕ∞)) (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet}
  zero_mem' := by
    change ContDiffOn ℝ (↑(⊤ : ℕ∞)) (cuspAffineOrbitVector cusp 0) UpperHalfPlane.upperHalfPlaneSet
    have zero : cuspAffineOrbitVector cusp 0 = fun _ => 0 := by
      funext point
      exact map_zero _
    rw [zero]
    exact contDiffOn_const
  add_mem' {first second} first_regular second_regular := by
    apply (first_regular.add second_regular).congr
    intro point _
    exact map_add _ first second
  smul_mem' scalar vector regular := by
    apply (regular.const_smul scalar).congr
    intro point _
    exact map_smul _ scalar vector

theorem cuspAffineSmoothValues_differentiable (cusp : CuspidalRepresentation)
    (vector : cuspAffineSmoothValues cusp) :
    DifferentiableAt ℝ (cuspAffineOrbitVector cusp vector.val) Complex.I :=
  (vector.property.contDiffAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds
    (show Complex.I.im > 0 by simp))).differentiableAt (by simp)

def cuspAffineDifferential (cusp : CuspidalRepresentation) (direction : ℂ) :
    Module.End ℂ (cuspAffineSmoothValues cusp) where
  toFun vector := ⟨fderiv ℝ (cuspAffineOrbitVector cusp vector.val) Complex.I direction,
    cuspAffineOrbitVector_derivative_contDiffOn cusp vector.val vector.property direction⟩
  map_add' first second := by
    apply Subtype.ext
    have orbit_add : cuspAffineOrbitVector cusp (first.val + second.val) =
        cuspAffineOrbitVector cusp first.val + cuspAffineOrbitVector cusp second.val := by
      funext point
      exact map_add _ first.val second.val
    change fderiv ℝ (cuspAffineOrbitVector cusp (first.val + second.val)) Complex.I direction = _
    rw [orbit_add, fderiv_add (cuspAffineSmoothValues_differentiable cusp first)
      (cuspAffineSmoothValues_differentiable cusp second)]
    rfl
  map_smul' scalar vector := by
    apply Subtype.ext
    have orbit_smul : cuspAffineOrbitVector cusp (scalar • vector.val) =
        scalar • cuspAffineOrbitVector cusp vector.val := by
      funext point
      exact map_smul _ scalar vector.val
    change fderiv ℝ (cuspAffineOrbitVector cusp (scalar • vector.val)) Complex.I direction = _
    rw [orbit_smul, fderiv_const_smul (cuspAffineSmoothValues_differentiable cusp vector) scalar]
    rfl

theorem cuspAffineDifferential_apply (cusp : CuspidalRepresentation) (direction : ℂ)
    (vector : cuspAffineSmoothValues cusp) :
    (cuspAffineDifferential cusp direction vector).val =
      fderiv ℝ (cuspAffineOrbitVector cusp vector.val) Complex.I direction := rfl

theorem cuspAffineDifferential_commutator (cusp : CuspidalRepresentation) :
    cuspAffineDifferential cusp Complex.I * cuspAffineDifferential cusp 1 -
      cuspAffineDifferential cusp 1 * cuspAffineDifferential cusp Complex.I = cuspAffineDifferential cusp 1 := by
  apply LinearMap.ext
  intro vector
  apply Subtype.ext
  exact cuspAffineOrbitVector_commutator cusp vector.val vector.property

theorem cuspAffineDifferential_skew (cusp : CuspidalRepresentation) (direction : ℂ)
    (first second : cuspAffineSmoothValues cusp) :
    inner ℂ first.val (cuspAffineDifferential cusp direction second).val +
      inner ℂ (cuspAffineDifferential cusp direction first).val second.val = 0 :=
  cuspAffineOrbitVector_derivative_skew cusp first.val second.val
    (cuspAffineSmoothValues_differentiable cusp first) (cuspAffineSmoothValues_differentiable cusp second) direction

end TernaryPeriodPolynomials.SphericalDetection.Helpers
