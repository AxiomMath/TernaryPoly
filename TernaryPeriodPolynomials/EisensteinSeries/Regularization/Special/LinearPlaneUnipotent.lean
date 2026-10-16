module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Special.LinearPlaneLevi

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

def specialLinearPlaneUnipotent {R : Type*} [CommRing R] (first second : R) :
    SpecialLinearGroup (Fin 3) R :=
  ⟨!![1, 0, first; 0, 1, second; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem specialLinearPlaneUnipotent_add {R : Type*} [CommRing R] (a b c d : R) :
    specialLinearPlaneUnipotent a b * specialLinearPlaneUnipotent c d =
      specialLinearPlaneUnipotent (a + c) (b + d) := by
  apply Subtype.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [specialLinearPlaneUnipotent, Matrix.mul_apply, Fin.sum_univ_three, add_comm]

theorem specialLinearPlaneUnipotent_zero {R : Type*} [CommRing R] :
    specialLinearPlaneUnipotent (0 : R) 0 = 1 := by
  apply Subtype.ext
  ext row column
  fin_cases row <;> fin_cases column <;> simp [specialLinearPlaneUnipotent]

theorem specialLinearPlaneUnipotent_map {R S : Type*} [CommRing R] [CommRing S]
    (map : R →+* S) (first second : R) :
    SpecialLinearGroup.map map (specialLinearPlaneUnipotent first second) =
      specialLinearPlaneUnipotent (map first) (map second) := by
  apply Subtype.ext
  ext row column
  fin_cases row <;> fin_cases column <;> simp [specialLinearPlaneUnipotent, Matrix.SpecialLinearGroup.map]

theorem specialLinearPlaneUnipotent_real (first second : ℝ) :
    specialLinearPlaneUnipotent first second = realSpecialPlane first second := rfl

theorem specialLinearPlaneLevi_unipotent_mul {R : Type*} [CommRing R]
    (binary : SpecialLinearGroup (Fin 2) R) (coordinates : Fin 2 → R) :
    specialLinearPlaneLevi binary * specialLinearPlaneUnipotent (coordinates 0) (coordinates 1) =
      specialLinearPlaneUnipotent ((binary.val *ᵥ coordinates) 0) ((binary.val *ᵥ coordinates) 1) *
        specialLinearPlaneLevi binary := by
  apply Subtype.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [specialLinearPlaneLevi, specialLinearPlaneUnipotent, planeBlock, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem realPlaneBase_levi_mul (binary : SpecialLinearGroup (Fin 2) ℝ)
    (matrix : SpecialLinearGroup (Fin 3) ℝ) :
    realPlaneBase (specialLinearPlaneLevi binary * matrix) =
      specialLinearPlaneLevi binary * realPlaneBase matrix := by
  have translated := specialLinearPlaneLevi_unipotent_mul binary (realPlaneCoordinate matrix)
  simp only [specialLinearPlaneUnipotent_real] at translated
  calc
    realPlaneBase (specialLinearPlaneLevi binary * matrix) =
        realPlaneBase (specialLinearPlaneLevi binary *
          (realSpecialPlane (realPlaneCoordinate matrix 0) (realPlaneCoordinate matrix 1) *
            realPlaneBase matrix)) := by rw [realPlaneBase_factorization]
    _ = realPlaneBase (realSpecialPlane ((binary.val *ᵥ realPlaneCoordinate matrix) 0)
        ((binary.val *ᵥ realPlaneCoordinate matrix) 1) *
        (specialLinearPlaneLevi binary * realPlaneBase matrix)) := by rw [← mul_assoc, translated, mul_assoc]
    _ = realPlaneBase (specialLinearPlaneLevi binary * realPlaneBase matrix) :=
      realPlaneBase_plane_mul _ _
    _ = _ := realPlaneBase_of_mem_normalSet _
      (realPlaneNormalSet_levi_invariant binary _ (realPlaneBase_mem_normalSet matrix))

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
