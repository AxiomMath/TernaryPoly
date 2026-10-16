module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.PlaneCoordinateIndependence

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def planeOppositeStandardMatrix {R : Type*} [CommRing R] (first second : R) : GeneralLinearGroup (Fin 3) R :=
  ⟨!![0,1,0;1,0,0;second,first,1], !![0,1,0;1,0,0;-first,-second,1], by
    funext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_three], by
    funext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

def planeFirstPivotCompact {R : Type*} [CommRing R] (ratio reciprocal : R) : GeneralLinearGroup (Fin 3) R :=
  ⟨!![1,0,0;0,0,1;ratio,1,reciprocal], !![1,0,0;-ratio,-reciprocal,1;0,1,0], by
    funext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_three], by
    funext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

def planeSecondPivotCompact {R : Type*} [CommRing R] (ratio reciprocal : R) : GeneralLinearGroup (Fin 3) R :=
  ⟨!![0,1,0;0,0,1;1,ratio,reciprocal], !![-ratio,-reciprocal,1;1,0,0;0,1,0], by
    funext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_three], by
    funext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem unit_mul_middle_inv {R : Type*} [CommRing R] (unit : Rˣ) (value : R) :
    unit.val * (value * unit.inv) = value := by
  calc
    unit.val * (value * unit.inv) = value * (unit.val * unit.inv) := by ring
    _ = value := by rw [unit.val_inv, mul_one]

def planeFirstPivotBinary {R : Type*} [CommRing R] (pivot : Rˣ) (other : R) : GeneralLinearGroup (Fin 2) R :=
  ⟨!![-other * pivot.inv,-pivot.inv;1,0], !![0,1;-pivot.val,-other], by
    funext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm], by
    funext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
    exact (congrArg (fun value : R => value + -other)
      (unit_mul_middle_inv pivot other)).trans (add_neg_cancel other)⟩

def planeSecondPivotBinary {R : Type*} [CommRing R] (pivot : Rˣ) (other : R) : GeneralLinearGroup (Fin 2) R :=
  ⟨!![1,0;-other * pivot.inv,-pivot.inv], !![1,0;-other,-pivot.val], by
    funext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm], by
    funext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
    exact (congrArg (fun value : R => -other + value)
      (unit_mul_middle_inv pivot other)).trans (neg_add_cancel other)⟩

theorem planeFirstPivotCompact_map {R S : Type*} [CommRing R] [CommRing S]
    (hom : R →+* S) (ratio reciprocal : R) :
    GeneralLinearGroup.map hom (planeFirstPivotCompact ratio reciprocal) =
      planeFirstPivotCompact (hom ratio) (hom reciprocal) := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;> simp [planeFirstPivotCompact, GeneralLinearGroup.map_apply]

theorem planeSecondPivotCompact_map {R S : Type*} [CommRing R] [CommRing S]
    (hom : R →+* S) (ratio reciprocal : R) :
    GeneralLinearGroup.map hom (planeSecondPivotCompact ratio reciprocal) =
      planeSecondPivotCompact (hom ratio) (hom reciprocal) := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;> simp [planeSecondPivotCompact, GeneralLinearGroup.map_apply]

theorem planeFirstPivotBinary_det {R : Type*} [CommRing R] (pivot : Rˣ) (other : R) :
    GeneralLinearGroup.det (planeFirstPivotBinary pivot other) = pivot⁻¹ := by
  apply Units.ext
  simp [GeneralLinearGroup.val_det_apply, planeFirstPivotBinary, Matrix.det_fin_two]

theorem planeSecondPivotBinary_det {R : Type*} [CommRing R] (pivot : Rˣ) (other : R) :
    GeneralLinearGroup.det (planeSecondPivotBinary pivot other) = -pivot⁻¹ := by
  apply Units.ext
  simp [GeneralLinearGroup.val_det_apply, planeSecondPivotBinary, Matrix.det_fin_two]

theorem planeOppositeStandard_first_pivot {R : Type*} [CommRing R] (pivot : Rˣ) (other : R) :
    planeOppositeStandardMatrix pivot.val other = planeUnipotent pivot.inv 0 *
      (planeLevi 1 pivot * (planeLevi (planeFirstPivotBinary pivot other) 1 *
        planeFirstPivotCompact (other * pivot.inv) pivot.inv)) := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [planeOppositeStandardMatrix, planeUnipotent, planeLevi, planeBlock, planeFirstPivotBinary,
      planeFirstPivotCompact, Matrix.mul_apply, Fin.sum_univ_three, mul_comm]
  exact (unit_mul_middle_inv pivot other).symm

theorem planeOppositeStandard_second_pivot {R : Type*} [CommRing R] (pivot : Rˣ) (other : R) :
    planeOppositeStandardMatrix other pivot.val = planeUnipotent 0 pivot.inv *
      (planeLevi 1 pivot * (planeLevi (planeSecondPivotBinary pivot other) 1 *
        planeSecondPivotCompact (other * pivot.inv) pivot.inv)) := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [planeOppositeStandardMatrix, planeUnipotent, planeLevi, planeBlock, planeSecondPivotBinary,
      planeSecondPivotCompact, Matrix.mul_apply, Fin.sum_univ_three, mul_comm]
  exact (unit_mul_middle_inv pivot other).symm

end TernaryPeriodPolynomials.SphericalDetection.Helpers
