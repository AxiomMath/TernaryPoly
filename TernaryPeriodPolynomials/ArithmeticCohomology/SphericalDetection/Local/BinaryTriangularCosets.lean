module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineFinitePivotValues

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def binaryPivotSwap {R : Type*} [CommRing R] : GeneralLinearGroup (Fin 2) R :=
  ⟨!![0,1;1,0], !![0,1;1,0], by
    funext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    funext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

def binaryUpperPivot {R : Type*} [CommRing R] (scale : Rˣ) (offset : R) : GeneralLinearGroup (Fin 2) R :=
  ⟨!![scale.val,offset;0,1], !![scale.inv,-scale.inv * offset;0,1], by
    funext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    funext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

def binaryLowerPivot {R : Type*} [CommRing R] (scale : Rˣ) (offset : R) : GeneralLinearGroup (Fin 2) R :=
  ⟨!![1,0;offset,scale.val], !![1,0;-scale.inv * offset,scale.inv], by
    funext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    funext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem binaryPivotSwap_map {R S : Type*} [CommRing R] [CommRing S] (hom : R →+* S) :
    GeneralLinearGroup.map hom binaryPivotSwap = binaryPivotSwap := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;> simp [binaryPivotSwap, GeneralLinearGroup.map_apply]

theorem binaryUpperPivot_map {R S : Type*} [CommRing R] [CommRing S] (hom : R →+* S)
    (scale : Rˣ) (offset : R) :
    GeneralLinearGroup.map hom (binaryUpperPivot scale offset) =
      binaryUpperPivot (Units.map hom.toMonoidHom scale) (hom offset) := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;> simp [binaryUpperPivot, GeneralLinearGroup.map_apply]

theorem binaryLowerPivot_map {R S : Type*} [CommRing R] [CommRing S] (hom : R →+* S)
    (scale : Rˣ) (offset : R) :
    GeneralLinearGroup.map hom (binaryLowerPivot scale offset) =
      binaryLowerPivot (Units.map hom.toMonoidHom scale) (hom offset) := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;> simp [binaryLowerPivot, GeneralLinearGroup.map_apply]

theorem binaryUpperPivot_mul {R : Type*} [CommRing R] (first second : Rˣ) (left right : R) :
    binaryUpperPivot first left * binaryUpperPivot second right =
      binaryUpperPivot (first * second) (left + first.val * right) := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [binaryUpperPivot, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem binaryLowerPivot_mul {R : Type*} [CommRing R] (first second : Rˣ) (left right : R) :
    binaryLowerPivot first left * binaryLowerPivot second right =
      binaryLowerPivot (first * second) (left + first.val * right) := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [binaryLowerPivot, Matrix.mul_apply, Fin.sum_univ_two]

theorem planeFirstPivotBinary_upper {R : Type*} [CommRing R] (pivot : Rˣ) (other : R) :
    planeFirstPivotBinary pivot other =
      binaryUpperPivot (-pivot⁻¹) (-other * pivot.inv) * binaryPivotSwap := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [planeFirstPivotBinary, binaryUpperPivot, binaryPivotSwap, Matrix.mul_apply, Fin.sum_univ_two]

theorem planeSecondPivotBinary_lower {R : Type*} [CommRing R] (pivot : Rˣ) (other : R) :
    planeSecondPivotBinary pivot other = binaryLowerPivot (-pivot⁻¹) (-other * pivot.inv) := by
  apply Units.ext
  rfl

theorem binaryUpperPivot_same_coset {R S : Type*} [CommRing R] [CommRing S] (hom : R →+* S)
    (scale : Sˣ) (offset : S) (unit : Rˣ) (shift : R) :
    binaryUpperPivot (scale * Units.map hom.toMonoidHom unit) (offset + scale.val * hom shift) =
      binaryUpperPivot scale offset * GeneralLinearGroup.map hom (binaryUpperPivot unit shift) := by
  rw [binaryUpperPivot_map, binaryUpperPivot_mul]

theorem binaryLowerPivot_same_coset {R S : Type*} [CommRing R] [CommRing S] (hom : R →+* S)
    (scale : Sˣ) (offset : S) (unit : Rˣ) (shift : R) :
    binaryLowerPivot (scale * Units.map hom.toMonoidHom unit) (offset + scale.val * hom shift) =
      binaryLowerPivot scale offset * GeneralLinearGroup.map hom (binaryLowerPivot unit shift) := by
  rw [binaryLowerPivot_map, binaryLowerPivot_mul]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
