module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.PlaneLevelFactorization
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.FlatSectionRealFinite

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

structure FinitePlaneLevelCoordinates (argument : FiniteGL) where
  first : FiniteAdeles
  second : FiniteAdeles
  scalar : FiniteAdelesˣ
  block : BinaryFiniteGL
  compact : finiteLevel
  scalar_three : Units.map finiteThree.toMonoidHom scalar = 1
  block_three : GeneralLinearGroup.map finiteThree block = 1
  factorization : argument = planeUnipotent first second *
    (planeLevi 1 scalar * (planeLevi block 1 * compact.val))

theorem planeInduction_scalar_entry {R : Type*} [CommRing R]
    (first second : R) (scalar : Rˣ) (block : GeneralLinearGroup (Fin 2) R) :
    (planeUnipotent first second * (planeLevi 1 scalar * planeLevi block 1)).val 2 2 = scalar.val := by
  simp [planeUnipotent, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three]

theorem planeInduction_block_entry {R : Type*} [CommRing R]
    (first second : R) (scalar : Rˣ) (block : GeneralLinearGroup (Fin 2) R) (row column : Fin 2) :
    (planeUnipotent first second * (planeLevi 1 scalar * planeLevi block 1)).val row.castSucc column.castSucc =
      block.val row column := by
  fin_cases row <;> fin_cases column <;>
    simp [planeUnipotent, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three]

theorem planeInduction_coordinates_map_eq_one {R S : Type*} [CommRing R] [CommRing S]
    (hom : R →+* S) (first second : R) (scalar : Rˣ) (block : GeneralLinearGroup (Fin 2) R)
    (identity : GeneralLinearGroup.map hom
      (planeUnipotent first second * (planeLevi 1 scalar * planeLevi block 1)) = 1) :
    Units.map hom.toMonoidHom scalar = 1 ∧ GeneralLinearGroup.map hom block = 1 := by
  constructor
  · apply Units.ext
    have equality := congrArg (fun matrix : GeneralLinearGroup (Fin 3) S => matrix.val 2 2) identity
    change hom ((planeUnipotent first second * (planeLevi 1 scalar * planeLevi block 1)).val 2 2) = 1 at equality
    rw [planeInduction_scalar_entry] at equality
    exact equality
  · apply Units.ext
    funext row column
    have equality := congrArg (fun matrix : GeneralLinearGroup (Fin 3) S =>
      matrix.val row.castSucc column.castSucc) identity
    change hom ((planeUnipotent first second * (planeLevi 1 scalar * planeLevi block 1)).val
      row.castSucc column.castSucc) = (1 : Matrix (Fin 3) (Fin 3) S) row.castSucc column.castSucc at equality
    rw [planeInduction_block_entry] at equality
    fin_cases row <;> fin_cases column <;> exact equality

end TernaryPeriodPolynomials.SphericalDetection.Helpers
