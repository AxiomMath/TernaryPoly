module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.ModularTransformation
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem binaryIntegral_mapGL_entry (R : Type*) [CommRing R] [Algebra ℤ R]
    (matrix : SpecialLinearGroup (Fin 2) ℤ) (row column : Fin 2) :
    (SpecialLinearGroup.mapGL R matrix).val row column = ((matrix.val row column : ℤ) : R) := by
  change algebraMap ℤ R (matrix.val row column) = _
  exact map_intCast (algebraMap ℤ R) _

theorem binaryIntegral_mapGL_map {R S : Type*} [CommRing R] [CommRing S] [Algebra ℤ R] [Algebra ℤ S]
    (ringMap : R →+* S) (matrix : SpecialLinearGroup (Fin 2) ℤ) :
    GeneralLinearGroup.map ringMap (SpecialLinearGroup.mapGL R matrix) = SpecialLinearGroup.mapGL S matrix := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  change ringMap ((SpecialLinearGroup.mapGL R matrix).val row column) =
    (SpecialLinearGroup.mapGL S matrix).val row column
  rw [binaryIntegral_mapGL_entry, binaryIntegral_mapGL_entry]
  exact map_intCast ringMap _

theorem binaryIntegral_adelic_factor (matrix : SpecialLinearGroup (Fin 2) ℤ) :
    GeneralLinearGroup.map rationalAdele (SpecialLinearGroup.mapGL ℚ matrix) =
      atInfinity (SpecialLinearGroup.mapGL ℝ matrix) * atFinite (SpecialLinearGroup.mapGL FiniteAdeles matrix) := by
  rw [binaryIntegral_mapGL_map]
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [atInfinity, atFinite, combineGL, pairMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      binaryIntegral_mapGL_entry] <;> rfl

theorem binaryIntegral_gamma_three_mem_principal (matrix : SpecialLinearGroup (Fin 2) ℤ)
    (member : matrix ∈ CongruenceSubgroup.Gamma 3) :
    SpecialLinearGroup.mapGL FiniteAdeles matrix ∈ binaryPrincipalLevel := by
  refine ⟨SpecialLinearGroup.mapGL IntegralAdeles matrix, ?_, binaryIntegral_mapGL_map integralEmbedding matrix⟩
  change GeneralLinearGroup.map integralReduction (SpecialLinearGroup.mapGL IntegralAdeles matrix) = 1
  rw [binaryIntegral_mapGL_map]
  change SpecialLinearGroup.toGL (SpecialLinearGroup.map (Int.castRingHom (ZMod 3)) matrix) = 1
  rw [CongruenceSubgroup.Gamma_mem'.mp member]
  simp

noncomputable def binaryRealPrincipalLevel : Subgroup BinaryRealGL :=
  (CongruenceSubgroup.Gamma 3).map (SpecialLinearGroup.mapGL ℝ)

theorem binaryRealPrincipalLevel_le_full :
    binaryRealPrincipalLevel ≤ (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range := by
  rintro matrix ⟨integralMatrix, _, equality⟩
  exact ⟨integralMatrix, equality⟩

theorem cusp_realize_integral_translation (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (integralMatrix : SpecialLinearGroup (Fin 2) ℤ)
    (fixed : cuspSmoothAction cusp (atFinite (SpecialLinearGroup.mapGL FiniteAdeles integralMatrix)) vector = vector)
    (matrix : BinaryRealGL) :
    cusp.realize vector (atInfinity (SpecialLinearGroup.mapGL ℝ integralMatrix) * atInfinity matrix) =
      cusp.realize vector (atInfinity matrix) := by
  have finite_identity (argument : BinaryAdelicGL) :=
    cusp.equivariant (atFinite (SpecialLinearGroup.mapGL FiniteAdeles integralMatrix)) vector argument
  change ∀ argument, cusp.realize
    (cuspSmoothAction cusp (atFinite (SpecialLinearGroup.mapGL FiniteAdeles integralMatrix)) vector) argument = _
    at finite_identity
  simp only [fixed] at finite_identity
  calc
    _ = cusp.realize vector ((atInfinity (SpecialLinearGroup.mapGL ℝ integralMatrix) * atInfinity matrix) *
        atFinite (SpecialLinearGroup.mapGL FiniteAdeles integralMatrix)) := finite_identity _
    _ = cusp.realize vector (GeneralLinearGroup.map rationalAdele (SpecialLinearGroup.mapGL ℚ integralMatrix) *
        atInfinity matrix) := by
      rw [binaryIntegral_adelic_factor, mul_assoc, binary_atInfinity_atFinite_commute matrix, ← mul_assoc]
    _ = _ := cusp.leftRational _ vector _

theorem cuspUpperHalfForm_integral_invariant (cusp : CuspidalRepresentation) (weight : ℝ)
    (vector : cuspFiniteFixedSubmodule cusp binaryPrincipalLevel)
    (matrix : SpecialLinearGroup (Fin 2) ℤ) (member : matrix ∈ CongruenceSubgroup.Gamma 3) :
    cuspUpperHalfForm cusp weight vector.val (atInfinity (SpecialLinearGroup.mapGL ℝ matrix)) =
      cuspUpperHalfForm cusp weight vector.val 1 := by
  have fixed : cuspSmoothAction cusp (atFinite (SpecialLinearGroup.mapGL FiniteAdeles matrix)) vector.val = vector.val :=
    Subtype.ext (vector.property ⟨_, binaryIntegral_gamma_three_mem_principal matrix member⟩)
  funext point
  simp only [cuspUpperHalfForm, cuspHolomorphicFunction, cuspUpperHalfOrbit_apply, one_mul,
    cusp_realize_integral_translation cusp vector.val matrix fixed]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
