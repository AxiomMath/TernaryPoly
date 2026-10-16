module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Modular.HeckeCorrespondence

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def modularHeckeTrace (representation : Rep ℂ BinaryRationalGL) (prime : Nat.Primes) :
    (UpperHalfPlane → representation) →ₗ[ℂ] (UpperHalfPlane → representation) where
  toFun function point := ∑ index : Option (Fin prime.val),
    representation.ρ (binaryHeckeRepresentative prime index)⁻¹
      (function (GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeRepresentative prime index) • point))
  map_add' first second := by
    funext point
    simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' scalar function := by
    funext point
    simp only [Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]

theorem modularHeckeTrace_apply (representation : Rep ℂ BinaryRationalGL) (prime : Nat.Primes)
    (function : UpperHalfPlane → representation) (point : UpperHalfPlane) :
    modularHeckeTrace representation prime function point = ∑ index : Option (Fin prime.val),
      representation.ρ (binaryHeckeRepresentative prime index)⁻¹
        (function (GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeRepresentative prime index) • point)) := rfl

theorem modularHeckeTransition_coefficient (representation : Rep ℂ BinaryRationalGL) (prime : Nat.Primes)
    (matrix : SpecialLinearGroup (Fin 2) ℤ) (index : Option (Fin prime.val)) :
    representation.ρ (binaryHeckeRepresentative prime (modularHeckePermutation prime matrix index))⁻¹ *
      representation.ρ (GeneralLinearGroup.map (Int.castRingHom ℚ)
        (SpecialLinearGroup.toGL (modularHeckeTransition prime matrix index))) =
    representation.ρ (GeneralLinearGroup.map (Int.castRingHom ℚ) (SpecialLinearGroup.toGL matrix)) *
      representation.ρ (binaryHeckeRepresentative prime index)⁻¹ := by
  rw [← map_mul, ← map_mul]
  congr 1
  apply inv_mul_eq_iff_eq_mul.mpr
  rw [← mul_assoc, modularHeckeTransition_rational, mul_inv_cancel_right]

theorem modularHeckeTrace_equivariant (representation : Rep ℂ BinaryRationalGL) (prime : Nat.Primes)
    (function : UpperHalfPlane → representation)
    (equivariant : ∀ (matrix : SpecialLinearGroup (Fin 2) ℤ) (point : UpperHalfPlane),
      function (GeneralLinearGroup.map (algebraMap ℚ ℝ)
        (GeneralLinearGroup.map (Int.castRingHom ℚ) (SpecialLinearGroup.toGL matrix)) • point) =
      representation.ρ (GeneralLinearGroup.map (Int.castRingHom ℚ) (SpecialLinearGroup.toGL matrix)) (function point))
    (matrix : SpecialLinearGroup (Fin 2) ℤ) (point : UpperHalfPlane) :
    modularHeckeTrace representation prime function
        (GeneralLinearGroup.map (algebraMap ℚ ℝ)
          (GeneralLinearGroup.map (Int.castRingHom ℚ) (SpecialLinearGroup.toGL matrix)) • point) =
      representation.ρ (GeneralLinearGroup.map (Int.castRingHom ℚ) (SpecialLinearGroup.toGL matrix))
        (modularHeckeTrace representation prime function point) := by
  rw [modularHeckeTrace_apply, modularHeckeTrace_apply, map_sum]
  rw [← Equiv.sum_comp (modularHeckePermutation prime matrix)]
  apply Finset.sum_congr rfl
  intro index _
  rw [← mul_smul, ← map_mul, modularHeckeTransition_rational, map_mul, mul_smul, equivariant]
  exact congrArg (fun action : Module.End ℂ representation => action
    (function (GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeRepresentative prime index) • point)))
      (modularHeckeTransition_coefficient representation prime matrix index)

theorem modularHeckeTrace_const (representation : Rep ℂ BinaryRationalGL) (prime : Nat.Primes)
    (potential : representation) (point : UpperHalfPlane) :
    modularHeckeTrace representation prime (fun _ => potential) point =
      ∑ index : Option (Fin prime.val), representation.ρ (binaryHeckeRepresentative prime index)⁻¹ potential := rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
