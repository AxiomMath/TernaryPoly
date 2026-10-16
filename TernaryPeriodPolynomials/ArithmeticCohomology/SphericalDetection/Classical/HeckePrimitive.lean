module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.HeckeCoefficient

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def modularHeckePointDerivative (prime : Nat.Primes) : Option (Fin prime.val) → ℂ
  | none => prime.val
  | some _ => (prime.val : ℂ)⁻¹

theorem modularHeckePoint_hasDerivAt (prime : Nat.Primes) (index : Option (Fin prime.val)) (point : ℂ) :
    HasDerivAt (modularHeckePoint prime index) (modularHeckePointDerivative prime index) point := by
  cases index with
  | none =>
    have result := (hasDerivAt_id point).const_mul (prime.val : ℂ)
    rw [mul_one] at result
    convert result using 1 <;> rfl
  | some index =>
    have result := ((hasDerivAt_id point).add_const (index.val : ℂ)).div_const (prime.val : ℂ)
    rw [one_div] at result
    convert result using 1 <;> rfl

def classicalHeckePrimitive {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (twist : ℤ) (prime : Nat.Primes) (point : ℂ) : Binary.HomogeneousPoly degree :=
  let action : Option (Fin prime.val) → Module.End ℂ (Binary.HomogeneousPoly degree) :=
    fun index => (rationalBinaryRep degree twist).ρ (binaryHeckeRepresentative prime index)⁻¹
  ∑ index : Option (Fin prime.val), action index (classicalBinaryPrimitive form degree (modularHeckePoint prime index point))

theorem classicalHeckePrimitive_eq_trace {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (twist : ℤ) (prime : Nat.Primes) (point : UpperHalfPlane) :
    classicalHeckePrimitive form degree twist prime point =
      modularHeckeTrace (rationalBinaryRep degree twist) prime
        (fun point => classicalBinaryPrimitive form degree point) point := by
  let action : Option (Fin prime.val) → Module.End ℂ (Binary.HomogeneousPoly degree) :=
    fun index => (rationalBinaryRep degree twist).ρ (binaryHeckeRepresentative prime index)⁻¹
  change (∑ index : Option (Fin prime.val), action index
      (classicalBinaryPrimitive form degree (modularHeckePoint prime index point))) =
    ∑ index : Option (Fin prime.val), action index (classicalBinaryPrimitive form degree
      ((GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeRepresentative prime index) • point : UpperHalfPlane) : ℂ))
  apply Finset.sum_congr rfl
  intro index _
  exact congrArg (fun argument : ℂ => action index (classicalBinaryPrimitive form degree argument))
    (modularHeckePoint_upper prime index point).symm

theorem classicalHeckePrimitive_functional_hasDerivAt {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (twist : ℤ) (prime : Nat.Primes)
    (functional : Binary.HomogeneousPoly degree →ₗ[ℂ] ℂ) (point : ℂ) (positive : 0 < point.im) :
    HasDerivAt (fun point => functional (classicalHeckePrimitive form degree twist prime point))
      (∑ index : Option (Fin prime.val),
        functional ((rationalBinaryRep degree twist).ρ (binaryHeckeRepresentative prime index)⁻¹
          (classicalBinaryForm form degree (modularHeckePoint prime index point))) *
            modularHeckePointDerivative prime index) point := by
  let action : Option (Fin prime.val) → Module.End ℂ (Binary.HomogeneousPoly degree) :=
    fun index => (rationalBinaryRep degree twist).ρ (binaryHeckeRepresentative prime index)⁻¹
  have derivative (index : Option (Fin prime.val)) :
      HasDerivAt (fun point => (functional.comp (action index))
          (classicalBinaryPrimitive form degree (modularHeckePoint prime index point)))
        ((functional.comp (action index)) (classicalBinaryForm form degree (modularHeckePoint prime index point)) *
          modularHeckePointDerivative prime index) point :=
    (classicalBinaryPrimitive_hasDerivAt form degree (functional.comp (action index)) _
      (modularHeckePoint_im_pos prime index point positive)).comp point (modularHeckePoint_hasDerivAt prime index point)
  have result := HasDerivAt.fun_sum (u := Finset.univ) (fun index _ => derivative index)
  convert result using 1
  all_goals first | (funext argument; exact map_sum functional _ _)

theorem classicalHeckePrimitive_differential {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (twist : ℤ) (prime : Nat.Primes)
    (functional : Binary.HomogeneousPoly degree →ₗ[ℂ] ℂ) (point : ℂ) (positive : 0 < point.im) :
    HasDerivAt (fun point => functional (classicalHeckePrimitive form degree twist prime point))
      (((prime.val : ℂ) ^ (-twist) * (prime.val : ℂ) ^ (degree + 1) *
          form (UpperHalfPlane.ofComplex (modularHeckePoint prime none point)) +
        (prime.val : ℂ) ^ (-twist) * (prime.val : ℂ)⁻¹ *
          ∑ index : Fin prime.val, form (UpperHalfPlane.ofComplex (modularHeckePoint prime (some index) point))) *
        functional (binaryPointPower degree point)) point := by
  let action : Option (Fin prime.val) → Module.End ℂ (Binary.HomogeneousPoly degree) :=
    fun index => (rationalBinaryRep degree twist).ρ (binaryHeckeRepresentative prime index)⁻¹
  have first : action none (classicalBinaryForm form degree (modularHeckePoint prime none point)) =
      form (UpperHalfPlane.ofComplex (modularHeckePoint prime none point)) •
        (((prime.val : ℂ) ^ (-twist) * (prime.val : ℂ) ^ degree) • binaryPointPower degree point) := by
    rw [classicalBinaryForm, map_smul]
    exact congrArg (form (UpperHalfPlane.ofComplex (modularHeckePoint prime none point)) • ·)
      (rationalBinaryRep_hecke_dilate_pointPower degree twist prime point)
  have other (index : Fin prime.val) :
      action (some index) (classicalBinaryForm form degree (modularHeckePoint prime (some index) point)) =
        form (UpperHalfPlane.ofComplex (modularHeckePoint prime (some index) point)) •
          ((prime.val : ℂ) ^ (-twist) • binaryPointPower degree point) := by
    rw [classicalBinaryForm, map_smul]
    exact congrArg (form (UpperHalfPlane.ofComplex (modularHeckePoint prime (some index) point)) • ·)
      (rationalBinaryRep_hecke_translate_pointPower degree twist prime index point)
  have result := classicalHeckePrimitive_functional_hasDerivAt form degree twist prime functional point positive
  change HasDerivAt _ (∑ index : Option (Fin prime.val),
    functional (action index (classicalBinaryForm form degree (modularHeckePoint prime index point))) *
      modularHeckePointDerivative prime index) point at result
  rw [Fintype.sum_option, first] at result
  simp_rw [other, map_smul, smul_eq_mul] at result
  have coefficient :
      (form (UpperHalfPlane.ofComplex (modularHeckePoint prime none point)) *
          ((prime.val : ℂ) ^ (-twist) * (prime.val : ℂ) ^ degree * functional (binaryPointPower degree point)) *
            (prime.val : ℂ) +
        ∑ index : Fin prime.val,
          form (UpperHalfPlane.ofComplex (modularHeckePoint prime (some index) point)) *
            ((prime.val : ℂ) ^ (-twist) * functional (binaryPointPower degree point)) * (prime.val : ℂ)⁻¹) =
      ((prime.val : ℂ) ^ (-twist) * (prime.val : ℂ) ^ (degree + 1) *
          form (UpperHalfPlane.ofComplex (modularHeckePoint prime none point)) +
        (prime.val : ℂ) ^ (-twist) * (prime.val : ℂ)⁻¹ *
          ∑ index : Fin prime.val, form (UpperHalfPlane.ofComplex (modularHeckePoint prime (some index) point))) *
        functional (binaryPointPower degree point) := by
    rw [← Finset.sum_mul, ← Finset.sum_mul, pow_succ]
    ring
  exact coefficient ▸ result

end TernaryPeriodPolynomials.SphericalDetection.Helpers
