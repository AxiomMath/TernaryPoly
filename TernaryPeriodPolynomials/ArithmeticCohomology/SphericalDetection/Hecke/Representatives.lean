module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.PrimeReduction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

local instance heckeRepresentativesPrimeFact (prime : Nat.Primes) : Fact prime.val.Prime := ⟨prime.property⟩

def binaryHeckeRepresentative (prime : Nat.Primes) : Option (Fin prime.val) → BinaryRationalGL
  | none => binaryHeckeDilate prime.val prime.property.pos
  | some index => binaryHeckeTranslate prime.val prime.property.pos index

def binaryHeckeIntegralMatrix (prime : Nat.Primes) :
    Option (Fin prime.val) → Matrix (Fin 2) (Fin 2) IntegralAdeles
  | none => !![(prime.val : IntegralAdeles), 0; 0, 1]
  | some index => !![1, (index.val : IntegralAdeles); 0, (prime.val : IntegralAdeles)]

theorem binaryHeckeIntegralMatrix_map (prime : Nat.Primes) (index : Option (Fin prime.val)) :
    integralEmbedding.mapMatrix (binaryHeckeIntegralMatrix prime index) =
      (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) (binaryHeckeRepresentative prime index)).val := by
  cases index with
  | none =>
    funext row column
    fin_cases row <;> fin_cases column <;>
      simp [binaryHeckeIntegralMatrix, binaryHeckeRepresentative, binaryHeckeDilate]
  | some index =>
    funext row column
    fin_cases row <;> fin_cases column <;>
      simp [binaryHeckeIntegralMatrix, binaryHeckeRepresentative, binaryHeckeTranslate]

theorem binaryHeckeIntegralMatrix_det (prime : Nat.Primes) (index : Option (Fin prime.val)) :
    (binaryHeckeIntegralMatrix prime index).det = prime.val := by
  cases index <;> simp [binaryHeckeIntegralMatrix, Matrix.det_fin_two]

theorem binaryHeckeRepresentative_finite_det (prime : Nat.Primes) (index : Option (Fin prime.val)) :
    (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) (binaryHeckeRepresentative prime index)).val.det =
      prime.val := by
  rw [← binaryHeckeIntegralMatrix_map, ← RingHom.map_det, binaryHeckeIntegralMatrix_det, map_natCast]

def binaryHeckeIndexEquiv (prime : Nat.Primes) : Option (Fin prime.val) ≃ OnePoint (ZMod prime.val) :=
  Equiv.optionCongr ((ZMod.finEquiv prime.val).toEquiv.trans (Equiv.neg (ZMod prime.val)))

theorem binaryHeckeIndexEquiv_none (prime : Nat.Primes) :
    binaryHeckeIndexEquiv prime none = OnePoint.infty := rfl

theorem binaryHeckeIndexEquiv_some (prime : Nat.Primes) (index : Fin prime.val) :
    binaryHeckeIndexEquiv prime (some index) = (((-(index.val : ZMod prime.val)) : ZMod prime.val) : OnePoint (ZMod prime.val)) := by
  rcases prime with ⟨prime, prime_property⟩
  cases prime with
  | zero => exact (prime_property.ne_zero rfl).elim
  | succ prime =>
    change some (-(index : ZMod (prime + 1))) = some (-(index.val : ZMod (prime + 1)))
    congr 2
    exact (Fin.cast_val_eq_self index).symm

def binaryHeckePermutation (prime : Nat.Primes) (compact : GeneralLinearGroup (Fin 2) IntegralAdeles) :
    Equiv.Perm (Option (Fin prime.val)) :=
  ((binaryHeckeIndexEquiv prime).trans
    (MulAction.toPerm (GeneralLinearGroup.map (integralPrimeReduction prime) compact))).trans
      (binaryHeckeIndexEquiv prime).symm

theorem binaryHeckePermutation_spec (prime : Nat.Primes) (compact : GeneralLinearGroup (Fin 2) IntegralAdeles)
    (index : Option (Fin prime.val)) :
    GeneralLinearGroup.map (integralPrimeReduction prime) compact • binaryHeckeIndexEquiv prime index =
      binaryHeckeIndexEquiv prime (binaryHeckePermutation prime compact index) := by
  simp [binaryHeckePermutation]

def residueHeckeMatrix {field : Type*} [Field field] : Option field → Matrix (Fin 2) (Fin 2) field
  | none => !![0, 0; 0, 1]
  | some scalar => !![1, scalar; 0, 0]

def residueHeckePoint {field : Type*} [Field field] : Option field → OnePoint field
  | none => OnePoint.infty
  | some scalar => (-scalar : field)

theorem residueHeckeMatrix_transition {field : Type*} [Field field] [DecidableEq field]
    (matrix : GeneralLinearGroup (Fin 2) field) (source target : Option field)
    (transforms : matrix • residueHeckePoint source = residueHeckePoint target) :
    residueHeckeMatrix target * matrix.val * (residueHeckeMatrix source).adjugate = 0 := by
  cases source with
  | none =>
    cases target with
    | none =>
      have bottom : matrix.val 1 0 = 0 := OnePoint.smul_infty_eq_self_iff.mp transforms
      ext row column
      fin_cases row <;> fin_cases column <;>
        simp [residueHeckeMatrix, Matrix.adjugate_fin_two, Matrix.mul_apply, Matrix.vecMul, dotProduct,
          Fin.sum_univ_two, bottom]
    | some scalar =>
      change matrix • OnePoint.infty = ((-scalar : field) : OnePoint field) at transforms
      rw [OnePoint.smul_infty_eq_ite] at transforms
      split_ifs at transforms with bottom
      · exact (OnePoint.coe_ne_infty (-scalar) transforms.symm).elim
      · have ratio : matrix.val 0 0 / matrix.val 1 0 = -scalar := OnePoint.coe_injective transforms
        have numerator : matrix.val 0 0 + scalar * matrix.val 1 0 = 0 := by
          have equality := (div_eq_iff bottom).mp ratio
          linear_combination equality
        ext row column
        fin_cases row <;> fin_cases column <;>
          simp [residueHeckeMatrix, Matrix.adjugate_fin_two, Matrix.mul_apply, Matrix.vecMul, dotProduct,
            Fin.sum_univ_two, numerator]
  | some source =>
    cases target with
    | none =>
      change matrix • ((-source : field) : OnePoint field) = OnePoint.infty at transforms
      rw [OnePoint.smul_some_eq_ite] at transforms
      split_ifs at transforms with bottom
      · have numerator : matrix.val 1 1 - matrix.val 1 0 * source = 0 := by linear_combination bottom
        ext row column
        fin_cases row <;> fin_cases column <;>
          simp [residueHeckeMatrix, Matrix.adjugate_fin_two, Matrix.mul_apply, Matrix.vecMul, dotProduct,
            Fin.sum_univ_two]
        linear_combination numerator
      · exact (OnePoint.coe_ne_infty _ transforms).elim
    | some target =>
      change matrix • ((-source : field) : OnePoint field) = ((-target : field) : OnePoint field) at transforms
      rw [OnePoint.smul_some_eq_ite] at transforms
      split_ifs at transforms with bottom
      · exact (OnePoint.coe_ne_infty _ transforms.symm).elim
      · have ratio : (matrix.val 0 0 * (-source) + matrix.val 0 1) /
            (matrix.val 1 0 * (-source) + matrix.val 1 1) = -target := OnePoint.coe_injective transforms
        have numerator : -(matrix.val 0 0 + target * matrix.val 1 0) * source +
            (matrix.val 0 1 + target * matrix.val 1 1) = 0 := by
          have equality := (div_eq_iff bottom).mp ratio
          linear_combination equality
        ext row column
        fin_cases row <;> fin_cases column <;>
          simp [residueHeckeMatrix, Matrix.adjugate_fin_two, Matrix.mul_apply, Matrix.vecMul, dotProduct,
            Fin.sum_univ_two]
        linear_combination numerator

theorem binaryHeckeIntegralMatrix_reduce (prime : Nat.Primes) (index : Option (Fin prime.val)) :
    (integralPrimeReduction prime).mapMatrix (binaryHeckeIntegralMatrix prime index) =
      residueHeckeMatrix (index.map (fun value => (value.val : ZMod prime.val))) := by
  cases index with
  | none =>
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [binaryHeckeIntegralMatrix, residueHeckeMatrix]
  | some index =>
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [binaryHeckeIntegralMatrix, residueHeckeMatrix]

theorem binaryHeckeIndexEquiv_eq_point (prime : Nat.Primes) (index : Option (Fin prime.val)) :
    binaryHeckeIndexEquiv prime index =
      residueHeckePoint (index.map (fun value => (value.val : ZMod prime.val))) := by
  cases index with
  | none => rfl
  | some index => exact binaryHeckeIndexEquiv_some prime index

theorem binaryHeckePermutation_reduction_zero (prime : Nat.Primes)
    (compact : GeneralLinearGroup (Fin 2) IntegralAdeles) (index : Option (Fin prime.val)) :
    (integralPrimeReduction prime).mapMatrix
      (binaryHeckeIntegralMatrix prime (binaryHeckePermutation prime compact index) * compact.val *
        (binaryHeckeIntegralMatrix prime index).adjugate) = 0 := by
  rw [map_mul, map_mul, RingHom.map_adjugate, binaryHeckeIntegralMatrix_reduce,
    binaryHeckeIntegralMatrix_reduce]
  apply residueHeckeMatrix_transition (GeneralLinearGroup.map (integralPrimeReduction prime) compact)
  simpa only [binaryHeckeIndexEquiv_eq_point] using binaryHeckePermutation_spec prime compact index

theorem binaryHeckePermutation_transition_integral (prime : Nat.Primes)
    (compact : GeneralLinearGroup (Fin 2) IntegralAdeles) (index : Option (Fin prime.val)) :
    GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles)
        (binaryHeckeRepresentative prime (binaryHeckePermutation prime compact index)) *
      GeneralLinearGroup.map integralEmbedding compact *
      (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) (binaryHeckeRepresentative prime index))⁻¹ ∈
        finiteIntegralGLLevel 2 := by
  let source := GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) (binaryHeckeRepresentative prime index)
  let target := GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles)
    (binaryHeckeRepresentative prime (binaryHeckePermutation prime compact index))
  let finite_compact := GeneralLinearGroup.map integralEmbedding compact
  let transition := target * finite_compact * source⁻¹
  let numerator := binaryHeckeIntegralMatrix prime (binaryHeckePermutation prime compact index) * compact.val *
    (binaryHeckeIntegralMatrix prime index).adjugate
  have numerator_zero : (integralPrimeReduction prime).mapMatrix numerator = 0 :=
    binaryHeckePermutation_reduction_zero prime compact index
  have divisible (row column : Fin 2) : (prime.val : IntegralAdeles) ∣ numerator row column := by
    apply (integralPrimeReduction_zero_iff_dvd prime _).mp
    exact congrArg (fun matrix : Matrix (Fin 2) (Fin 2) (ZMod prime.val) => matrix row column) numerator_zero
  choose quotient_values quotient_values_eq using divisible
  let quotient : Matrix (Fin 2) (Fin 2) IntegralAdeles := quotient_values
  have divided : integralEmbedding.mapMatrix numerator =
      (prime.val : FiniteAdeles) • integralEmbedding.mapMatrix quotient := by
    funext row column
    change integralEmbedding (numerator row column) =
      (prime.val : FiniteAdeles) * integralEmbedding (quotient_values row column)
    rw [quotient_values_eq, map_mul, map_natCast]
  have adjugate_eq : source.val.adjugate = (prime.val : FiniteAdeles) • source⁻¹.val := by
    have identity := congrArg (fun matrix : Matrix (Fin 2) (Fin 2) FiniteAdeles => matrix * source⁻¹.val)
      (Matrix.adjugate_mul source.val)
    rw [Matrix.mul_assoc, source.mul_inv, mul_one, Matrix.smul_mul, one_mul,
      binaryHeckeRepresentative_finite_det] at identity
    exact identity
  have multiplied : integralEmbedding.mapMatrix numerator = (prime.val : FiniteAdeles) • transition.val := by
    change integralEmbedding.mapMatrix (_ * _ * _) = _
    rw [map_mul, map_mul, RingHom.map_adjugate, binaryHeckeIntegralMatrix_map,
      binaryHeckeIntegralMatrix_map]
    change target.val * finite_compact.val * source.val.adjugate = _
    rw [adjugate_eq, Matrix.mul_smul]
    rfl
  have prime_unit : IsUnit (prime.val : FiniteAdeles) := by
    have unit : IsUnit (prime.val : ℚ) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr prime.property.ne_zero)
    simpa only [map_natCast] using unit.map (algebraMap ℚ FiniteAdeles)
  have quotient_eq : integralEmbedding.mapMatrix quotient = transition.val := by
    funext row column
    apply prime_unit.mul_left_cancel
    exact congrArg (fun matrix : Matrix (Fin 2) (Fin 2) FiniteAdeles => matrix row column)
      (divided.symm.trans multiplied)
  apply finiteIntegralGLLevel_mem_of_entries_det transition
    (fun row column => ⟨quotient row column, congrArg (fun matrix : Matrix (Fin 2) (Fin 2) FiniteAdeles =>
      matrix row column) quotient_eq⟩) (GeneralLinearGroup.det compact)
  change (target.val * finite_compact.val * source⁻¹.val).det = integralEmbedding compact.val.det
  rw [Matrix.det_mul, Matrix.det_mul]
  have same_det : target.val.det = source.val.det := by
    rw [binaryHeckeRepresentative_finite_det, binaryHeckeRepresentative_finite_det]
  rw [same_det, mul_right_comm, ← Matrix.det_mul, source.mul_inv, Matrix.det_one, one_mul]
  exact (RingHom.map_det integralEmbedding compact.val).symm

end TernaryPeriodPolynomials.SphericalDetection.Helpers
