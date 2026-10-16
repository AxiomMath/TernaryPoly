module

public import TernaryPeriodPolynomials.PeriodPolynomial.RationalHecke.Prime.Double
public import TernaryPeriodPolynomials.ModularForm.Hecke.Fourier

@[expose] public section

noncomputable section
open Matrix
open scoped MatrixGroups
namespace TernaryPoly.BinaryCuspHeckeEndomorphism
open BinaryModularSymbol (GL2)
open BinaryRationalHeckeArithmetic BinaryRationalHeckePrime

/-- Transposition as an actual invertible matrix, retaining its reversed multiplication law. -/
def transpose {R : Type*} [CommRing R] (g : Matrix.GeneralLinearGroup (Fin 2) R) :
    Matrix.GeneralLinearGroup (Fin 2) R :=
  ⟨g.val.transpose,g.inv.transpose,by rw [←Matrix.transpose_mul,g.inv_val,Matrix.transpose_one],
    by rw [←Matrix.transpose_mul,g.val_inv,Matrix.transpose_one]⟩

@[simp] theorem transpose_val {R : Type*} [CommRing R] (g : Matrix.GeneralLinearGroup (Fin 2) R) :
    (transpose g).val = g.val.transpose := rfl

@[simp] theorem transpose_transpose {R : Type*} [CommRing R] (g : Matrix.GeneralLinearGroup (Fin 2) R) :
    transpose (transpose g) = g := by apply Units.ext; exact Matrix.transpose_transpose _

@[simp] theorem transpose_mul {R : Type*} [CommRing R] (g h : Matrix.GeneralLinearGroup (Fin 2) R) :
    transpose (g*h) = transpose h * transpose g := by
  apply Units.ext
  exact Matrix.transpose_mul _ _

@[simp] theorem transpose_integral (g : RankTwoAugmentedFrames.IntegralGL) :
    transpose (integral g) = integral (transpose g) := rfl

/-- Transposition preserves the actual integral subgroup. -/
def transposeGamma (g : Gamma) : Gamma :=
  ⟨transpose g.val,by obtain ⟨h,hh⟩ := g.property; rw [←hh]; exact ⟨transpose h,rfl⟩⟩

/-- Scalar extension to the actual real matrix group acting on the upper half plane. -/
def realify : GL2 →* Matrix.GeneralLinearGroup (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.map (Rat.castHom ℝ)

/-- The upper triangular representatives in the standard cusp-form Hecke formula. -/
def upper (p : ℕ) [Fact p.Prime] (i : PrimeIndex p) : GL2 := transpose (primeRepresentative p i)

@[simp] theorem upper_matrix (p : ℕ) [Fact p.Prime] (i : PrimeIndex p) :
    (upper p i).val = match i with
      | .inl b => !![1,(b.val : ℚ);0,(p : ℚ)]
      | .inr _ => !![(p : ℚ),0;0,1] := by
  rw [upper,transpose_val,primeRepresentative_matrix]
  cases i <;> ext j k <;> fin_cases j <;> fin_cases k <;> rfl

@[simp] theorem det_primeRepresentative (p : ℕ) [Fact p.Prime] (i : PrimeIndex p) :
    (primeRepresentative p i).val.det = (p : ℚ) := by
  rw [primeRepresentative_matrix]
  cases i <;> simp [Matrix.det_fin_two]

@[simp] theorem det_upper (p : ℕ) [Fact p.Prime] (i : PrimeIndex p) :
    (upper p i).val.det = (p : ℚ) := by
  rw [upper,transpose_val,Matrix.det_transpose,det_primeRepresentative]

end TernaryPoly.BinaryCuspHeckeEndomorphism
