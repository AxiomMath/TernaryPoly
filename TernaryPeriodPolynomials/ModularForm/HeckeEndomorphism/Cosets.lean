module

public import TernaryPeriodPolynomials.ModularForm.HeckeEndomorphism.Matrices

@[expose] public section


noncomputable section
namespace TernaryPoly.BinaryCuspHeckeEndomorphism
open BinaryModularSymbol (GL2)
open BinaryRationalHeckeArithmetic BinaryRationalHeckePrime

/-- Distinct upper representatives are disjoint modulo the actual left integral group. -/
theorem upper_disjoint (p : ℕ) [Fact p.Prime] (i j : PrimeIndex p) (c : Gamma)
    (hc : upper p i = c.val * upper p j) : i=j := by
  apply primeRepresentative_disjoint p i j (transposeGamma c)
  have h := congrArg transpose hc
  simpa only [upper,transpose_transpose,transpose_mul,transposeGamma] using h

/-- Transposing the proved right double-coset classification gives the actual upper left cosets. -/
theorem upper_mul_complete (p : ℕ) [Fact p.Prime] (g : Gamma) (i : PrimeIndex p) :
    ∃! j : PrimeIndex p, ∃ c : Gamma, upper p i * g.val = c.val * upper p j := by
  obtain ⟨a,b,hi⟩ := primeRepresentative_doubleCoset p i
  obtain ⟨j,⟨c,hc⟩,_hj⟩ := primeRepresentative_complete p (transposeGamma g * a) b
  have he : transpose g.val * primeRepresentative p i = primeRepresentative p j * c.val := by
    rw [hi]
    simpa only [Subgroup.coe_mul,transposeGamma,mul_assoc] using hc
  have ht : upper p i * g.val = (transposeGamma c).val * upper p j := by
    have h := congrArg transpose he
    simpa only [transpose_mul,transpose_transpose,upper,transposeGamma] using h
  refine ⟨j,⟨transposeGamma c,ht⟩,?_⟩
  intro k hk
  obtain ⟨c',hc'⟩ := hk
  apply upper_disjoint p k j (c'⁻¹ * transposeGamma c)
  have hz := congrArg (fun x : GL2 => c'.val⁻¹ * x) (hc'.symm.trans ht)
  simpa only [Subgroup.coe_mul,Subgroup.coe_inv,mul_assoc,inv_mul_cancel_left] using hz

/-- The actual permutation of prime left cosets induced by right multiplication. -/
def reindex (p : ℕ) [Fact p.Prime] (g : Gamma) (i : PrimeIndex p) : PrimeIndex p :=
  Classical.choose (upper_mul_complete p g i)

def factor (p : ℕ) [Fact p.Prime] (g : Gamma) (i : PrimeIndex p) : Gamma :=
  Classical.choose (Classical.choose_spec (upper_mul_complete p g i)).1

theorem factor_spec (p : ℕ) [Fact p.Prime] (g : Gamma) (i : PrimeIndex p) :
    upper p i * g.val = (factor p g i).val * upper p (reindex p g i) :=
  Classical.choose_spec (Classical.choose_spec (upper_mul_complete p g i)).1

theorem reindex_injective (p : ℕ) [Fact p.Prime] (g : Gamma) : Function.Injective (reindex p g) := by
  intro i j hij
  have hi := factor_spec p g i
  have hj := factor_spec p g j
  rw [hij] at hi
  apply upper_disjoint p i j (factor p g i * (factor p g j)⁻¹)
  have he : upper p i * g.val =
      ((factor p g i).val * (factor p g j).val⁻¹) * (upper p j * g.val) := by
    rw [hj,hi]
    group
  have hz := congrArg (fun x : GL2 => x * g.val⁻¹) he
  simpa only [Subgroup.coe_mul,Subgroup.coe_inv,mul_assoc,mul_inv_cancel,mul_one] using hz

def reindexEquiv (p : ℕ) [Fact p.Prime] (g : Gamma) : PrimeIndex p ≃ PrimeIndex p :=
  Equiv.ofBijective (reindex p g)
    ⟨reindex_injective p g,Finite.surjective_of_injective (reindex_injective p g)⟩

/-- Since all representatives have determinant p, the integral correcting matrix retains det g. -/
theorem factor_det (p : ℕ) [Fact p.Prime] (g : Gamma) (i : PrimeIndex p) :
    (factor p g i).val.val.det = g.val.val.det := by
  have he := congrArg (fun a : GL2 => a.val.det) (factor_spec p g i)
  simp only [Matrix.GeneralLinearGroup.coe_mul,Matrix.det_mul,det_upper] at he
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  apply mul_left_cancel₀ hp
  simpa only [mul_comm] using he.symm

end TernaryPoly.BinaryCuspHeckeEndomorphism
