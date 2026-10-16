module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.PeriodRegularity

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.OrdinaryResiduePeriod
open SinglePoleCoordinate

/-- The literal symmetric separately odd binary period equations define a rational linear subspace. -/
def binaryPeriods : Submodule ℚ Binary where
  carrier := {q | SymmetricBinaryPeriodRelations q}
  zero_mem' := by constructor <;> simp
  add_mem' := by
    intro p q hp hq
    constructor
    · rw [map_add,hp.swap,hq.swap]
    · rw [map_add,hp.odd_first,hq.odd_first,neg_add]
    · rw [map_add,hp.odd_second,hq.odd_second,neg_add]
    · simp only [map_add]
      linear_combination hp.period + hq.period
  smul_mem' := by
    intro c q hq
    constructor
    · rw [map_smul,hq.swap]
    · rw [map_smul,hq.odd_first,smul_neg]
    · rw [map_smul,hq.odd_second,smul_neg]
    · rw [map_smul,map_smul,←smul_sub,←smul_add,hq.period,smul_zero]

/-- B_n is the actual degree-n homogeneous binary period submodule, with all four literal equations. -/
def periodSpace (n : ℕ) : Submodule ℚ (BinaryV n) :=
  binaryPeriods.comap (BinaryV n).subtype

@[simp] theorem mem_periodSpace (n : ℕ) (q : BinaryV n) :
    q ∈ periodSpace n ↔ SymmetricBinaryPeriodRelations q.val := Iff.rfl

end TernaryPoly.OrdinaryResiduePeriod
