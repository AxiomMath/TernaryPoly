module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.IntegerRows
public import Mathlib.Algebra.Module.ZLattice.Summable
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.PSeries

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.FlagSummability

def integerLattice : Submodule ℤ (Fin 3 → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 3)))

instance integerLattice_discrete : DiscreteTopology integerLattice :=
  ZSpan.discreteTopology_pi_basisFun

def integerEmbedding (row : Fin 3 → ℤ) : integerLattice :=
  ⟨∑ index, row index • Pi.basisFun ℝ (Fin 3) index,
    Submodule.sum_mem _ (fun index _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨index, rfl⟩))⟩

theorem integerEmbedding_val (row : Fin 3 → ℤ) :
    (integerEmbedding row).val = fun index => (row index : ℝ) := by
  ext index
  fin_cases index <;> simp [integerEmbedding, Pi.basisFun_apply, zsmul_eq_mul, Fin.sum_univ_succ]

theorem integerEmbedding_injective : Function.Injective integerEmbedding := by
  intro first second equality
  have coordinates := congrArg Subtype.val equality
  rw [integerEmbedding_val, integerEmbedding_val] at coordinates
  ext index
  exact Int.cast_injective (congrFun coordinates index)

theorem integerLattice_finrank : Module.finrank ℤ integerLattice = 3 := by
  unfold integerLattice
  rw [Module.finrank_eq_card_basis ((Pi.basisFun ℝ (Fin 3)).restrictScalars ℤ)]
  rfl

theorem integer_rows_summable (exponent : ℝ) (bound : exponent < -3) :
    Summable (fun row : Fin 3 → ℤ => ‖fun index => (row index : ℝ)‖ ^ exponent) := by
  have lattice := ZLattice.summable_norm_rpow integerLattice exponent (by
    rw [integerLattice_finrank]
    exact bound)
  have restricted := lattice.comp_injective integerEmbedding_injective
  change Summable (fun row => ‖(integerEmbedding row).val‖ ^ exponent) at restricted
  simpa only [integerEmbedding_val] using restricted

def flagHeight (flag : Flags .plane) : ℝ := ‖fun index => (IntegerRows.flagRow flag index : ℝ)‖

theorem flagHeight_pos (flag : Flags .plane) : 0 < flagHeight flag := by
  apply norm_pos_iff.mpr
  intro zero
  apply IntegerRows.flagRow_nonzero flag
  ext index
  apply Int.cast_injective (α := ℝ)
  simpa using congrFun zero index

theorem flagHeight_summable (exponent : ℝ) (bound : exponent < -3) :
    Summable (fun flag : Flags .plane => flagHeight flag ^ exponent) :=
  (integer_rows_summable exponent bound).comp_injective IntegerRows.flagRow_injective

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.FlagSummability
