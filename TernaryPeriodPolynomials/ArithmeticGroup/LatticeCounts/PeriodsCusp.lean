module

public import TernaryPeriodPolynomials.PeriodPolynomial.Defs
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Hecke.DictionaryCusp

@[expose] public section


open TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeDictionary
open TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeOperator
open Matrix UpperHalfPlane
open TernaryPeriodPolynomials.Argument.LatticeCounts

example {k : ℤ} (h : CuspForm TernaryPeriodPolynomials.Argument.levelOne k) {m : ℕ} (hm : 0 < m)
    (g : GL (Fin 2) ℝ) (hg : 0 < (Matrix.GeneralLinearGroup.det g).val) :
    ∑ t ∈ hnfData m, Fh k ⇑h (Gl t g) =
      (m : ℂ) ^ (1 - (k : ℂ) / 2) *
        (Nf k (Sgl⁻¹ * g) * latticeOp k m ⇑h ((Sgl⁻¹ * g) • UpperHalfPlane.I)) :=
  TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeDictionaryCusp.sum_Fh_lower_cusp h hm g hg
