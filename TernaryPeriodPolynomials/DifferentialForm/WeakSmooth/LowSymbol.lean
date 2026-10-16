module

public import TernaryPeriodPolynomials.DifferentialForm.Coordinate.Symbol
public import TernaryPeriodPolynomials.Topology.SmoothLocal.DeRhamLowDegree

@[expose] public section


/-! The actual exterior symbols in degrees zero and one, with coefficient values retained. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open PolynomialFormCoordinates PolynomialFormMetric PolynomialCoefficientMetric SymmetricSpaceCharts
open SmoothLocalDeRham ContinuousAlternatingMap

/-- The genuine degree-zero symbol is ordinary scalar multiplication by the coordinate covector. -/
theorem symbol_zero_value (n : ℕ) (d : Fin 5) (c : Coefficients n) (v : Coordinates) :
    oneEquiv.symm (symbol n 0 d (zeroEquiv c)) v = v d • c := by
  simp [symbol, oneEquiv, zeroEquiv, alternatizeUncurryFin_apply]

/-- The genuine degree-one symbol is the literal antisymmetric exterior product. -/
theorem symbol_one_value (n : ℕ) (d : Fin 5) (a : FormValue n 1) (u v : Coordinates) :
    symbol n 1 d a ![u,v] = u d • oneEquiv.symm a v - v d • oneEquiv.symm a u := by
  have h0 : (![v] : Fin 1 → Coordinates) = fun _ => v := by ext i; fin_cases i; rfl
  have h1 : Fin.removeNth (1 : Fin 2) (Matrix.vecCons u (fun _ : Fin 1 => v)) = fun _ => u := by ext i; fin_cases i; rfl
  simp [symbol, oneEquiv, alternatizeUncurryFin_apply, Fin.sum_univ_two, sub_eq_add_neg, h0, h1]

end TernaryPoly.PolynomialFormWeakSmooth
