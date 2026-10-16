module

public import TernaryPeriodPolynomials.ModularForm.Symbol.ChartLimits
public import TernaryPeriodPolynomials.ModularForm.Symbol.ChartAlgebra

@[expose] public section


noncomputable section
open Complex Matrix Filter
open UpperHalfPlane hiding I
open scoped Topology

namespace TernaryPoly.BinaryCuspSymbol
open BinaryCuspPeriod BinaryModularSymbol

/-- Choose a genuine integral determinant-one chart for each actual rational cusp. -/
def cuspChart (L : Line) : SL2 := (exists_sl_chart L).choose

theorem cuspChart_spec (L : Line) : lineAction (slRational (cuspChart L)) infinity = L :=
  (exists_sl_chart L).choose_spec

/-- Actual normalized cusp endpoint, initially represented in the chosen SL2 chart. -/
def endpoint {d : ℕ} (f : Forms d) (L : Line) (v : Coordinates) : ℂ :=
  slConstant f (cuspChart L) v

/-- Endpoint convergence holds along every positive rational chart with the given cusp. -/
theorem endpoint_tendsto {d : ℕ} (f : Forms d) (L : Line) (v : Coordinates)
    (g : GL2) (hg : 0 < g.det.val) (hL : lineAction g infinity = L) :
    Tendsto (fun t : ℝ => eichlerIntegral f (v 0) (v 1) (rationalMobius g (I*t)))
      atTop (𝓝 (endpoint f L v)) := by
  apply eichlerIntegral_chart_tendsto f v (cuspChart L) g hg
  exact lowerLeft_eq_zero_of_same_cusp g (slRational (cuspChart L)) (hL.trans (cuspChart_spec L).symm)

/-- In particular, endpoint values are independent of every choice of integral chart. -/
theorem endpoint_eq_slConstant {d : ℕ} (f : Forms d) (g : SL2) (v : Coordinates) :
    endpoint f (lineAction (slRational g) infinity) v = slConstant f g v := by
  have h₁ := endpoint_tendsto f (lineAction (slRational g) infinity) v (slRational g)
    (by rw [slRational_det]; norm_num) rfl
  have h₂ := eichlerIntegral_chart_tendsto f v g (slRational g)
    (by rw [slRational_det]; norm_num) (by simp)
  exact tendsto_nhds_unique h₁ h₂

/-- Actual cusp endpoints satisfy the exact modular transformation with its genuine constant. -/
theorem endpoint_sl {d : ℕ} (f : Forms d) (g : SL2) (L : Line) (v : Coordinates) :
    endpoint f (lineAction (slRational g) L) v =
      endpoint f L (slCoordinates g⁻¹ v) + slConstant f g v := by
  have he : lineAction (slRational (g*cuspChart L)) infinity = lineAction (slRational g) L := by
    rw [map_mul, lineAction_mul, cuspChart_spec]
  rw [←he, endpoint_eq_slConstant, slConstant_mul]
  exact add_comm _ _

@[simp] theorem endpoint_infinity {d : ℕ} (f : Forms d) (v : Coordinates) :
    endpoint f infinity v = 0 := by
  simpa using endpoint_eq_slConstant f 1 v

end TernaryPoly.BinaryCuspSymbol
