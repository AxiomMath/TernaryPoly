module

public import TernaryPeriodPolynomials.ModularForm.Symbol.Shift
public import TernaryPeriodPolynomials.ModularForm.HeckeEndomorphism.Basic

@[expose] public section


noncomputable section
open Complex Filter
open UpperHalfPlane hiding I
open scoped Topology

namespace TernaryPoly.BinaryCuspSymbol
open BinaryCuspPeriod

/-- Actual primitive term belonging to the infinite adjugate prime representative. -/
def heckePrimitiveInfinity {d : ℕ} (f : Forms d) (p : ℕ) (x y z : ℂ) : ℂ :=
  eichlerIntegral f x (y/p) (p*z)

/-- Actual primitive term belonging to the finite adjugate prime representative indexed by b. -/
def heckePrimitiveFinite {d : ℕ} (f : Forms d) (p : ℕ) (b : Fin p) (x y z : ℂ) : ℂ :=
  eichlerIntegral f ((x+b.val*y)/p) y ((z+b.val)/p)

theorem heckePrimitiveInfinity_hasDerivAt {d : ℕ} (f : Forms d) (p : ℕ) (hp : 0 < p)
    (x y : ℂ) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (heckePrimitiveInfinity f p x y)
      (f (ofComplex (p*z)) * (z*y-x)^d * p) z := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hr : (0 : ℝ) < p := by exact_mod_cast hp
  have hz' : 0 < ((p : ℂ)*z).im := by simpa using mul_pos hr hz
  have h := (eichlerIntegral_hasDerivAt f x (y/p) _ hz').comp z
    ((hasDerivAt_id z).const_mul (p : ℂ))
  have he : (p : ℂ)*z*(y/p)-x = z*y-x := by field_simp
  simpa only [Function.comp_def, id_eq, mul_one, periodIntegrand, he,
    heckePrimitiveInfinity] using! h

theorem heckePrimitiveFinite_hasDerivAt {d : ℕ} (f : Forms d) (p : ℕ) (hp : 0 < p)
    (b : Fin p) (x y : ℂ) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (heckePrimitiveFinite f p b x y)
      (f (ofComplex ((z+b.val)/p)) * (z*y-x)^d / (p : ℂ)^(d+1)) z := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hr : (0 : ℝ) < p := by exact_mod_cast hp
  have hz' : 0 < ((z+(b.val : ℂ))/p).im := by simpa using div_pos hz hr
  have h := (eichlerIntegral_hasDerivAt f ((x+b.val*y)/p) y _ hz').comp z
    (((hasDerivAt_id z).add_const (b.val : ℂ)).div_const (p : ℂ))
  have he : ((z+(b.val : ℂ))/p)*y-(x+b.val*y)/p = (z*y-x)/p := by ring
  have hd : periodIntegrand f ((x+b.val*y)/p) y ((z+b.val)/p) * (1/(p : ℂ)) =
      f (ofComplex ((z+b.val)/p))*(z*y-x)^d/(p : ℂ)^(d+1) := by
    rw [periodIntegrand, he, div_pow, pow_succ]
    field_simp
  simpa only [Function.comp_def, id_eq, hd, heckePrimitiveFinite] using! h

theorem heckePrimitiveInfinity_tendsto {d : ℕ} (f : Forms d) (p : ℕ) (hp : 0 < p)
    (x y : ℂ) : Tendsto (fun t : ℝ => heckePrimitiveInfinity f p x y (I*t)) atTop (𝓝 0) := by
  have hr : (0 : ℝ) < p := by exact_mod_cast hp
  have h := (eichlerIntegral_axis_tendsto_infty f x (y/p)).comp
    (Tendsto.const_mul_atTop hr tendsto_id)
  convert h using 1
  funext t
  unfold heckePrimitiveInfinity
  congr 1
  simp only [id_eq]
  push_cast
  ring

theorem heckePrimitiveFinite_tendsto {d : ℕ} (f : Forms d) (p : ℕ) (hp : 0 < p)
    (b : Fin p) (x y : ℂ) : Tendsto (fun t : ℝ => heckePrimitiveFinite f p b x y (I*t)) atTop (𝓝 0) := by
  have hr : (0 : ℝ) < p := by exact_mod_cast hp
  have h := (eichlerIntegral_realShift_axis_tendsto_infty f ((x+b.val*y)/p) y ((b.val : ℝ)/p)).comp
    (Tendsto.const_mul_atTop (inv_pos.mpr hr) tendsto_id)
  convert h using 1
  funext t
  unfold heckePrimitiveFinite
  congr 1
  simp only [id_eq]
  push_cast
  ring

end TernaryPoly.BinaryCuspSymbol
