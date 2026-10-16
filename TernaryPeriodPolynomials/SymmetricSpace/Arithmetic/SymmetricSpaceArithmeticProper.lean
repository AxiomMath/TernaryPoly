module

public import TernaryPeriodPolynomials.SymmetricSpace.PositiveAction
public import TernaryPeriodPolynomials.Building.ModThreeGoodAction
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Data.Int.Order.Units
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.Semicontinuity.Hemicontinuity

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceArithmeticProper
open Matrix SymmetricSpacePositive
abbrev IntegralGL := ModThreeGoodAction.IntegralGL

/-- Literal coefficient cast, preserving the actual integral general linear group. -/
def realIntegral : IntegralGL →* RealGL :=
  Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ)

@[simp] theorem realIntegral_apply (g : IntegralGL) (i j : Fin 3) :
    (realIntegral g).val i j = (g.val i j : ℝ) := rfl

theorem realIntegral_injective : Function.Injective realIntegral := by
  intro g h hgh
  apply Units.ext
  ext i j
  have he := congrArg (fun k : RealGL => k.val i j) hgh
  change (g.val i j : ℝ) = (h.val i j : ℝ) at he
  exact_mod_cast he

@[simp] theorem realIntegral_det (g : IntegralGL) :
    (realIntegral g).val.det = (g.val.det : ℝ) := by
  change (g.val.map (Int.castRingHom ℝ)).det = _
  exact ((Int.castRingHom ℝ).map_det g.val).symm

/-- The determinant±1 property is retained exactly after casting to the reals. -/
theorem realIntegral_det_sq (g : IntegralGL) : (realIntegral g).val.det^2 = 1 := by
  rw [realIntegral_det]
  have h : g.val.det^2 = 1 := congrArg Units.val (Int.units_sq (Matrix.GeneralLinearGroup.det g))
  exact_mod_cast h

/-- Unnormalized congruence preserves determinant for every actual integral invertible matrix. -/
theorem integral_conjugate_det (g : IntegralGL) (S : Mat) :
    (conjugate (realIntegral g) S).det = S.det := by
  change ((realIntegral g).val*S*(realIntegral g).val.conjTranspose).det = S.det
  rw [Matrix.det_mul,Matrix.det_mul,Matrix.det_conjTranspose]
  simp only [star_trivial]
  calc
    _ = (realIntegral g).val.det^2*S.det := by ring
    _ = S.det := by rw [realIntegral_det_sq,one_mul]

/-- The positive scalar removed by trace normalization. -/
def scale (g : IntegralGL) (S : Space) : ℝ := (conjugate (realIntegral g) S.val).trace

theorem scale_pos (g : IntegralGL) (S : Space) : 0 < scale g S :=
  (conjugate_positive (realIntegral g) S.val S.property.1).trace_pos

/-- The actual normalized action differs from congruence by exactly this positive scalar. -/
theorem conjugate_eq_scale_smul (g : IntegralGL) (S : Space) :
    conjugate (realIntegral g) S.val = scale g S • (act (realIntegral g) S).val := by
  change conjugate (realIntegral g) S.val =
    scale g S • ((scale g S)⁻¹ • conjugate (realIntegral g) S.val)
  rw [smul_smul,mul_inv_cancel₀ (ne_of_gt (scale_pos g S)),one_smul]

/-- Determinants account explicitly for the scalar in the actual trace-normalized action. -/
theorem normalized_determinant (g : IntegralGL) (S : Space) :
    S.val.det = scale g S^3 * (act (realIntegral g) S).val.det := by
  calc
    S.val.det = (conjugate (realIntegral g) S.val).det := (integral_conjugate_det g S.val).symm
    _ = (scale g S • (act (realIntegral g) S).val).det := congrArg Matrix.det (conjugate_eq_scale_smul g S)
    _ = _ := by rw [Matrix.det_smul]; rfl

/-- A stabilizer has scalar one, proved from determinant rather than assumed isometry. -/
theorem stabilizer_scale_eq_one (g : IntegralGL) (S : Space)
    (h : act (realIntegral g) S = S) : scale g S = 1 := by
  have hd := normalized_determinant g S
  rw [h] at hd
  have hdet : S.val.det ≠ 0 := ne_of_gt S.property.1.det_pos
  have hpow : scale g S^3 = 1 := (mul_right_cancel₀ hdet (hd.symm.trans (one_mul S.val.det).symm))
  exact (pow_eq_one_iff_of_nonneg (le_of_lt (scale_pos g S)) (by decide : (3 : ℕ) ≠ 0)).mp hpow

/-- Every actual integral stabilizer preserves the original positive form itself. -/
theorem stabilizer_conjugate_eq (g : IntegralGL) (S : Space)
    (h : act (realIntegral g) S = S) : conjugate (realIntegral g) S.val = S.val := by
  rw [conjugate_eq_scale_smul,h,stabilizer_scale_eq_one g S h,one_smul]

end TernaryPoly.SymmetricSpaceArithmeticProper
