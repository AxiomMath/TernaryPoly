module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Push
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Analysis.Analytic.Within
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Topology.WithTopology

/-! Elementary integral Möbius and coordinate geometry, independent of period forms. -/
@[expose] public section
noncomputable section
open Complex Matrix MatrixGroups
open UpperHalfPlane hiding I

namespace TernaryPoly.BinaryCuspSymbol

abbrev Coordinates := Fin 2 → ℂ
abbrev SL2 := Matrix.SpecialLinearGroup (Fin 2) ℤ

/-- The literal fractional-linear action of an integral special-linear matrix. -/
def slMobius (g : SL2) (z : ℂ) : ℂ :=
  ((g 0 0 : ℂ)*z+(g 0 1 : ℂ))/((g 1 0 : ℂ)*z+(g 1 1 : ℂ))

/-- Actual linear coordinate action of the same integral matrix. -/
def slCoordinates (g : SL2) (v : Coordinates) : Coordinates :=
  ((g.val.map (Int.castRingHom ℂ)).mulVec v)

/-- The inverse-coordinate action is the literal adjugate formula. -/
theorem slCoordinates_inv (g : SL2) (v : Coordinates) :
    slCoordinates g⁻¹ v =
      ![(g 1 1 : ℂ)*v 0-(g 0 1 : ℂ)*v 1, -(g 1 0 : ℂ)*v 0+(g 0 0 : ℂ)*v 1] := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  funext i
  fin_cases i <;> simp only [slCoordinates, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · change (g 1 1 : ℂ)*v 0 + ((-(g 0 1) : ℤ) : ℂ)*v 1 = _
    push_cast
    ring
  · change ((-(g 1 0) : ℤ) : ℂ)*v 0 + (g 0 0 : ℂ)*v 1 = _
    push_cast
    ring

/-- The literal Möbius expression agrees with the actual upper-half-plane action. -/
theorem slMobius_eq_action (g : SL2) {z : ℂ} (hz : 0 < z.im) :
    slMobius g z = ((g • ofComplex z : ℍ) : ℂ) := by
  rw [ofComplex_apply_of_im_pos hz, coe_specialLinearGroup_apply]
  simp [slMobius]

theorem slMobius_im_pos (g : SL2) {z : ℂ} (hz : 0 < z.im) : 0 < (slMobius g z).im := by
  rw [slMobius_eq_action g hz]
  exact (g • ofComplex z).im_pos

theorem slDenom (g : SL2) (z : ℂ) :
    denom (g : GL (Fin 2) ℝ) z = (g 1 0 : ℂ)*z+(g 1 1 : ℂ) := by
  change (((g 1 0 : ℤ) : ℝ) : ℂ)*z+(((g 1 1 : ℤ) : ℝ) : ℂ) = _
  norm_cast

theorem slDenom_ne_zero (g : SL2) {z : ℂ} (hz : 0 < z.im) :
    (g 1 0 : ℂ)*z+(g 1 1 : ℂ) ≠ 0 := by
  rw [←slDenom]
  exact denom_ne_zero_of_im _ hz.ne'

theorem slDet (g : SL2) :
    (g 0 0 : ℂ)*(g 1 1 : ℂ)-(g 0 1 : ℂ)*(g 1 0 : ℂ) = 1 := by
  have h := g.det_coe
  rw [Matrix.det_fin_two] at h
  exact_mod_cast h

/-- The actual complex derivative of the fractional-linear map. -/
theorem slMobius_hasDerivAt (g : SL2) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (slMobius g) (1/((g 1 0 : ℂ)*z+(g 1 1 : ℂ))^2) z := by
  have h := (((hasDerivAt_id z).const_mul (g 0 0 : ℂ)).add_const (g 0 1 : ℂ)).div
    (((hasDerivAt_id z).const_mul (g 1 0 : ℂ)).add_const (g 1 1 : ℂ)) (slDenom_ne_zero g hz)
  have he : (g 0 0 : ℂ)*((g 1 0 : ℂ)*z+(g 1 1 : ℂ))-
      ((g 0 0 : ℂ)*z+(g 0 1 : ℂ))*(g 1 0 : ℂ) = 1 := by
    linear_combination slDet g
  simpa only [mul_one, id_eq, he, slMobius, Pi.div_apply] using! h

@[simp] theorem slCoordinates_one (v : Coordinates) : slCoordinates 1 v = v := by
  simp [slCoordinates]

theorem slCoordinates_mul (g h : SL2) (v : Coordinates) :
    slCoordinates (g*h) v = slCoordinates g (slCoordinates h v) := by
  unfold slCoordinates
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec]
  congr 1
  exact (Int.castRingHom ℂ).mapMatrix.map_mul g.val h.val

@[simp] theorem slCoordinates_inv_self (g : SL2) (v : Coordinates) :
    slCoordinates g⁻¹ (slCoordinates g v) = v := by
  rw [←slCoordinates_mul, inv_mul_cancel, slCoordinates_one]

@[simp] theorem slCoordinates_self_inv (g : SL2) (v : Coordinates) :
    slCoordinates g (slCoordinates g⁻¹ v) = v := by
  rw [←slCoordinates_mul, mul_inv_cancel, slCoordinates_one]

@[simp] theorem slMobius_one (z : ℂ) : slMobius 1 z = z := by
  simp [slMobius]

theorem slMobius_mul (g h : SL2) {z : ℂ} (hz : 0 < z.im) :
    slMobius (g*h) z = slMobius g (slMobius h z) := by
  rw [slMobius_eq_action _ hz, slMobius_eq_action _ (slMobius_im_pos h hz),
    slMobius_eq_action h hz, ofComplex_apply, mul_smul]

end TernaryPoly.BinaryCuspSymbol
