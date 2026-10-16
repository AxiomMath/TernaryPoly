/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard

The multiplicative Haar-character construction is adapted from
ImperialCollegeLondon/FLT,
FLT/HaarMeasure/HaarChar/Ring.lean.
-/
module

public import TernaryPeriodPolynomials.ArithmeticGroup.Adelic.Haar
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
public import Mathlib.Topology.Algebra.IsUniformGroup.Order

@[expose] public section


noncomputable section
namespace GeneralEisenstein.Adelic
open MeasureTheory
open scoped NNReal ENNReal

/-- The actual adelic norm character, defined by its scaling of additive Haar measure. -/
def adeleNorm : Adelesˣ →* ℝ≥0 where
  toFun u := addEquivAddHaarChar (ContinuousAddEquiv.mulLeft u)
  map_one' := by
    have he : ContinuousAddEquiv.mulLeft (1 : Adelesˣ) = ContinuousAddEquiv.refl Adeles := by
      apply ContinuousAddEquiv.ext
      intro x
      exact one_mul x
    rw [he, addEquivAddHaarChar_refl]
  map_mul' u v := by
    have he : ContinuousAddEquiv.mulLeft (u * v) =
        (ContinuousAddEquiv.mulLeft v).trans (ContinuousAddEquiv.mulLeft u) := by
      apply ContinuousAddEquiv.ext
      intro x
      exact mul_assoc u.val v.val x
    rw [he, addEquivAddHaarChar_trans, mul_comm]

/-- The global character is strictly positive on every actual adelic unit. -/
theorem adeleNorm_pos (u : Adelesˣ) : 0 < adeleNorm u :=
  addEquivAddHaarChar_pos _

/-- Embed an actual real unit with finite coordinate one. -/
def realAdeleUnit (t : ℝˣ) : Adelesˣ where
  val := (t.val,1)
  inv := (t.inv,1)
  val_inv := by change (t.val * t.inv, (1:FiniteAdeles)*1) = (1,1); simp
  inv_val := by change (t.inv * t.val, (1:FiniteAdeles)*1) = (1,1); simp

/-- Embed an actual integral finite unit with real coordinate one. -/
def integralAdeleUnit (k : IntegralAdelesˣ) : Adelesˣ where
  val := (1,integralEmbedding k.val)
  inv := (1,integralEmbedding k.inv)
  val_inv := by
    change ((1:ℝ)*1, integralEmbedding k.val * integralEmbedding k.inv) = (1,1)
    rw [← map_mul, k.val_inv, map_one, one_mul]
  inv_val := by
    change ((1:ℝ)*1, integralEmbedding k.inv * integralEmbedding k.val) = (1,1)
    rw [← map_mul, k.inv_val, map_one, one_mul]


end GeneralEisenstein.Adelic

end
