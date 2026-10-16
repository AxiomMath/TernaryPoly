module

public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.Fintype.Order
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
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Tactic.ComputeDegree

@[expose] public section


open MvPolynomial

noncomputable section

namespace TernaryPoly

local notation "BP" => MvPolynomial (Fin 2) ℚ

/-- Quarter rotation of the binary variables. -/
def binaryRotation (p : BP) : BP := bind₁ ![X 1, -X 0] p

/-- The homogeneous binary primitive extracted from the boundary polynomial. -/
def binaryPeriodPrimitive (n : ℕ) (p : BP) : BP :=
  -(1 / ((n : ℚ)+1)) • (X 0 * binaryRotation p + X 1 * p)

private theorem binaryRotation_pderiv (p : BP) :
    pderiv 1 (binaryRotation p) = binaryRotation (pderiv 0 p) := by
  change pderiv 1 (bind₁ ![X 1, -X 0] p) = bind₁ ![X 1, -X 0] (pderiv 0 p)
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    fin_cases i <;> simp [map_mul, map_add, hp]

/-- Euler's identity makes the extraction a negative primitive in the second variable. -/
theorem binaryPeriodPrimitive_pderiv {p : BP} {n : ℕ} (hp : p.IsHomogeneous n)
    (hrotation : binaryRotation (pderiv 0 p) = pderiv 0 p) :
    pderiv 1 (binaryPeriodPrimitive n p) = -p := by
  have he : X 0 * pderiv 0 p + X 1 * pderiv 1 p = (n : ℚ) • p := by
    simpa only [Fin.sum_univ_two, Nat.cast_smul_eq_nsmul] using hp.sum_X_mul_pderiv
  have hd : pderiv 1 (X 0 * binaryRotation p + X 1 * p) = ((n : ℚ)+1) • p := by
    calc
      pderiv 1 (X 0 * binaryRotation p + X 1 * p) =
          (X 0 * pderiv 0 p + X 1 * pderiv 1 p) + p := by
        simp [binaryRotation_pderiv, hrotation]
        ring
      _ = ((n : ℚ)+1) • p := by rw [he, add_smul, one_smul]
  rw [binaryPeriodPrimitive, Derivation.map_smul, hd, smul_smul]
  have hden : (n : ℚ)+1 ≠ 0 := Nat.cast_add_one_ne_zero n
  rw [neg_mul, div_mul_cancel₀ 1 hden, neg_one_smul]

private def binarySubstitute (p a b : BP) : BP := bind₁ ![a,b] p

private theorem binarySubstitute_comp (p a b x y : BP) :
    binarySubstitute (binarySubstitute p a b) x y =
      binarySubstitute p (binarySubstitute a x y) (binarySubstitute b x y) := by
  simp only [binarySubstitute, bind₁_bind₁]
  congr 2
  funext i
  fin_cases i <;> rfl

private theorem binarySubstitute_identity (p : BP) :
    binarySubstitute p (X 0) (X 1) = p := by
  have ht : (![X 0, X 1] : Fin 2 → BP) = X := by
    funext i
    fin_cases i <;> rfl
  simp [binarySubstitute, ht]

private theorem binarySubstitute_even_first {p : BP}
    (hp : bind₁ ![-X 0, X 1] p = p) (a b : BP) :
    binarySubstitute p (-a) b = binarySubstitute p a b := by
  have h := congrArg (fun g => binarySubstitute g a b) hp
  change binarySubstitute (binarySubstitute p (-X 0) (X 1)) a b = _ at h
  rw [binarySubstitute_comp] at h
  simpa [binarySubstitute] using h

private theorem binarySubstitute_odd_second {p : BP}
    (hp : bind₁ ![X 0, -X 1] p = -p) (a b : BP) :
    binarySubstitute p a (-b) = -binarySubstitute p a b := by
  have h := congrArg (fun g => binarySubstitute g a b) hp
  change binarySubstitute (binarySubstitute p (X 0) (-X 1)) a b = _ at h
  rw [binarySubstitute_comp] at h
  simpa [binarySubstitute] using h

private theorem binarySubstitute_axis {p : BP}
    (hp : bind₁ (![0, X 1] : Fin 2 → BP) p = 0) (b : BP) : binarySubstitute p 0 b = 0 := by
  have h := congrArg (fun g => binarySubstitute g 0 b) hp
  change binarySubstitute (binarySubstitute p 0 (X 1)) 0 b = _ at h
  rw [binarySubstitute_comp] at h
  simpa [binarySubstitute] using h

private theorem binaryPeriodPrimitive_substitute (n : ℕ) (p a b : BP) :
    binarySubstitute (binaryPeriodPrimitive n p) a b =
      -(1 / ((n : ℚ)+1)) •
        (a * binarySubstitute p b (-a) + b * binarySubstitute p a b) := by
  change binarySubstitute
    (-(1 / ((n : ℚ)+1)) • (X 0 * binarySubstitute p (X 1) (-X 0) + X 1 * p)) a b = _
  simp only [binarySubstitute, map_smul, map_add, map_mul, bind₁_X_right,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  change -(1 / ((n : ℚ)+1)) •
    (a * binarySubstitute (binarySubstitute p (X 1) (-X 0)) a b +
      b * binarySubstitute p a b) = _
  rw [binarySubstitute_comp]
  simp [binarySubstitute]

/-- Oddness of the source in its second variable makes the extracted polynomial alternating. -/
theorem binaryPeriodPrimitive_swap (n : ℕ) {p : BP}
    (hy : bind₁ ![X 0, -X 1] p = -p) :
    bind₁ ![X 1, X 0] (binaryPeriodPrimitive n p) = -binaryPeriodPrimitive n p := by
  change binarySubstitute (binaryPeriodPrimitive n p) (X 1) (X 0) = _
  rw [binaryPeriodPrimitive_substitute]
  have hq := binaryPeriodPrimitive_substitute n p (X 0) (X 1)
  rw [binarySubstitute_identity] at hq
  rw [hq, binarySubstitute_odd_second hy, binarySubstitute_odd_second hy,
    ← smul_neg]
  congr 1
  ring

/-- The extracted polynomial is even in its first variable. -/
theorem binaryPeriodPrimitive_even_first (n : ℕ) {p : BP}
    (hx : bind₁ ![-X 0, X 1] p = p) (hy : bind₁ ![X 0, -X 1] p = -p) :
    bind₁ ![-X 0, X 1] (binaryPeriodPrimitive n p) = binaryPeriodPrimitive n p := by
  change binarySubstitute (binaryPeriodPrimitive n p) (-X 0) (X 1) = _
  rw [binaryPeriodPrimitive_substitute]
  have hq := binaryPeriodPrimitive_substitute n p (X 0) (X 1)
  rw [binarySubstitute_identity] at hq
  rw [hq, neg_neg, binarySubstitute_even_first hx, binarySubstitute_odd_second hy]
  congr 1
  ring

/-- The extracted polynomial is even in its second variable. -/
theorem binaryPeriodPrimitive_even_second (n : ℕ) {p : BP}
    (hx : bind₁ ![-X 0, X 1] p = p) (hy : bind₁ ![X 0, -X 1] p = -p) :
    bind₁ ![X 0, -X 1] (binaryPeriodPrimitive n p) = binaryPeriodPrimitive n p := by
  change binarySubstitute (binaryPeriodPrimitive n p) (X 0) (-X 1) = _
  rw [binaryPeriodPrimitive_substitute]
  have hq := binaryPeriodPrimitive_substitute n p (X 0) (X 1)
  rw [binarySubstitute_identity] at hq
  rw [hq, binarySubstitute_even_first hx, binarySubstitute_odd_second hy (X 0) (X 1)]
  congr 1
  ring

/-- The normalization of the source implies vanishing on the first axis. -/
theorem binaryPeriodPrimitive_axis_first (n : ℕ) {p : BP}
    (haxis : bind₁ (![0, X 1] : Fin 2 → BP) p = 0) :
    bind₁ (![0, X 1] : Fin 2 → BP) (binaryPeriodPrimitive n p) = 0 := by
  change binarySubstitute (binaryPeriodPrimitive n p) 0 (X 1) = _
  rw [binaryPeriodPrimitive_substitute, binarySubstitute_axis haxis]
  simp

/-- The same normalization implies vanishing on the second axis. -/
theorem binaryPeriodPrimitive_axis_second (n : ℕ) {p : BP}
    (haxis : bind₁ (![0, X 1] : Fin 2 → BP) p = 0) :
    bind₁ (![X 0, 0] : Fin 2 → BP) (binaryPeriodPrimitive n p) = 0 := by
  change binarySubstitute (binaryPeriodPrimitive n p) (X 0) 0 = _
  rw [binaryPeriodPrimitive_substitute, binarySubstitute_axis haxis]
  simp

end TernaryPoly
