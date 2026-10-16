module

public import TernaryPeriodPolynomials.SymmetricSpace.PositiveAction
public import Mathlib.Data.Rat.Encodable
public import Mathlib.Basic.Countable.Basic

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceRationalAction
open Matrix SymmetricSpacePositive

abbrev RationalGL := Matrix.GeneralLinearGroup (Fin 3) ℚ

/-- Literal scalar extension of rational chart matrices to the actual real action group. -/
def realRational : RationalGL →* RealGL :=
  Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)

@[simp] theorem realRational_apply (g : RationalGL) (i j : Fin 3) :
    (realRational g).val i j=(g.val i j : ℝ) := rfl

theorem realRational_injective : Function.Injective realRational := by
  intro g h he
  apply Units.ext
  ext i j
  have hh := congrArg (fun a : RealGL => a.val i j) he
  change (g.val i j : ℝ)=(h.val i j : ℝ) at hh
  exact_mod_cast hh

/-- The actual rational chart index set is countable. -/
theorem rationalGL_countable : Countable RationalGL := by
  let : Countable (Matrix (Fin 3) (Fin 3) ℚ) :=
    inferInstanceAs (Countable (Fin 3 → Fin 3 → ℚ))
  exact (Units.val_injective : Function.Injective (Units.val : RationalGL → Matrix (Fin 3) (Fin 3) ℚ)).countable

/-- Rational chart changes act by genuine homeomorphisms on the actual positive-form space. -/
def rationalHomeomorph (g : RationalGL) : Space ≃ₜ Space :=
  actionHomeomorph (realRational g)

@[simp] theorem rationalHomeomorph_apply (g : RationalGL) (S : Space) :
    rationalHomeomorph g S=act (realRational g) S := rfl

/-- The actual integral action agrees with its rational and then real scalar extension. -/
theorem realRational_integral (g : Matrix.GeneralLinearGroup (Fin 3) ℤ) :
    realRational (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) g)=
      Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) g := by
  apply Units.ext
  ext i j
  change ((g.val i j : ℚ) : ℝ)=(g.val i j : ℝ)
  exact Rat.cast_intCast _

end TernaryPoly.SymmetricSpaceRationalAction
