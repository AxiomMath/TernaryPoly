module

public import TernaryPeriodPolynomials.Building.ModThreeGoodAction
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Ring.Pow

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceArithmeticProper

/-- An explicit finite integer-coordinate box contains every integral GL3 matrix with a
uniform real entry bound. No discreteness or proper-action hypothesis is used. -/
theorem finite_integral_entry_bound (R : ℝ) :
    {g : ModThreeGoodAction.IntegralGL | ∀ i j, |(g.val i j : ℝ)| ≤ R}.Finite := by
  let N : ℤ := ⌈R⌉
  have hb : {m : Matrix (Fin 3) (Fin 3) ℤ | ∀ i j, m i j ∈ Set.Icc (-N) N}.Finite :=
    Set.Finite.pi' (fun _ => Set.Finite.pi' (fun _ => Set.finite_Icc (-N) N))
  refine Set.Finite.of_injOn (f := fun g : ModThreeGoodAction.IntegralGL => g.val)
    ?_ Units.val_injective.injOn hb
  intro g hg i j
  have h := abs_le.mp ((hg i j).trans (Int.le_ceil R))
  constructor
  · exact_mod_cast h.1
  · exact_mod_cast h.2

end TernaryPoly.SymmetricSpaceArithmeticProper
