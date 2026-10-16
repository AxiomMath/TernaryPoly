module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.Star.SelfFourInvDup

@[expose] public section



/-! Unconditional antisymmetry of `star1to4` under swapping its first two output indices,
mirroring `star2to3_swap01` (`HodgeStar.lean`) one degree up via the same `eps5_swap01`
rewrite. Combined with `IsAlternatingFour`'s unconditional first clause, this reduces the
`i > j` slices of `star1to4_star4to1_self` to the already-established `i < j` slices (the ten
`AuxIJ` modules). -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity

theorem star1to4_swap01 (β : OneCoordinates) (i j k l : Fin 5) :
    star1to4 β i j k l = - star1to4 β j i k l := by
  show (∑ m : Fin 5, (eps5 i j k l m * tangentWeight m) • β m)
    = - (∑ m : Fin 5, (eps5 j i k l m * tangentWeight m) • β m)
  have hS : (∑ m : Fin 5, (eps5 i j k l m * tangentWeight m) • β m)
      = (-1 : ℝ) • ∑ m : Fin 5, (eps5 j i k l m * tangentWeight m) • β m := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [smul_smul]
    congr 1
    rw [eps5_swap01 i j k l m]
    ring
  rw [hS]
  module

/-- Reduces the `i > j` case of `star1to4_star4to1_self` to the already-established `j < i`
case, via `star1to4_swap01` and the unconditional first-clause antisymmetry of
`IsAlternatingFour`. -/
theorem star1to4_star4to1_self_of_swap {a : FourCoordinates} (ha : IsAlternatingFour a)
    {i j : Fin 5} (k l : Fin 5)
    (h : star1to4 (star4to1 a) j i k l = (1 / 96 : ℝ) • a j i k l) :
    star1to4 (star4to1 a) i j k l = (1 / 96 : ℝ) • a i j k l := by
  rw [star1to4_swap01, h, ha.1 j i k l]
  module

end TernaryPeriodPolynomials.Argument.Coercivity
