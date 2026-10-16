module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.AltExtension

@[expose] public section



/-! The Hodge-star-style reindexing from one-forms to four-forms, mirroring `star2to3`/`star3to2`
one degree further. Needed to state R3/R4. -/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity

def star1to4 (β : OneCoordinates) : FourCoordinates := fun i j k l =>
  ∑ m : Fin 5, (eps5 i j k l m * tangentWeight m) • β m

/-- If `eps5 i j k l m'` vanishes for every `m' ≠ m`, then the sum defining `star1to4 X i j k l`
collapses to its single term at `m`. -/
theorem star1to4_eq_single (X : OneCoordinates) (i j k l m : Fin 5)
    (h : ∀ m', m' ≠ m → eps5 i j k l m' = 0) :
    star1to4 X i j k l = (eps5 i j k l m * tangentWeight m) • X m := by
  refine Finset.sum_eq_single_of_mem m (Finset.mem_univ m) fun m' _ hm' => ?_
  rw [h m' hm', zero_mul, zero_smul]

/-- If `eps5 j k l m i ≠ 0`, the five indices `j, k, l, m, i` exhaust `Fin 5`, so the sum defining
`star1to4 X j k l m` collapses to its single term at `i`. -/
theorem star1to4_eq_single_of_ne (X : OneCoordinates) (j k l m i : Fin 5)
    (h : eps5 j k l m i ≠ 0) :
    star1to4 X j k l m = (eps5 j k l m i * tangentWeight i) • X i := by
  refine star1to4_eq_single X j k l m i fun m' hm' => ?_
  by_contra h'
  have hinj : Function.Injective ![j, k, l, m, i] := by
    by_contra hn
    exact h (epsFive_eq_zero_of_not_injective hn)
  have hinj' : Function.Injective ![j, k, l, m, m'] := by
    by_contra hn
    exact h' (epsFive_eq_zero_of_not_injective hn)
  obtain ⟨p, hp⟩ := (Finite.injective_iff_surjective.mp hinj) m'
  have hp4 : p ≠ 4 := fun h4 => hm' (by rw [← hp, h4]; rfl)
  have hval : (![j, k, l, m, m'] : Fin 5 → Fin 5) p = (![j, k, l, m, m'] : Fin 5 → Fin 5) 4 := by
    fin_cases p
    · exact hp
    · exact hp
    · exact hp
    · exact hp
    · exact absurd rfl hp4
  exact hp4 (hinj' hval)

end TernaryPeriodPolynomials.Argument.Coercivity
