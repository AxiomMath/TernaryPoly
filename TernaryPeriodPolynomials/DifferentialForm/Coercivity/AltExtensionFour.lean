module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.HodgeFour
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.AltExtension

@[expose] public section



/-! Degree-4 analog of `AltExtension.lean`'s swap/diagonal lemmas for `IsAlternatingThree`:
derives all six pairwise-position swap identities and all six pairwise-position
diagonal-vanishing facts for an alternating `FourCoordinates`, from the three primitive clauses
of `IsAlternatingFour` (`HodgeFour.lean`). Also records the three ADJACENT swaps in a
hypothesis-gated `_of_gt` form.


-/
noncomputable section
namespace TernaryPeriodPolynomials.Argument.Coercivity

open TernaryPoly.SL3PolynomialCoercivity

/-- The "swap middle two" transposition for an alternating `FourCoordinates`, derived from the
defining swap-first-two and cyclic-first-three clauses. -/
theorem alternatingFour_swap12 {a : FourCoordinates} (ha : IsAlternatingFour a)
    (i j k l : Fin 5) : a i j k l = -a i k j l :=
  (ha.2.1 i j k l).trans (ha.1 k i j l)

/-- Applying the signed 4-cycle clause twice: an unsigned simultaneous swap of positions `(0,2)`
and `(1,3)`, used only to derive `alternatingFour_swap23`. -/
theorem alternatingFour_shift2 {a : FourCoordinates} (ha : IsAlternatingFour a)
    (i j k l : Fin 5) : a i j k l = a k l i j := by
  rw [ha.2.2 i j k l, ha.2.2 l i j k, neg_neg]

/-- The "swap last two" transposition for an alternating `FourCoordinates`. -/
theorem alternatingFour_swap23 {a : FourCoordinates} (ha : IsAlternatingFour a)
    (i j k l : Fin 5) : a i j k l = -a i j l k := by
  rw [alternatingFour_shift2 ha i j k l, ha.1 k l i j, alternatingFour_shift2 ha l k i j]

/-- The "swap first and third" transposition for an alternating `FourCoordinates`. -/
theorem alternatingFour_swap02 {a : FourCoordinates} (ha : IsAlternatingFour a)
    (i j k l : Fin 5) : a i j k l = -a k j i l := by
  rw [ha.1 i j k l, alternatingFour_swap12 ha j i k l, ha.1 j k i l]
  ring

/-- The "swap first and last" transposition for an alternating `FourCoordinates`. -/
theorem alternatingFour_swap03 {a : FourCoordinates} (ha : IsAlternatingFour a)
    (i j k l : Fin 5) : a i j k l = -a l j k i := by
  rw [alternatingFour_swap23 ha i j k l, alternatingFour_swap02 ha i j l k,
    alternatingFour_swap23 ha l j i k]
  ring

/-- The "swap second and last" transposition for an alternating `FourCoordinates`. -/
theorem alternatingFour_swap13 {a : FourCoordinates} (ha : IsAlternatingFour a)
    (i j k l : Fin 5) : a i j k l = -a i l k j := by
  rw [ha.1 i j k l, alternatingFour_swap03 ha j i k l, ha.1 l i k j]
  ring

theorem alternatingFour_diag01 {a : FourCoordinates} (ha : IsAlternatingFour a)
    (i k l : Fin 5) : a i i k l = 0 :=
  poly_self_neg_eq_zero (ha.1 i i k l)

theorem alternatingFour_diag12 {a : FourCoordinates} (ha : IsAlternatingFour a)
    (i j l : Fin 5) : a i j j l = 0 :=
  poly_self_neg_eq_zero (alternatingFour_swap12 ha i j j l)

theorem alternatingFour_diag23 {a : FourCoordinates} (ha : IsAlternatingFour a)
    (i j k : Fin 5) : a i j k k = 0 :=
  poly_self_neg_eq_zero (alternatingFour_swap23 ha i j k k)

theorem alternatingFour_diag02 {a : FourCoordinates} (ha : IsAlternatingFour a)
    (i j l : Fin 5) : a i j i l = 0 :=
  poly_self_neg_eq_zero (alternatingFour_swap02 ha i j i l)

theorem alternatingFour_diag03 {a : FourCoordinates} (ha : IsAlternatingFour a)
    (i j k : Fin 5) : a i j k i = 0 :=
  poly_self_neg_eq_zero (alternatingFour_swap03 ha i j k i)

theorem alternatingFour_diag13 {a : FourCoordinates} (ha : IsAlternatingFour a)
    (i j k : Fin 5) : a i j k j = 0 :=
  poly_self_neg_eq_zero (alternatingFour_swap13 ha i j k j)

/-- Gated form of the swap-first-two clause, firing only when the
first index exceeds the second.
-/
theorem alternatingFour_swap01_of_gt {a : FourCoordinates} (ha : IsAlternatingFour a)
    (i j k l : Fin 5) (_h : j < i) : a i j k l = -a j i k l :=
  ha.1 i j k l

/-- Gated form of `alternatingFour_swap12`, firing only when the middle pair is out of order. -/
theorem alternatingFour_swap12_of_gt {a : FourCoordinates} (ha : IsAlternatingFour a)
    (i j k l : Fin 5) (_h : k < j) : a i j k l = -a i k j l :=
  alternatingFour_swap12 ha i j k l

/-- Gated form of `alternatingFour_swap23`, firing only when the last pair is out of order. -/
theorem alternatingFour_swap23_of_gt {a : FourCoordinates} (ha : IsAlternatingFour a)
    (i j k l : Fin 5) (_h : l < k) : a i j k l = -a i j l k :=
  alternatingFour_swap23 ha i j k l

/-- Degree-4 analog of `alternatingFour_swap23` combined with `alternatingFour_swap12`: cycling
the LAST three slots, unsigned, needed only for `alternatingFour_fix_first`. -/
theorem alternatingFour_cycle123 {a : FourCoordinates} (ha : IsAlternatingFour a)
    (i j k l : Fin 5) : a i j k l = a i l j k := by
  rw [alternatingFour_swap23 ha i j k l, alternatingFour_swap12 ha i j l k, neg_neg]

/-- Fixing the first index of an alternating `FourCoordinates` leaves an alternating
`ThreeCoordinates` in the remaining three slots. -/
theorem alternatingFour_fix_first {a : FourCoordinates} (ha : IsAlternatingFour a) (v : Fin 5) :
    IsAlternatingThree (fun x y z => a v x y z) :=
  ⟨alternatingFour_swap12 ha v, alternatingFour_cycle123 ha v⟩

/-- Canonical alternating extension of an arbitrary `c : FourCoordinates`: zero whenever two of
the four indices coincide; otherwise, whichever of the four is smallest is brought to the front
(picking up the sign for the number of adjacent transpositions needed to do so — `0, 1, 2, 3`
swaps for the smallest sitting at position `0, 1, 2, 3` respectively), and the remaining three
indices are canonicalized by `altThree`. -/
def altFour (c : FourCoordinates) : FourCoordinates :=
  fun i j k l =>
    if i < j ∧ i < k ∧ i < l then altThree (fun x y z => c i x y z) j k l
    else if j < i ∧ j < k ∧ j < l then -altThree (fun x y z => c j x y z) i k l
    else if k < i ∧ k < j ∧ k < l then altThree (fun x y z => c k x y z) i j l
    else if l < i ∧ l < j ∧ l < k then -altThree (fun x y z => c l x y z) i j k
    else 0

theorem altFour_eq_of_alternating {a : FourCoordinates} (ha : IsAlternatingFour a) :
    a = altFour a := by
  funext i j k l
  show a i j k l = (if i < j ∧ i < k ∧ i < l then altThree (fun x y z => a i x y z) j k l
    else if j < i ∧ j < k ∧ j < l then -altThree (fun x y z => a j x y z) i k l
    else if k < i ∧ k < j ∧ k < l then altThree (fun x y z => a k x y z) i j l
    else if l < i ∧ l < j ∧ l < k then -altThree (fun x y z => a l x y z) i j k
    else 0)
  split_ifs with h1 h2 h3 h4
  · exact congrFun (congrFun (congrFun
      (altThree_eq_of_alternating (alternatingFour_fix_first ha i)) j) k) l
  · exact (ha.1 i j k l).trans (congrArg Neg.neg (congrFun (congrFun (congrFun
      (altThree_eq_of_alternating (alternatingFour_fix_first ha j)) i) k) l))
  · exact (ha.2.1 i j k l).trans (congrFun (congrFun (congrFun
      (altThree_eq_of_alternating (alternatingFour_fix_first ha k)) i) j) l)
  · exact (ha.2.2 i j k l).trans (congrArg Neg.neg (congrFun (congrFun (congrFun
      (altThree_eq_of_alternating (alternatingFour_fix_first ha l)) i) j) k))
  · have hcase : i = j ∨ i = k ∨ i = l ∨ j = k ∨ j = l ∨ k = l := by omega
    rcases hcase with h | h | h | h | h | h
    · rw [h]; exact alternatingFour_diag01 ha j k l
    · rw [h]; exact alternatingFour_diag02 ha k j l
    · rw [h]; exact alternatingFour_diag03 ha l j k
    · rw [h]; exact alternatingFour_diag12 ha i k l
    · rw [h]; exact alternatingFour_diag13 ha i l k
    · rw [h]; exact alternatingFour_diag23 ha i j l

end TernaryPeriodPolynomials.Argument.Coercivity
