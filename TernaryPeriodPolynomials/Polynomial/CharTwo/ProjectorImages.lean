module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.Projector
public import TernaryPeriodPolynomials.Polynomial.CharTwo.NormGenerators

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.CharTwoProjectorImages
open CharTwoNorm
open CharTwoProjector (projector atom sub form)

/-- The exact eighteen substitution frames used by the polynomial projector. -/
def frame : Fin 18 → (Poly →ₐ[ZMod 2] Poly) :=
  ![bind₁ ![form 1, form 2, form 5],
    bind₁ ![form 1, form 2, form 6],
    bind₁ ![form 1, form 3, form 4],
    bind₁ ![form 1, form 3, form 6],
    bind₁ ![form 1, form 3, form 7],
    bind₁ ![form 1, form 4, form 6],
    bind₁ ![form 1, form 5, form 6],
    bind₁ ![form 1, form 5, form 7],
    bind₁ ![form 2, form 3, form 4],
    bind₁ ![form 2, form 3, form 5],
    bind₁ ![form 2, form 3, form 7],
    bind₁ ![form 2, form 4, form 5],
    bind₁ ![form 2, form 5, form 6],
    bind₁ ![form 2, form 6, form 7],
    bind₁ ![form 3, form 4, form 5],
    bind₁ ![form 3, form 4, form 6],
    bind₁ ![form 4, form 5, form 7],
    bind₁ ![form 4, form 6, form 7]]

/-- The standard monomials in actual elementary symmetric coordinates. -/
def standardMonomial : Fin 28 → Poly :=
  ![1,
    a,
    b,
    a ^ 2,
    c,
    a * b,
    a ^ 3,
    b ^ 2,
    a * c,
    a ^ 2 * b,
    b * c,
    a * b ^ 2,
    a ^ 2 * c,
    a ^ 3 * b,
    c ^ 2,
    b ^ 3,
    a * b * c,
    a ^ 2 * b ^ 2,
    b ^ 2 * c,
    a * c ^ 2,
    a * b ^ 3,
    b * c ^ 2,
    b ^ 4,
    a * b ^ 2 * c,
    c ^ 3,
    b ^ 3 * c,
    b ^ 5,
    b * c ^ 3]

/-- The exact proposed images, expressed in the eight norm generators. -/
def generatorImage : Fin 28 → Poly :=
  ![0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    generator 0,
    0,
    generator 1,
    generator 1,
    0,
    0,
    generator 2,
    0,
    0,
    generator 3,
    generator 4,
    generator 3 + generator 4,
    generator 5,
    0,
    generator 5,
    generator 6,
    0,
    generator 7,
    d7 * generator 0 + d6 * generator 1 + d4 * generator 4]

private theorem ofNat_mod (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : Poly) = ((n % 2 : ℕ) : Poly) :=
  CharP.cast_eq_mod Poly 2 n



private theorem frame_invariant_0 (j : Fin 3) :
    frame 0 (invariant j) = invariant j := by
  fin_cases j <;> simp [frame, form, invariant, d4, d6, d7, cplus, a, b, c] <;>
    ring_nf <;> simp only [ofNat_mod] <;> norm_num

private theorem frame_invariant_1 (j : Fin 3) :
    frame 1 (invariant j) = invariant j := by
  fin_cases j <;> simp [frame, form, invariant, d4, d6, d7, cplus, a, b, c] <;>
    ring_nf <;> simp only [ofNat_mod] <;> norm_num

private theorem frame_invariant_2 (j : Fin 3) :
    frame 2 (invariant j) = invariant j := by
  fin_cases j <;> simp [frame, form, invariant, d4, d6, d7, cplus, a, b, c] <;>
    ring_nf <;> simp only [ofNat_mod] <;> norm_num

private theorem frame_invariant_3 (j : Fin 3) :
    frame 3 (invariant j) = invariant j := by
  fin_cases j <;> simp [frame, form, invariant, d4, d6, d7, cplus, a, b, c] <;>
    ring_nf <;> simp only [ofNat_mod] <;> norm_num

private theorem frame_invariant_4 (j : Fin 3) :
    frame 4 (invariant j) = invariant j := by
  fin_cases j <;> simp [frame, form, invariant, d4, d6, d7, cplus, a, b, c] <;>
    ring_nf <;> simp only [ofNat_mod] <;> norm_num

private theorem frame_invariant_5 (j : Fin 3) :
    frame 5 (invariant j) = invariant j := by
  fin_cases j <;> simp [frame, form, invariant, d4, d6, d7, cplus, a, b, c] <;>
    ring_nf <;> simp only [ofNat_mod] <;> norm_num

private theorem frame_invariant_6 (j : Fin 3) :
    frame 6 (invariant j) = invariant j := by
  fin_cases j <;> simp [frame, form, invariant, d4, d6, d7, cplus, a, b, c] <;>
    ring_nf <;> simp only [ofNat_mod] <;> norm_num

private theorem frame_invariant_7 (j : Fin 3) :
    frame 7 (invariant j) = invariant j := by
  fin_cases j <;> simp [frame, form, invariant, d4, d6, d7, cplus, a, b, c] <;>
    ring_nf <;> simp only [ofNat_mod] <;> norm_num

private theorem frame_invariant_8 (j : Fin 3) :
    frame 8 (invariant j) = invariant j := by
  fin_cases j <;> simp [frame, form, invariant, d4, d6, d7, cplus, a, b, c] <;>
    ring_nf <;> simp only [ofNat_mod] <;> norm_num

private theorem frame_invariant_9 (j : Fin 3) :
    frame 9 (invariant j) = invariant j := by
  fin_cases j <;> simp [frame, form, invariant, d4, d6, d7, cplus, a, b, c] <;>
    ring_nf <;> simp only [ofNat_mod] <;> norm_num

private theorem frame_invariant_10 (j : Fin 3) :
    frame 10 (invariant j) = invariant j := by
  fin_cases j <;> simp [frame, form, invariant, d4, d6, d7, cplus, a, b, c] <;>
    ring_nf <;> simp only [ofNat_mod] <;> norm_num

private theorem frame_invariant_11 (j : Fin 3) :
    frame 11 (invariant j) = invariant j := by
  fin_cases j <;> simp [frame, form, invariant, d4, d6, d7, cplus, a, b, c] <;>
    ring_nf <;> simp only [ofNat_mod] <;> norm_num

private theorem frame_invariant_12 (j : Fin 3) :
    frame 12 (invariant j) = invariant j := by
  fin_cases j <;> simp [frame, form, invariant, d4, d6, d7, cplus, a, b, c] <;>
    ring_nf <;> simp only [ofNat_mod] <;> norm_num

private theorem frame_invariant_13 (j : Fin 3) :
    frame 13 (invariant j) = invariant j := by
  fin_cases j <;> simp [frame, form, invariant, d4, d6, d7, cplus, a, b, c] <;>
    ring_nf <;> simp only [ofNat_mod] <;> norm_num

private theorem frame_invariant_14 (j : Fin 3) :
    frame 14 (invariant j) = invariant j := by
  fin_cases j <;> simp [frame, form, invariant, d4, d6, d7, cplus, a, b, c] <;>
    ring_nf <;> simp only [ofNat_mod] <;> norm_num

private theorem frame_invariant_15 (j : Fin 3) :
    frame 15 (invariant j) = invariant j := by
  fin_cases j <;> simp [frame, form, invariant, d4, d6, d7, cplus, a, b, c] <;>
    ring_nf <;> simp only [ofNat_mod] <;> norm_num

private theorem frame_invariant_16 (j : Fin 3) :
    frame 16 (invariant j) = invariant j := by
  fin_cases j <;> simp [frame, form, invariant, d4, d6, d7, cplus, a, b, c] <;>
    ring_nf <;> simp only [ofNat_mod] <;> norm_num

private theorem frame_invariant_17 (j : Fin 3) :
    frame 17 (invariant j) = invariant j := by
  fin_cases j <;> simp [frame, form, invariant, d4, d6, d7, cplus, a, b, c] <;>
    ring_nf <;> simp only [ofNat_mod] <;> norm_num

/-- Every actual projector frame fixes each of the three Dickson invariants. -/
theorem frame_invariant (i : Fin 18) (j : Fin 3) :
    frame i (invariant j) = invariant j := by
  fin_cases i
  · exact frame_invariant_0 j
  · exact frame_invariant_1 j
  · exact frame_invariant_2 j
  · exact frame_invariant_3 j
  · exact frame_invariant_4 j
  · exact frame_invariant_5 j
  · exact frame_invariant_6 j
  · exact frame_invariant_7 j
  · exact frame_invariant_8 j
  · exact frame_invariant_9 j
  · exact frame_invariant_10 j
  · exact frame_invariant_11 j
  · exact frame_invariant_12 j
  · exact frame_invariant_13 j
  · exact frame_invariant_14 j
  · exact frame_invariant_15 j
  · exact frame_invariant_16 j
  · exact frame_invariant_17 j

/-- The explicit projector is the sum of its eighteen algebra homomorphisms. -/
theorem projector_eq_sum (f : Poly) : projector f = ∑ i, frame i f := by
  simp [projector, frame, atom, sub, Fin.sum_univ_succ]
  ring

/-- Every polynomial in the invariant coordinates is fixed by each frame. -/
theorem frame_invariantEval (i : Fin 18) (F : Poly) :
    frame i (invariantEval F) = invariantEval F :=
  map_invariantEval (frame i) (frame_invariant i) F

/-- The projector is linear over polynomial expressions in the Dickson invariants. -/
theorem projector_invariantEval_mul (F f : Poly) :
    projector (invariantEval F * f) = invariantEval F * projector f := by
  simp only [projector_eq_sum, map_mul, frame_invariantEval, Finset.mul_sum]


private theorem projector_standardMonomial_0 :
    projector (standardMonomial 0) = generatorImage 0 := by
  simp [standardMonomial, generatorImage, projector, atom, sub, form]
  ring_nf
  simp only [ofNat_mod]
  norm_num

private theorem projector_standardMonomial_1 :
    projector (standardMonomial 1) = generatorImage 1 := by
  simp [standardMonomial, generatorImage, projector, atom, sub, form, a]
  ring_nf
  simp only [ofNat_mod]
  norm_num

private theorem projector_standardMonomial_2 :
    projector (standardMonomial 2) = generatorImage 2 := by
  simp [standardMonomial, generatorImage, projector, atom, sub, form, b]
  ring_nf
  simp only [ofNat_mod]
  norm_num

private theorem projector_standardMonomial_3 :
    projector (standardMonomial 3) = generatorImage 3 := by
  simp [standardMonomial, generatorImage, projector, atom, sub, form, a]
  ring_nf
  simp only [ofNat_mod]
  norm_num

private theorem projector_standardMonomial_4 :
    projector (standardMonomial 4) = generatorImage 4 := by
  simp [standardMonomial, generatorImage, projector, atom, sub, form, c]
  ring_nf
  simp only [ofNat_mod]
  norm_num

private theorem projector_standardMonomial_5 :
    projector (standardMonomial 5) = generatorImage 5 := by
  simp [standardMonomial, generatorImage, projector, atom, sub, form, a, b]
  ring_nf
  simp only [ofNat_mod]
  norm_num

private theorem projector_standardMonomial_6 :
    projector (standardMonomial 6) = generatorImage 6 := by
  simp [standardMonomial, generatorImage, projector, atom, sub, form, a]
  ring_nf
  simp only [ofNat_mod]
  norm_num

private theorem projector_standardMonomial_7 :
    projector (standardMonomial 7) = generatorImage 7 := by
  simp [standardMonomial, generatorImage, projector, atom, sub, form, b]
  ring_nf
  simp only [ofNat_mod]
  norm_num

private theorem projector_standardMonomial_8 :
    projector (standardMonomial 8) = generatorImage 8 := by
  simp [standardMonomial, generatorImage, projector, atom, sub, form, a, c]
  ring_nf
  simp only [ofNat_mod]
  norm_num

private theorem projector_standardMonomial_9 :
    projector (standardMonomial 9) = generatorImage 9 := by
  simp [standardMonomial, generatorImage, projector, atom, sub, form, generator, basis, cplus, a, b, c]
  ring_nf
  simp only [ofNat_mod]
  norm_num

private theorem projector_standardMonomial_10 :
    projector (standardMonomial 10) = generatorImage 10 := by
  simp [standardMonomial, generatorImage, projector, atom, sub, form, b, c]
  ring_nf
  simp only [ofNat_mod]
  norm_num

private theorem projector_standardMonomial_11 :
    projector (standardMonomial 11) = generatorImage 11 := by
  simp [standardMonomial, generatorImage, projector, atom, sub, form, generator, basis, cplus, a, b, c]
  ring_nf
  simp only [ofNat_mod]
  norm_num

private theorem projector_standardMonomial_12 :
    projector (standardMonomial 12) = generatorImage 12 := by
  simp [standardMonomial, generatorImage, projector, atom, sub, form, generator, basis, cplus, a, b, c]
  ring_nf
  simp only [ofNat_mod]
  norm_num

private theorem projector_standardMonomial_13 :
    projector (standardMonomial 13) = generatorImage 13 := by
  simp [standardMonomial, generatorImage, projector, atom, sub, form, a, b]
  ring_nf
  simp only [ofNat_mod]
  norm_num

private theorem projector_standardMonomial_14 :
    projector (standardMonomial 14) = generatorImage 14 := by
  simp [standardMonomial, generatorImage, projector, atom, sub, form, c]
  ring_nf
  simp only [ofNat_mod]
  norm_num

private theorem projector_standardMonomial_15 :
    projector (standardMonomial 15) = generatorImage 15 := by
  simp [standardMonomial, generatorImage, projector, atom, sub, form, generator, basis, cplus, a, b, c]
  ring_nf
  simp only [ofNat_mod]
  norm_num

private theorem projector_standardMonomial_16 :
    projector (standardMonomial 16) = generatorImage 16 := by
  simp [standardMonomial, generatorImage, projector, atom, sub, form, a, b, c]
  ring_nf
  simp only [ofNat_mod]
  norm_num

private theorem projector_standardMonomial_17 :
    projector (standardMonomial 17) = generatorImage 17 := by
  simp [standardMonomial, generatorImage, projector, atom, sub, form, a, b]
  ring_nf
  simp only [ofNat_mod]
  norm_num

private theorem projector_standardMonomial_18 :
    projector (standardMonomial 18) = generatorImage 18 := by
  simp [standardMonomial, generatorImage, projector, atom, sub, form, generator, basis, cplus, a, b, c]
  ring_nf
  simp only [ofNat_mod]
  norm_num

private theorem projector_standardMonomial_19 :
    projector (standardMonomial 19) = generatorImage 19 := by
  simp [standardMonomial, generatorImage, projector, atom, sub, form, generator, basis, cplus, a, b, c]
  ring_nf
  simp only [ofNat_mod]
  norm_num

private theorem projector_standardMonomial_20 :
    projector (standardMonomial 20) = generatorImage 20 := by
  simp [standardMonomial, generatorImage, projector, atom, sub, form, generator, basis, cplus, a, b, c]
  ring_nf
  simp only [ofNat_mod]
  norm_num

private theorem projector_standardMonomial_21 :
    projector (standardMonomial 21) = generatorImage 21 := by
  simp [standardMonomial, generatorImage, projector, atom, sub, form, generator, basis, cplus, a, b, c]
  ring_nf
  simp only [ofNat_mod]
  norm_num

private theorem projector_standardMonomial_22 :
    projector (standardMonomial 22) = generatorImage 22 := by
  simp [standardMonomial, generatorImage, projector, atom, sub, form, b]
  ring_nf
  simp only [ofNat_mod]
  norm_num

private theorem projector_standardMonomial_23 :
    projector (standardMonomial 23) = generatorImage 23 := by
  simp [standardMonomial, generatorImage, projector, atom, sub, form, generator, basis, cplus, a, b, c]
  ring_nf
  simp only [ofNat_mod]
  norm_num

private theorem projector_standardMonomial_24 :
    projector (standardMonomial 24) = generatorImage 24 := by
  simp [standardMonomial, generatorImage, projector, atom, sub, form, generator, basis, cplus, a, b, c]
  ring_nf
  simp only [ofNat_mod]
  norm_num

private theorem projector_standardMonomial_25 :
    projector (standardMonomial 25) = generatorImage 25 := by
  simp [standardMonomial, generatorImage, projector, atom, sub, form, b, c]
  ring_nf
  simp only [ofNat_mod]
  norm_num

private theorem projector_standardMonomial_26 :
    projector (standardMonomial 26) = generatorImage 26 := by
  simp [standardMonomial, generatorImage, projector, atom, sub, form, generator, basis, cplus, a, b, c]
  ring_nf
  simp only [ofNat_mod]
  norm_num

private theorem projector_standardMonomial_27 :
    projector (standardMonomial 27) = generatorImage 27 := by
  simp [standardMonomial, generatorImage, projector, atom, sub, form, generator, basis, d4, d6, d7, cplus, a, b, c]
  ring_nf
  simp only [ofNat_mod]
  norm_num

/-- All twenty-eight projector images are exact identities in the full polynomial ring. -/
theorem projector_standardMonomial (i : Fin 28) :
    projector (standardMonomial i) = generatorImage i := by
  fin_cases i
  · exact projector_standardMonomial_0
  · exact projector_standardMonomial_1
  · exact projector_standardMonomial_2
  · exact projector_standardMonomial_3
  · exact projector_standardMonomial_4
  · exact projector_standardMonomial_5
  · exact projector_standardMonomial_6
  · exact projector_standardMonomial_7
  · exact projector_standardMonomial_8
  · exact projector_standardMonomial_9
  · exact projector_standardMonomial_10
  · exact projector_standardMonomial_11
  · exact projector_standardMonomial_12
  · exact projector_standardMonomial_13
  · exact projector_standardMonomial_14
  · exact projector_standardMonomial_15
  · exact projector_standardMonomial_16
  · exact projector_standardMonomial_17
  · exact projector_standardMonomial_18
  · exact projector_standardMonomial_19
  · exact projector_standardMonomial_20
  · exact projector_standardMonomial_21
  · exact projector_standardMonomial_22
  · exact projector_standardMonomial_23
  · exact projector_standardMonomial_24
  · exact projector_standardMonomial_25
  · exact projector_standardMonomial_26
  · exact projector_standardMonomial_27

end TernaryPoly.CharTwoProjectorImages
