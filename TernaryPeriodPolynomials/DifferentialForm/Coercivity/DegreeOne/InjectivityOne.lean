module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.DegreeOne.Algebra

@[expose] public section



/-! # Injectivity of `exteriorOne` on homogeneous degree-one coordinates

For `a : OneCoordinates` homogeneous of degree `1`, `exteriorOne a = 0 → a = 0`. This is the
`n = 1` special case needed for `algebraicHodgeOne`'s coercivity: the
Casimir + Cauchy-Schwarz bound planned for `n ≥ 2` fails exactly at `n = 1`, where instead
`exteriorOne` alone is already injective on this `15`-dimensional space. We show this by
explicit Gaussian elimination on the `pderiv`-coordinates against the literal `tangentFrame`
matrices, following the 15-step elimination chain (numerically
cross-checked there against the eigenvalues of `algebraicHodgeOne`). -/

noncomputable section
open TernaryPoly.SL3PolynomialCoercivity MvPolynomial

namespace TernaryPeriodPolynomials.Argument.CoercivityOne

/-- A homogeneous degree-one polynomial has vanishing second partial derivatives: its first
partials are homogeneous of degree `0`, i.e. constant, so their own partials vanish. -/
theorem pderiv_pderiv_eq_zero_of_isHomogeneous_one {p : Poly} (hp : p.IsHomogeneous 1)
    (i j : Fin 3) : pderiv j (pderiv i p) = 0 := by
  have h0 : (pderiv i p).IsHomogeneous 0 := hp.pderiv
  rw [← totalDegree_zero_iff_isHomogeneous (Fin 3), totalDegree_eq_zero_iff_eq_C] at h0
  rw [h0, pderiv_C]

/-- The `q`-th partial of `infinitesimal A p`, when `p` is homogeneous of degree one. -/
theorem pderiv_infinitesimal_of_isHomogeneous_one (A : Mat) {p : Poly}
    (hp : p.IsHomogeneous 1) (q : Fin 3) :
    pderiv q (infinitesimal A p) = -∑ r : Fin 3, A r q • pderiv r p := by
  rw [infinitesimal_apply]
  simp only [map_neg, map_sum, Derivation.map_smul, pderiv_mul,
    pderiv_pderiv_eq_zero_of_isHomogeneous_one hp, mul_zero, add_zero]
  congr 1
  fin_cases q <;> simp [pderiv_X, Fin.sum_univ_succ]

/-- Reading `exteriorOne a i j = 0` off at one `pderiv`-component: the pointwise linear
relation this forces between the (constant) first partials of `a i` and `a j`. -/
theorem pderiv_exteriorOne_eq (a : OneCoordinates) (ha : ∀ i, (a i).IsHomogeneous 1)
    (i j : Fin 5) (hz : exteriorOne a i j = 0) (q : Fin 3) :
    ∑ r : Fin 3, (tangentFrame j) r q • pderiv r (a i) =
      ∑ r : Fin 3, (tangentFrame i) r q • pderiv r (a j) := by
  have h := congrArg (pderiv q) hz
  simp only [exteriorOne, map_sub, map_zero,
    pderiv_infinitesimal_of_isHomogeneous_one _ (ha j) q,
    pderiv_infinitesimal_of_isHomogeneous_one _ (ha i) q] at h
  linear_combination h

/-- Euler reconstruction: a homogeneous degree-one polynomial with all partials vanishing is
itself zero. -/
theorem eq_zero_of_forall_pderiv_eq_zero {p : Poly} (hp : p.IsHomogeneous 1)
    (h : ∀ q : Fin 3, pderiv q p = 0) : p = 0 := by
  have he := hp.sum_X_mul_pderiv
  simp only [h, mul_zero, Finset.sum_const_zero, one_smul] at he
  exact he.symm

/-- The hard combinatorial fact for `n = 1`: `exteriorOne` alone (no `contractionOne` needed)
is already injective on homogeneous degree-one `OneCoordinates`. Proved by the 15-step
elimination chain, using the pairs
`(0,1), (0,3), (0,4), (1,2), (1,3), (2,3), (1,4)`. -/
theorem exteriorOne_injective_of_isHomogeneous_one (a : OneCoordinates)
    (ha : ∀ i, (a i).IsHomogeneous 1) (hz : exteriorOne a = 0) : a = 0 := by
  have hz' : ∀ i j : Fin 5, exteriorOne a i j = 0 := fun i j => by simp [hz]
  have raw : ∀ i j q, ∑ r : Fin 3, (tangentFrame j) r q • pderiv r (a i) =
      ∑ r : Fin 3, (tangentFrame i) r q • pderiv r (a j) :=
    fun i j q => pderiv_exteriorOne_eq a ha i j (hz' i j) q
  have s1 : pderiv (2 : Fin 3) (a 0) = 0 := by
    have h := raw 0 1 2
    simp [tangentFrame, Fin.sum_univ_succ] at h
    exact h
  have s2 : pderiv (0 : Fin 3) (a 0) = 0 := by
    have h := raw 0 3 2
    simp [tangentFrame, Fin.sum_univ_succ] at h
    exact h
  have s3 : pderiv (1 : Fin 3) (a 0) = 0 := by
    have h := raw 0 4 2
    simp [tangentFrame, Fin.sum_univ_succ] at h
    exact h
  have s4 : pderiv (0 : Fin 3) (a 1) = 0 := by
    have h := raw 0 1 0
    simp [tangentFrame, Fin.sum_univ_succ, s2] at h
    exact h.symm
  have s5 : pderiv (1 : Fin 3) (a 1) = 0 := by
    have h := raw 0 1 1
    simp [tangentFrame, Fin.sum_univ_succ, s3] at h
    exact h
  have s6 : pderiv (0 : Fin 3) (a 2) = 0 := by
    have h := raw 1 2 0
    simp [tangentFrame, Fin.sum_univ_succ, s5] at h
    exact h.symm
  have s7 : pderiv (1 : Fin 3) (a 2) = 0 := by
    have h := raw 1 2 1
    simp [tangentFrame, Fin.sum_univ_succ, s4] at h
    exact h.symm
  have s8 : pderiv (2 : Fin 3) (a 2) = 0 := by
    have h := raw 1 2 2
    simp [tangentFrame, Fin.sum_univ_succ] at h
    exact h
  have s9 : pderiv (2 : Fin 3) (a 1) = pderiv (0 : Fin 3) (a 3) := by
    have h := raw 1 3 0
    simp [tangentFrame, Fin.sum_univ_succ] at h
    exact h
  have s10 : pderiv (1 : Fin 3) (a 3) = 0 := by
    have h := raw 1 3 1
    simp [tangentFrame, Fin.sum_univ_succ] at h
    exact h.symm
  have s11 : pderiv (2 : Fin 3) (a 3) = 0 := by
    have h := raw 1 3 2
    simp [tangentFrame, Fin.sum_univ_succ, s4] at h
    exact h
  have s12a : pderiv (0 : Fin 3) (a 3) = 0 := by
    have h := raw 2 3 1
    simp [tangentFrame, Fin.sum_univ_succ] at h
    exact h.symm
  have s12b : pderiv (2 : Fin 3) (a 1) = 0 := s9.trans s12a
  have s13 : pderiv (0 : Fin 3) (a 4) = 0 := by
    have h := raw 0 4 0
    simp [tangentFrame, Fin.sum_univ_succ] at h
    exact h.symm
  have s14 : pderiv (1 : Fin 3) (a 4) = 0 := by
    have h := raw 0 4 1
    simp [tangentFrame, Fin.sum_univ_succ, s1] at h
    exact h
  have s15 : pderiv (2 : Fin 3) (a 4) = 0 := by
    have h := raw 1 4 2
    simp [tangentFrame, Fin.sum_univ_succ, s5] at h
    exact h
  funext i
  show a i = 0
  fin_cases i
  · exact eq_zero_of_forall_pderiv_eq_zero (ha 0) (fun q => by
      fin_cases q
      exacts [s2, s3, s1])
  · exact eq_zero_of_forall_pderiv_eq_zero (ha 1) (fun q => by
      fin_cases q
      exacts [s4, s5, s12b])
  · exact eq_zero_of_forall_pderiv_eq_zero (ha 2) (fun q => by
      fin_cases q
      exacts [s6, s7, s8])
  · exact eq_zero_of_forall_pderiv_eq_zero (ha 3) (fun q => by
      fin_cases q
      exacts [s12a, s10, s11])
  · exact eq_zero_of_forall_pderiv_eq_zero (ha 4) (fun q => by
      fin_cases q
      exacts [s13, s14, s15])

end TernaryPeriodPolynomials.Argument.CoercivityOne
