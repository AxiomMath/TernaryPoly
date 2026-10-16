module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.NormGenerators
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Data.Fintype.Order
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Tactic.ComputeDegree

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.CharTwoNorm

/-- The invariant coefficient ring whose three generators all have even degree. -/
def invariantEvenEval : Poly →ₐ[ZMod 2] Poly := bind₁ ![d4, d6, d7^2]

/-- Every polynomial in the invariants splits according to the parity of the d7 exponent. -/
theorem invariant_parity_split (q : Poly) :
    ∃ p r : Poly, invariantEval q = invariantEvenEval p + d7*invariantEvenEval r := by
  induction q using MvPolynomial.induction_on with
  | C t => exact ⟨C t, 0, by simp [invariantEval, invariantEvenEval]⟩
  | add f g hf hg =>
    obtain ⟨p,r,hf⟩ := hf
    obtain ⟨s,t,hg⟩ := hg
    exact ⟨p+s,r+t, by rw [map_add, hf, hg, map_add, map_add]; ring⟩
  | mul_X f i hf =>
    obtain ⟨p,r,hf⟩ := hf
    fin_cases i
    · refine ⟨p*X 0,r*X 0,?_⟩
      simp only [map_mul, hf]
      simp [invariantEval, invariantEvenEval, invariant]
      ring
    · refine ⟨p*X 1,r*X 1,?_⟩
      simp only [map_mul, hf]
      simp [invariantEval, invariantEvenEval, invariant]
      ring
    · refine ⟨r*X 2,p,?_⟩
      simp only [map_mul, hf]
      simp [invariantEval, invariantEvenEval, invariant]
      ring

/-- Euler's degree derivation, with values in characteristic two. -/
def degreeEuler (f : Poly) : Poly :=
  X 0*pderiv 0 f + X 1*pderiv 1 f + X 2*pderiv 2 f

@[simp] theorem degreeEuler_C (t : ZMod 2) : degreeEuler (C t) = 0 := by simp [degreeEuler]
@[simp] theorem degreeEuler_zero : degreeEuler 0 = 0 := by simp [degreeEuler]
@[simp] theorem degreeEuler_one : degreeEuler 1 = 0 := by simp [degreeEuler]
@[simp] theorem degreeEuler_X (i : Fin 3) : degreeEuler (X i) = X i := by
  fin_cases i <;> simp [degreeEuler]

theorem degreeEuler_add (f g : Poly) : degreeEuler (f+g) = degreeEuler f+degreeEuler g := by
  simp only [degreeEuler, map_add]
  ring

theorem degreeEuler_mul (f g : Poly) :
    degreeEuler (f*g) = degreeEuler f*g + f*degreeEuler g := by
  simp only [degreeEuler, pderiv_mul]
  ring

theorem degreeEuler_pow (f : Poly) (n : ℕ) :
    degreeEuler (f^n) = n • (f^(n-1)*degreeEuler f) := by
  simp only [degreeEuler, pderiv_pow]
  simp only [nsmul_eq_mul]
  ring

theorem degreeEuler_square (f : Poly) : degreeEuler (f^2) = 0 := by
  rw [pow_two, degreeEuler_mul, mul_comm (degreeEuler f), CharTwo.add_self_eq_zero]

theorem degreeEuler_a : degreeEuler a = a := by simp [a, degreeEuler_add]
theorem degreeEuler_b : degreeEuler b = 0 := by
  simp [b, degreeEuler_add, degreeEuler_mul, CharTwo.add_self_eq_zero]
theorem degreeEuler_c : degreeEuler c = c := by
  simp [c, degreeEuler_mul, CharTwo.add_self_eq_zero]
theorem degreeEuler_cplus : degreeEuler cplus = cplus := by
  simp [cplus, degreeEuler_add, degreeEuler_mul, degreeEuler_a, degreeEuler_b, degreeEuler_c]

theorem degreeEuler_d4 : degreeEuler d4 = 0 := by
  rw [d4, degreeEuler_add, degreeEuler_add]
  have h4 : degreeEuler (a^4) = 0 := by rw [show a^4=(a^2)^2 by ring, degreeEuler_square]
  simp [h4, degreeEuler_square, degreeEuler_mul, degreeEuler_a, degreeEuler_c,
    CharTwo.add_self_eq_zero]

theorem degreeEuler_d6 : degreeEuler d6 = 0 := by
  have h3 : degreeEuler (a^3) = a^3 := by
    rw [show a^3=a*a*a by ring]
    simp [degreeEuler_mul, degreeEuler_a, CharTwo.add_self_eq_zero]
  simp [d6, degreeEuler_add, degreeEuler_mul, degreeEuler_square, h3,
    degreeEuler_a, degreeEuler_b, degreeEuler_c, CharTwo.add_self_eq_zero]

theorem degreeEuler_d7 : degreeEuler d7 = d7 := by
  simp [d7, degreeEuler_mul, degreeEuler_a, degreeEuler_c, degreeEuler_cplus,
    CharTwo.add_self_eq_zero]

theorem degreeEuler_invariantEvenEval (p : Poly) : degreeEuler (invariantEvenEval p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C t => simp [invariantEvenEval]
  | add f g hf hg => simp only [map_add, degreeEuler_add, hf, hg, zero_add]
  | mul_X f i hf =>
    rw [map_mul, degreeEuler_mul, hf, zero_mul, zero_add]
    suffices degreeEuler (invariantEvenEval (X i)) = 0 by rw [this, mul_zero]
    fin_cases i <;> simp [invariantEvenEval, degreeEuler_d4, degreeEuler_d6, degreeEuler_square]

/-- The four odd-degree basis elements are indexed by 1,3,4,6. -/
def basisOdd : Fin 8 → Bool := ![false,true,false,true,true,false,true,false]

private theorem ofNat_mod (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : Poly) = ((n % 2 : ℕ) : Poly) :=
  CharP.cast_eq_mod Poly 2 n

theorem degreeEuler_basis (i : Fin 8) :
    degreeEuler (basis i) = if basisOdd i then basis i else 0 := by
  fin_cases i <;>
    simp [basis, basisOdd, degreeEuler_add, degreeEuler_mul, degreeEuler_pow,
      degreeEuler_a, degreeEuler_b, degreeEuler_c, degreeEuler_cplus, nsmul_eq_mul] <;>
    ring_nf <;> simp only [ofNat_mod] <;> norm_num

theorem degreeEuler_sum {ι : Type*} (s : Finset ι) (f : ι → Poly) :
    degreeEuler (∑ i ∈ s, f i) = ∑ i ∈ s, degreeEuler (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, degreeEuler_add, ih]

/-- Homogeneous polynomials of even degree are killed by the degree derivation. -/
theorem degreeEuler_eq_zero_of_even {g : Poly} {n : ℕ}
    (hg : g.IsHomogeneous n) (he : Even n) : degreeEuler g = 0 := by
  have h : (∑ i : Fin 3, X i * pderiv i g) = (n : ZMod 2) • g := by
    simpa only [Nat.cast_smul_eq_nsmul] using hg.sum_X_mul_pderiv
  rw [he.natCast_zmod_two, zero_smul] at h
  simpa only [Fin.sum_univ_three, degreeEuler] using h

/-- The complete even part can be extracted from any polynomial basis expansion.
No uniqueness or linear-independence hypothesis is needed. -/
theorem even_basis_expansion {g : Poly} (he : degreeEuler g = 0)
    (q : Fin 8 → Poly) (hq : g = ∑ i, invariantEval (q i)*basis i) :
    ∃ r : Fin 8 → Poly, g = ∑ i,
      (if basisOdd i then d7*invariantEvenEval (r i) else invariantEvenEval (r i))*basis i := by
  classical
  choose p r hr using fun i => invariant_parity_split (q i)
  let ev : Fin 8 → Poly := fun i =>
    (if basisOdd i then d7*invariantEvenEval (r i) else invariantEvenEval (p i))*basis i
  let od : Fin 8 → Poly := fun i =>
    (if basisOdd i then invariantEvenEval (p i) else d7*invariantEvenEval (r i))*basis i
  have hsplit : g = (∑ i, ev i)+(∑ i, od i) := by
    rw [hq, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hr]
    cases hb : basisOdd i <;> simp [ev, od, hb] <;> ring
  have hev (i : Fin 8) : degreeEuler (ev i) = 0 := by
    cases hb : basisOdd i <;>
      simp [ev, hb, degreeEuler_mul, degreeEuler_invariantEvenEval, degreeEuler_d7,
        degreeEuler_basis, CharTwo.add_self_eq_zero]
  have hod (i : Fin 8) : degreeEuler (od i) = od i := by
    cases hb : basisOdd i <;>
      simp [od, hb, degreeEuler_mul, degreeEuler_invariantEvenEval, degreeEuler_d7,
        degreeEuler_basis]
  have hz : (∑ i, od i) = 0 := by
    have h := congrArg degreeEuler hsplit
    simpa only [he, degreeEuler_add, degreeEuler_sum, hev, hod, Finset.sum_const_zero,
      zero_add] using h.symm
  rw [hz, add_zero] at hsplit
  refine ⟨fun i => if basisOdd i then r i else p i, ?_⟩
  rw [hsplit]
  apply Finset.sum_congr rfl
  intro i _
  cases hb : basisOdd i <;> simp [ev, hb]

end TernaryPoly.CharTwoNorm
