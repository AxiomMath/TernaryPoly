module

public import TernaryPeriodPolynomials.Polynomial.GLAction
public import TernaryPeriodPolynomials.Building.Primitive.LineHeight
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.Algebra.MvPolynomial.Nilpotent

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.SinglePole
open ModThreeGoodAction AugmentedFrameComplex PrimitiveLineHeight

abbrev Poly := MvPolynomial (Fin 3) ℚ
abbrev Frac := FractionRing Poly
abbrev V (n : ℕ) := PolynomialGLAction.HomogeneousPoly n
abbrev Normal := RationalLine

/-- Literal rational linear form associated to a normal row. -/
def form (v : Space) : Poly := ∑ i, C (v i) * X i

@[simp] theorem form_coeff (v : Space) (i : Fin 3) :
    (form v).coeff (Finsupp.single i 1) = v i := by
  classical
  simp only [form,coeff_sum,coeff_C_mul,coeff_X]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hne : Finsupp.single j 1 ≠ Finsupp.single i 1 := by
      intro he
      exact hji ((Finsupp.single_left_inj (by decide : (1 : ℕ) ≠ 0)).mp he)
    simp [hne]
  · simp

theorem form_injective : Function.Injective form := by
  intro v w h
  funext i
  simpa only [form_coeff] using congrArg (·.coeff (Finsupp.single i 1)) h

@[simp] theorem form_zero : form 0 = 0 := by simp [form]

theorem form_ne_zero {v : Space} (hv : v ≠ 0) : form v ≠ 0 := by
  intro h
  exact hv (form_injective (h.trans form_zero.symm))

theorem form_homogeneous (v : Space) : (form v).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro i _
  exact isHomogeneous_C_mul_X (v i) i

theorem form_smul (u : ℚ) (v : Space) : form (u • v) = C u * form v := by
  simp only [form,Pi.smul_apply,smul_eq_mul,map_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Nonzero rational linear forms are actual polynomial primes. -/
theorem form_prime {v : Space} (hv : v ≠ 0) : Prime (form v) := by
  apply Irreducible.prime
  apply irreducible_of_totalDegree_eq_one ((form_homogeneous v).totalDegree (form_ne_zero hv))
  intro r hr
  apply isUnit_iff_ne_zero.mpr
  intro hr0
  subst r
  apply hv
  funext i
  have he := hr (Finsupp.single i 1)
  simpa only [form_coeff,zero_dvd_iff,Pi.zero_apply] using he

/-- Divisibility of homogeneous polynomials has a quotient in the exact expected degree. -/
theorem homogeneous_divisor {L p : Poly} {n : ℕ} (hL : L.IsHomogeneous 1)
    (hp : p.IsHomogeneous (n+1)) (h : L ∣ p) :
    ∃ q : V n, L * q.val = p := by
  let : GradedAlgebra (homogeneousSubmodule (Fin 3) ℚ) := MvPolynomial.gradedAlgebra
  obtain ⟨q,hq⟩ := h
  refine ⟨DirectSum.decompose (homogeneousSubmodule (Fin 3) ℚ) q n, ?_⟩
  have he := DirectSum.coe_decompose_mul_add_of_left_mem
    (homogeneousSubmodule (Fin 3) ℚ) (a := L) (b := q) (j := n) hL
  rw [← hq, Nat.add_comm 1 n, DirectSum.decompose_of_mem_same _ hp] at he
  exact he.symm

/-- Chosen denominators for actual rational normal lines. -/
def denominator (H : Normal) : Poly := form (rationalVector (primitiveGenerator H))

theorem denominator_prime (H : Normal) : Prime (denominator H) :=
  form_prime (primitiveGenerator_ne_zero H)

theorem denominator_ne_zero (H : Normal) : denominator H ≠ 0 := (denominator_prime H).ne_zero

theorem denominator_homogeneous (H : Normal) : (denominator H).IsHomogeneous 1 :=
  form_homogeneous _

/-- A rational normal is recovered from its denominator, up to its required scalar equivalence. -/
theorem denominator_dvd_iff (H J : Normal) : denominator H ∣ denominator J ↔ H = J := by
  constructor
  · intro hd
    obtain ⟨q,hq⟩ := homogeneous_divisor (n := 0)
      (denominator_homogeneous H) (denominator_homogeneous J) hd
    have hq0 : q.val = C (q.val.coeff 0) := by
      exact (homogeneousComponent_eq_self q.property).symm.trans (homogeneousComponent_zero q.val)
    let c := q.val.coeff 0
    have hrow : rationalVector (primitiveGenerator J) =
        c • rationalVector (primitiveGenerator H) := by
      apply form_injective
      rw [form_smul]
      change denominator J = C c * denominator H
      rw [← hq,hq0,mul_comm]
    have hc : c ≠ 0 := by
      intro hc
      rw [hc,zero_smul] at hrow
      exact primitiveGenerator_ne_zero J hrow
    apply Subtype.ext
    rw [← primitiveGenerator_span H,← primitiveGenerator_span J,hrow]
    exact (Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc) _).symm
  · rintro rfl
    exact dvd_rfl

end TernaryPoly.SinglePole
