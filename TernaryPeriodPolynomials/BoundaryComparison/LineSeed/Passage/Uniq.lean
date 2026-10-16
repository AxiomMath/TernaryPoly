module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.FStar

@[expose] public section


/-!
# Uniqueness of the moment primitives, and their reflection (Passage 6)

On the upper half plane two functions with the same derivative which agree at `i` are equal (`eq_of_hasDerivAt_upper`).  Consequently the normalized moment primitives of a form depend only
on the values of the form on `ℍ` (`momentPrim_congr`), and for the reflected form `f^*(z) = \overline{f(-\bar z)}` they satisfy
`\overline{G_j(-\bar z)} = (-1)^{j+1} G^*_j(z)` (`momentPrim_reflect`), where `G_j`, `G^*_j` are the primitives of `f` and `f^*`.

Formalized by Claude Sonnet 5.5.
-/

open ComplexConjugate UpperHalfPlane ModularForm

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3S4c (Lvl1 fStar fStar_cuspH momentPrim_fStar_hasDerivAt)

/-- **Primitives on the upper half plane are unique up to the value at `i`.** -/
theorem eq_of_hasDerivAt_upper {F G k : ℂ → ℂ} (hF : ∀ z : ℂ, 0 < z.im → HasDerivAt F (k z) z)
    (hG : ∀ z : ℂ, 0 < z.im → HasDerivAt G (k z) z) (h0 : F Complex.I = G Complex.I) (z : ℂ) (hz : 0 < z.im) :
    F z = G z := by
  have hs : Convex ℝ {c : ℂ | 0 < c.im} := convex_halfSpace_im_gt 0
  have hop : IsOpen {c : ℂ | 0 < c.im} := isOpen_lt continuous_const Complex.continuous_im
  have hdiff : DifferentiableOn ℂ (fun c => F c - G c) {c : ℂ | 0 < c.im} := fun c hc =>
    ((hF c hc).sub (hG c hc)).differentiableAt.differentiableWithinAt
  have hI : Complex.I ∈ {c : ℂ | 0 < c.im} := by simp
  have key := hs.is_const_of_fderivWithin_eq_zero hdiff (fun c hc => by
    rw [fderivWithin_of_isOpen hop hc]
    have := ((hF c hc).sub (hG c hc)).hasFDerivAt
    change fderiv ℂ (F - G) c = 0
    rw [this.fderiv]
    ext
    simp) hz hI
  have := key
  simp only [h0, sub_self] at this
  exact sub_eq_zero.mp this

/-- The normalized moment primitives of two forms with the same values on `ℍ` coincide on `ℍ`. -/
theorem momentPrim_congr {Λ Λ' : Subgroup (GL (Fin 2) ℝ)} [Λ.HasDetOne] [Λ'.HasDetOne] {n : ℕ}
    (f : CuspForm Λ ((n + 3 : ℕ) : ℤ)) (f' : CuspForm Λ' ((n + 3 : ℕ) : ℤ))
    (hff : ∀ z : ℂ, 0 < z.im → cuspH Λ n f z = cuspH Λ' n f' z) (j : ℕ) (z : ℂ) (hz : 0 < z.im) :
    momentPrim Λ n f j z = momentPrim Λ' n f' j z :=
  eq_of_hasDerivAt_upper (k := fun z => cuspH Λ' n f' z * z ^ j)
    (fun z hz => by rw [← hff z hz]; exact momentPrim_hasDerivAt Λ n f j z hz)
    (fun z hz => momentPrim_hasDerivAt Λ' n f' j z hz)
    (by rw [momentPrim_zero, momentPrim_zero]) z hz

/-- **Reflection of the moment primitives:** `\overline{G_j(-\bar z)} = (-1)^{j+1} G^*_j(z)`. -/
theorem momentPrim_reflect {n : ℕ} (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) (j : ℕ) (z : ℂ) (hz : 0 < z.im) :
    conj (momentPrim Lvl1 n f j (-conj z)) = (-1 : ℂ) ^ (j + 1) * momentPrim Lvl1 n (fStar f) j z := by
  have hF : ∀ z : ℂ, 0 < z.im → HasDerivAt (fun z => conj (momentPrim Lvl1 n f j (-conj z)))
      ((-1 : ℂ) ^ (j + 1) * (conj (f (ofComplex (-conj z))) * z ^ j)) z := by
    intro z hz
    have hw : 0 < (-conj z).im := by simpa using hz
    have h1 := momentPrim_hasDerivAt Lvl1 n f j (-conj z) hw
    have h2 : HasDerivAt (fun w => momentPrim Lvl1 n f j (-w))
        (cuspH Lvl1 n f (-conj z) * (-conj z) ^ j * (-1)) (conj z) :=
      HasDerivAt.comp (conj z) h1 (hasDerivAt_neg (conj z))
    have h3 := h2.conj_conj
    simp only [Complex.conj_conj] at h3
    refine h3.congr_deriv ?_
    simp only [map_neg, map_mul, map_pow, Complex.conj_conj, cuspH, map_one]
    ring
  have hG : ∀ z : ℂ, 0 < z.im → HasDerivAt (fun z => (-1 : ℂ) ^ (j + 1) * momentPrim Lvl1 n (fStar f) j z)
      ((-1 : ℂ) ^ (j + 1) * (conj (f (ofComplex (-conj z))) * z ^ j)) z :=
    fun z hz => (momentPrim_fStar_hasDerivAt f j z hz).const_mul _
  refine eq_of_hasDerivAt_upper (F := fun z => conj (momentPrim Lvl1 n f j (-conj z)))
    (G := fun z => (-1 : ℂ) ^ (j + 1) * momentPrim Lvl1 n (fStar f) j z) hF hG ?_ z hz
  simp [momentPrim_zero]

end TernaryPeriodPolynomials.Argument.LineSeed
