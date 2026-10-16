module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Assembly.Degree
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Assembly.Degrees
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Cover.Principal
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Cover.Conjugate

@[expose] public section


/-!
# Proposition C.1: coercivity with a constant independent of the arithmetic group

Formalized by Claude Sonnet 5.5.

For every `n > 0` there is a constant `c > 0` such that for every admissible group `Γ` (a subgroup of
`GL₃(ℝ)` of determinant one acting freely and properly discontinuously on the trace-one positive
model; in particular every subgroup of a principal congruence subgroup of level divisible by three,
and every conjugate of such a group) the estimate
`c ‖ω‖² ≤ ‖dω‖² + ‖δω‖²` holds for all smooth `Γ`-equivariant `Sym^n`-valued forms `ω` of positive
degree with compact support in the orbit space `Γ \ X`, and `c ‖ω‖² ≤ ‖dω‖²` for forms of degree zero.
Here `‖·‖` is the `L²` norm of the orbit space for its Riemannian volume, `d` is the exterior
derivative and `δ` is the explicit local formula for its formal adjoint (which is the formal adjoint
of `d` for the `L²` pairing by `Admissible.l2Form_d`).  The coefficient metric is the Fischer metric
of the repository.  The quantifier order is `∃ c, ∀ Γ`.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCovering

/-- The coercivity estimate with constant `c` for the polynomial coefficients of degree `n` on the
orbit space of `Γ`: `c ‖a‖² ≤ ‖d a‖²` for compactly supported equivariant `0`-forms `a`, and
`c ‖a‖² ≤ ‖δ a‖² + ‖d a‖²` for compactly supported equivariant `(k + 1)`-forms `a`, with the `L²`
norms of the orbit space. -/
def CoerciveOn (n : ℕ) (c : ℝ) (Γ : Subgroup RealGL) : Prop :=
  (∀ a : CForm Γ n 0, c * normSq a ≤ normSq (CForm.d Γ n 0 a)) ∧
    ∀ (k : ℕ) (a : CForm Γ n (k + 1)),
      c * normSq a ≤ normSq (CForm.delta Γ n k a) + normSq (CForm.d Γ n (k + 1) a)

/-- The coercivity estimate holds for an admissible group as soon as the group-free pointwise
constant `c` is available in every degree. -/
theorem Admissible.coerciveOn {n : ℕ} {c : ℝ} {Γ : Subgroup RealGL} (h : Admissible Γ)
    (h0 : BottomCoercive n c) (hk : ∀ k, PositiveCoercive n k c) : CoerciveOn n c Γ :=
  ⟨fun a => h.coercive_bottom h0 (symmetricAdjoint n 0) (bottomDivergence n) a,
    fun k a => h.coercive_positive (hk k) (symmetricAdjoint n k) (symmetricAdjoint n (k + 1))
      (positiveDivergence n k) a⟩

/-- **Proposition C.1 (coercivity), general form.**  For every `n > 0` there is one constant
`c > 0`, depending only on `n`, such that for every admissible subgroup `Γ` of `GL₃(ℝ)` and every
smooth `Γ`-equivariant `Coefficients n`-valued form `a` with compact support in the orbit space,
`c ‖a‖² ≤ ‖d a‖²` in degree zero and `c ‖a‖² ≤ ‖δ a‖² + ‖d a‖²` in degree `k + 1`. -/
theorem general_coercivity (n : ℕ) (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ Γ : Subgroup RealGL, Admissible Γ →
      (∀ a : CForm Γ n 0, c * normSq a ≤ normSq (CForm.d Γ n 0 a)) ∧
        ∀ (k : ℕ) (a : CForm Γ n (k + 1)),
          c * normSq a ≤ normSq (CForm.delta Γ n k a) + normSq (CForm.d Γ n (k + 1) a) := by
  obtain ⟨c, hc, h0, hk⟩ := exists_pointwise_constant hn
  exact ⟨c, hc, fun Γ h => h.coerciveOn h0 hk⟩

/-- The same constant works for all principal congruence subgroups `Γ(N)` of level divisible by
three, and for all of their subgroups. -/
theorem coercivity_principal (n : ℕ) (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 3 ∣ N → ∀ H : Subgroup RealGL, H ≤ principalReal N →
      CoerciveOn n c H := by
  obtain ⟨c, hc, h⟩ := general_coercivity n hn
  exact ⟨c, hc, fun N h3 H hH => h H ((admissible_principalReal h3).mono hH)⟩

/-- The same constant works for every conjugate, by an element of `GL₃(ℝ)`, of a subgroup of a
principal congruence subgroup of level divisible by three. -/
theorem coercivity_conjugate (n : ℕ) (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 3 ∣ N → ∀ H : Subgroup RealGL, H ≤ principalReal N →
      ∀ g : RealGL, CoerciveOn n c (conjSubgroup H g) := by
  obtain ⟨c, hc, h⟩ := general_coercivity n hn
  exact ⟨c, hc, fun N h3 H hH g => h _ (((admissible_principalReal h3).mono hH).conj g)⟩

/-- The same constant works for every rational conjugate of a subgroup of a principal congruence
subgroup of level divisible by three. -/
theorem coercivity_rational_conjugate (n : ℕ) (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 3 ∣ N → ∀ H : Subgroup RealGL, H ≤ principalReal N →
      ∀ g : Matrix.GeneralLinearGroup (Fin 3) ℚ,
        CoerciveOn n c (conjSubgroup H (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g)) := by
  obtain ⟨c, hc, h⟩ := coercivity_conjugate n hn
  exact ⟨c, hc, fun N h3 H hH g => h N h3 H hH _⟩

/-- The estimate for the cover `Γ(6) ∩ K` of the paper, with the same constant. -/
theorem coercivity_frozen_cover (n : ℕ) (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ CoerciveOn n c principalSixInKReal := by
  obtain ⟨c, hc, h⟩ := general_coercivity n hn
  exact ⟨c, hc, h _ admissible_principalSixInKReal⟩

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
