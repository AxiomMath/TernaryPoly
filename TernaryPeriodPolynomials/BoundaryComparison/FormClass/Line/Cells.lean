module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Faces.LineGroup
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Unfold.Orbit

@[expose] public section


/-!
# The line radical acting on the cosets `Γ_P \ Γ(N)` (the two cells of the line constant term)

Formalized by Claude Sonnet 5.5.
Paper: "Two planes are either equal or distinct. A line is either contained in or
complementary to the source plane."

A coset `Γ_P γ` of `Γ(N)` is determined by the bottom row `r = e₃ᵀγ` of `γ` (`cosetRow`), i.e. by the plane `ker r = γ⁻¹⟨e₁, e₂⟩`.  The line `ℚ e₁` stabilized by `Q` is contained in
this plane iff `r₀ = 0`.
* `nQ N ℓ`: the radical element `[[1, Nℓ₀, Nℓ₁], [0, 1, 0], [0, 0, 1]]` of `Γ_Q`, as an element of `Γ(N)`.
* `lineRow_nQ`: right multiplication by `nQ ℓ` changes the row `(r₀, r₁, r₂)` to `(r₀, r₁ + N r₀ ℓ₀, r₂ + N r₀ ℓ₁)`.
* `cosetMulR_nQ_of_zero`: if `r₀ = 0` (the line lies in the plane) the radical lattice fixes the coset.
* `cosetMulR_nQ_injective`: if `r₀ ≠ 0` (the complementary cell) the radical lattice acts freely: `ℓ ↦ c · nQ ℓ` is injective.
-/

open scoped MatrixGroups
noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormClassK

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.EisensteinClass

variable (N : ℕ)

/-- The radical element `[[1, Nℓ₀, Nℓ₁], [0, 1, 0], [0, 0, 1]]` of `Γ(N) ∩ Q(ℤ)`. -/
def nQ (ℓ : Fin 2 → ℤ) : ↥(gammaN N) :=
  ⟨radEltQ N (Multiplicative.ofAdd (ℓ 0, ℓ 1)), radEltQ_mem_gammaN N _⟩

theorem nQ_zero : nQ N 0 = 1 := by
  apply Subtype.ext
  show radEltQ N (Multiplicative.ofAdd ((0 : Fin 2 → ℤ) 0, (0 : Fin 2 → ℤ) 1)) = 1
  exact radEltQ_one N

theorem nQ_add (ℓ ℓ' : Fin 2 → ℤ) : nQ N (ℓ + ℓ') = nQ N ℓ * nQ N ℓ' := by
  apply Subtype.ext
  show radEltQ N (Multiplicative.ofAdd ((ℓ + ℓ') 0, (ℓ + ℓ') 1)) =
    radEltQ N (Multiplicative.ofAdd (ℓ 0, ℓ 1)) * radEltQ N (Multiplicative.ofAdd (ℓ' 0, ℓ' 1))
  rw [← radEltQ_mul]
  rfl

theorem lineRow_nQ (ℓ : Fin 2 → ℤ) (c : Cs N) :
    cosetRow (gammaN N) (cosetMulR (gammaN N) (nQ N ℓ) c) 0 = cosetRow (gammaN N) c 0 ∧
    cosetRow (gammaN N) (cosetMulR (gammaN N) (nQ N ℓ) c) 1 =
      cosetRow (gammaN N) c 1 + (N : ℤ) * (cosetRow (gammaN N) c 0 * ℓ 0) ∧
    cosetRow (gammaN N) (cosetMulR (gammaN N) (nQ N ℓ) c) 2 =
      cosetRow (gammaN N) c 2 + (N : ℤ) * (cosetRow (gammaN N) c 0 * ℓ 1) := by
  induction c using Quotient.inductionOn with | _ a => ?_
  rw [cosetMulR_mk]
  have e : ∀ j, cosetRow (gammaN N) (Quotient.mk _ (a * nQ N ℓ)) j =
      ((a.1 * radEltQ N (Multiplicative.ofAdd (ℓ 0, ℓ 1)) : SL(3, ℤ)) :
        Matrix (Fin 3) (Fin 3) ℤ) 2 j := fun j => rfl
  have e' : ∀ j, cosetRow (gammaN N) (Quotient.mk _ a) j =
      (a.1 : Matrix (Fin 3) (Fin 3) ℤ) 2 j := fun j => rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [e, e', Matrix.SpecialLinearGroup.coe_mul]
    simp [Matrix.mul_apply, Fin.sum_univ_three, radEltQ]
  · rw [e, e', e', Matrix.SpecialLinearGroup.coe_mul]
    simp [Matrix.mul_apply, Fin.sum_univ_three, radEltQ]
    ring
  · rw [e, e', e', Matrix.SpecialLinearGroup.coe_mul]
    simp [Matrix.mul_apply, Fin.sum_univ_three, radEltQ]
    ring

/-- **The line lies in the plane**: if `r₀ = 0` the radical lattice of `Q` fixes the coset. -/
theorem cosetMulR_nQ_of_zero (ℓ : Fin 2 → ℤ) (c : Cs N) (h0 : cosetRow (gammaN N) c 0 = 0) :
    cosetMulR (gammaN N) (nQ N ℓ) c = c := by
  apply cosetRow_injective
  obtain ⟨a, b, d⟩ := lineRow_nQ N ℓ c
  funext j
  fin_cases j
  · exact a
  · simp [b, h0]
  · simp [d, h0]

/-- **The complementary cell**: if `r₀ ≠ 0` the radical lattice of `Q` acts freely on the coset. -/
theorem cosetMulR_nQ_injective (c : Cs N) [NeZero N] (h0 : cosetRow (gammaN N) c 0 ≠ 0) :
    Function.Injective (fun ℓ : Fin 2 → ℤ => cosetMulR (gammaN N) (nQ N ℓ) c) := by
  intro ℓ ℓ' h
  obtain ⟨-, b, d⟩ := lineRow_nQ N ℓ c
  obtain ⟨-, b', d'⟩ := lineRow_nQ N ℓ' c
  have hN : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have h1 := congrFun (congrArg (cosetRow (gammaN N)) h) 1
  have h2 := congrFun (congrArg (cosetRow (gammaN N)) h) 2
  rw [b, b'] at h1
  rw [d, d'] at h2
  funext i
  fin_cases i
  · have : (N : ℤ) * (cosetRow (gammaN N) c 0) * (ℓ 0 - ℓ' 0) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (mul_ne_zero hN h0)
    · simpa [sub_eq_zero] using h
  · have : (N : ℤ) * (cosetRow (gammaN N) c 0) * (ℓ 1 - ℓ' 1) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (mul_ne_zero hN h0)
    · simpa [sub_eq_zero] using h

end TernaryPeriodPolynomials.Argument.FormClassK
