module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.UnfoldReal
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Unfold.Sum
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Line.Cells

@[expose] public section


/-!
# The line radical lattice acting on the cosets `Γ_P \ Γ(N)`

Paper: "Two planes are either equal
or distinct. A line is either contained in or complementary to the source plane."

`latQ ℓ ∈ Γ(N)` is the element with `realMat = qMat (N ℓ)` (the image under the face translation by `Nℓ`).
Right multiplication by it changes the bottom row `(r₀, r₁, r₂)` of a coset to
`(r₀, r₁ - N r₀ ℓ₁, r₂ - N r₀ ℓ₀)`: it fixes the coset iff `r₀ = 0` (`latQ_fix`) and acts freely on a
coset with `r₀ ≠ 0` (`latQ_free`). The coefficient `PhiQ` of the face pullback of the summand at `γ qMat w`
is equivariant: `PhiQ (c · latQ ℓ) w = PhiQ c (N ℓ + w)` (`PhiQ_latQ`).

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial
open scoped MatrixGroups ContDiff
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.SeedC3S4c
  TernaryPeriodPolynomials.Argument.FormClassK TernaryPeriodPolynomials.Argument.GammaNFaces

section Lattice

variable (N : ℕ)

/-- The lattice element of `Γ(N)` acting on the line-face model by the translation `N ℓ`. -/
def latQ (ℓ : Fin 2 → ℤ) : ↥(gammaN N) := nQ N ![-(ℓ 1), -(ℓ 0)]

theorem realMat_latQ (ℓ : Fin 2 → ℤ) : realMat (latQ N ℓ).1 = qMat ((N : ℝ) • intVec ℓ) := by
  have hv : ((radEltQ N (Multiplicative.ofAdd (-(ℓ 1), -(ℓ 0))) : SL(3, ℤ)) :
      Matrix (Fin 3) (Fin 3) ℤ) = !![1, (N : ℤ) * (-(ℓ 1)), (N : ℤ) * (-(ℓ 0)); 0, 1, 0; 0, 0, 1] := rfl
  show realMat (radEltQ N (Multiplicative.ofAdd (-(ℓ 1), -(ℓ 0)))) = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realMat_apply, hv, qMat, intVec]

theorem latQ_zero : latQ N 0 = 1 := by
  have : (![-((0 : Fin 2 → ℤ) 1), -((0 : Fin 2 → ℤ) 0)] : Fin 2 → ℤ) = 0 := by
    funext i; fin_cases i <;> simp
  unfold latQ
  rw [this, nQ_zero]

theorem latQ_add (ℓ ℓ' : Fin 2 → ℤ) : latQ N (ℓ + ℓ') = latQ N ℓ * latQ N ℓ' := by
  have : (![-((ℓ + ℓ') 1), -((ℓ + ℓ') 0)] : Fin 2 → ℤ) =
      ![-(ℓ 1), -(ℓ 0)] + ![-(ℓ' 1), -(ℓ' 0)] := by
    funext i; fin_cases i <;> simp <;> ring
  unfold latQ
  rw [this, nQ_add]

theorem cosetRow_latQ (ℓ : Fin 2 → ℤ) (c : PlaneCoset (gammaN N)) :
    cosetRow (gammaN N) (cosetMulR (gammaN N) (latQ N ℓ) c) 0 = cosetRow (gammaN N) c 0 ∧
    cosetRow (gammaN N) (cosetMulR (gammaN N) (latQ N ℓ) c) 1 =
      cosetRow (gammaN N) c 1 - (N : ℤ) * (cosetRow (gammaN N) c 0 * ℓ 1) ∧
    cosetRow (gammaN N) (cosetMulR (gammaN N) (latQ N ℓ) c) 2 =
      cosetRow (gammaN N) c 2 - (N : ℤ) * (cosetRow (gammaN N) c 0 * ℓ 0) := by
  obtain ⟨e0, e1, e2⟩ := lineRow_nQ N ![-(ℓ 1), -(ℓ 0)] c
  refine ⟨e0, ?_, ?_⟩
  · rw [show cosetMulR (gammaN N) (latQ N ℓ) c = cosetMulR (gammaN N) (nQ N ![-(ℓ 1), -(ℓ 0)]) c from rfl, e1]
    simp; ring
  · rw [show cosetMulR (gammaN N) (latQ N ℓ) c = cosetMulR (gammaN N) (nQ N ![-(ℓ 1), -(ℓ 0)]) c from rfl, e2]
    simp; ring

/-- The line lies in the plane (`r₀ = 0`): the lattice fixes the coset. -/
theorem latQ_fix (ℓ : Fin 2 → ℤ) (c : PlaneCoset (gammaN N))
    (h0 : cosetRow (gammaN N) c 0 = 0) : cosetMulR (gammaN N) (latQ N ℓ) c = c :=
  cosetMulR_nQ_of_zero N _ c h0

/-- The complementary cell (`r₀ ≠ 0`): the lattice acts freely. -/
theorem latQ_free [NeZero N] (c : PlaneCoset (gammaN N)) (h0 : cosetRow (gammaN N) c 0 ≠ 0) :
    Function.Injective (fun ℓ : Fin 2 → ℤ => cosetMulR (gammaN N) (latQ N ℓ) c) := by
  intro ℓ ℓ' h
  have := cosetMulR_nQ_injective N c h0 (a₁ := ![-(ℓ 1), -(ℓ 0)]) (a₂ := ![-(ℓ' 1), -(ℓ' 0)]) h
  funext i
  fin_cases i
  · have := congrFun this 1; simpa using this
  · have := congrFun this 0; simpa using this

end Lattice

end TernaryPeriodPolynomials.Argument.EisensteinClass
