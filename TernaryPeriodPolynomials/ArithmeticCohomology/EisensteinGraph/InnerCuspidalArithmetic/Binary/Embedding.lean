module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.Radical.Action

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous Adelic Matrix MvPolynomial

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

def binaryPolynomialEmbedding : Binary.Poly →ₐ[ℂ] Poly :=
  MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3)

theorem binaryPolynomialEmbedding_injective : Function.Injective binaryPolynomialEmbedding :=
  MvPolynomial.rename_injective _ (Fin.succ_injective 2)

def binaryHomogeneousEmbedding (degree : ℕ) :
    Binary.HomogeneousPoly degree →ₗ[ℂ] HomogeneousPoly degree where
  toFun polynomial :=
    ⟨binaryPolynomialEmbedding polynomial.val,
      polynomial.property.rename_isHomogeneous⟩
  map_add' first second := by
    apply Subtype.ext
    exact binaryPolynomialEmbedding.map_add first.val second.val
  map_smul' scalar polynomial := by
    apply Subtype.ext
    exact binaryPolynomialEmbedding.toLinearMap.map_smul scalar polynomial.val

theorem binaryHomogeneousEmbedding_injective (degree : ℕ) :
    Function.Injective (binaryHomogeneousEmbedding degree) := by
  intro first second equality
  apply Subtype.ext
  exact binaryPolynomialEmbedding_injective (congrArg Subtype.val equality)

theorem binaryPolynomialEmbedding_lineUnipotent (first second : ℂ)
    (polynomial : Binary.Poly) :
    action (-1) (lineUnipotent first second) (binaryPolynomialEmbedding polynomial) =
      binaryPolynomialEmbedding polynomial := by
  rw [action_lineUnipotent]
  change bind₁ _ ((MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3)) polynomial) = _
  rw [bind₁_rename]
  have forms :
      ( ![X 0 - C first * X 1 - C second * X 2, X 1, X 2] : Fin 3 → Poly) ∘
        (Fin.succ : Fin 2 → Fin 3) =
          fun index => (X index.succ : Poly) := by
    funext index
    fin_cases index <;> rfl
  rw [forms]
  have identity :
      bind₁ (fun index : Fin 2 => (X index.succ : Poly)) = binaryPolynomialEmbedding := by
    ext index
    simp [binaryPolynomialEmbedding]
  rw [identity]

theorem binaryHomogeneousEmbedding_lineUnipotent (degree : ℕ)
    (first second : ℚ) (polynomial : Binary.HomogeneousPoly degree) :
    rationalCoefficientComponent degree trivialCharacter (lineUnipotent first second)
        (binaryHomogeneousEmbedding degree polynomial) =
      binaryHomogeneousEmbedding degree polynomial := by
  apply Subtype.ext
  rw [rationalCoefficientComponent_lineUnipotent]
  change bind₁ _ (binaryPolynomialEmbedding polynomial.val) = _
  rw [← action_lineUnipotent]
  exact binaryPolynomialEmbedding_lineUnipotent _ _ polynomial.val

def lineRadicalInvariants (degree : ℕ) : Submodule ℂ (HomogeneousPoly degree) where
  carrier := {polynomial | ∀ first second : ℚ,
    rationalCoefficientComponent degree trivialCharacter (lineUnipotent first second)
      polynomial = polynomial}
  zero_mem' := by
    intro first second
    exact map_zero _
  add_mem' := by
    intro first second firstInvariant secondInvariant parameterOne parameterTwo
    rw [map_add, firstInvariant, secondInvariant]
  smul_mem' := by
    intro scalar polynomial invariant first second
    rw [map_smul, invariant]

theorem binaryHomogeneousEmbedding_range_le_invariants (degree : ℕ) :
    LinearMap.range (binaryHomogeneousEmbedding degree) ≤ lineRadicalInvariants degree := by
  rintro polynomial ⟨binary, rfl⟩
  exact fun first second => binaryHomogeneousEmbedding_lineUnipotent degree first second binary

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
