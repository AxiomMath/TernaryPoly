module

public import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
public import TernaryPeriodPolynomials.Topology.Rational.Relative.ExcisionAlgebra

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalRelativeSupport
open CategoryTheory Limits

variable {C : Type*} [Category C] [Abelian C]
variable {L₁ L₂ : ShortComplex C} (f : L₁ ⟶ L₂)

/-- The literal componentwise quotient row of a commuting diagram of short complexes. -/
def quotientRow : ShortComplex C :=
  ShortComplex.mk
    (cokernel.map f.τ₁ f.τ₂ L₁.f L₂.f f.comm₁₂)
    (cokernel.map f.τ₂ f.τ₃ L₁.g L₂.g f.comm₂₃) (by
      apply (cancel_epi (cokernel.π f.τ₁)).mp
      simp only [cokernel.map, Category.assoc, cokernel.π_desc_assoc, comp_zero]
      erw [cokernel.π_desc, ← Category.assoc, L₂.zero, zero_comp])

/-- The quotient row carries the literal three cokernel projections. -/
def quotientProjection : L₂ ⟶ quotientRow f where
  τ₁ := cokernel.π f.τ₁
  τ₂ := cokernel.π f.τ₂
  τ₃ := cokernel.π f.τ₃
  comm₁₂ := by simp [quotientRow, cokernel.map]
  comm₂₃ := by simp [quotientRow, cokernel.map]

/-- The original diagram vanishes in its literal componentwise quotient. -/
theorem quotientProjection_condition : f ≫ quotientProjection f = 0 := by
  ext <;> exact cokernel.condition _

/-- The componentwise quotient row is the actual categorical cokernel of the diagram. -/
def quotientIsCokernel : IsColimit
    (CokernelCofork.ofπ (quotientProjection f) (quotientProjection_condition f)) := by
  refine CokernelCofork.IsColimit.ofπ _ _ (fun {Z} s hs => ?_) ?_ ?_
  · refine
      { τ₁ := cokernel.desc f.τ₁ s.τ₁ ?_
        τ₂ := cokernel.desc f.τ₂ s.τ₂ ?_
        τ₃ := cokernel.desc f.τ₃ s.τ₃ ?_
        comm₁₂ := ?_
        comm₂₃ := ?_ }
    · exact congrArg ShortComplex.Hom.τ₁ hs
    · exact congrArg ShortComplex.Hom.τ₂ hs
    · exact congrArg ShortComplex.Hom.τ₃ hs
    · apply (cancel_epi (cokernel.π f.τ₁)).mp
      dsimp [quotientRow]
      simp only [Category.assoc, cokernel.map, cokernel.π_desc_assoc]
      erw [cokernel.π_desc_assoc, cokernel.π_desc]
      exact s.comm₁₂
    · apply (cancel_epi (cokernel.π f.τ₂)).mp
      dsimp [quotientRow]
      simp only [Category.assoc, cokernel.map, cokernel.π_desc_assoc]
      erw [cokernel.π_desc_assoc, cokernel.π_desc]
      exact s.comm₂₃
  · intro Z s hs
    ext <;> exact cokernel.π_desc _ _ _
  · intro Z s hs m hm
    ext
    · apply (cancel_epi (cokernel.π f.τ₁)).mp
      erw [cokernel.π_desc]
      exact congrArg ShortComplex.Hom.τ₁ hm
    · apply (cancel_epi (cokernel.π f.τ₂)).mp
      erw [cokernel.π_desc]
      exact congrArg ShortComplex.Hom.τ₂ hm
    · apply (cancel_epi (cokernel.π f.τ₃)).mp
      erw [cokernel.π_desc]
      exact congrArg ShortComplex.Hom.τ₃ hm

/-- The snake input for the genuine quotient of two exact rows. -/
def quotientSnake (h₁ : L₁.ShortExact) (h₂ : L₂.ShortExact) : ShortComplex.SnakeInput C where
  L₀ := kernel f
  L₁ := L₁
  L₂ := L₂
  L₃ := quotientRow f
  v₀₁ := kernel.ι f
  v₁₂ := f
  v₂₃ := quotientProjection f
  w₀₂ := kernel.condition f
  w₁₃ := quotientProjection_condition f
  h₀ := kernelIsKernel f
  h₃ := quotientIsCokernel f
  L₁_exact := h₁.exact
  epi_L₁_g := h₁.epi_g
  L₂_exact := h₂.exact
  mono_L₂_f := h₂.mono_f

/-- Quotienting two exact rows by a diagram monic at the right preserves short exactness. -/
theorem quotientRow_shortExact (h₁ : L₁.ShortExact) (h₂ : L₂.ShortExact) [Mono f.τ₃] :
    (quotientRow f).ShortExact := by
  let S := quotientSnake f h₁ h₂
  have : Epi S.L₂.g := h₂.epi_g
  have : Mono S.v₁₂.τ₃ := inferInstanceAs (Mono f.τ₃)
  have hz : IsZero S.L₀.X₃ := KernelFork.IsLimit.isZero_of_mono S.h₀τ₃
  exact
    { exact := S.L₃_exact
      mono_f := (S.L₂'.exact_iff_mono (hz.eq_of_src _ _)).mp S.L₂'_exact
      epi_g := S.epi_L₃_g }

end TernaryPoly.RationalRelativeSupport
