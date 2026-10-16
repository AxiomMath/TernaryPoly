module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import TernaryPeriodPolynomials.Analysis.HilbertComplex.MinimalComplex

@[expose] public section


/-! Actual densely defined operators obtained from linear maps on embedded cores. -/
noncomputable section
namespace TernaryPoly.EmbeddedLinearOperator
open scoped LinearPMap InnerProductSpace
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Transport the prescribed core map to precisely the range of an injective embedding. -/
def operator (i : V →ₗ[ℝ] E) (hi : Function.Injective i) (D : V →ₗ[ℝ] F) : E →ₗ.[ℝ] F where
  domain := i.range
  toFun := D.comp (LinearEquiv.ofInjective i hi).symm.toLinearMap

@[simp] theorem operator_domain (i : V →ₗ[ℝ] E) (hi : Function.Injective i) (D : V →ₗ[ℝ] F) :
    (operator i hi D).domain = i.range := rfl

@[simp] theorem operator_apply (i : V →ₗ[ℝ] E) (hi : Function.Injective i)
    (D : V →ₗ[ℝ] F) (v : V) :
    operator i hi D ⟨i v, ⟨v, rfl⟩⟩ = D v := by
  change D ((LinearEquiv.ofInjective i hi).symm ((LinearEquiv.ofInjective i hi) v)) = D v
  rw [LinearEquiv.symm_apply_apply]

/-- The actual transported domain is dense whenever the original embedding has dense range. -/
theorem domain_dense (i : V →ₗ[ℝ] E) (hi : Function.Injective i) (D : V →ₗ[ℝ] F)
    (hd : DenseRange i) : Dense ((operator i hi D).domain : Set E) := hd

/-- The integral integration-by-parts identity on cores is exactly formal adjointness. -/
theorem isFormalAdjoint (i : V →ₗ[ℝ] E) (hi : Function.Injective i)
    (j : W →ₗ[ℝ] F) (hj : Function.Injective j) (D : V →ₗ[ℝ] W) (A : W →ₗ[ℝ] V)
    (h : ∀ v w, inner ℝ (j (D v)) (j w) = inner ℝ (i v) (i (A w))) :
    (operator i hi (j.comp D)).IsFormalAdjoint (operator j hj (i.comp A)) := by
  intro v w
  obtain ⟨v0, hv0⟩ := v.property
  obtain ⟨w0, hw0⟩ := w.property
  have hv : v = ⟨i v0, ⟨v0, rfl⟩⟩ := Subtype.ext hv0.symm
  have hw : w = ⟨j w0, ⟨w0, rfl⟩⟩ := Subtype.ext hw0.symm
  subst v w
  simpa only [operator_apply, LinearMap.comp_apply] using h v0 w0

/-- A genuine integration-by-parts core identity proves closability of the transported operator. -/
theorem isClosable [CompleteSpace F] (i : V →ₗ[ℝ] E) (hi : Function.Injective i)
    (j : W →ₗ[ℝ] F) (hj : Function.Injective j) (hdj : DenseRange j)
    (D : V →ₗ[ℝ] W) (A : W →ₗ[ℝ] V)
    (h : ∀ v w, inner ℝ (j (D v)) (j w) = inner ℝ (i v) (i (A w))) :
    (operator i hi (j.comp D)).IsClosable :=
  HilbertClosedOperator.isClosable_of_formalAdjoint _ _ (domain_dense j hj _ hdj)
    (isFormalAdjoint i hi j hj D A h)

end TernaryPoly.EmbeddedLinearOperator
