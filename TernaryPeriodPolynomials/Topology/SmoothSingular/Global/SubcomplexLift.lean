module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.Subcomplex
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.KernelComparison

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Limits HomologicalComplex

namespace CochainSubmodules
variable {K A : CochainComplex (ModuleCat.{0} ℝ) ℕ} (P : CochainSubmodules K)
  (f : A ⟶ K) (hf : ∀ n (x : A.X n), f.f n x ∈ P.term n)

/-- Lift an actual cochain map into a literal stable-submodule complex using proved membership. -/
def lift : A ⟶ P.toComplex :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom {
    toFun := fun x => ⟨f.f n x,hf n x⟩
    map_add' := fun x y => Subtype.ext (map_add _ x y)
    map_smul' := fun c x => Subtype.ext (map_smul _ c x) }) (by
      intro n
      simp only [toComplex,CochainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact Subtype.ext (congrArg (fun u => u.hom x) (f.comm n (n+1))))

/-- The genuine lift preserves the literal ambient cochain map. -/
theorem lift_inclusion : P.lift f hf ≫ P.inclusion = f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- The actual stable-submodule inclusion is degreewise injective. -/
theorem inclusion_injective (n : ℕ) : Function.Injective (P.inclusion.f n) := Subtype.val_injective

end CochainSubmodules

/-- Every actual element annihilated by a cochain restriction has a genuine element in its categorical kernel. -/
theorem cochainKernel_element {A B : CochainComplex (ModuleCat.{0} ℝ) ℕ}
    (r : A ⟶ B) (n : ℕ) (x : A.X n) (hx : r.f n x = 0) :
    ∃ y : (kernel r).X n, (kernel.ι r).f n y = x := by
  let S := ShortComplex.mk (kernel.ι r) r (kernel.condition r)
  have hS : S.Exact := ShortComplex.exact_of_f_is_kernel S (kernelIsKernel r)
  have hn := (HomologicalComplex.exact_iff_degreewise_exact S).mp hS n
  exact ((S.map (eval (ModuleCat ℝ) (ComplexShape.up ℕ) n)).moduleCat_exact_iff).mp hn x hx

/-- Actual categorical-kernel elements are annihilated by the literal restriction in every degree. -/
theorem cochainKernel_condition {A B : CochainComplex (ModuleCat.{0} ℝ) ℕ}
    (r : A ⟶ B) (n : ℕ) (x : (kernel r).X n) : r.f n ((kernel.ι r).f n x) = 0 :=
  congrArg (fun f : kernel r ⟶ B => (f.f n).hom x) (kernel.condition r)

end TernaryPoly.SmoothSingularGlobal
