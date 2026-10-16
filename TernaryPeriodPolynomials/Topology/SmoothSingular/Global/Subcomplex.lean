module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.TotalWindow

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory

/-- Actual real cochain submodules stable under the literal differential. -/
structure CochainSubmodules (K : CochainComplex (ModuleCat.{0} ℝ) ℕ) where
  term : ∀ n, Submodule ℝ (K.X n)
  differential_mem : ∀ n (x : K.X n), x ∈ term n → K.d n (n+1) x ∈ term (n+1)

namespace CochainSubmodules
variable {K : CochainComplex (ModuleCat.{0} ℝ) ℕ} (P : CochainSubmodules K)

def differential (n : ℕ) : P.term n →ₗ[ℝ] P.term (n+1) where
  toFun x := ⟨K.d n (n+1) x.val,P.differential_mem n x.val x.property⟩
  map_add' x y := Subtype.ext (map_add _ x.val y.val)
  map_smul' c x := Subtype.ext (map_smul _ c x.val)

/-- The literal subcomplex of the original real cochain complex. -/
def toComplex : CochainComplex (ModuleCat ℝ) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of ℝ (P.term n))
    (fun n => ModuleCat.ofHom (P.differential n)) (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact congrArg (fun f => f.hom x.val) (K.d_comp_d n (n+1) (n+1+1)))

theorem differential_eq (n : ℕ) : (P.toComplex.d n (n+1)).hom = P.differential n := by
  simp only [toComplex,CochainComplex.of_d,ModuleCat.hom_ofHom]
  rfl

/-- Actual inclusion into the original real cochain complex. -/
def inclusion : P.toComplex ⟶ K :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (P.term n).subtype) (by
    intro n
    simp only [toComplex,CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl)

variable {L : CochainComplex (ModuleCat.{0} ℝ) ℕ} (Q : CochainSubmodules L) (f : K ⟶ L)
  (hf : ∀ n (x : K.X n), x ∈ P.term n → f.f n x ∈ Q.term n)

/-- Restricting an actual cochain map to its actual stable submodules. -/
def map : P.toComplex ⟶ Q.toComplex :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom {
    toFun := fun x => ⟨f.f n x.val,hf n x.val x.property⟩
    map_add' := fun x y => Subtype.ext (map_add _ x.val y.val)
    map_smul' := fun c x => Subtype.ext (map_smul _ c x.val) }) (by
      intro n
      simp only [toComplex,CochainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact Subtype.ext (congrArg (fun g => g.hom x.val) (f.comm n (n+1))))

/-- Restricted actual maps commute literally with the original inclusions. -/
theorem map_inclusion : P.map Q f hf ≫ Q.inclusion = P.inclusion ≫ f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

end CochainSubmodules
end TernaryPoly.SmoothSingularGlobal
