module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.OverlapPrimitives
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.Module.Projective

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set CategoryTheory HomologicalComplex
open SmoothCoveringDeRham SymmetricSpaceCovering

/-- Exact real linear maps admit a linear primitive on the actual kernel, hence one which
preserves literal zero. No continuity or arbitrary-support assertion is included. -/
theorem exists_linear_primitive {A B C : Type} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [Module ℝ A] [Module ℝ B] [Module ℝ C]
    (f : A →ₗ[ℝ] B) (g : B →ₗ[ℝ] C) (hgf : g.comp f = 0)
    (he : ∀ w, g w = 0 → ∃ z, f z = w) :
    ∃ s : LinearMap.ker g →ₗ[ℝ] A, ∀ w, f (s w) = w.val := by
  let f' : A →ₗ[ℝ] LinearMap.ker g := f.codRestrict (LinearMap.ker g) (by
    intro z
    exact congrArg (fun l : A →ₗ[ℝ] C => l z) hgf)
  have hf' : Function.Surjective f' := by
    intro w
    obtain ⟨z,hz⟩ := he w.val w.property
    exact ⟨z,Subtype.ext hz⟩
  obtain ⟨s,hs⟩ := f'.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf')
  refine ⟨s,fun w => ?_⟩
  exact congrArg Subtype.val (congrArg (fun l : LinearMap.ker g →ₗ[ℝ] LinearMap.ker g => l w) hs)

/-- A selected linear primitive on closed cochains of an actual exact real complex. -/
def complexLinearPrimitive (C : CochainComplex (ModuleCat.{0} ℝ) ℕ) (n : ℕ)
    (he : C.ExactAt (n+1)) : LinearMap.ker (C.d (n+1) (n+2)).hom →ₗ[ℝ] C.X n :=
  Classical.choose (exists_linear_primitive (C.d n (n+1)).hom (C.d (n+1) (n+2)).hom
    (by exact congrArg ModuleCat.Hom.hom (C.d_comp_d n (n+1) (n+2)))
    (complex_primitive_of_exactAt n he))

theorem complexLinearPrimitive_d (C : CochainComplex (ModuleCat.{0} ℝ) ℕ) (n : ℕ)
    (he : C.ExactAt (n+1)) (w : LinearMap.ker (C.d (n+1) (n+2)).hom) :
    C.d n (n+1) (complexLinearPrimitive C n he w) = w.val :=
  Classical.choose_spec (exists_linear_primitive (C.d n (n+1)).hom (C.d (n+1) (n+2)).hom
    (by exact congrArg ModuleCat.Hom.hom (C.d_comp_d n (n+1) (n+2)))
    (complex_primitive_of_exactAt n he)) w

@[simp] theorem complexLinearPrimitive_zero (C : CochainComplex (ModuleCat.{0} ℝ) ℕ) (n : ℕ)
    (he : C.ExactAt (n+1)) : complexLinearPrimitive C n he 0 = 0 := map_zero _

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F)

/-- Zero-preserving actual smooth primitives on each genuine finite overlap. The derivative
and the zero equality are literal equalities in the equivariant-form model. -/
theorem cechOverlap_form_primitive_zero {n : ℕ} (t : Fin (n+1) → ConvexSheet) (p : ℕ)
    (w : EquivariantForm ρ (cechDomain ConvexSheet.quotientDomain t) (p+1))
    (hw : differential ρ (cechDomain_isOpen ConvexSheet.quotientDomain
      ConvexSheet.quotientDomain_isOpen t) (p+1) w = 0) :
    ∃ z : EquivariantForm ρ (cechDomain ConvexSheet.quotientDomain t) p,
      differential ρ (cechDomain_isOpen ConvexSheet.quotientDomain
        ConvexSheet.quotientDomain_isOpen t) p z = w ∧ (w = 0 → z = 0) := by
  classical
  by_cases h : w = 0
  · exact ⟨0,by simp [h],fun _ => rfl⟩
  · obtain ⟨z,hz⟩ := cechOverlap_form_primitive ρ t p w hw
    exact ⟨z,hz,fun h' => (h h').elim⟩

omit [FiniteDimensional ℝ F] in
/-- Zero-preserving actual singular primitives on each genuine finite overlap. -/
theorem cechOverlap_singular_primitive_zero {n : ℕ} (t : Fin (n+1) → ConvexSheet) (p : ℕ)
    (w : (coveringCochains ρ (cechDomain ConvexSheet.quotientDomain t)).X (p+1))
    (hw : (coveringCochains ρ (cechDomain ConvexSheet.quotientDomain t)).d (p+1) (p+2) w = 0) :
    ∃ z, (coveringCochains ρ (cechDomain ConvexSheet.quotientDomain t)).d p (p+1) z = w ∧
      (w = 0 → z = 0) := by
  classical
  by_cases h : w = 0
  · exact ⟨0,by simp [h],fun _ => rfl⟩
  · obtain ⟨z,hz⟩ := cechOverlap_singular_primitive ρ t p w hw
    exact ⟨z,hz,fun h' => (h h').elim⟩

omit [FiniteDimensional ℝ F] in
/-- Actual overlap coefficient sections can also be recovered without creating a nonzero
section from a zero singular cocycle. -/
theorem cechOverlap_singular_zero_zero {n : ℕ} (t : Fin (n+1) → ConvexSheet)
    (w : (coveringCochains ρ (cechDomain ConvexSheet.quotientDomain t)).X 0)
    (hw : (coveringCochains ρ (cechDomain ConvexSheet.quotientDomain t)).d 0 1 w = 0) :
    ∃ z, coefficientSingularMap ρ (cechDomain ConvexSheet.quotientDomain t) z = w ∧
      (w = 0 → z = 0) := by
  classical
  by_cases h : w = 0
  · exact ⟨0,by simp only [map_zero, h]; rfl,fun _ => rfl⟩
  · obtain ⟨z,hz⟩ := cechOverlap_singular_zero ρ t w hw
    exact ⟨z,hz,fun h' => (h h').elim⟩

end TernaryPoly.SmoothSingularGlobal
