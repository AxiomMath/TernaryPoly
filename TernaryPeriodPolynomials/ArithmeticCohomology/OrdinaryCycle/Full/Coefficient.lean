module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Full.ActionFrames
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Apartment.Evaluation

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryFullCoefficient
open ModThreeGoodAction OrdinaryApartmentPresentation OrdinaryApartmentFrames
open OrdinaryApartmentEvaluation OrdinaryFullAction GoodRelativeChains AugmentedFrameComplex

variable {E : Type*} [AddCommGroup E] [Module ℚ E]

/-- The exact integral frame equations for a coefficient in an arbitrary rational representation. -/
structure Relations (ρ : Representation ℚ GL3 E) (v : E) : Prop where
  signs : ∀ s : Finset (Fin 3), ρ (integral (signFrame s)) v = v
  cyclic : ρ (integral ReferenceCoefficientMatrices.c) v = v
  swap : ρ (integral ReferenceCoefficientMatrices.s) v = -v
  norm : v + ρ (integral ReferenceCoefficientMatrices.a) v +
    ρ (integral (ReferenceCoefficientMatrices.a^2)) v = 0

/-- Exact relations provide the genuine generic evaluator, including all column-sign ambiguities. -/
def frameValues (ρ : Representation ℚ GL3 E) (v : E) (hv : Relations ρ v) : FrameValues E where
  value g := ρ (integral g) v
  lines g h he := by
    have hh : augmentedLine g 0=augmentedLine h 0 ∧
        augmentedLine g 1=augmentedLine h 1 ∧ augmentedLine g 2=augmentedLine h 2 := by
      simpa only [triangleList,List.cons.injEq,and_true] using he
    obtain ⟨s,rfl⟩ := eq_mul_signFrame_of_column_lines g h (by
      intro j; fin_cases j
      · exact hh.1
      · exact hh.2.1
      · exact hh.2.2)
    rw [map_mul,map_mul,Module.End.mul_apply,hv.signs]
  cyclic g := by rw [map_mul,map_mul,Module.End.mul_apply,hv.cyclic]
  swap g := by rw [map_mul,map_mul,Module.End.mul_apply,hv.swap,map_neg]
  norm g := by
    rw [map_mul,map_mul,Module.End.mul_apply,map_mul,map_mul,Module.End.mul_apply,
      ←map_add,←map_add,hv.norm,map_zero]

/-- Evaluation on the actual ordinary cycles, via the proved unrestricted apartment presentation. -/
def functional (ρ : Representation ℚ GL3 E) (v : E) (hv : Relations ρ v) :
    OrdinaryIncidenceChains.Cycles →ₗ[ℚ] E :=
  (relativeEvaluator (frameValues ρ v hv)).comp presentation.symm.toLinearMap

@[simp] theorem functional_frame (ρ : Representation ℚ GL3 E) (v : E) (hv : Relations ρ v)
    (g : IntegralGL) : functional ρ v hv (frameCycle g) = ρ (integral g) v := by
  change relativeEvaluator (frameValues ρ v hv) (presentation.symm (frameCycle g)) = _
  rw [←presentation_triangle,presentation.symm_apply_apply,relativeEvaluator_triangle]
  rfl

@[simp] theorem functional_reference (ρ : Representation ℚ GL3 E) (v : E) (hv : Relations ρ v) :
    functional ρ v hv (frameCycle 1) = v := by
  rw [functional_frame,map_one,map_one]
  rfl

/-- Full GL3(Z) equivariance is established on actual frame cycles and extended by their proved span. -/
theorem functional_equivariant (ρ : Representation ℚ GL3 E) (v : E) (hv : Relations ρ v)
    (g : IntegralGL) (c : OrdinaryIncidenceChains.Cycles) :
    functional ρ v hv (cycleAction (integral g) c) = ρ (integral g) (functional ρ v hv c) := by
  have he : (functional ρ v hv).comp (cycleAction (integral g)) =
      (ρ (integral g)).comp (functional ρ v hv) := by
    apply cycle_functional_ext
    intro h
    simp only [LinearMap.comp_apply,OrdinaryFullAction.frameCycle_equivariant,functional_frame,
      map_mul,Module.End.mul_apply]
  exact LinearMap.congr_fun he c

/-- The genuine space of full integral-equivariant functionals on the rational ordinary cycle module. -/
def Hom (ρ : Representation ℚ GL3 E) : Submodule ℚ (OrdinaryIncidenceChains.Cycles →ₗ[ℚ] E) where
  carrier := {f | ∀ g : IntegralGL, ∀ c, f (cycleAction (integral g) c) = ρ (integral g) (f c)}
  zero_mem' := by simp
  add_mem' := by
    intro f h hf hh g c
    simp only [LinearMap.add_apply,map_add]
    rw [hf g c,hh g c]
  smul_mem' := by
    intro q f hf g c
    simp only [LinearMap.smul_apply,map_smul]
    rw [hf g c]

/-- The frame values of a genuine equivariant functional are its representation orbit. -/
theorem hom_frame (ρ : Representation ℚ GL3 E) (f : Hom ρ) (g : IntegralGL) :
    f.val (frameCycle g) = ρ (integral g) (f.val (frameCycle 1)) := by
  have he := f.property g (frameCycle 1)
  rwa [OrdinaryFullAction.frameCycle_equivariant,mul_one] at he

/-- Every full equivariant cycle functional satisfies exactly the listed reference equations. -/
theorem hom_relations (ρ : Representation ℚ GL3 E) (f : Hom ρ) :
    Relations ρ (f.val (frameCycle 1)) where
  signs s := by
    rw [←hom_frame]
    have h := OrdinaryFullAction.frameCycle_signFrame 1 s
    rw [one_mul] at h
    rw [h]
  cyclic := by
    rw [←hom_frame]
    have h := OrdinaryFullAction.frameCycle_cyclic 1
    rw [one_mul] at h
    rw [h]
  swap := by
    rw [←hom_frame]
    have h := OrdinaryFullAction.frameCycle_swap 1
    rw [one_mul] at h
    rw [h,map_neg]
  norm := by
    rw [←hom_frame,←hom_frame,←map_add,←map_add]
    have h := OrdinaryFullAction.frameCycle_norm 1
    rw [one_mul,one_mul] at h
    rw [h,map_zero]

/-- Reference evaluation is injective, by the actual integral apartment span. -/
theorem reference_injective (ρ : Representation ℚ GL3 E) :
    Function.Injective (fun f : Hom ρ => f.val (frameCycle 1)) := by
  intro f h he
  apply Subtype.ext
  apply cycle_functional_ext
  intro g
  rw [hom_frame ρ f g,hom_frame ρ h g]
  exact congrArg (ρ (integral g)) he

/-- Its image is exactly the coefficient solution space, without any coefficient-model hypothesis. -/
theorem exists_hom_iff (ρ : Representation ℚ GL3 E) (v : E) :
    (∃ f : Hom ρ, f.val (frameCycle 1) = v) ↔ Relations ρ v := by
  constructor
  · rintro ⟨f,rfl⟩
    exact hom_relations ρ f
  · intro hv
    exact ⟨⟨functional ρ v hv,functional_equivariant ρ v hv⟩,functional_reference ρ v hv⟩

/-- The reference coefficient and the actual full-level cycle functional determine each other. -/
def coefficientEquiv (ρ : Representation ℚ GL3 E) : Hom ρ ≃ {v : E // Relations ρ v} where
  toFun f := ⟨f.val (frameCycle 1),hom_relations ρ f⟩
  invFun v := ⟨functional ρ v.val v.property,functional_equivariant ρ v.val v.property⟩
  left_inv _f := reference_injective ρ (functional_reference ρ _ _)
  right_inv _v := Subtype.ext (functional_reference ρ _ _)

/-- Reference evaluation is a linear map on the actual full-level Hom space. -/
def reference (ρ : Representation ℚ GL3 E) : Hom ρ →ₗ[ℚ] E where
  toFun f := f.val (frameCycle 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The concrete linear image is exactly the solutions of the integral apartment equations. -/
theorem mem_range_reference (ρ : Representation ℚ GL3 E) (v : E) :
    v ∈ (reference ρ).range ↔ Relations ρ v := exists_hom_iff ρ v

end TernaryPoly.OrdinaryFullCoefficient
