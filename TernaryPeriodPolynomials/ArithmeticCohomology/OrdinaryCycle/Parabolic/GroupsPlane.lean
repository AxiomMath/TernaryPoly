module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Parabolic.GroupsActions

@[expose] public section

noncomputable section
namespace TernaryPoly.OrdinaryParabolicGroups
open Matrix ModThreeGoodAction RelativeStabilizerParameters RelativeStabilizerMatrices
open RadicalFirstCohomologyLattice

abbrev PlaneProduct := planeRadical ⋊[planeAction] PlaneLevi

/-- The literal radical-times-Levi multiplication map into integral matrices. -/
def planeLift : PlaneProduct →* IntegralGL :=
  SemidirectProduct.lift planeRadical.subtype planeLevi (fun q => by ext u; rfl)

theorem planeLift_mem (g : PlaneProduct) : planeLift g ∈ P :=
  P.mul_mem (planeRadical_le_P g.left.property) (planeLevi_mem g.right)

def planeToParabolic : PlaneProduct →* P := planeLift.codRestrict P planeLift_mem

/-- The full Levi, including its last unit, is recovered uniquely from the product. -/
theorem plane_normal_form_levi (u v : planeRadical) (q r : PlaneLevi)
    (he : u.val * planeLevi q = v.val * planeLevi r) : q = r := by
  obtain ⟨a,ha⟩ := u.property
  obtain ⟨b,hb⟩ := v.property
  rw [←ha,←hb] at he
  change RelativeStabilizerParameters.planeElement 1 _ * planeElement q.1 0 q.2 =
    RelativeStabilizerParameters.planeElement 1 _ * planeElement r.1 0 r.2 at he
  rw [plane_radical_levi,plane_radical_levi] at he
  apply Prod.ext
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j
    all_goals
      first
      | simpa [planeElement_val,planeMatrix] using congrArg (fun g : IntegralGL => g.val 0 0) he
      | simpa [planeElement_val,planeMatrix] using congrArg (fun g : IntegralGL => g.val 0 1) he
      | simpa [planeElement_val,planeMatrix] using congrArg (fun g : IntegralGL => g.val 1 0) he
      | simpa [planeElement_val,planeMatrix] using congrArg (fun g : IntegralGL => g.val 1 1) he
  · apply Units.ext
    simpa [planeElement_val,planeMatrix] using congrArg (fun g : IntegralGL => g.val 2 2) he

theorem planeToParabolic_injective : Function.Injective planeToParabolic := by
  intro g h he
  have he' : g.left.val * planeLevi g.right = h.left.val * planeLevi h.right :=
    congrArg Subtype.val he
  have hr := plane_normal_form_levi g.left h.left g.right h.right he'
  apply SemidirectProduct.ext
  · apply Subtype.ext
    rw [hr] at he'
    exact mul_right_cancel he'
  · exact hr

theorem planeToParabolic_surjective : Function.Surjective planeToParabolic := by
  intro g
  obtain ⟨M,u,ε,hu⟩ := (mem_P_iff_parameter g.val).mp g.property
  let v := (ε⁻¹).val • u
  refine ⟨⟨planeParamEquiv (Multiplicative.ofAdd (v 0,v 1)),(M,ε)⟩,?_⟩
  apply Subtype.ext
  change RelativeStabilizerParameters.planeElement 1 ![v 0,v 1] * planeElement M 0 ε = g.val
  have hv : ![v 0,v 1] = v := by funext i; fin_cases i <;> rfl
  rw [hu,hv,plane_radical_levi]
  congr 1
  ext i
  simp [v,Pi.smul_apply,←mul_assoc,←Units.val_mul]

/-- The full integral plane parabolic is the actual radical semidirect its full Levi. -/
def planeEquiv : PlaneProduct ≃* P :=
  MulEquiv.ofBijective planeToParabolic ⟨planeToParabolic_injective,planeToParabolic_surjective⟩

@[simp] theorem planeEquiv_val (g : PlaneProduct) :
    (planeEquiv g).val = g.left.val * planeLevi g.right := rfl

end TernaryPoly.OrdinaryParabolicGroups
