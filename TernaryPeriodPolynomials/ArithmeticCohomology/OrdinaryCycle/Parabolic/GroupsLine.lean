module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Parabolic.GroupsActions

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryParabolicGroups
open Matrix ModThreeGoodAction RelativeStabilizerParameters RelativeStabilizerMatrices
open RadicalFirstCohomologyLattice

abbrev LineProduct := lineRadical ⋊[lineAction] LineLevi

/-- The literal radical-times-Levi multiplication map, with unrestricted lower block. -/
def lineLift : LineProduct →* IntegralGL :=
  SemidirectProduct.lift lineRadical.subtype lineLevi (fun q => by ext u; rfl)

theorem lineLift_mem (g : LineProduct) : lineLift g ∈ Q :=
  Q.mul_mem (lineRadical_le_Q g.left.property) (lineLevi_mem g.right)

def lineToParabolic : LineProduct →* Q := lineLift.codRestrict Q lineLift_mem

theorem line_normal_form_levi (u v : lineRadical) (q r : LineLevi)
    (he : u.val * lineLevi q = v.val * lineLevi r) : q = r := by
  obtain ⟨a,ha⟩ := u.property
  obtain ⟨b,hb⟩ := v.property
  rw [←ha,←hb] at he
  change lineElement 1 _ 1 * lineElement q.1 0 q.2 =
    lineElement 1 _ 1 * lineElement r.1 0 r.2 at he
  rw [RelativeVertexCohomology.line_radical_levi,RelativeVertexCohomology.line_radical_levi] at he
  apply Prod.ext
  · apply Units.ext
    simpa [lineElement_val,lineMatrix] using congrArg (fun g : IntegralGL => g.val 0 0) he
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j
    all_goals
      first
      | simpa [lineElement_val,lineMatrix] using congrArg (fun g : IntegralGL => g.val 1 1) he
      | simpa [lineElement_val,lineMatrix] using congrArg (fun g : IntegralGL => g.val 1 2) he
      | simpa [lineElement_val,lineMatrix] using congrArg (fun g : IntegralGL => g.val 2 1) he
      | simpa [lineElement_val,lineMatrix] using congrArg (fun g : IntegralGL => g.val 2 2) he

theorem lineToParabolic_injective : Function.Injective lineToParabolic := by
  intro g h he
  have he' : g.left.val * lineLevi g.right = h.left.val * lineLevi h.right :=
    congrArg Subtype.val he
  have hr := line_normal_form_levi g.left h.left g.right h.right he'
  apply SemidirectProduct.ext
  · apply Subtype.ext
    rw [hr] at he'
    exact mul_right_cancel he'
  · exact hr

theorem lineToParabolic_surjective : Function.Surjective lineToParabolic := by
  intro g
  obtain ⟨ε,u,D,hu⟩ := (mem_Q_iff_parameter g.val).mp g.property
  let v := Matrix.vecMul u (D⁻¹).val
  refine ⟨⟨lineParamEquiv (Multiplicative.ofAdd (v 0,v 1)),(ε,D)⟩,?_⟩
  apply Subtype.ext
  change lineElement 1 ![v 0,v 1] 1 * lineElement ε 0 D = g.val
  have hv : ![v 0,v 1] = v := by funext i; fin_cases i <;> rfl
  rw [hu,hv,RelativeVertexCohomology.line_radical_levi]
  dsimp [v]
  rw [Matrix.vecMul_vecMul]
  have hD : (D⁻¹).val * D.val = 1 := by rw [←Units.val_mul,inv_mul_cancel,Units.val_one]
  rw [hD,Matrix.vecMul_one]

/-- The full integral line parabolic is its actual radical semidirect its full Levi. -/
def lineEquiv : LineProduct ≃* Q :=
  MulEquiv.ofBijective lineToParabolic ⟨lineToParabolic_injective,lineToParabolic_surjective⟩

@[simp] theorem lineEquiv_val (g : LineProduct) :
    (lineEquiv g).val = g.left.val * lineLevi g.right := rfl

end TernaryPoly.OrdinaryParabolicGroups
