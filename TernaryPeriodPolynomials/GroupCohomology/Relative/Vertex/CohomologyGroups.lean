module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.Vertex.CohomologySemidirect

@[expose] public section


open CategoryTheory CategoryTheory.Limits Matrix
noncomputable section
namespace TernaryPoly.RelativeVertexCohomology
open ModThreeGoodAction RelativeStabilizerParameters RelativeStabilizerMatrices
open RelativeStabilizerConsumer RadicalFirstCohomologyLattice

/-- The actual multiplication map from plane radical and Levi. -/
def planeLift : (planeRadical ⋊[planeAction] GL2) →* IntegralGL :=
  SemidirectProduct.lift planeRadical.subtype planeLevi (fun M => by ext u; rfl)

/-- The actual multiplication map from line radical and Levi. -/
def lineLift : (lineRadical ⋊[lineAction] (ℤˣ × Gamma)) →* IntegralGL :=
  SemidirectProduct.lift lineRadical.subtype lineLevi (fun q => by ext u; rfl)

theorem planeLift_mem (g : planeRadical ⋊[planeAction] GL2) : planeLift g ∈ HPGroup := by
  apply HPGroup.mul_mem
  · obtain ⟨u,hu⟩ := g.left.property
    change g.left.val ∈ HPGroup
    rw [← hu]
    exact planeHom_mem_HP u
  · exact planeElement_mem _ _

theorem lineLift_mem (g : lineRadical ⋊[lineAction] (ℤˣ × Gamma)) : lineLift g ∈ HLGroup := by
  apply HLGroup.mul_mem
  · obtain ⟨u,hu⟩ := g.left.property
    change g.left.val ∈ HLGroup
    rw [← hu]
    exact lineHom_mem_HL u
  · exact (lineElement_mem_iff _ _ _).mpr ((mem_Gamma_iff _).mp g.right.2.property)

def planeToStabilizer : (planeRadical ⋊[planeAction] GL2) →* HPGroup :=
  planeLift.codRestrict HPGroup planeLift_mem

def lineToStabilizer : (lineRadical ⋊[lineAction] (ℤˣ × Gamma)) →* HLGroup :=
  lineLift.codRestrict HLGroup lineLift_mem

theorem plane_normal_form_levi (u v : planeRadical) (M D : GL2)
    (he : u.val * planeLevi M = v.val * planeLevi D) : M = D := by
  obtain ⟨a,ha⟩ := u.property
  obtain ⟨b,hb⟩ := v.property
  rw [← ha, ← hb] at he
  change planeElement 1 _ * planeElement M 0 = planeElement 1 _ * planeElement D 0 at he
  rw [plane_radical_levi,plane_radical_levi] at he
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    first
    | simpa [planeElement_val,planeMatrix] using congrArg (fun g : IntegralGL => g.val 0 0) he
    | simpa [planeElement_val,planeMatrix] using congrArg (fun g : IntegralGL => g.val 0 1) he
    | simpa [planeElement_val,planeMatrix] using congrArg (fun g : IntegralGL => g.val 1 0) he
    | simpa [planeElement_val,planeMatrix] using congrArg (fun g : IntegralGL => g.val 1 1) he

theorem line_normal_form_levi (u v : lineRadical) (q r : ℤˣ × Gamma)
    (he : u.val * lineLevi q = v.val * lineLevi r) : q = r := by
  obtain ⟨a,ha⟩ := u.property
  obtain ⟨b,hb⟩ := v.property
  rw [← ha, ← hb] at he
  change lineElement 1 _ 1 * lineElement q.1 0 q.2.val =
    lineElement 1 _ 1 * lineElement r.1 0 r.2.val at he
  rw [line_radical_levi,line_radical_levi] at he
  apply Prod.ext
  · apply Units.ext
    simpa [lineElement_val,lineMatrix] using congrArg (fun g : IntegralGL => g.val 0 0) he
  · apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j
    all_goals
      first
      | simpa [lineElement_val,lineMatrix] using congrArg (fun g : IntegralGL => g.val 1 1) he
      | simpa [lineElement_val,lineMatrix] using congrArg (fun g : IntegralGL => g.val 1 2) he
      | simpa [lineElement_val,lineMatrix] using congrArg (fun g : IntegralGL => g.val 2 1) he
      | simpa [lineElement_val,lineMatrix] using congrArg (fun g : IntegralGL => g.val 2 2) he

theorem planeToStabilizer_injective : Function.Injective planeToStabilizer := by
  intro g h he
  have he' : g.left.val * planeLevi g.right = h.left.val * planeLevi h.right :=
    congrArg Subtype.val he
  have hr := plane_normal_form_levi g.left h.left g.right h.right he'
  apply SemidirectProduct.ext
  · apply Subtype.ext
    rw [hr] at he'
    exact mul_right_cancel he'
  · exact hr

theorem lineToStabilizer_injective : Function.Injective lineToStabilizer := by
  intro g h he
  have he' : g.left.val * lineLevi g.right = h.left.val * lineLevi h.right :=
    congrArg Subtype.val he
  have hr := line_normal_form_levi g.left h.left g.right h.right he'
  apply SemidirectProduct.ext
  · apply Subtype.ext
    rw [hr] at he'
    exact mul_right_cancel he'
  · exact hr

theorem planeToStabilizer_surjective : Function.Surjective planeToStabilizer := by
  intro g
  obtain ⟨M,u,hu⟩ := (hp_iff_parameter g.val).mp g.property
  refine ⟨⟨planeParamEquiv (Multiplicative.ofAdd (u 0,u 1)),M⟩, ?_⟩
  apply Subtype.ext
  change planeElement 1 ![u 0,u 1] * planeElement M 0 = g.val
  rw [hu,plane_radical_levi]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem lineToStabilizer_surjective : Function.Surjective lineToStabilizer := by
  intro g
  obtain ⟨ε,u,D,hD,hu⟩ := (hl_iff_parameter g.val).mp g.property
  let v := Matrix.vecMul u (D⁻¹).val
  refine ⟨⟨lineParamEquiv (Multiplicative.ofAdd (v 0,v 1)),
    (ε,⟨D,(mem_Gamma_iff _).mpr hD⟩)⟩, ?_⟩
  apply Subtype.ext
  change lineElement 1 ![v 0,v 1] 1 * lineElement ε 0 D = g.val
  have hv : ![v 0,v 1] = v := by funext i; fin_cases i <;> rfl
  rw [hu,hv,line_radical_levi]
  dsimp [v]
  rw [Matrix.vecMul_vecMul]
  have hD' : (D⁻¹).val * D.val = 1 := by rw [← Units.val_mul,inv_mul_cancel,Units.val_one]
  rw [hD',Matrix.vecMul_one]

/-- Actual HP is its literal integral radical semidirect GL₂. -/
def planeEquiv : (planeRadical ⋊[planeAction] GL2) ≃* HPGroup :=
  MulEquiv.ofBijective planeToStabilizer ⟨planeToStabilizer_injective,planeToStabilizer_surjective⟩

/-- Actual HL is its literal radical semidirect (independent sign × exact congruence subgroup). -/
def lineEquiv : (lineRadical ⋊[lineAction] (ℤˣ × Gamma)) ≃* HLGroup :=
  MulEquiv.ofBijective lineToStabilizer ⟨lineToStabilizer_injective,lineToStabilizer_surjective⟩

@[simp] theorem planeEquiv_val (g : planeRadical ⋊[planeAction] GL2) :
    (planeEquiv g).val = g.left.val * planeLevi g.right := rfl

@[simp] theorem lineEquiv_val (g : lineRadical ⋊[lineAction] (ℤˣ × Gamma)) :
    (lineEquiv g).val = g.left.val * lineLevi g.right := rfl

end TernaryPoly.RelativeVertexCohomology
