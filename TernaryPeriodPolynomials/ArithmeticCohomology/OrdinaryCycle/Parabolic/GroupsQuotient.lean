module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Parabolic.GroupsPlane
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Parabolic.GroupsLine
public import Mathlib.GroupTheory.QuotientGroup.Basic

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryParabolicGroups
open ModThreeGoodAction RadicalFirstCohomologyLattice

/-- The actual plane Levi quotient map recovered by the proved full factorization. -/
def planeProjection : P →* PlaneLevi :=
  SemidirectProduct.rightHom.comp planeEquiv.symm.toMonoidHom

/-- The full plane Levi section into the actual integral parabolic. -/
def planeSection : PlaneLevi →* P :=
  planeEquiv.toMonoidHom.comp SemidirectProduct.inr

/-- Inclusion of the existing actual plane radical into its full parabolic. -/
def planeRadicalInclusion : planeRadical →* P :=
  planeEquiv.toMonoidHom.comp SemidirectProduct.inl

@[simp] theorem planeProjection_equiv (g : PlaneProduct) :
    planeProjection (planeEquiv g) = g.right := by simp [planeProjection]

@[simp] theorem planeSection_val (q : PlaneLevi) :
    (planeSection q).val = planeLevi q := by simp [planeSection]

@[simp] theorem planeRadicalInclusion_val (u : planeRadical) :
    (planeRadicalInclusion u).val = u.val := by simp [planeRadicalInclusion]

@[simp] theorem planeProjection_section (q : PlaneLevi) :
    planeProjection (planeSection q) = q := by simp [planeSection]

@[simp] theorem planeProjection_radical (u : planeRadical) :
    planeProjection (planeRadicalInclusion u) = 1 := by simp [planeRadicalInclusion]

theorem planeProjection_surjective : Function.Surjective planeProjection :=
  fun q => ⟨planeSection q,planeProjection_section q⟩

theorem planeSection_injective : Function.Injective planeSection :=
  Function.LeftInverse.injective planeProjection_section

theorem planeLevi_injective : Function.Injective planeLevi := by
  intro q r he
  apply planeSection_injective
  apply Subtype.ext
  simpa using he

/-- The actual radical viewed inside the full parabolic. -/
def planeRadicalInParabolic : Subgroup P := planeRadical.comap P.subtype

/-- The kernel is exactly the existing actual integral radical, with no coefficient hypothesis. -/
theorem planeProjection_ker : planeProjection.ker = planeRadicalInParabolic := by
  ext g
  constructor
  · intro hg
    let x := planeEquiv.symm g
    have hx : x.right = 1 := hg
    have he : (SemidirectProduct.inl x.left : PlaneProduct) = x :=
      SemidirectProduct.ext rfl hx.symm
    have hg' : planeRadicalInclusion x.left = g := by
      change planeEquiv (SemidirectProduct.inl x.left) = g
      rw [he]
      exact planeEquiv.apply_symm_apply g
    change g.val ∈ planeRadical
    rw [←hg',planeRadicalInclusion_val]
    exact x.left.property
  · intro hg
    change g.val ∈ planeRadical at hg
    let u : planeRadical := ⟨g.val,hg⟩
    have he : planeRadicalInclusion u = g := by
      apply Subtype.ext
      exact planeRadicalInclusion_val u
    change planeProjection g = 1
    rw [←he,planeProjection_radical]

instance planeRadicalInParabolic_normal : planeRadicalInParabolic.Normal := by
  rw [←planeProjection_ker]
  infer_instance

/-- The quotient by the actual integral radical is the full independent-sign Levi. -/
def planeQuotientEquiv : P ⧸ planeRadicalInParabolic ≃* PlaneLevi :=
  (QuotientGroup.quotientMulEquivOfEq planeProjection_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective planeProjection planeProjection_surjective)

/-- The actual line Levi quotient map recovered by the proved full factorization. -/
def lineProjection : Q →* LineLevi :=
  SemidirectProduct.rightHom.comp lineEquiv.symm.toMonoidHom

/-- The full line Levi section into the actual integral parabolic. -/
def lineSection : LineLevi →* Q :=
  lineEquiv.toMonoidHom.comp SemidirectProduct.inr

/-- Inclusion of the existing actual line radical into its full parabolic. -/
def lineRadicalInclusion : lineRadical →* Q :=
  lineEquiv.toMonoidHom.comp SemidirectProduct.inl

@[simp] theorem lineProjection_equiv (g : LineProduct) :
    lineProjection (lineEquiv g) = g.right := by simp [lineProjection]

@[simp] theorem lineSection_val (q : LineLevi) :
    (lineSection q).val = lineLevi q := by simp [lineSection]

@[simp] theorem lineRadicalInclusion_val (u : lineRadical) :
    (lineRadicalInclusion u).val = u.val := by simp [lineRadicalInclusion]

@[simp] theorem lineProjection_section (q : LineLevi) :
    lineProjection (lineSection q) = q := by simp [lineSection]

@[simp] theorem lineProjection_radical (u : lineRadical) :
    lineProjection (lineRadicalInclusion u) = 1 := by simp [lineRadicalInclusion]

theorem lineProjection_surjective : Function.Surjective lineProjection :=
  fun q => ⟨lineSection q,lineProjection_section q⟩

theorem lineSection_injective : Function.Injective lineSection :=
  Function.LeftInverse.injective lineProjection_section

theorem lineLevi_injective : Function.Injective lineLevi := by
  intro q r he
  apply lineSection_injective
  apply Subtype.ext
  simpa using he

/-- The actual radical viewed inside the full parabolic. -/
def lineRadicalInParabolic : Subgroup Q := lineRadical.comap Q.subtype

/-- The kernel is exactly the existing actual integral radical, with no coefficient hypothesis. -/
theorem lineProjection_ker : lineProjection.ker = lineRadicalInParabolic := by
  ext g
  constructor
  · intro hg
    let x := lineEquiv.symm g
    have hx : x.right = 1 := hg
    have he : (SemidirectProduct.inl x.left : LineProduct) = x :=
      SemidirectProduct.ext rfl hx.symm
    have hg' : lineRadicalInclusion x.left = g := by
      change lineEquiv (SemidirectProduct.inl x.left) = g
      rw [he]
      exact lineEquiv.apply_symm_apply g
    change g.val ∈ lineRadical
    rw [←hg',lineRadicalInclusion_val]
    exact x.left.property
  · intro hg
    change g.val ∈ lineRadical at hg
    let u : lineRadical := ⟨g.val,hg⟩
    have he : lineRadicalInclusion u = g := by
      apply Subtype.ext
      exact lineRadicalInclusion_val u
    change lineProjection g = 1
    rw [←he,lineProjection_radical]

instance lineRadicalInParabolic_normal : lineRadicalInParabolic.Normal := by
  rw [←lineProjection_ker]
  infer_instance

/-- The quotient by the actual integral radical is the full independent-sign Levi. -/
def lineQuotientEquiv : Q ⧸ lineRadicalInParabolic ≃* LineLevi :=
  (QuotientGroup.quotientMulEquivOfEq lineProjection_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective lineProjection lineProjection_surjective)

end TernaryPoly.OrdinaryParabolicGroups
