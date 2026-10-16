module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.IncidenceChains
public import TernaryPeriodPolynomials.Building.Good.ApartmentCycles
public import Mathlib.LinearAlgebra.Finsupp.LSum

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryPlaneEdge
open OrdinaryIncidence OrdinaryIncidenceChains GoodApartmentCycles
attribute [local instance] Classical.propDecidable

/-- Actual rational lines incident with a specified rational plane. -/
abbrev StarLine (P : OrdinaryIncidence.Plane) := {L : OrdinaryIncidence.Line // L.val ≤ P.val}
abbrev Divisors (P : OrdinaryIncidence.Plane) := StarLine P →₀ ℚ

def augmentation (P : OrdinaryIncidence.Plane) : Divisors P →ₗ[ℚ] ℚ :=
  Finsupp.lsum ℚ (fun _ => LinearMap.id)

@[simp] theorem augmentation_single (P : OrdinaryIncidence.Plane) (L : StarLine P) (q : ℚ) :
    augmentation P (Finsupp.single L q) = q := by simp [augmentation]

abbrev St (P : OrdinaryIncidence.Plane) := LinearMap.ker (augmentation P)

/-- The minus sign agrees with the ordered symbol [second line]-[first line]. -/
def edgeValue (P : OrdinaryIncidence.Plane) (e : OrdinaryIncidenceChains.Edge) : Divisors P :=
  if he : e.val.2 = P then -Finsupp.single ⟨e.val.1,he ▸ le_of_lt e.property⟩ 1 else 0

/-- Projection takes the coefficients of the oriented flags ending at the chosen plane. -/
def projection (P : OrdinaryIncidence.Plane) : OrdinaryIncidenceChains.EdgeChains →ₗ[ℚ] Divisors P :=
  Finsupp.lsum ℚ (fun e => LinearMap.toSpanSingleton ℚ (Divisors P) (edgeValue P e))

@[simp] theorem projection_single (P : OrdinaryIncidence.Plane) (e : OrdinaryIncidenceChains.Edge) (q : ℚ) :
    projection P (Finsupp.single e q) = q • edgeValue P e := by
  simp [projection]

@[simp] theorem projection_flag (P : OrdinaryIncidence.Plane) (L : OrdinaryIncidence.Line)
    (hL : L.val ≤ P.val) :
    projection P (flagChain (fun _ => True) L P hL) = -Finsupp.single ⟨L,hL⟩ 1 := by
  simp [flagChain,edgeValue]

theorem projection_flag_ne (P Q : OrdinaryIncidence.Plane) (h : Q ≠ P) (L : OrdinaryIncidence.Line)
    (hL : L.val ≤ Q.val) : projection P (flagChain (fun _ => True) L Q hL) = 0 := by
  simp [flagChain,edgeValue,h]

/-- The degree of the projected divisor is the negative boundary coefficient at the actual plane vertex. -/
theorem augmentation_projection (P : OrdinaryIncidence.Plane) (c : OrdinaryIncidenceChains.EdgeChains) :
    augmentation P (projection P c) = -(OrdinaryIncidenceChains.boundary c) (.inr P) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero,Finsupp.zero_apply,neg_zero]
  | add c d hc hd => simp only [map_add,Finsupp.add_apply,hc,hd,neg_add]
  | single e q =>
    rw [projection_single,map_smul,BipartitePathChains.boundary_single]
    by_cases h : e.val.2 = P
    · subst P
      simp [edgeValue]
    · simp [edgeValue,h,Ne.symm h]

/-- An actual incidence cycle yields an actual degree-zero divisor on the incident lines. -/
def project (P : OrdinaryIncidence.Plane) : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] St P :=
  ((projection P).comp OrdinaryIncidenceChains.Cycles.subtype).codRestrict _ (by
    intro c
    change augmentation P (projection P c.val) = 0
    rw [augmentation_projection,show OrdinaryIncidenceChains.boundary c.val = 0 from c.property]
    rfl)

@[simp] theorem project_val (P : OrdinaryIncidence.Plane) (c : OrdinaryIncidenceChains.Cycles) :
    (project P c).val = projection P c.val := rfl

/-- A two-line chain with an endpoint outside P has no flags ending at P. -/
theorem projection_lineChain_outside (P : OrdinaryIncidence.Plane) (E L : OrdinaryIncidence.Line)
    (hE : ¬E.val ≤ P.val) : projection P (lineChain (fun _ => True) E L) = 0 := by
  by_cases he : E = L
  · subst L
    rw [lineChain_self,map_zero]
  · have hP : GoodIncidenceConnected.spanPlane (fun _ => True) E L he ≠ P := by
      intro h
      apply hE
      rw [←h]
      exact line_le_spanPlane_left _ _ _ _
    rw [lineChain_of_ne _ _ _ he,map_sub,projection_flag_ne _ _ hP,projection_flag_ne _ _ hP,sub_zero]

/-- The canonical path from the chosen plane to a fixed exterior line. -/
def rawCone (P : OrdinaryIncidence.Plane) (E : OrdinaryIncidence.Line) :
    Divisors P →ₗ[ℚ] OrdinaryIncidenceChains.EdgeChains :=
  Finsupp.lsum ℚ (fun L => LinearMap.toSpanSingleton ℚ OrdinaryIncidenceChains.EdgeChains
    (-lineChain (fun _ => True) E L.val - flagChain (fun _ => True) L.val P L.property))

@[simp] theorem rawCone_single (P : OrdinaryIncidence.Plane) (E : OrdinaryIncidence.Line)
    (L : StarLine P) (q : ℚ) :
    rawCone P E (Finsupp.single L q) =
      q • (-lineChain (fun _ => True) E L.val - flagChain (fun _ => True) L.val P L.property) := by
  simp [rawCone]

/-- All cone paths have the same boundary; a degree-zero combination is a cycle. -/
theorem boundary_rawCone (P : OrdinaryIncidence.Plane) (E : OrdinaryIncidence.Line) (c : Divisors P) :
    OrdinaryIncidenceChains.boundary (rawCone P E c) =
      augmentation P c • (Finsupp.single (.inl E) 1 - Finsupp.single (.inr P) 1) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero,zero_smul]
  | add c d hc hd => simp only [map_add,hc,hd,add_smul]
  | single L q =>
    rw [rawCone_single,map_smul,map_sub,map_neg,boundary_lineChain,boundary_flagChain,augmentation_single]
    congr 1
    abel

/-- The actual linear coning of degree-zero incident-line divisors into ordinary incidence cycles. -/
def cone (P : OrdinaryIncidence.Plane) (E : OrdinaryIncidence.Line) :
    St P →ₗ[ℚ] OrdinaryIncidenceChains.Cycles :=
  ((rawCone P E).comp (St P).subtype).codRestrict _ (by
    intro c
    change OrdinaryIncidenceChains.boundary (rawCone P E c.val) = 0
    rw [boundary_rawCone,c.property,zero_smul])

/-- Projection of the cone is literally the original divisor when its exterior line is outside the plane. -/
theorem projection_rawCone (P : OrdinaryIncidence.Plane) (E : OrdinaryIncidence.Line)
    (hE : ¬E.val ≤ P.val) (c : Divisors P) : projection P (rawCone P E c) = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add,hc,hd]
  | single L q =>
    rw [rawCone_single,map_smul,map_sub,map_neg,projection_lineChain_outside P E L.val hE,
      projection_flag,neg_zero,zero_sub,neg_neg]
    simp

@[simp] theorem project_cone (P : OrdinaryIncidence.Plane) (E : OrdinaryIncidence.Line)
    (hE : ¬E.val ≤ P.val) (c : St P) : project P (cone P E c) = c :=
  Subtype.ext (projection_rawCone P E hE c.val)

/-- The literal two-line divisor with the same ordered-symbol convention as the binary model. -/
def symbol (P : OrdinaryIncidence.Plane) (L M : StarLine P) : St P :=
  ⟨Finsupp.single M 1 - Finsupp.single L 1,by simp⟩

/-- Coning a symbol gives the actual oriented apartment with that exterior vertex. -/
theorem cone_symbol (P : OrdinaryIncidence.Plane) (E : OrdinaryIncidence.Line) (L M : StarLine P) :
    cone P E (symbol P L M) = apartmentCycle (fun _ => True) E L.val M.val := by
  apply Subtype.ext
  change rawCone P E (Finsupp.single M 1 - Finsupp.single L 1) = _
  rw [map_sub,rawCone_single,rawCone_single,one_smul,one_smul]
  rw [apartmentCycle_coe,apartmentChain,lineChain_of_common_plane _ L.val M.val P L.property M.property,
    lineChain_reverse _ E M.val]
  abel

/-- The reference orientation projects an exterior-first apartment to [M]-[L]. -/
theorem project_apartment (P : OrdinaryIncidence.Plane) (E : OrdinaryIncidence.Line)
    (hE : ¬E.val ≤ P.val) (L M : StarLine P) :
    project P (apartmentCycle (fun _ => True) E L.val M.val) = symbol P L M := by
  rw [←cone_symbol,project_cone P E hE]

end TernaryPoly.OrdinaryPlaneEdge
