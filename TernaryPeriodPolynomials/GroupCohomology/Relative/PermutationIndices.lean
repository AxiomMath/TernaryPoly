module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Relative.GraphAction
public import TernaryPeriodPolynomials.GroupCohomology.Relative.PermutationQuotient

@[expose] public section

noncomputable section
namespace TernaryPoly.RelativePermutationIndices
open ModThreeGoodAction OrdinaryIncidence OrdinaryIncidenceChains
open RelativePermutationQuotient
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The actual Good-vertex predicate on the ordinary rational incidence vertices. -/
def VertexGood : Vertex → Prop
  | .inl L => Good L.val
  | .inr P => Good P.val
/-- An ordinary flag lies in the Good subgraph exactly when its line is Good. -/
def EdgeGood (e : Edge) : Prop := Good e.val.1.val

/-- Goodness of a line forces goodness of every incident plane. -/
theorem good_plane_of_good_line (e : Edge) (h : EdgeGood e) : Good e.val.2.val :=
  h.mono e.property.le

def asGoodLine (L : Line) (h : Good L.val) : GoodBuilding.GoodLine := ⟨L.val,L.property.1,h⟩
def asGoodPlane (P : Plane) (h : Good P.val) : GoodBuilding.GoodPlane :=
  ⟨P.val,(GoodBuilding.plane_iff_good P.val).mpr ⟨P.property.1,h⟩⟩

theorem goodVertex_range (v : Vertex) :
    (∃ w, goodVertex w = v) ↔ VertexGood v := by
  cases v with
  | inl L =>
    constructor
    · rintro ⟨w,hw⟩
      cases w with
      | inl M =>
        have he := congrArg (fun L : Line => L.val) (Sum.inl.inj hw)
        change Good L.val
        change M.val = L.val at he
        rw [← he]
        exact M.property.2
      | inr P => cases hw
    · intro h
      exact ⟨.inl (asGoodLine L h),rfl⟩
  | inr P =>
    constructor
    · rintro ⟨w,hw⟩
      cases w with
      | inl L => cases hw
      | inr Q =>
        have he := congrArg (fun P : Plane => P.val) (Sum.inr.inj hw)
        change Good P.val
        change Q.val = P.val at he
        rw [← he]
        exact ((GoodBuilding.plane_iff_good Q.val).mp Q.property).2
    · intro h
      exact ⟨.inr (asGoodPlane P h),rfl⟩

theorem goodEdge_range (e : Edge) : (∃ a, goodEdge a = e) ↔ EdgeGood e := by
  constructor
  · rintro ⟨a,rfl⟩
    exact a.val.1.property.2
  · intro h
    exact ⟨⟨(asGoodLine e.val.1 h,asGoodPlane e.val.2 (good_plane_of_good_line e h)),e.property⟩,rfl⟩

abbrev BadLine := {L : Line // ¬Good L.val}
abbrev BadPlane := {P : Plane // ¬Good P.val}
abbrev BB := {e : Edge // ¬Good e.val.1.val ∧ ¬Good e.val.2.val}
abbrev BG := {e : Edge // ¬Good e.val.1.val ∧ Good e.val.2.val}

/-- All relative vertices are exactly bad lines or bad planes. -/
def vertexSplit : Outside VertexGood ≃ (BadLine ⊕ BadPlane) where
  toFun
    | ⟨.inl L,h⟩ => .inl ⟨L,h⟩
    | ⟨.inr P,h⟩ => .inr ⟨P,h⟩
  invFun
    | .inl L => ⟨.inl L.val,L.property⟩
    | .inr P => ⟨.inr P.val,P.property⟩
  left_inv v := by rcases v with ⟨v,h⟩; cases v <;> rfl
  right_inv v := by cases v <;> rfl

/-- Every relative edge has bad line and either bad or Good plane, with no third type. -/
def edgeSplit : Outside EdgeGood ≃ (BB ⊕ BG) where
  toFun e := if h : Good e.val.val.2.val then .inr ⟨e.val,e.property,h⟩ else .inl ⟨e.val,e.property,h⟩
  invFun
    | .inl e => ⟨e.val,e.property.1⟩
    | .inr e => ⟨e.val,e.property.1⟩
  left_inv e := by
    by_cases h : Good e.val.val.2.val
    · dsimp only; rw [dite_eq_left h]
    · dsimp only; rw [dite_eq_right h]
  right_inv e := by
    cases e with
    | inl e => exact dite_eq_right e.property.2
    | inr e => exact dite_eq_left e.property.2

theorem VertexGood_action (g : GoodBuilding.K) (v : Vertex) :
    VertexGood (OrdinaryIncidence.vertexAction g v) ↔ VertexGood v := by
  cases v <;> exact good_act_iff g _
theorem EdgeGood_action (g : GoodBuilding.K) (e : Edge) :
    EdgeGood (OrdinaryIncidenceChains.edgeAction g e) ↔ EdgeGood e := good_act_iff g _

/-- Literal K permutations of the four complementary incidence types. -/
def badLineAction (g : GoodBuilding.K) : Equiv.Perm BadLine :=
  (lineAction g).subtypeEquiv (fun L => (not_congr (good_act_iff g L.val)).symm)
def badPlaneAction (g : GoodBuilding.K) : Equiv.Perm BadPlane :=
  (planeAction g).subtypeEquiv (fun P => (not_congr (good_act_iff g P.val)).symm)
def bbAction (g : GoodBuilding.K) : Equiv.Perm BB :=
  (OrdinaryIncidenceChains.edgeAction g).subtypeEquiv (fun e =>
    (and_congr (not_congr (good_act_iff g e.val.1.val))
      (not_congr (good_act_iff g e.val.2.val))).symm)
def bgAction (g : GoodBuilding.K) : Equiv.Perm BG :=
  (OrdinaryIncidenceChains.edgeAction g).subtypeEquiv (fun e =>
    (and_congr (not_congr (good_act_iff g e.val.1.val)) (good_act_iff g e.val.2.val)).symm)

theorem vertexSplit_natural (g : GoodBuilding.K) (v : Outside VertexGood) :
    vertexSplit (outsideEquiv VertexGood (OrdinaryIncidence.vertexAction g) (VertexGood_action g) v) =
      Equiv.sumCongr (badLineAction g) (badPlaneAction g) (vertexSplit v) := by
  rcases v with ⟨v,h⟩
  cases v <;> rfl

theorem edgeSplit_natural (g : GoodBuilding.K) (e : Outside EdgeGood) :
    edgeSplit (outsideEquiv EdgeGood (OrdinaryIncidenceChains.edgeAction g) (EdgeGood_action g) e) =
      Equiv.sumCongr (bbAction g) (bgAction g) (edgeSplit e) := by
  by_cases h : Good e.val.val.2.val
  · have ht : Good (act g e.val.val.2.val) := (good_act_iff g _).mpr h
    simp only [edgeSplit,Equiv.coe_fn_mk]
    change (if _ : Good (act g e.val.val.2.val) then _ else _) = _
    rw [dite_eq_left ht,dite_eq_left h]
    rfl
  · have ht : ¬Good (act g e.val.val.2.val) := fun hh => h ((good_act_iff g _).mp hh)
    simp only [edgeSplit,Equiv.coe_fn_mk]
    change (if _ : Good (act g e.val.val.2.val) then _ else _) = _
    rw [dite_eq_right ht,dite_eq_right h]
    rfl

end TernaryPoly.RelativePermutationIndices
