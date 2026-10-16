module

public import TernaryPeriodPolynomials.Building.Good.Building
public import TernaryPeriodPolynomials.Building.BipartitePathChains

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryIncidence
open GoodIncidenceConnected

/-- All rational lines: the additional predicate is identically true. -/
abbrev Line := GoodIncidenceConnected.Line (fun _ => True)
/-- All rational planes, together with a redundant existence proof of a contained line. -/
abbrev Plane := GoodIncidenceConnected.Plane (fun _ => True)
abbrev Vertex := Line ⊕ Plane

/-- Every rational plane contains a rational line, so no plane is omitted by the model. -/
theorem plane_iff (P : RationalSubspace) :
    (Module.finrank ℚ P = 2 ∧ ∃ L : Line, L.val ≤ P) ↔ Module.finrank ℚ P = 2 := by
  refine ⟨And.left,fun hP => ⟨hP,?_⟩⟩
  have hn : P ≠ ⊥ := by intro h; rw [h,finrank_bot] at hP; omega
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  exact ⟨⟨Submodule.span ℚ {v},finrank_span_singleton hv0,trivial⟩,
    Submodule.span_le.mpr (by intro w hw; rcases hw with rfl; exact hv)⟩

abbrev incidence (L : Line) (P : Plane) : Prop := L.val < P.val
abbrev graph := BipartitePathChains.graph incidence

/-- The unrestricted rational incidence graph is exactly the generic true-predicate graph. -/
def graphIso : GoodIncidenceConnected.graph (fun _ => True) ≃g graph where
  toEquiv := Equiv.refl Vertex
  map_rel_iff' := by intro u v; cases u <;> cases v <;> rfl

theorem connected : graph.Connected := by
  have hc := GoodIncidenceConnected.connected (fun _ => True)
    ⟨ModThreeGoodAction.firstLine,ModThreeGoodAction.firstLine_finrank,trivial⟩
  exact { preconnected := fun u v =>
    ((GoodIncidenceConnected.vertexWalk (fun _ => True) u v).map graphIso.toHom).reachable
          nonempty := hc.nonempty }

/-- Literal inclusion of a Good line, retaining the same rational subspace. -/
def goodLine (L : GoodBuilding.GoodLine) : Line := ⟨L.val,L.property.1,trivial⟩
/-- Literal inclusion of a Good plane, retaining the same rational subspace. -/
def goodPlane (P : GoodBuilding.GoodPlane) : Plane :=
  ⟨P.val,P.property.1,by obtain ⟨L,hL⟩ := P.property.2; exact ⟨goodLine L,hL⟩⟩
def goodVertex : GoodBuilding.GoodVertex → Vertex := Sum.map goodLine goodPlane

theorem goodLine_injective : Function.Injective goodLine := fun _ _ h =>
  Subtype.ext (congrArg (fun L : Line => L.val) h)
theorem goodPlane_injective : Function.Injective goodPlane := fun _ _ h =>
  Subtype.ext (congrArg (fun P : Plane => P.val) h)
theorem goodVertex_injective : Function.Injective goodVertex := by
  intro u v h
  cases u <;> cases v
  · exact congrArg Sum.inl (goodLine_injective (Sum.inl.inj h))
  · cases h
  · cases h
  · exact congrArg Sum.inr (goodPlane_injective (Sum.inr.inj h))

/-- The ordinary action is the actual rational subspace action of the same congruence subgroup K. -/
def lineAction (g : GoodBuilding.K) : Equiv.Perm Line :=
  GoodBuilding.lineEquiv (fun _ => True) (GoodBuilding.subspaceEquiv g)
    (ModThreeGoodAction.act_finrank g) (fun _ => Iff.rfl)
def planeAction (g : GoodBuilding.K) : Equiv.Perm Plane :=
  GoodBuilding.planeEquiv (fun _ => True) (GoodBuilding.subspaceEquiv g)
    (ModThreeGoodAction.act_finrank g) (fun _ => Iff.rfl)
def vertexAction (g : GoodBuilding.K) : Equiv.Perm Vertex :=
  Equiv.sumCongr (lineAction g) (planeAction g)

theorem incidence_action_iff (g : GoodBuilding.K) (L : Line) (P : Plane) :
    incidence (lineAction g L) (planeAction g P) ↔ incidence L P :=
  ModThreeGoodAction.act_lt_act_iff g L.val P.val

theorem goodLine_equivariant (g : GoodBuilding.K) (L : GoodBuilding.GoodLine) :
    goodLine (GoodBuilding.lineAction g L) = lineAction g (goodLine L) := rfl
theorem goodPlane_equivariant (g : GoodBuilding.K) (P : GoodBuilding.GoodPlane) :
    goodPlane (GoodBuilding.planeAction g P) = planeAction g (goodPlane P) := rfl
theorem goodVertex_equivariant (g : GoodBuilding.K) (v : GoodBuilding.GoodVertex) :
    goodVertex (g • v) = vertexAction g (goodVertex v) := by cases v <;> rfl

theorem vertexAction_one (v : Vertex) : vertexAction 1 v = v := by
  cases v with
  | inl L =>
    change Sum.inl (lineAction 1 L) = Sum.inl L
    apply congrArg Sum.inl
    exact Subtype.ext (ModThreeGoodAction.act_one _)
  | inr P =>
    change Sum.inr (planeAction 1 P) = Sum.inr P
    apply congrArg Sum.inr
    exact Subtype.ext (ModThreeGoodAction.act_one _)
theorem vertexAction_mul (g h : GoodBuilding.K) (v : Vertex) :
    vertexAction (g*h) v = vertexAction g (vertexAction h v) := by
  cases v with
  | inl L =>
    change Sum.inl (lineAction (g*h) L) = Sum.inl (lineAction g (lineAction h L))
    apply congrArg Sum.inl
    exact Subtype.ext (ModThreeGoodAction.act_mul g h _)
  | inr P =>
    change Sum.inr (planeAction (g*h) P) = Sum.inr (planeAction g (planeAction h P))
    apply congrArg Sum.inr
    exact Subtype.ext (ModThreeGoodAction.act_mul g h _)

end TernaryPoly.OrdinaryIncidence
