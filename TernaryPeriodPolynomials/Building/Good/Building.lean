module

public import TernaryPeriodPolynomials.Building.Good.IncidenceConnected
public import TernaryPeriodPolynomials.Building.ModThreeGoodAction

@[expose] public section

noncomputable section
namespace TernaryPoly.GoodBuilding

open GoodIncidenceConnected

section Equivariance

variable (Good : RationalSubspace → Prop)
variable (e : RationalSubspace ≃o RationalSubspace)
variable (hdim : ∀ L, Module.finrank ℚ (e L) = Module.finrank ℚ L)
variable (hgood : ∀ L, Good (e L) ↔ Good L)
include hdim hgood

/-- An order automorphism preserving dimension and goodness permutes the good lines. -/
def lineEquiv : Line Good ≃ Line Good :=
  e.toEquiv.subtypeEquiv (by
    intro L
    change (Module.finrank ℚ L = 1 ∧ Good L) ↔ (Module.finrank ℚ (e L) = 1 ∧ Good (e L))
    rw [hdim, hgood])

@[simp] theorem lineEquiv_val (L : Line Good) :
    (lineEquiv Good e hdim hgood L).val = e L.val := rfl

/-- The same order automorphism preserves exactly the good-plane predicate. -/
theorem plane_property_iff (P : RationalSubspace) :
    (Module.finrank ℚ P = 2 ∧ ∃ L : Line Good, L.val ≤ P) ↔
      (Module.finrank ℚ (e P) = 2 ∧ ∃ L : Line Good, L.val ≤ e P) := by
  rw [hdim]
  constructor
  · rintro ⟨hP, L, hL⟩
    exact ⟨hP, lineEquiv Good e hdim hgood L, e.monotone hL⟩
  · rintro ⟨hP, M, hM⟩
    obtain ⟨L, rfl⟩ := (lineEquiv Good e hdim hgood).surjective M
    exact ⟨hP, L, e.le_iff_le.mp hM⟩

/-- Good planes are permuted through their underlying rational subspaces. -/
def planeEquiv : Plane Good ≃ Plane Good :=
  e.toEquiv.subtypeEquiv (plane_property_iff Good e hdim hgood)

@[simp] theorem planeEquiv_val (P : Plane Good) :
    (planeEquiv Good e hdim hgood P).val = e P.val := rfl

/-- The induced permutation preserves the line and plane vertex types. -/
def vertexEquiv : Vertex Good ≃ Vertex Good :=
  Equiv.sumCongr (lineEquiv Good e hdim hgood) (planeEquiv Good e hdim hgood)

@[simp] theorem vertexEquiv_inl (L : Line Good) :
    vertexEquiv Good e hdim hgood (.inl L) = .inl (lineEquiv Good e hdim hgood L) := rfl

@[simp] theorem vertexEquiv_inr (P : Plane Good) :
    vertexEquiv Good e hdim hgood (.inr P) = .inr (planeEquiv Good e hdim hgood P) := rfl

/-- Strict incidence is preserved and reflected, giving a genuine graph automorphism. -/
def graphEquiv : (GoodIncidenceConnected.graph Good) ≃g (GoodIncidenceConnected.graph Good) where
  toEquiv := vertexEquiv Good e hdim hgood
  map_rel_iff' := by
    intro u v
    cases u <;> cases v
    · exact Iff.rfl
    · exact e.lt_iff_lt
    · exact e.lt_iff_lt
    · exact Iff.rfl

end Equivariance

/-- The genuine congruence subgroup of integral invertible matrices. -/
abbrev K := ModThreeGoodAction.K
abbrev GoodLine := Line ModThreeGoodAction.Good
abbrev GoodPlane := Plane ModThreeGoodAction.Good
abbrev GoodVertex := Vertex ModThreeGoodAction.Good

/-- The restricted rational incidence graph for the actual mod-three goodness condition. -/
def graph : SimpleGraph GoodVertex := GoodIncidenceConnected.graph ModThreeGoodAction.Good

/-- For the actual lattice predicate, the plane definition is exactly goodness and dimension two. -/
theorem plane_iff_good (P : RationalSubspace) :
    (Module.finrank ℚ P = 2 ∧ ∃ L : GoodLine, L.val ≤ P) ↔
      (Module.finrank ℚ P = 2 ∧ ModThreeGoodAction.Good P) := by
  constructor
  · rintro ⟨hP, L, hL⟩
    exact ⟨hP, L.property.2.mono hL⟩
  · rintro ⟨hP, hgood⟩
    obtain ⟨L, hdim, hL, hle⟩ := (ModThreeGoodAction.good_iff_contains_good_line P).mp hgood
    exact ⟨hP, ⟨L, hdim, hL⟩, hle⟩

/-- The actual rational matrix action is an order automorphism on subspaces. -/
def subspaceEquiv (g : K) : RationalSubspace ≃o RationalSubspace where
  toFun := ModThreeGoodAction.act g
  invFun := ModThreeGoodAction.act g⁻¹
  left_inv := ModThreeGoodAction.act_inv_act g
  right_inv L := by
    rw [← ModThreeGoodAction.act_mul, mul_inv_cancel, ModThreeGoodAction.act_one]
  map_rel_iff' := ModThreeGoodAction.act_le_act_iff g _ _

@[simp] theorem subspaceEquiv_apply (g : K) (L : RationalSubspace) :
    subspaceEquiv g L = ModThreeGoodAction.act g L := rfl

/-- Permutation of actual good lines by the rational image of an integral matrix. -/
def lineAction (g : K) : Equiv.Perm GoodLine :=
  lineEquiv ModThreeGoodAction.Good (subspaceEquiv g)
    (ModThreeGoodAction.act_finrank g) (ModThreeGoodAction.good_act_iff g)

/-- Permutation of actual good planes by the same rational action. -/
def planeAction (g : K) : Equiv.Perm GoodPlane :=
  planeEquiv ModThreeGoodAction.Good (subspaceEquiv g)
    (ModThreeGoodAction.act_finrank g) (ModThreeGoodAction.good_act_iff g)

@[simp] theorem lineAction_val (g : K) (L : GoodLine) :
    (lineAction g L).val = ModThreeGoodAction.act g L.val := rfl

@[simp] theorem planeAction_val (g : K) (P : GoodPlane) :
    (planeAction g P).val = ModThreeGoodAction.act g P.val := rfl

/-- The actual line and plane permutations preserve exactly the incidence relation. -/
theorem incidence_action_iff (g : K) (L : GoodLine) (P : GoodPlane) :
    (lineAction g L).val < (planeAction g P).val ↔ L.val < P.val :=
  ModThreeGoodAction.act_lt_act_iff g L.val P.val

/-- The induced permutation preserves the two vertex types. -/
def vertexAction (g : K) : Equiv.Perm GoodVertex :=
  Equiv.sumCongr (lineAction g) (planeAction g)

/-- The actual matrix action acts by automorphisms of the restricted graph. -/
def graphAction (g : K) : graph ≃g graph :=
  graphEquiv ModThreeGoodAction.Good (subspaceEquiv g)
    (ModThreeGoodAction.act_finrank g) (ModThreeGoodAction.good_act_iff g)

@[simp] theorem graphAction_apply (g : K) (v : GoodVertex) :
    graphAction g v = vertexAction g v := rfl

/-- The permutations satisfy the genuine group identity and multiplication laws. -/
def vertexRepresentation : K →* Equiv.Perm GoodVertex where
  toFun := vertexAction
  map_one' := by
    apply Equiv.ext
    intro v
    cases v with
    | inl L =>
      change Sum.inl (lineAction 1 L) = Sum.inl L
      apply congrArg Sum.inl
      apply Subtype.ext
      exact ModThreeGoodAction.act_one L.val
    | inr P =>
      change Sum.inr (planeAction 1 P) = Sum.inr P
      apply congrArg Sum.inr
      apply Subtype.ext
      exact ModThreeGoodAction.act_one P.val
  map_mul' g h := by
    apply Equiv.ext
    intro v
    cases v with
    | inl L =>
      change Sum.inl (lineAction (g*h) L) = Sum.inl (lineAction g (lineAction h L))
      apply congrArg Sum.inl
      apply Subtype.ext
      exact ModThreeGoodAction.act_mul g h L.val
    | inr P =>
      change Sum.inr (planeAction (g*h) P) = Sum.inr (planeAction g (planeAction h P))
      apply congrArg Sum.inr
      apply Subtype.ext
      exact ModThreeGoodAction.act_mul g h P.val

instance vertexMulAction : MulAction K GoodVertex where
  smul g v := vertexRepresentation g v
  one_smul v := by
    change vertexRepresentation 1 v = v
    rw [map_one]
    rfl
  mul_smul g h v := by
    change vertexRepresentation (g*h) v = vertexRepresentation g (vertexRepresentation h v)
    rw [map_mul]
    rfl

@[simp] theorem smul_inl (g : K) (L : GoodLine) :
    g • (Sum.inl L : GoodVertex) = Sum.inl (lineAction g L) := rfl

@[simp] theorem smul_inr (g : K) (P : GoodPlane) :
    g • (Sum.inr P : GoodVertex) = Sum.inr (planeAction g P) := rfl

/-- Adjacency is preserved and reflected by the actual subgroup action. -/
theorem smul_adj_iff (g : K) (u v : GoodVertex) :
    graph.Adj (g • u) (g • v) ↔ graph.Adj u v :=
  (graphAction g).map_adj_iff

/-- Underlying rational subspace of a good vertex. -/
def subspace : GoodVertex → RationalSubspace
  | .inl L => L.val
  | .inr P => P.val

@[simp] theorem subspace_smul (g : K) (v : GoodVertex) :
    subspace (g • v) = ModThreeGoodAction.act g (subspace v) := by
  cases v <;> rfl

theorem subspace_good (v : GoodVertex) : ModThreeGoodAction.Good (subspace v) := by
  cases v with
  | inl L => exact L.property.2
  | inr P =>
    obtain ⟨L, hL⟩ := P.property.2
    exact L.property.2.mono hL

/-- The first coordinate line is a concrete vertex of the restricted graph. -/
def baseLine : GoodLine :=
  ⟨ModThreeGoodAction.firstLine, ModThreeGoodAction.firstLine_finrank,
    ModThreeGoodAction.firstLine_good⟩

def baseVertex : GoodVertex := .inl baseLine

/-- The actual restricted good graph is connected. -/
theorem connected : graph.Connected :=
  GoodIncidenceConnected.connected ModThreeGoodAction.Good ModThreeGoodAction.exists_good_line

/-- Concrete simple paths in the actual graph, with no graph-connectivity assumption. -/
def path (u v : GoodVertex) : graph.Path u v :=
  GoodIncidenceConnected.vertexPath ModThreeGoodAction.Good u v

theorem path_length_le_four (u v : GoodVertex) : (path u v).val.length ≤ 4 :=
  GoodIncidenceConnected.vertexPath_length_le_four ModThreeGoodAction.Good u v

/-- A chosen finite path from the concrete first coordinate line to every good vertex. -/
def pathFromBase (v : GoodVertex) : graph.Path baseVertex v := path baseVertex v

theorem pathFromBase_length_le_four (v : GoodVertex) : (pathFromBase v).val.length ≤ 4 :=
  path_length_le_four baseVertex v

end TernaryPoly.GoodBuilding
