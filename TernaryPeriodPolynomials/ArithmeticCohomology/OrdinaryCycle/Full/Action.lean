module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.IncidenceChains

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryFullAction
open ModThreeGoodAction OrdinaryIncidence

abbrev GL3 := Matrix.GeneralLinearGroup (Fin 3) ℚ

def integral : IntegralGL →* GL3 := Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ)

/-- The actual rational matrix acts by its linear equivalence on rational three-space. -/
def vectorAction : GL3 →* (Space ≃ₗ[ℚ] Space) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv ℚ Space).toMonoidHom.comp
    Matrix.GeneralLinearGroup.toLin.toMonoidHom

@[simp] theorem vectorAction_integral (g : IntegralGL) :
    vectorAction (integral g) = rationalRepresentation g := rfl

def subspaceAction (g : GL3) : RationalSubspace ≃o RationalSubspace :=
  Submodule.orderIsoMapComap (vectorAction g)

@[simp] theorem subspaceAction_apply (g : GL3) (L : RationalSubspace) :
    subspaceAction g L = L.map (vectorAction g).toLinearMap := rfl

@[simp] theorem subspaceAction_one (L : RationalSubspace) : subspaceAction 1 L = L := by
  simp [subspaceAction_apply]

theorem subspaceAction_mul (g h : GL3) (L : RationalSubspace) :
    subspaceAction (g*h) L = subspaceAction g (subspaceAction h L) := by
  simpa only [subspaceAction_apply,map_mul,LinearEquiv.coe_toLinearMap_mul,
    Module.End.mul_eq_comp] using
      (Submodule.map_comp (vectorAction h).toLinearMap (vectorAction g).toLinearMap L)

theorem subspaceAction_finrank (g : GL3) (L : RationalSubspace) :
    Module.finrank ℚ (subspaceAction g L) = Module.finrank ℚ L :=
  ((vectorAction g).submoduleMap L).finrank_eq.symm

/-- Every rational line and plane is transported by the actual rational matrix. -/
def lineAction (g : GL3) : Equiv.Perm Line :=
  GoodBuilding.lineEquiv (fun _ => True) (subspaceAction g)
    (subspaceAction_finrank g) (fun _ => Iff.rfl)
def planeAction (g : GL3) : Equiv.Perm Plane :=
  GoodBuilding.planeEquiv (fun _ => True) (subspaceAction g)
    (subspaceAction_finrank g) (fun _ => Iff.rfl)
def vertexAction (g : GL3) : Equiv.Perm Vertex :=
  Equiv.sumCongr (lineAction g) (planeAction g)

theorem incidence_action_iff (g : GL3) (L : Line) (P : Plane) :
    incidence (lineAction g L) (planeAction g P) ↔ incidence L P :=
  (subspaceAction g).lt_iff_lt

theorem vertexAction_one (v : Vertex) : vertexAction 1 v = v := by
  cases v with
  | inl L => exact congrArg Sum.inl (Subtype.ext (subspaceAction_one L.val))
  | inr P => exact congrArg Sum.inr (Subtype.ext (subspaceAction_one P.val))
theorem vertexAction_mul (g h : GL3) (v : Vertex) :
    vertexAction (g*h) v = vertexAction g (vertexAction h v) := by
  cases v with
  | inl L => exact congrArg Sum.inl (Subtype.ext (subspaceAction_mul g h L.val))
  | inr P => exact congrArg Sum.inr (Subtype.ext (subspaceAction_mul g h P.val))

@[simp] theorem lineAction_K (g : GoodBuilding.K) (L : Line) :
    lineAction (integral g.val) L = OrdinaryIncidence.lineAction g L := rfl
@[simp] theorem planeAction_K (g : GoodBuilding.K) (P : Plane) :
    planeAction (integral g.val) P = OrdinaryIncidence.planeAction g P := rfl

end TernaryPoly.OrdinaryFullAction
