module

public import TernaryPeriodPolynomials.Topology.Covering.CoefficientDual
public import TernaryPeriodPolynomials.Topology.SingularLocal.Homology.Degrees
public import TernaryPeriodPolynomials.Topology.SingularLocal.CoefficientComplex

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalDuality
open CategoryTheory FreeActionLinearization CoveringSingularOrbits
open SingularLocalCoefficient SingularLocalHomology
open scoped Classical

variable {G : Type} [Group G]

section
attribute [local instance] contragredientAction contragredientSMulComm

/-- The actual full contragredient representation: g acts on a functional by precomposition
with the inverse of its action on V. -/
def dualRepresentation (V : Rep.{0} ℚ G) : Rep.{0} ℚ G :=
  Rep.of (Representation.ofDistribMulAction ℚ G (Module.Dual ℚ V))
end

attribute [local instance] contragredientAction contragredientSMulComm

/-- The underlying linear functional of a contragredient vector. -/
def dualValue {V : Rep.{0} ℚ G} (φ : dualRepresentation V) : Module.Dual ℚ V := φ

@[simp] theorem dualRepresentation_apply (V : Rep.{0} ℚ G) (g : G)
    (φ : dualRepresentation V) (v : V) : dualValue ((dualRepresentation V).ρ g φ) v = dualValue φ (g⁻¹ • v) := rfl

variable {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) (V : Rep.{0} ℚ G)

/-- The full dual of finite geometric chains is the actual unrestricted product of dual-fiber
coefficients, hence precisely the geometric cochains with contragredient coefficients. -/
def degreeDuality (n : ℕ) :
    VertexCochain p hp (dualRepresentation V) n ≃ₗ[ℚ]
      Module.Dual ℚ (VertexChain p hp V n) :=
  (LinearEquiv.piCongrRight (fun σ : SingularSimplex B n =>
    dualCoefficientFiberEquiv (V := V) p hp (atVertex σ))) ≪≫ₗ DFinsupp.lsum ℚ

omit [ContinuousConstSMul G E] in
/-- Evaluation on one actual simplex is the literal fiber pairing. -/
theorem degreeDuality_single (n : ℕ) (φ : VertexCochain p hp (dualRepresentation V) n)
    (σ : SingularSimplex B n) (c : FiberCoefficient p hp V (atVertex σ)) :
    degreeDuality p hp V n φ (DFinsupp.single σ c) =
      dualCoefficientFiberEquiv (V := V) p hp (atVertex σ) (φ σ) c :=
  DFinsupp.lsum_single ℚ _ _ _

omit [ContinuousConstSMul G E] in
/-- At any lift of the first vertex, the chain/cochain pairing is ordinary functional evaluation. -/
theorem degreeDuality_single_at (n : ℕ) (φ : VertexCochain p hp (dualRepresentation V) n)
    (σ : SingularSimplex B n) (c : FiberCoefficient p hp V (atVertex σ))
    (e : Fiber p (atVertex σ)) :
    degreeDuality p hp V n φ (DFinsupp.single σ c) = dualValue ((φ σ).val e) (c.val e) := by
  rw [degreeDuality_single]
  exact dualCoefficientFiberEquiv_apply (V := V) p hp (φ σ) c e

omit [ContinuousConstSMul G E] in
/-- Moving a dual coefficient forward is adjoint to moving a chain coefficient backward. -/
theorem fiber_transport_adjoint {x y : B} (γ : Path.Homotopic.Quotient x y)
    (φ : FiberCoefficient p hp (dualRepresentation V) x) (c : FiberCoefficient p hp V y) :
    dualCoefficientFiberEquiv (V := V) p hp y (coefficientTransport p hp γ φ) c =
      dualCoefficientFiberEquiv (V := V) p hp x φ (coefficientTransport p hp γ.symm c) := by
  have h : coefficientTransport p hp γ (coefficientTransport p hp γ.symm c) = c := by
    rw [← coefficientTransport_trans]
    simp
  exact (congrArg (dualCoefficientFiberEquiv (V := V) p hp y (coefficientTransport p hp γ φ)) h.symm).trans
    (dualCoefficientFiberEquiv_transport (V := V) p hp γ φ _)

end TernaryPoly.SingularLocalDuality
