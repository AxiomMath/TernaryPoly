module

public import TernaryPeriodPolynomials.SymmetricSpace.Rational.GluingInterior
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Algebra.Group.TransferInstance

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceRationalGluing
open SymmetricSpacePositive SymmetricSpaceFlagCoordinates SymmetricSpaceRationalAction
open SymmetricSpaceRationalCharts Topology

/-- Simultaneous left translation of rational frames preserves every actual overlap. -/
theorem overlap_left (a g h : RationalGL) : overlap (a*g) (a*h)=overlap g h := by
  simp only [overlap,changeMatrix_left]

theorem transition_congr {r s : RealGL} (h : r=s) (p : domain r) (q : domain s)
    (hp : p.val=q.val) : (transition r p).val=(transition s q).val := by
  subst s
  exact congrArg (fun x => (transition r x).val) (Subtype.ext hp)

/-- Chart equality is invariant under literal left multiplication of rational indices. -/
theorem chart_eq_left (a g h : RationalGL) (p q : Corner)
    (hpq : chart g p=chart h q) : chart (a*g) p=chart (a*h) q := by
  obtain ⟨hp,he⟩ := (chart_eq_iff g h p q).mp hpq
  have hp' : p∈overlap (a*g) (a*h) := (overlap_left a g h).symm ▸ hp
  apply (chart_eq_iff (a*g) (a*h) p q).mpr
  refine ⟨hp',?_⟩
  exact (transition_congr (changeMatrix_left a g h) ⟨p,hp'⟩ ⟨p,hp⟩ rfl).trans he

/-- A chart representative, used only to define the quotient action. -/
def representative (x : Glued) : Σ _ : RationalGL,Corner :=
  ⟨(chart_jointly_surjective x).choose,(chart_jointly_surjective x).choose_spec.choose⟩

theorem representative_spec (x : Glued) : chart (representative x).1 (representative x).2=x :=
  (chart_jointly_surjective x).choose_spec.choose_spec

/-- Rational left multiplication on the actual glued space. -/
def leftAction (a : RationalGL) (x : Glued) : Glued :=
  chart (a*(representative x).1) (representative x).2

@[simp] theorem leftAction_chart (a g : RationalGL) (p : Corner) :
    leftAction a (chart g p)=chart (a*g) p :=
  chart_eq_left a _ g _ p (representative_spec (chart g p))

@[simp] theorem leftAction_one (x : Glued) : leftAction 1 x=x := by
  obtain ⟨g,p,rfl⟩ := chart_jointly_surjective x
  simp

theorem leftAction_mul (a b : RationalGL) (x : Glued) :
    leftAction (a*b) x=leftAction a (leftAction b x) := by
  obtain ⟨g,p,rfl⟩ := chart_jointly_surjective x
  simp [mul_assoc]

/-- Continuity out of the gluing can be checked on its actual open charts. -/
theorem continuous_of_chart {X : Type*} [TopologicalSpace X] (f : Glued → X)
    (hf : ∀ g,Continuous (f ∘ chart g)) : Continuous f := by
  rw [continuous_def]
  intro U hU
  exact (glueData.isOpen_iff _).mpr (fun g => (hf g).isOpen_preimage U hU)

theorem continuous_leftAction (a : RationalGL) : Continuous (leftAction a) := by
  apply continuous_of_chart
  intro g
  have he : leftAction a ∘ chart g=chart (a*g) := funext (leftAction_chart a g)
  rw [he]
  exact continuous_chart _

/-- Every rational matrix acts by a genuine homeomorphism. -/
def leftHomeomorph (a : RationalGL) : Glued ≃ₜ Glued where
  toFun := leftAction a
  invFun := leftAction a⁻¹
  left_inv x := by rw [←leftAction_mul,inv_mul_cancel,leftAction_one]
  right_inv x := by rw [←leftAction_mul,mul_inv_cancel,leftAction_one]
  continuous_toFun := continuous_leftAction a
  continuous_invFun := continuous_leftAction a⁻¹

/-- The glued action agrees exactly with the original normalized real matrix action. -/
theorem leftAction_embedding (a : RationalGL) (S : Space) :
    leftAction a (embedding S)=embedding (act (realRational a) S) := by
  rw [embedding,leftAction_chart,←chartEmbedding_left_action a 1 S,chart_embedding]

/-- The rational action is a homomorphism into actual self-homeomorphisms. -/
def leftHomeomorphHom : RationalGL →* (Glued ≃ₜ Glued) where
  toFun := leftHomeomorph
  map_one' := by ext x; exact leftAction_one x
  map_mul' a b := by ext x; exact leftAction_mul a b x

instance rationalMulAction : MulAction RationalGL Glued where
  smul := leftAction
  one_smul := leftAction_one
  mul_smul := leftAction_mul

instance rationalContinuousConstSMul : ContinuousConstSMul RationalGL Glued where
  continuous_const_smul := continuous_leftAction

/-- Rational matrices equipped with the discrete topology appropriate to rational boundary flags. -/
abbrev DiscreteRationalGL := WithDiscreteTopology RationalGL

instance discreteRationalGroup : Group DiscreteRationalGL :=
  (WithTopology.equiv RationalGL ⊥).group

def discreteRationalEquiv : DiscreteRationalGL ≃* RationalGL :=
  (WithTopology.equiv RationalGL ⊥).mulEquiv

instance discreteRationalMulAction : MulAction DiscreteRationalGL Glued where
  smul a x := leftAction (discreteRationalEquiv a) x
  one_smul x := by change leftAction (discreteRationalEquiv 1) x=x; rw [map_one,leftAction_one]
  mul_smul a b x := by
    change leftAction (discreteRationalEquiv (a*b)) x=_
    rw [map_mul,leftAction_mul]
    rfl

/-- The rational boundary action is jointly continuous for the discrete rational group. -/
instance discreteRationalContinuousSMul : ContinuousSMul DiscreteRationalGL Glued where
  continuous_smul := continuous_prod_of_discrete_left.mpr fun a =>
    continuous_leftAction (discreteRationalEquiv a)

/-- Integral matrices act through their literal scalar extension to rational matrices. -/
def integralRational : Matrix.GeneralLinearGroup (Fin 3) ℤ →* RationalGL :=
  Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ)

def integralAction (a : Matrix.GeneralLinearGroup (Fin 3) ℤ) : Glued → Glued :=
  leftAction (integralRational a)

instance integralMulAction : MulAction (Matrix.GeneralLinearGroup (Fin 3) ℤ) Glued where
  smul := integralAction
  one_smul x := by change leftAction (integralRational 1) x=x; rw [map_one,leftAction_one]
  mul_smul a b x := by change leftAction (integralRational (a*b)) x=_; rw [map_mul,leftAction_mul]; rfl

/-- The arithmetic action is jointly continuous in the actual discrete integral matrix topology. -/
instance integralContinuousSMul : ContinuousSMul (Matrix.GeneralLinearGroup (Fin 3) ℤ) Glued where
  continuous_smul := continuous_prod_of_discrete_left.mpr fun a =>
    continuous_leftAction (integralRational a)

/-- Arithmetic equivariance uses exactly the existing real integral matrix action. -/
theorem integralAction_embedding (a : Matrix.GeneralLinearGroup (Fin 3) ℤ) (S : Space) :
    integralAction a (embedding S)=
      embedding (act (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) a) S) := by
  rw [integralAction,leftAction_embedding]
  exact congrArg (fun r => embedding (act r S)) (realRational_integral a)

@[simp] theorem integralAction_chart (a : Matrix.GeneralLinearGroup (Fin 3) ℤ)
    (g : RationalGL) (p : Corner) : integralAction a (chart g p)=chart (integralRational a*g) p :=
  leftAction_chart _ g p

end TernaryPoly.SymmetricSpaceRationalGluing
