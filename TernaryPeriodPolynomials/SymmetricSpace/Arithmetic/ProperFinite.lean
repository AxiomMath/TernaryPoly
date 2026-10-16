module

public import TernaryPeriodPolynomials.SymmetricSpace.Arithmetic.ProperTransport
public import TernaryPeriodPolynomials.SymmetricSpace.Arithmetic.ProperDiscrete
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceArithmeticProper
open Matrix SymmetricSpacePositive

/-- The literal integral action obtained from integer coefficient cast. -/
instance integralMulAction : MulAction IntegralGL Space := MulAction.compHom Space realIntegral

@[simp] theorem integral_smul (g : IntegralGL) (S : Space) :
    g • S = act (realIntegral g) S := rfl

/-- The actual compact-transporter set for the trace-normalized arithmetic action. -/
def transporter (C D : Set Space) : Set IntegralGL :=
  {g | ∃ S ∈ C, act (realIntegral g) S ∈ D}

/-- Actual compact transporters are finite. This proves the arithmetic finiteness conclusion
from positivity, determinant±1, compactness and finite integer-coordinate boxes. -/
theorem compact_transporter_finite (C D : Set Space) (hC : IsCompact C) (hD : IsCompact D) :
    (transporter C D).Finite := by
  obtain ⟨R,hR⟩ := compact_transporter_entry_bound C D hC hD
  exact (finite_integral_entry_bound R).subset (fun g hg => hR g hg)

/-- The actual stabilizer subgroup, without an assumed finiteness property. -/
def integralStabilizer (S : Space) : Subgroup IntegralGL := MulAction.stabilizer IntegralGL S

@[simp] theorem mem_integralStabilizer (S : Space) (g : IntegralGL) :
    g ∈ integralStabilizer S ↔ act (realIntegral g) S = S := Iff.rfl

/-- Every actual integral stabilizer is finite, as a singleton compact transporter. -/
theorem integralStabilizer_finite_set (S : Space) : (integralStabilizer S : Set IntegralGL).Finite := by
  refine (compact_transporter_finite {S} {S} isCompact_singleton isCompact_singleton).subset ?_
  intro g hg
  exact ⟨S,rfl,hg⟩

instance integralStabilizer_finite (S : Space) : Finite (integralStabilizer S) :=
  (integralStabilizer_finite_set S).to_subtype

/-- An integral matrix fixing an actual positive trace-one form has finite order. -/
theorem integral_fixed_isOfFinOrder (g : IntegralGL) (S : Space)
    (h : act (realIntegral g) S = S) : IsOfFinOrder g :=
  (integralStabilizer S).subtype.isOfFinOrder
    (isOfFinOrder_of_finite (⟨g,h⟩ : integralStabilizer S))

end TernaryPoly.SymmetricSpaceArithmeticProper
