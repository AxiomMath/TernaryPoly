module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.Cocycle
public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.BoundaryClasses

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryActualEvaluation
open CategoryTheory Limits HomologicalComplex SingularLocalCap.BoundaryClasses

variable {s : ComplexShape ℕ}

/-- The scalar family of an actual abstract cycle remains a cycle. -/
theorem abstractCycleFamily_condition (K : HomologicalComplex (ModuleCat.{0} ℚ) s)
    (i j : ℕ) (x : K.cycles i) : elementMap (K.iCycles i x) ≫ K.d i j = 0 := by
  rw [← elementMap_comp, Category.assoc, iCycles_d, comp_zero]

/-- Lifting the family of a cycle's literal values returns the original cycle family. -/
theorem abstractCycleFamily_lift (K : HomologicalComplex (ModuleCat.{0} ℚ) s)
    (i j : ℕ) (hij : s.next i = j) (x : K.cycles i) :
    K.liftCycles (elementMap (K.iCycles i x)) j hij (abstractCycleFamily_condition K i j x) =
      elementMap x := by
  apply (cancel_mono (K.iCycles i)).mp
  rw [liftCycles_i, elementMap_comp]

/-- The genuine LES connecting map uses the positive differential of an actual lifted
representative, stated directly on the canonical abstract cycle objects. -/
theorem connecting_abstract_cycles
    (S : ShortComplex (HomologicalComplex (ModuleCat.{0} ℚ) s)) (hS : S.ShortExact)
    (i j : ℕ) (hij : s.Rel i j) (x₃ : S.X₃.cycles i) (x₂ : S.X₂.X i)
    (x₁ : S.X₁.cycles j)
    (h₂ : S.g.f i x₂ = S.X₃.iCycles i x₃)
    (h₁ : S.f.f j (S.X₁.iCycles j x₁) = S.X₂.d i j x₂) :
    hS.δ i j hij (S.X₃.homologyπ i x₃) = S.X₁.homologyπ j x₁ := by
  have h₂' : elementMap x₂ ≫ S.g.f i = elementMap (S.X₃.iCycles i x₃) :=
    (elementMap_comp _ _).trans (congrArg elementMap h₂)
  have h₁' : elementMap (S.X₁.iCycles j x₁) ≫ S.f.f j = elementMap x₂ ≫ S.X₂.d i j :=
    (elementMap_comp _ _).trans ((congrArg elementMap h₁).trans (elementMap_comp _ _).symm)
  have he := hS.δ_eq i j hij (elementMap (S.X₃.iCycles i x₃))
    (abstractCycleFamily_condition S.X₃ i j x₃) (elementMap x₂) h₂'
    (elementMap (S.X₁.iCycles j x₁)) h₁' (s.next j) rfl
  have hleft := abstractCycleFamily_lift S.X₃ i j (s.next_eq' hij) x₃
  have hright : S.X₁.liftCycles (elementMap (S.X₁.iCycles j x₁)) (s.next j) rfl
      (by exact abstractCycleFamily_condition S.X₁ j (s.next j) x₁) = elementMap x₁ :=
    abstractCycleFamily_lift S.X₁ j (s.next j) rfl x₁
  rw [hleft, hright, ← Category.assoc, elementMap_comp, elementMap_comp, elementMap_comp] at he
  have h := congrArg (fun f => f (1 : ℚ)) he
  change (1 : ℚ) • (hS.δ i j hij (S.X₃.homologyπ i x₃)) =
    (1 : ℚ) • (S.X₁.homologyπ j x₁) at h
  simpa only [one_smul] using h

end TernaryPoly.OrdinaryBoundaryActualEvaluation
