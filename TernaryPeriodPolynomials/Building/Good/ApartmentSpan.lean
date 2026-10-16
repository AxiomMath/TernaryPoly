module

public import TernaryPeriodPolynomials.Building.Good.ApartmentCycles
public import TernaryPeriodPolynomials.Building.IncidenceCycleGeneration

@[expose] public section


noncomputable section
namespace TernaryPoly.GoodApartmentCycles
open GoodIncidenceConnected BipartitePathChains

variable (Good : RationalSubspace → Prop) (B : Line Good)

/-- Close every incidence vertex to a fixed good line using at most three edges. -/
def apartmentPaths : PathFamily (Incidence Good) (.inl B) where
  path
    | .inl L => lineChain Good L B
    | .inr P => -flagChain Good P.property.2.choose P P.property.2.choose_spec +
        lineChain Good P.property.2.choose B
  boundary_path v := by
    cases v with
    | inl L => exact boundary_lineChain Good L B
    | inr P =>
      simp only [map_add,map_neg,boundary_flagChain,boundary_lineChain]
      abel

/-- Each closed single-edge generator is literally one rational apartment. -/
theorem apartmentPaths_single (e : Edge (Incidence Good)) :
    (apartmentPaths Good B).toCycles (Finsupp.single e 1) =
      apartmentCycle Good B e.val.1 e.val.2.property.2.choose := by
  apply Subtype.ext
  change (apartmentPaths Good B).projection (Finsupp.single e 1) = _
  rw [PathFamily.projection_single]
  change Finsupp.single e 1 +
    (-flagChain Good e.val.2.property.2.choose e.val.2 e.val.2.property.2.choose_spec +
      lineChain Good e.val.2.property.2.choose B) - lineChain Good e.val.1 B =
    apartmentChain Good B e.val.1 e.val.2.property.2.choose
  rw [apartmentChain,lineChain_of_common_plane Good e.val.1 _ e.val.2 e.property.le
    e.val.2.property.2.choose_spec,lineChain_reverse Good B e.val.1]
  have hf : Finsupp.single e (1 : ℚ) = flagChain Good e.val.1 e.val.2 e.property.le := rfl
  rw [hf]
  abel

include B

/-- Agreement on all actual apartments determines a functional on the whole cycle kernel. -/
theorem apartment_functional_ext {E : Type*} [AddCommGroup E] [Module ℚ E]
    (F H : Cycles Good →ₗ[ℚ] E)
    (h : ∀ L M N, F (apartmentCycle Good L M N) = H (apartmentCycle Good L M N)) : F = H := by
  apply (apartmentPaths Good B).functional_ext F H
  intro e
  rw [apartmentPaths_single]
  exact h _ _ _

/-- The span is formed from genuine apartments in the incidence boundary kernel. -/
def apartmentSpan : Submodule ℚ (Cycles Good) :=
  Submodule.span ℚ (Set.range (fun t : Line Good × Line Good × Line Good =>
    apartmentCycle Good t.1 t.2.1 t.2.2))

/-- Rational good apartments generate every cycle, with no unimodularity assumption. -/
theorem apartmentSpan_eq_top : apartmentSpan Good = ⊤ := by
  apply top_unique
  intro c hc
  clear hc
  obtain ⟨d,rfl⟩ := (apartmentPaths Good B).toCycles_surjective c
  induction d using Finsupp.induction_linear with
  | zero => simpa only [map_zero] using (apartmentSpan Good).zero_mem
  | add d e hd he => simpa only [map_add] using (apartmentSpan Good).add_mem hd he
  | single e a =>
    have ha : Finsupp.single e a = a • Finsupp.single e (1 : ℚ) := by simp
    rw [ha,map_smul,apartmentPaths_single]
    apply (apartmentSpan Good).smul_mem
    exact Submodule.subset_span ⟨(B,e.val.1,e.val.2.property.2.choose),rfl⟩

end TernaryPoly.GoodApartmentCycles
