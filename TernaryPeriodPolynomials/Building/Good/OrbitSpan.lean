module

public import TernaryPeriodPolynomials.Building.Good.UnimodularSpan
public import TernaryPeriodPolynomials.Building.Good.UnimodularOrbit

@[expose] public section


noncomputable section
namespace TernaryPoly.GoodOrbitSpan
open GoodBuilding GoodChainComplex GoodUnimodularSpan GoodUnimodularOrbit

/-- The actual K-orbit span of the reference coordinate apartment. -/
def orbitSpan : Submodule ℚ GoodChainComplex.Cycles :=
  Submodule.span ℚ (Set.range (fun g : K => complex.cyclesAction g referenceApartment))

/-- The reference apartment generates the whole genuine cycle module as a K-module. -/
theorem orbitSpan_eq_top : orbitSpan = ⊤ := by
  have h : unimodularSpan ≤ orbitSpan := by
    apply Submodule.span_le.mpr
    rintro c ⟨M,rfl⟩
    obtain ⟨g,_,hg⟩ := exists_frameApartment_translate M.val M.property.1 M.property.2
    change (GoodIntegralFrames.frameApartment M.val M.property.1 : GoodChainComplex.Cycles) ∈ orbitSpan
    exact hg.symm ▸ (show complex.cyclesAction g referenceApartment ∈ orbitSpan from
      Submodule.subset_span ⟨g,rfl⟩)
  rw [unimodularSpan_eq_top] at h
  exact top_unique h

/-- Linear functionals are determined by values on the genuine K-orbit. -/
theorem orbit_ext {E : Type*} [AddCommGroup E] [Module ℚ E]
    (F H : GoodChainComplex.Cycles →ₗ[ℚ] E)
    (h : ∀ g : K, F (complex.cyclesAction g referenceApartment) =
      H (complex.cyclesAction g referenceApartment)) : F = H := by
  apply LinearMap.ext
  intro c
  have hc : c ∈ orbitSpan := by rw [orbitSpan_eq_top]; trivial
  induction hc using Submodule.span_induction with
  | mem c hc => obtain ⟨g,rfl⟩ := hc; exact h g
  | zero => simp only [map_zero]
  | add c d _ _ hc hd => simp only [map_add,hc,hd]
  | smul a c _ hc => simp only [map_smul,hc]

/-- An equivariant polynomial cycle map is determined by its one reference value. -/
theorem polynomialCycleMap_ext {n : ℕ} {e : ℤ}
    (F H : PolynomialCycleMap n e) (h : F.map referenceApartment = H.map referenceApartment) :
    F = H := by
  have hm : F.map = H.map := by
    apply orbit_ext
    intro g
    rw [F.equivariant,H.equivariant,h]
  cases F
  cases H
  cases hm
  rfl

end TernaryPoly.GoodOrbitSpan
