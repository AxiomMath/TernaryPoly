module

public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.LowDegree.OneInflation
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryCochainNormalization

@[expose] public section


noncomputable section
namespace TernaryPoly.LowDegreeHochschildSerre
open CategoryTheory groupCohomology BoundaryCochainNormalization
variable {N Q H : Type} [Group N] [Group Q] [Group H]

/-- Transport the constructed degree-one normal form through an actual semidirect decomposition.
This supplies normalized face cocycles without replacing the group by an abstract quotient model. -/
theorem exists_normalized_along_equiv (φ : Q →* MulAut N) (e : G φ ≃* H) (A : Rep ℚ H)
    (hvan : ∀ v : groupCohomology (radicalRep φ (Rep.res e.toMonoidHom A)) 1,
      (∀ q,(cohomologyRep φ (Rep.res e.toMonoidHom A) 1).ρ q v=v) → v=0)
    (c : cocycles₁ A) :
    ∃ u : A,
      (∀ n,normalize A c u (e (nIn φ n))=0) ∧
      ∀ h,normalize A c u h ∈ (radicalRep φ (Rep.res e.toMonoidHom A)).ρ.invariants := by
  let cPull := BoundaryCochainNormalization.restrict A e.toMonoidHom c
  obtain ⟨u,b,hb⟩ := exists_inflated_one φ (Rep.res e.toMonoidHom A) hvan cPull
  have hv (h : H) : normalize A c u h=(b (e.symm h).right : A) := by
    have hh := hb (e.symm h)
    change c (e (e.symm h))=A.ρ (e (e.symm h)) u-u+(b (e.symm h).right : A) at hh
    rw [e.apply_symm_apply] at hh
    rw [BoundaryCochainNormalization.normalize_apply,hh]
    abel
  refine ⟨u,?_,?_⟩
  · intro n
    rw [hv,e.symm_apply_apply]
    change (b 1 : A)=0
    rw [cocycles₁_map_one]
    rfl
  · intro h
    rw [hv]
    exact (b (e.symm h).right).property

end TernaryPoly.LowDegreeHochschildSerre
