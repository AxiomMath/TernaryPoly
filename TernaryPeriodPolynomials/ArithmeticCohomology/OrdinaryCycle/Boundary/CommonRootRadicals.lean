module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Boundary.CommonRootSupport
public import TernaryPeriodPolynomials.GroupCohomology.Radical.FirstCohomologyLattice

@[expose] public section

noncomputable section
namespace TernaryPoly.OrdinaryBoundaryCommonRoot
open ModThreeGoodAction RadicalCoinvariantAlgebra RadicalFirstCohomologyLattice
open RelativeStabilizerParameters RelativeStabilizerMatrices

 theorem root_in_plane (a : ℤ) : rootElement 1 a ∈ planeRadical := by
  refine ⟨Multiplicative.ofAdd (a,0), ?_⟩
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeHom, rootElement, planeMatrix, bbMatrix]

 theorem root_in_line (a : ℤ) : rootElement 1 a ∈ lineRadical := by
  refine ⟨Multiplicative.ofAdd (0,a), ?_⟩
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lineHom, rootElement, lineMatrix, bbMatrix]

/-- The common root is literally the intersection of the two existing actual integral radicals. -/
theorem commonRoot_eq_intersection : commonRoot = planeRadical ⊓ lineRadical := by
  apply le_antisymm
  · rintro g ⟨a,rfl⟩
    exact ⟨root_in_plane a, root_in_line a⟩
  · rintro g ⟨⟨p,hp⟩,⟨q,hq⟩⟩
    have hzero : p.toAdd.2 = 0 := by
      have he := congrArg (fun h : IntegralGL => h.val 1 2) (hp.trans hq.symm)
      simpa [planeHom,lineHom,planeMatrix,lineMatrix] using he
    refine ⟨p.toAdd.1, ?_⟩
    rw [← hp]
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [planeHom, rootElement, planeMatrix, bbMatrix, hzero]

end TernaryPoly.OrdinaryBoundaryCommonRoot
