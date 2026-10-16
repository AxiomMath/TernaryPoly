module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.Edge.CohomologyCocycles
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Edge.CohomologyMatrices

@[expose] public section


noncomputable section
namespace TernaryPoly.RelativeEdgeCohomologyGenerators
open RelativeStabilizerConsumer RelativeEdgeCohomologyMatrices RelativeEdgeCohomologyCocycles
open groupCohomology

lemma bb_eq_zero (A : Rep.{0} ℚ HBBGroup) (f : cocycles₁ A)
    (hs : f bbFirst = 0) (ht : f bbSecond = 0)
    (hr : ∀ k, f (bbRoot k 1) = 0) : f = 0 := by
  let Z := zeroSubgroup A f
  have hroot (k : Fin 3) (t : ℤ) : bbRoot k t ∈ Z := by
    rw [bbRoot_zpow]
    exact Z.zpow_mem (hr k) t
  have hsign (ε₀ ε₁ : ℤˣ) : bbSigns (ε₀,ε₁) ∈ Z := by
    rcases Int.units_eq_one_or ε₀ with rfl | rfl <;>
      rcases Int.units_eq_one_or ε₁ with rfl | rfl
    · exact (map_one bbSigns).symm ▸ Z.one_mem
    · exact ht
    · exact hs
    · have he : bbSigns (-1,-1) = bbFirst*bbSecond := by
        rw [← map_mul]; rfl
      rw [he]
      exact Z.mul_mem hs ht
  apply cocycles₁_ext
  intro g
  obtain ⟨ε₀,ε₁,a,b,c,rfl⟩ := bb_factor g
  exact Z.mul_mem (Z.mul_mem (Z.mul_mem (hroot 2 c) (hroot 1 b)) (hroot 0 a)) (hsign ε₀ ε₁)

lemma bg_eq_zero (A : Rep.{0} ℚ HBGGroup) (f : cocycles₁ A)
    (hs : f bgFirst = 0) (ht : f bgSecond = 0)
    (hr : ∀ k, f (bgRoot k 1) = 0) : f = 0 := by
  let Z := zeroSubgroup A f
  have hroot (k : Fin 3) (t : ℤ) : bgRoot k t ∈ Z := by
    rw [bgRoot_zpow]
    exact Z.zpow_mem (hr k) t
  have hsign (ε₀ ε₁ : ℤˣ) : bgSigns (ε₀,ε₁) ∈ Z := by
    rcases Int.units_eq_one_or ε₀ with rfl | rfl <;>
      rcases Int.units_eq_one_or ε₁ with rfl | rfl
    · exact (map_one bgSigns).symm ▸ Z.one_mem
    · exact ht
    · exact hs
    · have he : bgSigns (-1,-1) = bgFirst*bgSecond := by
        rw [← map_mul]; rfl
      rw [he]
      exact Z.mul_mem hs ht
  apply cocycles₁_ext
  intro g
  obtain ⟨ε₀,ε₁,a,b,k,rfl⟩ := bg_factor g
  exact Z.mul_mem (Z.mul_mem (Z.mul_mem (hroot 1 k) (hroot 2 a)) (hroot 0 b)) (hsign ε₀ ε₁)

end TernaryPoly.RelativeEdgeCohomologyGenerators
