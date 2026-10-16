module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Boundary.ConeMVFaces

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryCone
open CategoryTheory groupCohomology
variable {G : Type} [Group G] (A : Rep ℚ G) (P Q : Subgroup G)

/-- Degree-zero cone cocycles are a common value fixed by both full faces. -/
theorem d0_eq_zero_iff (v : C0 A) : d0 A P Q v = 0 ↔
    v.1 ∈ InvariantsP A P ∧ v.2 ∈ InvariantsQ A Q ∧ v.1 = v.2 := by
  change (d₀₁ (faceP A P) v.1,d₀₁ (faceQ A Q) v.2,v.1-v.2) = (0,0,0) ↔ _
  simp only [Prod.mk.injEq,sub_eq_zero]
  have hp : d₀₁ (faceP A P) v.1 = 0 ↔ v.1 ∈ InvariantsP A P := by
    change v.1 ∈ LinearMap.ker (d₀₁ (faceP A P)).hom ↔ _
    rw [d₀₁_ker_eq_invariants]
  have hq : d₀₁ (faceQ A Q) v.2 = 0 ↔ v.2 ∈ InvariantsQ A Q := by
    change v.2 ∈ LinearMap.ker (d₀₁ (faceQ A Q)).hom ↔ _
    rw [d₀₁_ker_eq_invariants]
  exact and_congr hp (and_congr hq Iff.rfl)

abbrev CommonInvariants := InvariantsP A P ⊓ InvariantsQ A Q

/-- The first map in MV sends a common invariant to its two identical face values. -/
def invariantDiagonal : CommonInvariants A P Q →ₗ[ℚ] (InvariantsP A P × InvariantsQ A Q) where
  toFun v := (⟨v.val,v.property.1⟩,⟨v.val,v.property.2⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem invariantDiagonal_injective : Function.Injective (invariantDiagonal A P Q) := by
  intro v w h
  apply Subtype.ext
  exact congrArg (fun x => x.1.val) h

/-- Exactness at the pair of actual degree-zero face groups. -/
theorem range_invariantDiagonal_eq_ker_invariantDifference :
    LinearMap.range (invariantDiagonal A P Q) = LinearMap.ker (invariantDifference A P Q) := by
  ext v
  constructor
  · rintro ⟨w,rfl⟩
    apply Subtype.ext
    exact sub_self w.val
  · intro hv
    have hval : v.1.val-v.2.val = 0 := congrArg Subtype.val hv
    have heq := sub_eq_zero.mp hval
    refine ⟨⟨v.1.val,⟨v.1.property,?_⟩⟩,?_⟩
    · rw [heq]
      exact v.2.property
    · apply Prod.ext
      · rfl
      · exact Subtype.ext heq

/-- Equality of pure corner classes is exactly the quotient by differences of face invariants. -/
theorem connecting_eq_connecting_iff (u v : InvariantsB A P Q) :
    connecting A P Q u = connecting A P Q v ↔
      u-v ∈ LinearMap.range (invariantDifference A P Q) := by
  rw [← sub_eq_zero,← map_sub,connecting_eq_zero_iff]
  rfl

end TernaryPoly.OrdinaryBoundaryCone
