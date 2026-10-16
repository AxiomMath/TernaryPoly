module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Parabolic.GroupsQuotient

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryParabolicGroups
open Matrix ModThreeGoodAction RelativeStabilizerParameters RelativeStabilizerMatrices
open RadicalFirstCohomologyLattice

/-- The ambient multiplication map is injective and has exactly the full plane parabolic as image. -/
theorem planeLift_injective : Function.Injective planeLift := by
  intro g h he
  exact planeToParabolic_injective (Subtype.ext he)

theorem planeLift_range : planeLift.range = P := by
  ext g
  constructor
  · rintro ⟨x,rfl⟩
    exact planeLift_mem x
  · intro hg
    obtain ⟨x,hx⟩ := planeToParabolic_surjective ⟨g,hg⟩
    exact ⟨x,congrArg Subtype.val hx⟩

theorem lineLift_injective : Function.Injective lineLift := by
  intro g h he
  exact lineToParabolic_injective (Subtype.ext he)

theorem lineLift_range : lineLift.range = Q := by
  ext g
  constructor
  · rintro ⟨x,rfl⟩
    exact lineLift_mem x
  · intro hg
    obtain ⟨x,hx⟩ := lineToParabolic_surjective ⟨g,hg⟩
    exact ⟨x,congrArg Subtype.val hx⟩

/-- The abstractly packaged Levi quotient literally reads off the top block and last scalar. -/
theorem planeProjection_coordinates (g : P) :
    (planeProjection g).1.val = topBlock g.val ∧
      (planeProjection g).2.val = g.val.val 2 2 := by
  obtain ⟨x,rfl⟩ := planeEquiv.surjective g
  rw [planeProjection_equiv]
  obtain ⟨a,ha⟩ := x.left.property
  have hv : (planeEquiv x).val =
      planeElement x.right.1 (x.right.2.val • ![a.toAdd.1,a.toAdd.2]) x.right.2 := by
    rw [planeEquiv_val,←ha]
    exact plane_radical_levi _ _ _
  rw [hv]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [topBlock,planeMatrix]
  · simp [planeMatrix]

/-- The full line quotient literally reads off the first scalar and lower GL₂ block. -/
theorem lineProjection_coordinates (g : Q) :
    (lineProjection g).1.val = g.val.val 0 0 ∧
      (lineProjection g).2.val = bottomBlock g.val := by
  obtain ⟨x,rfl⟩ := lineEquiv.surjective g
  rw [lineProjection_equiv]
  obtain ⟨a,ha⟩ := x.left.property
  have hv : (lineEquiv x).val =
      lineElement x.right.1 (Matrix.vecMul ![a.toAdd.1,a.toAdd.2] x.right.2.val) x.right.2 := by
    rw [lineEquiv_val,←ha]
    exact RelativeVertexCohomology.line_radical_levi _ _ _
  rw [hv]
  constructor
  · simp [lineMatrix]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [bottomBlock,lineMatrix]

@[simp] theorem planeQuotientEquiv_mk (g : P) :
    planeQuotientEquiv (QuotientGroup.mk g) = planeProjection g := rfl

@[simp] theorem lineQuotientEquiv_mk (g : Q) :
    lineQuotientEquiv (QuotientGroup.mk g) = lineProjection g := rfl

end TernaryPoly.OrdinaryParabolicGroups
