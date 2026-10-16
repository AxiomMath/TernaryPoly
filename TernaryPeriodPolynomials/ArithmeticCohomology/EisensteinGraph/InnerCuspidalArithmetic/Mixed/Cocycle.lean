module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.LeviCrossedAction

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous Adelic

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

variable {GroupType Radical Levi Value : Type} [Group GroupType] [Group Radical] [Group Levi]
  [AddCommGroup Value] [Module ℂ Value]

def inhomogeneousTwoCycles (representation : Representation ℂ GroupType Value) :
    Submodule ℂ (GroupType → GroupType → Value) where
  carrier := {cochain | ∀ first second third,
    representation first (cochain second third) - cochain (first * second) third +
      cochain first (second * third) - cochain first second = 0}
  zero_mem' := by simp
  add_mem' := by
    intro first second firstCycle secondCycle elementOne elementTwo elementThree
    have firstIdentity := firstCycle elementOne elementTwo elementThree
    have secondIdentity := secondCycle elementOne elementTwo elementThree
    simp only [Pi.add_apply, map_add]
    calc
      _ = (representation elementOne (first elementTwo elementThree) -
          first (elementOne * elementTwo) elementThree + first elementOne (elementTwo * elementThree) -
          first elementOne elementTwo) +
        (representation elementOne (second elementTwo elementThree) -
          second (elementOne * elementTwo) elementThree + second elementOne (elementTwo * elementThree) -
          second elementOne elementTwo) := by abel
      _ = 0 := by rw [firstIdentity, secondIdentity, add_zero]
  smul_mem' := by
    intro scalar cochain cycle first second third
    change representation first (scalar • cochain second third) -
      scalar • cochain (first * second) third + scalar • cochain first (second * third) -
        scalar • cochain first second = 0
    rw [map_smul, ← smul_sub, ← smul_add, ← smul_sub, cycle, smul_zero]

variable (action : Levi →* MulAut Radical)
  (representation : Representation ℂ (SemidirectProduct Radical Levi action) Value)

def radicalZeroTwoCycles :
    Submodule ℂ (inhomogeneousTwoCycles representation) where
  carrier := {cochain | ∀ first second : Radical,
    cochain.val (SemidirectProduct.inl first) (SemidirectProduct.inl second) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro first second firstZero secondZero elementOne elementTwo
    change first.val _ _ + second.val _ _ = 0
    rw [firstZero, secondZero, add_zero]
  smul_mem' := by
    intro scalar cochain zero first second
    change scalar • cochain.val _ _ = 0
    rw [zero, smul_zero]

def mixedCrossedCochain (cycle : radicalZeroTwoCycles action representation) (element : Levi)
    (radical : Radical) : Value :=
  cycle.val.val (SemidirectProduct.inr element)
      (SemidirectProduct.inl (action element⁻¹ radical)) -
    cycle.val.val (SemidirectProduct.inl radical) (SemidirectProduct.inr element)

theorem mixedCrossedCochain_cocycle (cycle : radicalZeroTwoCycles action representation)
    (element : Levi) (first second : Radical) :
    mixedCrossedCochain action representation cycle element (first * second) =
      mixedCrossedCochain action representation cycle element first +
        representation (SemidirectProduct.inl first)
          (mixedCrossedCochain action representation cycle element second) := by
  have firstIdentity := cycle.val.property (SemidirectProduct.inr element)
    (SemidirectProduct.inl (action element⁻¹ first))
    (SemidirectProduct.inl (action element⁻¹ second))
  have secondIdentity := cycle.val.property (SemidirectProduct.inl first)
    (SemidirectProduct.inr element) (SemidirectProduct.inl (action element⁻¹ second))
  have thirdIdentity := cycle.val.property (SemidirectProduct.inl first)
    (SemidirectProduct.inl second) (SemidirectProduct.inr element)
  rw [cycle.property, map_zero, zero_sub] at firstIdentity
  rw [cycle.property, sub_zero] at thirdIdentity
  rw [semidirect_conjugation_intertwines] at firstIdentity secondIdentity
  rw [← map_mul] at firstIdentity thirdIdentity
  dsimp only [mixedCrossedCochain]
  rw [map_mul, map_sub]
  have combined := congrArg₂ (fun first second : Value => first - second)
    firstIdentity secondIdentity
  have combined := congrArg₂ (fun first second : Value => first + second)
    combined thirdIdentity
  apply sub_eq_zero.mp
  convert combined using 1 <;> abel

def mixedCrossedMap (element : Levi) :
    radicalZeroTwoCycles action representation →ₗ[ℂ]
      crossedCocycles (representation.comp SemidirectProduct.inl) where
  toFun cycle := ⟨mixedCrossedCochain action representation cycle element,
    mixedCrossedCochain_cocycle action representation cycle element⟩
  map_add' first second := by
    apply Subtype.ext
    funext radical
    change (first.val.val _ _ + second.val.val _ _) -
        (first.val.val _ _ + second.val.val _ _) =
      (first.val.val _ _ - first.val.val _ _) + (second.val.val _ _ - second.val.val _ _)
    abel
  map_smul' scalar cycle := by
    apply Subtype.ext
    funext radical
    exact (smul_sub scalar _ _).symm

theorem mixedCrossedMap_mul (cycle : radicalZeroTwoCycles action representation)
    (first second : Levi) :
    mixedCrossedMap action representation (first * second) cycle =
      mixedCrossedMap action representation first cycle +
        leviCrossedAction action representation first
          (mixedCrossedMap action representation second cycle) +
        crossedBoundary (representation.comp SemidirectProduct.inl)
          (cycle.val.val (SemidirectProduct.inr first) (SemidirectProduct.inr second)) := by
  apply Subtype.ext
  funext radical
  have firstIdentity := cycle.val.property (SemidirectProduct.inr first)
    (SemidirectProduct.inr second) (SemidirectProduct.inl (action (first * second)⁻¹ radical))
  have secondIdentity := cycle.val.property (SemidirectProduct.inl radical)
    (SemidirectProduct.inr first) (SemidirectProduct.inr second)
  have thirdIdentity := cycle.val.property (SemidirectProduct.inr first)
    (SemidirectProduct.inl (action first⁻¹ radical)) (SemidirectProduct.inr second)
  have conjugated :
      (SemidirectProduct.inr second : SemidirectProduct Radical Levi action) *
          SemidirectProduct.inl (action (first * second)⁻¹ radical) =
        SemidirectProduct.inl (action first⁻¹ radical) * SemidirectProduct.inr second := by
    simpa only [mul_inv_rev, map_mul, MulAut.mul_apply] using
      semidirect_conjugation_intertwines action second (action first⁻¹ radical)
  rw [← map_mul, conjugated] at firstIdentity
  rw [← map_mul] at secondIdentity
  rw [semidirect_conjugation_intertwines] at thirdIdentity
  change mixedCrossedCochain action representation cycle (first * second) radical =
    mixedCrossedCochain action representation cycle first radical +
      representation (SemidirectProduct.inr first)
        (mixedCrossedCochain action representation cycle second (action first⁻¹ radical)) +
      (representation (SemidirectProduct.inl radical)
        (cycle.val.val (SemidirectProduct.inr first) (SemidirectProduct.inr second)) -
      cycle.val.val (SemidirectProduct.inr first) (SemidirectProduct.inr second))
  dsimp only [mixedCrossedCochain]
  rw [map_sub]
  simp only [mul_inv_rev, map_mul, MulAut.mul_apply]
  simp only [mul_inv_rev, map_mul, MulAut.mul_apply] at firstIdentity secondIdentity thirdIdentity
  have combined := congrArg₂ (fun first second : Value => -first - second)
    firstIdentity secondIdentity
  have combined := congrArg₂ (fun first second : Value => first + second)
    combined thirdIdentity
  apply sub_eq_zero.mp
  convert combined using 1 <;> abel

def mixedH1CocycleMap :
    radicalZeroTwoCycles action representation →ₗ[ℂ]
      crossedCocycles (leviCrossedH1Representation action representation) where
  toFun cycle := ⟨fun element =>
    (crossedBoundaries (representation.comp SemidirectProduct.inl)).mkQ
      (mixedCrossedMap action representation element cycle), by
    intro first second
    change (crossedBoundaries (representation.comp SemidirectProduct.inl)).mkQ
        (mixedCrossedMap action representation (first * second) cycle) =
      (crossedBoundaries (representation.comp SemidirectProduct.inl)).mkQ
          (mixedCrossedMap action representation first cycle) +
        leviCrossedH1Representation action representation first
          ((crossedBoundaries (representation.comp SemidirectProduct.inl)).mkQ
            (mixedCrossedMap action representation second cycle))
    rw [mixedCrossedMap_mul, map_add, map_add,
      ← leviCrossedH1Representation_mk]
    have boundaryZero :
        (crossedBoundaries (representation.comp SemidirectProduct.inl)).mkQ
          (crossedBoundary (representation.comp SemidirectProduct.inl)
            (cycle.val.val (SemidirectProduct.inr first) (SemidirectProduct.inr second))) = 0 := by
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨_, rfl⟩
    rw [boundaryZero, add_zero]⟩
  map_add' first second := by
    apply Subtype.ext
    funext element
    change (crossedBoundaries (representation.comp SemidirectProduct.inl)).mkQ
        (mixedCrossedMap action representation element (first + second)) =
      (crossedBoundaries (representation.comp SemidirectProduct.inl)).mkQ
          (mixedCrossedMap action representation element first) +
        (crossedBoundaries (representation.comp SemidirectProduct.inl)).mkQ
          (mixedCrossedMap action representation element second)
    rw [map_add, map_add]
  map_smul' scalar cycle := by
    apply Subtype.ext
    funext element
    change (crossedBoundaries (representation.comp SemidirectProduct.inl)).mkQ
        (mixedCrossedMap action representation element (scalar • cycle)) =
      scalar • (crossedBoundaries (representation.comp SemidirectProduct.inl)).mkQ
        (mixedCrossedMap action representation element cycle)
    rw [map_smul, map_smul]

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
