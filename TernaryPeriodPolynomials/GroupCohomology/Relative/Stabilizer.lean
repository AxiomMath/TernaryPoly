module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.Stabilizer.Conjugacy
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Stabilizer.Parameters

@[expose] public section

noncomputable section
namespace TernaryPoly.RelativeStabilizerConsumer
open ModThreeGoodAction RelativeStabilizerCoordinates RelativeStabilizerConjugacy
open RelativeStabilizerMatrices RelativeStabilizerParameters

/-- Stabilizers of actual rational subspaces as actual subgroups. -/
def stabilizer (L : RationalSubspace) : Subgroup IntegralGL where
  carrier := {g | Stabilizes g L}
  one_mem' := by simp [Stabilizes]
  mul_mem' := by
    intro g h hg hh
    change L.map (rationalRepresentation (g*h)).toLinearMap = L
    rw [map_mul,LinearEquiv.coe_toLinearMap_mul,Module.End.mul_eq_comp,Submodule.map_comp]
    rw [show L.map (rationalRepresentation h).toLinearMap = L from hh]
    exact hg
  inv_mem' := by
    intro g hg
    have he := congrArg (fun M : RationalSubspace => M.map (rationalRepresentation g⁻¹).toLinearMap) hg
    change (L.map (rationalRepresentation g).toLinearMap).map (rationalRepresentation g⁻¹).toLinearMap = _ at he
    rw [← Submodule.map_comp,← Module.End.mul_eq_comp,← LinearEquiv.coe_toLinearMap_mul,← map_mul,inv_mul_cancel,map_one] at he
    simpa [Stabilizes] using he.symm

def HPGroup : Subgroup IntegralGL := K3 ⊓ stabilizer P0
def HLGroup : Subgroup IntegralGL := K3 ⊓ stabilizer L0
def HBBGroup : Subgroup IntegralGL := K3 ⊓ (stabilizer L0 ⊓ stabilizer P0)
def HBGGroup : Subgroup IntegralGL := K3 ⊓ (stabilizer L0 ⊓ stabilizer P1)

@[simp] theorem mem_HPGroup (g : IntegralGL) : g ∈ HPGroup ↔ HP g := Iff.rfl
@[simp] theorem mem_HLGroup (g : IntegralGL) : g ∈ HLGroup ↔ HL g := Iff.rfl
@[simp] theorem mem_HBBGroup (g : IntegralGL) : g ∈ HBBGroup ↔ HBB g := Iff.rfl
@[simp] theorem mem_HBGGroup (g : IntegralGL) : g ∈ HBGGroup ↔ HBG g := Iff.rfl

/-- The common diagonal subgroup is literally the range of the independent signs. -/
def D0 : Subgroup IntegralGL := diagonalHom.range

theorem D0_le_HBBGroup : D0 ≤ HBBGroup := by
  rintro g ⟨ε,rfl⟩
  exact (diagonalHom_mem_both ε).1

theorem D0_le_HBGGroup : D0 ≤ HBGGroup := by
  rintro g ⟨ε,rfl⟩
  exact (diagonalHom_mem_both ε).2

/-- Neither independent sign is lost when passing to the actual edge stabilizers. -/
def diagonalEquiv : (ℤˣ × ℤˣ) ≃* D0 :=
  MonoidHom.ofInjective diagonalHom_injective

theorem changeSpace_injective : Function.Injective changeSpace :=
  Submodule.map_injective_of_injective (rationalRepresentation B).injective

theorem stabilizes_changeSpace_iff (g : K3) (L : RationalSubspace) :
    Stabilizes (K3EquivK g).val (changeSpace L) ↔ Stabilizes g.val L := by
  change act (K3EquivK g) (changeSpace L) = changeSpace L ↔ act3 g L = L
  rw [← changeSpace_act3]
  exact changeSpace_injective.eq_iff

/-- The two representative vertices really have the advertised bad/good geometry. -/
theorem representative_geometry :
    Module.finrank ℚ L0 = 1 ∧ Module.finrank ℚ P0 = 2 ∧ Module.finrank ℚ P1 = 2 ∧
      L0 ≤ P0 ∧ L0 ≤ P1 ∧ ¬ Good3 L0 ∧ ¬ Good3 P0 ∧ Good3 P1 :=
  ⟨finrank_L0,finrank_P0,finrank_P1,L0_le_P0,L0_le_P1,not_good3_L0,not_good3_P0,good3_P1⟩

/-- The original K action has the exact same bad/bad matrix stabilizer after basis change. -/
theorem old_bad_bad_iff_parameter (g : K3) :
    (act (K3EquivK g) (changeSpace L0) = changeSpace L0 ∧
      act (K3EquivK g) (changeSpace P0) = changeSpace P0) ↔
    ∃ (ε₀ ε₁ : ℤˣ) (a b c : ℤ), g.val = bbElement ε₀ ε₁ a b c := by
  change (Stabilizes (K3EquivK g).val (changeSpace L0) ∧
    Stabilizes (K3EquivK g).val (changeSpace P0)) ↔ _
  rw [stabilizes_changeSpace_iff,stabilizes_changeSpace_iff,← hbb_iff_parameter]
  exact ⟨fun h => ⟨g.property,h⟩,fun h => h.2⟩

/-- The original K action has the exact same bad/good matrix stabilizer after basis change. -/
theorem old_bad_good_iff_parameter (g : K3) :
    (act (K3EquivK g) (changeSpace L0) = changeSpace L0 ∧
      act (K3EquivK g) (changeSpace P1) = changeSpace P1) ↔
    ∃ (ε₀ ε₁ : ℤˣ) (a b k : ℤ), g.val = bgElement ε₀ ε₁ a b k := by
  change (Stabilizes (K3EquivK g).val (changeSpace L0) ∧
    Stabilizes (K3EquivK g).val (changeSpace P1)) ↔ _
  rw [stabilizes_changeSpace_iff,stabilizes_changeSpace_iff,← hbg_iff_parameter]
  exact ⟨fun h => ⟨g.property,h⟩,fun h => h.2⟩

end TernaryPoly.RelativeStabilizerConsumer
