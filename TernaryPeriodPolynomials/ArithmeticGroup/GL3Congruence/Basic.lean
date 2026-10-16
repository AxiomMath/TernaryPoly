module

public import TernaryPeriodPolynomials.Building.ModThreeGoodAction
public import TernaryPeriodPolynomials.Polynomial.GLAction
public import Mathlib.GroupTheory.Index
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.RingTheory.FreeCommRing
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.RingTheory.Valuation.IsTrivialOn
public import Mathlib.Topology.Algebra.Module.UniformConvergence
public import Mathlib.Topology.Algebra.SeparationQuotient.Section
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.WithTopology

@[expose] public section


open Matrix
noncomputable section
namespace TernaryPoly.IntegralGL3Congruence
open ModThreeGoodAction

/-- The actual matrix reduction homomorphism at every integral modulus. -/
def reductionMod (N : ℕ) : IntegralGL →* GeneralLinearGroup (Fin 3) (ZMod N) :=
  GeneralLinearGroup.map (Int.castRingHom (ZMod N))

/-- The actual principal congruence subgroup, as the kernel of matrix reduction. -/
def principal (N : ℕ) : Subgroup IntegralGL := (reductionMod N).ker

abbrev principalSix : Subgroup IntegralGL := principal 6
abbrev principalThree : Subgroup IntegralGL := principal 3

instance principal_normal (N : ℕ) : (principal N).Normal := by
  unfold principal
  infer_instance
instance principal_finiteIndex (N : ℕ) [NeZero N] : (principal N).FiniteIndex := by
  unfold principal
  infer_instance

/-- Entrywise divisibility is exactly membership in the actual congruence kernel. -/
theorem mem_principal_iff (N : ℕ) (g : IntegralGL) :
    g∈principal N ↔ ∀ i j,(N : ℤ) ∣ g.val i j-(1 : Matrix (Fin 3) (Fin 3) ℤ) i j := by
  have hone (i j : Fin 3) : (((1 : Matrix (Fin 3) (Fin 3) ℤ) i j : ℤ) : ZMod N)=
      (1 : Matrix (Fin 3) (Fin 3) (ZMod N)) i j := by
    by_cases h : i=j <;> simp [Matrix.one_apply,h]
  change reductionMod N g=1 ↔ _
  constructor
  · intro hg i j
    have he := congrArg (fun A : GeneralLinearGroup (Fin 3) (ZMod N) => A.val i j) hg
    change (g.val i j : ZMod N)=(1 : Matrix (Fin 3) (Fin 3) (ZMod N)) i j at he
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp
    rw [Int.cast_sub,hone,he,sub_self]
  · intro hg
    apply Units.ext
    ext i j
    have he := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mpr (hg i j)
    rw [Int.cast_sub,hone,sub_eq_zero] at he
    exact he

theorem principalSix_le_three : principalSix≤principalThree := by
  intro g hg
  apply (mem_principal_iff 3 g).mpr
  intro i j
  exact dvd_trans (by norm_num : (3 : ℤ) ∣ 6) ((mem_principal_iff 6 g).mp hg i j)

theorem principalThree_le_K : principalThree≤K := by
  intro g hg
  have hr : reduction g=1 := hg
  change Matrix.vecMul fixedRow (reduction g).val=fixedRow
  rw [hr,Units.val_one,Matrix.vecMul_one]

theorem principalSix_le_K : principalSix≤K := principalSix_le_three.trans principalThree_le_K

/-- Every level-three congruence element already has determinant one over the integers. -/
theorem principalThree_det_one (g : IntegralGL) (hg : g∈principalThree) : g.val.det=1 := by
  have hr : reduction g=1 := hg
  have hd : (g.val.det : ZMod 3)=1 := by
    calc
      _=(reduction g).val.det := (Int.castRingHom (ZMod 3)).map_det _
      _=1 := by rw [hr,Units.val_one,Matrix.det_one]
  have hu : IsUnit g.val.det := (GeneralLinearGroup.det g).isUnit
  rcases Int.isUnit_iff.mp hu with h|h
  · exact h
  · rw [h] at hd
    have hn : (-1 : ZMod 3)≠1 := by decide
    exact (hn (by simpa using hd)).elim

theorem principalSix_det_one (g : IntegralGL) (hg : g∈principalSix) : g.val.det=1 :=
  principalThree_det_one g (principalSix_le_three hg)

/-- The exact principal level-six subgroup inside the actual sum-covector fixer. -/
def principalSixInK : Subgroup K := ((reductionMod 6).comp K.subtype).ker

instance principalSixInK_normal : principalSixInK.Normal := by
  unfold principalSixInK
  infer_instance
instance principalSixInK_finiteIndex : principalSixInK.FiniteIndex := by
  unfold principalSixInK
  infer_instance

theorem mem_principalSixInK (g : K) : g∈principalSixInK ↔ g.val∈principalSix := Iff.rfl

/-- All determinant characters are trivial on this explicit congruence subgroup. -/
theorem principalSix_determinantCharacter (e : ℤ) (g : IntegralGL) (hg : g∈principalSix) :
    PolynomialGLAction.determinantCharacter e
      (GeneralLinearGroup.map (Int.castRingHom ℚ) g)=1 := by
  have hd : (GeneralLinearGroup.map (Int.castRingHom ℚ) g).val.det=1 := by
    calc
      _=(g.val.det : ℚ) := ((Int.castRingHom ℚ).map_det _).symm
      _=1 := by rw [principalSix_det_one g hg]; rfl
  change (GeneralLinearGroup.map (Int.castRingHom ℚ) g).val.det^e=1
  rw [hd,one_zpow]

end TernaryPoly.IntegralGL3Congruence
