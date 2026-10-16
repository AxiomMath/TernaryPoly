module

public import TernaryPeriodPolynomials.ArithmeticGroup.GL2Free.Matrices
public import Mathlib.GroupTheory.CoprodI
public import Mathlib.Tactic.Linarith

@[expose] public section


open Matrix Monoid
noncomputable section
namespace TernaryPoly.IntegralGL2Free
open RelativeStabilizerParameters
open scoped Pointwise

local instance : MulAction GL2 (Fin 2 → ℤ) where
  smul g v := g.val.mulVec v
  one_smul v := Matrix.one_mulVec v
  mul_smul g h v := (Matrix.mulVec_mulVec v g.val h.val).symm

lemma upper_vector (t : ℤ) (v : Fin 2 → ℤ) : root 0 t • v=![v 0+2*t*v 1,v 1] := by
  ext i
  fin_cases i <;> simp [HSMul.hSMul,SMul.smul,Matrix.mulVec,dotProduct,root,rootMatrix,Fin.sum_univ_two]

lemma lower_vector (t : ℤ) (v : Fin 2 → ℤ) : root 1 t • v=![v 0,v 1+2*t*v 0] := by
  ext i
  fin_cases i <;> simp [HSMul.hSMul,SMul.smul,Matrix.mulVec,dotProduct,root,rootMatrix,Fin.sum_univ_two,add_comm]

/-- The even transvections expand strict coordinate dominance for every nonzero power. -/
lemma expand_dominance (x y t : ℤ) (ht : t≠0) (hxy : |x| < |y|) : |y| < |x+2*t*y| := by
  have ht1 : 1≤|t| := by have h := abs_pos.mpr ht; omega
  have hy0 : 0≤|y| := abs_nonneg y
  have htri := abs_add_le (x+2*t*y) (-x)
  have he : (x+2*t*y)+(-x)=2*t*y := by ring
  rw [he,abs_neg,abs_mul,abs_mul] at htri
  norm_num at htri
  nlinarith

def pingSet (i : Fin 2) : Set (Fin 2 → ℤ) :=
  ![{v | |v 1| < |v 0|},{v | |v 0| < |v 1|}] i

lemma pingSet_nonempty (i : Fin 2) : (pingSet i).Nonempty := by
  fin_cases i
  · exact ⟨![1,0],by norm_num [pingSet]⟩
  · exact ⟨![0,1],by norm_num [pingSet]⟩

lemma pingSet_disjoint : Pairwise (fun i j => Disjoint (pingSet i) (pingSet j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro v hi hj
  fin_cases i <;> fin_cases j <;> simp_all [pingSet]
  all_goals omega

lemma root_ping_pong : Pairwise (fun i j => ∀ t : ℤ, t≠0 → root i t • pingSet j ⊆ pingSet i) := by
  intro i j hij t ht v hv
  obtain ⟨w,hw,rfl⟩ := hv
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · change root 0 t • w ∈ pingSet 0
    rw [upper_vector]
    exact expand_dominance (w 0) (w 1) t ht hw
  · change root 1 t • w ∈ pingSet 1
    rw [lower_vector]
    exact expand_dominance (w 1) (w 0) t ht hw
  · exact False.elim (hij rfl)

/-- Ping-pong proves injectivity of the actual integral two-generator representation. -/
theorem lift_injective : Function.Injective (FreeGroup.lift (fun i : Fin 2 => root i 1)) := by
  let f : (i : Fin 2) → FreeGroup Unit →* GL2 :=
    fun i => FreeGroup.lift (fun _ => root i 1)
  have hcard : 3≤Cardinal.mk (Fin 2) ∨ ∃ i : Fin 2, 3≤Cardinal.mk (FreeGroup Unit) := by
    right
    refine ⟨0,?_⟩
    let : Infinite (FreeGroup Unit) := Infinite.of_injective
      FreeGroup.freeGroupUnitEquivInt.symm FreeGroup.freeGroupUnitEquivInt.symm.injective
    exact Cardinal.natCast_le_aleph0.trans (Cardinal.aleph0_le_mk _)
  have hpp : Pairwise (fun i j => ∀ h : FreeGroup Unit, h≠1 → f i h • pingSet j ⊆ pingSet i) := by
    intro i j hij h hne
    obtain ⟨t,rfl⟩ := FreeGroup.freeGroupUnitEquivInt.symm.surjective h
    change (FreeGroup.lift (fun _ : Unit => root i 1)) ((FreeGroup.of ())^t) • pingSet j ⊆ pingSet i
    have ht : t≠0 := by
      intro ht
      subst t
      exact hne (by rfl)
    rw [map_zpow,FreeGroup.lift_apply_of,← root_zpow]
    exact root_ping_pong hij t ht
  have hinj := CoprodI.lift_injective_of_ping_pong f hcard pingSet pingSet_nonempty pingSet_disjoint hpp
  have he : FreeGroup.lift (fun i : Fin 2 => root i 1) =
      (CoprodI.lift f).comp (@freeGroupEquivCoprodI (Fin 2)).toMonoidHom := by
    ext i
    simp [f]
  rw [he,MonoidHom.coe_comp]
  exact hinj.comp freeGroupEquivCoprodI.injective

/-- The literal image subgroup is a free group. -/
noncomputable def generatedEquiv : FreeGroup (Fin 2) ≃* generated :=
  MulEquiv.ofBijective (FreeGroup.lift (fun i : Fin 2 => root i 1)).rangeRestrict
    ⟨fun _ _ h => lift_injective (congrArg Subtype.val h), MonoidHom.rangeRestrict_surjective _⟩

instance generated_isFree : IsFreeGroup generated :=
  ((FreeGroupBasis.ofFreeGroup (Fin 2)).map generatedEquiv).isFreeGroup

end TernaryPoly.IntegralGL2Free
