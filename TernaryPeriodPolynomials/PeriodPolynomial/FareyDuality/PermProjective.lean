module

public import Mathlib.RepresentationTheory.Rep.Iso
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Units.Opposite
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.GroupTheory.Perm.Option
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


/-!
# Permutation representations with finite stabilizers are projective

Formalized by Claude Sonnet 5.5.

For a group `Γ`, a `Γ`-set `X` all of whose stabilizers are finite, and a field `k` of characteristic zero,
the permutation representation `Rep.ofMulAction k Γ X` is a retract of the free representation on the orbit
space (`projPi`, `projIota`, `projIota_projPi`), hence projective (`ofMulAction_projective`).  The section
`projIota` averages over the finitely many group elements carrying the chosen orbit representative to the point.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.BinaryDuality

open CategoryTheory Representation Rep
open scoped Classical MonoidAlgebra

variable {k : Type} [Field k] {Γ : Type} [Group Γ] {X : Type} [MulAction Γ X]

/-- The orbit space. -/
abbrev OrbSp (Γ X : Type) [Group Γ] [MulAction Γ X] := MulAction.orbitRel.Quotient Γ X

/-- The chosen representative of the orbit of `x`. -/
def orbRep (x : X) : X := (Quotient.mk'' x : OrbSp Γ X).out

theorem exists_smul_orbRep (x : X) : ∃ γ : Γ, γ • orbRep (Γ := Γ) x = x := by
  have h : MulAction.orbitRel Γ X (orbRep (Γ := Γ) x) x := Quotient.mk_out (s := MulAction.orbitRel Γ X) x
  have h' : MulAction.orbitRel Γ X x (orbRep (Γ := Γ) x) := (MulAction.orbitRel Γ X).iseqv.symm h
  rw [MulAction.orbitRel_apply] at h'
  obtain ⟨γ, hγ⟩ := h'
  exact ⟨γ, hγ⟩

/-- The group elements carrying the orbit representative of `x` to `x`. -/
def carrierSet (x : X) : Set Γ := {γ | γ • orbRep (Γ := Γ) x = x}

theorem carrierSet_finite (hfin : ∀ x : X, Finite (MulAction.stabilizer Γ x)) (x : X) :
    (carrierSet (Γ := Γ) x).Finite := by
  obtain ⟨γ₀, hγ₀⟩ := exists_smul_orbRep (Γ := Γ) x
  have : carrierSet (Γ := Γ) x = (fun s => γ₀ * s) '' (MulAction.stabilizer Γ (orbRep (Γ := Γ) x) : Set Γ) := by
    ext γ
    simp only [carrierSet, Set.mem_ofPred_eq, Set.mem_image, SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    constructor
    · intro h
      refine ⟨γ₀⁻¹ * γ, ?_, mul_inv_cancel_left γ₀ γ⟩
      rw [mul_smul, h, inv_smul_eq_iff, hγ₀]
    · rintro ⟨s, hs, rfl⟩
      rw [mul_smul, hs, hγ₀]
  rw [this]
  have := hfin (orbRep (Γ := Γ) x)
  exact Set.Finite.image _ (Set.toFinite _)

/-- The orbit label of a point. -/
def lab (Γ : Type) [Group Γ] {X : Type} [MulAction Γ X] (x : X) : OrbSp Γ X := Quotient.mk'' x

theorem lab_smul (g : Γ) (x : X) : lab Γ (g • x) = lab Γ x := by
  apply Quotient.sound
  change MulAction.orbitRel Γ X (g • x) x
  rw [MulAction.orbitRel_apply]
  exact ⟨g, rfl⟩

theorem orbRep_smul (g : Γ) (x : X) : orbRep (Γ := Γ) (g • x) = orbRep (Γ := Γ) x := by
  unfold orbRep
  exact congrArg Quotient.out (lab_smul g x)

theorem carrierSet_smul (g : Γ) (x : X) :
    carrierSet (Γ := Γ) (g • x) = (fun γ => g * γ) '' carrierSet (Γ := Γ) x := by
  ext γ
  simp only [carrierSet, Set.mem_ofPred_eq, Set.mem_image, orbRep_smul]
  constructor
  · intro h
    refine ⟨g⁻¹ * γ, ?_, mul_inv_cancel_left g γ⟩
    rw [mul_smul, h, inv_smul_eq_iff]
  · rintro ⟨s, hs, rfl⟩
    rw [mul_smul, hs]

/-- The normalized sum over the group elements carrying the orbit representative to `x`. -/
def vecAt (hfin : ∀ x : X, Finite (MulAction.stabilizer Γ x)) (x : X) : (OrbSp Γ X →₀ MonoidAlgebra k Γ) :=
  ((((carrierSet_finite hfin x).toFinset.card : k))⁻¹) •
    ∑ γ ∈ (carrierSet_finite hfin x).toFinset, Finsupp.single (lab Γ x) (MonoidAlgebra.single γ (1 : k))

theorem toFinset_carrierSet_smul (hfin : ∀ x : X, Finite (MulAction.stabilizer Γ x)) (g : Γ) (x : X) :
    (carrierSet_finite hfin (g • x)).toFinset =
      (carrierSet_finite hfin x).toFinset.image (fun γ => g * γ) := by
  ext γ
  simp only [Set.Finite.mem_toFinset, Finset.mem_image, carrierSet_smul, Set.mem_image]

theorem card_carrierSet_smul (hfin : ∀ x : X, Finite (MulAction.stabilizer Γ x)) (g : Γ) (x : X) :
    (carrierSet_finite hfin (g • x)).toFinset.card = (carrierSet_finite hfin x).toFinset.card := by
  rw [toFinset_carrierSet_smul hfin, Finset.card_image_of_injective _ (mul_right_injective g)]

theorem vecAt_smul (hfin : ∀ x : X, Finite (MulAction.stabilizer Γ x)) (g : Γ) (x : X) :
    vecAt (k := k) hfin (g • x) = Representation.free k Γ (OrbSp Γ X) g (vecAt hfin x) := by
  unfold vecAt
  rw [card_carrierSet_smul hfin, lab_smul, toFinset_carrierSet_smul hfin, map_smul, map_sum,
    Finset.sum_image (fun a _ b _ h => mul_left_cancel h)]
  congr 1
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [Representation.free_single_single]

/-- The surjection from the free module on the orbits. -/
def projPi (k Γ X : Type) [Field k] [Group Γ] [MulAction Γ X] :
    Rep.free k Γ (OrbSp Γ X) ⟶ Rep.ofMulAction k Γ X :=
  Rep.freeLift k Γ (Rep.ofMulAction k Γ X)
    (fun ω : OrbSp Γ X => (MonoidAlgebra.single (Quotient.out ω) (1 : k) : k[X]))

theorem projPi_apply (ω : OrbSp Γ X) (γ : Γ) (r : k) :
    (projPi k Γ X).hom (Finsupp.single ω (MonoidAlgebra.single γ r)) =
      MonoidAlgebra.single (γ • Quotient.out ω) r := by
  simp only [projPi, Rep.hom_ofHom]
  rw [Representation.freeLift_single_single]
  rw [Representation.ofMulAction_single]
  simp [MonoidAlgebra.smul_single]

/-- The linear map underlying the section. -/
def iotaLin (hfin : ∀ x : X, Finite (MulAction.stabilizer Γ x)) :
    k[X] →ₗ[k] (OrbSp Γ X →₀ MonoidAlgebra k Γ) :=
  Finsupp.linearCombination k (vecAt (k := k) hfin) ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

theorem iotaLin_single (hfin : ∀ x : X, Finite (MulAction.stabilizer Γ x)) (x : X) (r : k) :
    iotaLin (k := k) hfin (MonoidAlgebra.single x r) = r • vecAt hfin x := by
  simp [iotaLin]

theorem iotaLin_equivariant (hfin : ∀ x : X, Finite (MulAction.stabilizer Γ x)) (g : Γ) (v : k[X]) :
    iotaLin hfin (Representation.ofMulAction k Γ X g v) =
      Representation.free k Γ (OrbSp Γ X) g (iotaLin hfin v) := by
  have key : iotaLin hfin ∘ₗ Representation.ofMulAction k Γ X g =
      Representation.free k Γ (OrbSp Γ X) g ∘ₗ iotaLin hfin := by
    refine MonoidAlgebra.lhom_ext' fun x => LinearMap.ext_ring ?_
    simp only [LinearMap.comp_apply, MonoidAlgebra.lsingle_apply]
    rw [Representation.ofMulAction_single, iotaLin_single, iotaLin_single, vecAt_smul, map_smul]
  exact LinearMap.congr_fun key v

/-- The section of `projPi`. -/
def projIota (hfin : ∀ x : X, Finite (MulAction.stabilizer Γ x)) :
    Rep.ofMulAction k Γ X ⟶ Rep.free k Γ (OrbSp Γ X) :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap (ρ := (Rep.ofMulAction k Γ X).ρ)
    (σ := (Rep.free k Γ (OrbSp Γ X)).ρ) (iotaLin hfin) (iotaLin_equivariant hfin))

theorem projPi_vecAt [CharZero k] (hfin : ∀ x : X, Finite (MulAction.stabilizer Γ x)) (x : X) :
    (projPi k Γ X).hom (vecAt (k := k) hfin x) = MonoidAlgebra.single x (1 : k) := by
  unfold vecAt
  rw [map_smul, map_sum]
  have : ∀ γ ∈ (carrierSet_finite hfin x).toFinset,
      (projPi k Γ X).hom (Finsupp.single (lab Γ x) (MonoidAlgebra.single γ (1 : k))) =
        MonoidAlgebra.single x (1 : k) := by
    intro γ hγ
    rw [projPi_apply]
    have : γ • Quotient.out (lab Γ x) = x := by
      have := (Set.Finite.mem_toFinset _).mp hγ
      exact this
    rw [this]
  rw [Finset.sum_congr rfl this, Finset.sum_const]
  have hpos : ((carrierSet_finite hfin x).toFinset.card : k) ≠ 0 := by
    obtain ⟨γ₀, hγ₀⟩ := exists_smul_orbRep (Γ := Γ) x
    have hne : (carrierSet_finite hfin x).toFinset.card ≠ 0 :=
      Finset.card_ne_zero_of_mem (a := γ₀) ((Set.Finite.mem_toFinset _).mpr hγ₀)
    exact_mod_cast hne
  rw [← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀ hpos, one_smul]

theorem projIota_projPi [CharZero k] (hfin : ∀ x : X, Finite (MulAction.stabilizer Γ x)) :
    projIota (k := k) hfin ≫ projPi k Γ X = 𝟙 _ := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  refine MonoidAlgebra.lhom_ext' fun x => LinearMap.ext_ring ?_
  change (projPi k Γ X).hom (iotaLin hfin (MonoidAlgebra.single x (1 : k))) = MonoidAlgebra.single x 1
  rw [iotaLin_single, one_smul]
  exact projPi_vecAt hfin x

/-- **Permutation representations with finite stabilizers are projective in characteristic zero.** -/
theorem ofMulAction_projective [CharZero k] (hfin : ∀ x : X, Finite (MulAction.stabilizer Γ x)) :
    Projective (Rep.ofMulAction k Γ X) :=
  (⟨projIota hfin, projPi k Γ X, projIota_projPi hfin⟩ : Retract (Rep.ofMulAction k Γ X)
    (Rep.free k Γ (OrbSp Γ X))).projective

end TernaryPeriodPolynomials.Argument.BinaryDuality
