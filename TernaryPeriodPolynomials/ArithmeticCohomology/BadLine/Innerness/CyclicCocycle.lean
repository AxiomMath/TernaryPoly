module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.RadicalExtension
public import Mathlib.GroupTheory.SemidirectProduct

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]

def representationMulAut (representation : Representation ℂ G V) : G →* MulAut (Multiplicative V) where
  toFun g :=
    { toFun := fun v => Multiplicative.ofAdd (representation g v.toAdd)
      invFun := fun v => Multiplicative.ofAdd (representation g⁻¹ v.toAdd)
      left_inv := by
        intro v
        change representation g⁻¹ (representation g v.toAdd) = v.toAdd
        rw [← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
      right_inv := by
        intro v
        change representation g (representation g⁻¹ v.toAdd) = v.toAdd
        rw [← Module.End.mul_apply,← map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
      map_mul' := by
        intro v w
        change representation g (v.toAdd+w.toAdd) = representation g v.toAdd+representation g w.toAdd
        exact map_add _ _ _ }
  map_one' := by
    ext v
    change representation 1 v.toAdd = v.toAdd
    rw [map_one,Module.End.one_apply]
  map_mul' g h := by
    ext v
    change representation (g*h) v.toAdd = representation g (representation h v.toAdd)
    rw [map_mul,Module.End.mul_apply]

theorem integerCocycle_exists (representation : Representation ℂ (Multiplicative ℤ) V) (p : V) :
    ∃ values : ℤ → V, values 1 = p ∧ ∀ k l,
      values (k+l) = values k+representation (Multiplicative.ofAdd k) (values l) := by
  let generator : SemidirectProduct (Multiplicative V) (Multiplicative ℤ)
      (representationMulAut representation) := ⟨Multiplicative.ofAdd p,Multiplicative.ofAdd 1⟩
  let values := fun k : ℤ => (generator^k).left.toAdd
  have right_power (k : ℤ) : (generator^k).right = Multiplicative.ofAdd k := by
    change SemidirectProduct.rightHom (generator^k) = _
    rw [map_zpow]
    change (Multiplicative.ofAdd (1 : ℤ))^k = Multiplicative.ofAdd k
    rw [← ofAdd_zsmul]
    simp
  refine ⟨values,?_,?_⟩
  · simp [values]
    rfl
  · intro k l
    change (generator^(k+l)).left.toAdd = _
    rw [zpow_add,SemidirectProduct.mul_left,right_power]
    rfl

theorem integerCocycle_ext (representation : Representation ℂ (Multiplicative ℤ) V)
    (first second : ℤ → V)
    (first_relation : ∀ k l, first (k+l) = first k+representation (Multiplicative.ofAdd k) (first l))
    (second_relation : ∀ k l, second (k+l) = second k+representation (Multiplicative.ofAdd k) (second l))
    (generator : first 1 = second 1) : first = second := by
  have first_zero : first 0 = 0 := by
    have relation := first_relation 0 0
    simpa using relation
  have second_zero : second 0 = 0 := by
    have relation := second_relation 0 0
    simpa using relation
  let equalizer : AddSubgroup ℤ :=
    { carrier := {k | first k = second k}
      zero_mem' := first_zero.trans second_zero.symm
      add_mem' := by
        intro k l hk hl
        change first (k+l) = second (k+l)
        rw [first_relation,second_relation,hk,hl]
      neg_mem' := by
        intro k hk
        change first (-k) = second (-k)
        apply representation_apply_injective representation (Multiplicative.ofAdd k)
        have first_eq := first_relation k (-k)
        have second_eq := second_relation k (-k)
        rw [add_neg_cancel,first_zero,hk] at first_eq
        rw [add_neg_cancel,second_zero] at second_eq
        exact add_left_cancel (first_eq.symm.trans second_eq) }
  funext k
  have member := equalizer.zsmul_mem generator k
  change first (k • (1 : ℤ)) = second (k • (1 : ℤ)) at member
  simpa using member

theorem integerCocycle_lift {W : Type*} [AddCommGroup W] [Module ℂ W]
    (source : Representation ℂ (Multiplicative ℤ) V)
    (target : Representation ℂ (Multiplicative ℤ) W)
    (boundary : V →ₗ[ℂ] W)
    (equivariant : ∀ k v, boundary (source (Multiplicative.ofAdd k) v) =
      target (Multiplicative.ofAdd k) (boundary v))
    (values : ℤ → W)
    (relation : ∀ k l, values (k+l) = values k+target (Multiplicative.ofAdd k) (values l))
    (adjustment : W) (p : V)
    (generator : values 1+target (Multiplicative.ofAdd 1) adjustment-adjustment = boundary p) :
    ∃ lifted : ℤ → V,
      (∀ k l, lifted (k+l) = lifted k+source (Multiplicative.ofAdd k) (lifted l)) ∧
      ∀ k, values k+target (Multiplicative.ofAdd k) adjustment-adjustment = boundary (lifted k) := by
  obtain ⟨lifted,at_one,lifted_relation⟩ := integerCocycle_exists source p
  refine ⟨lifted,lifted_relation,?_⟩
  have equal := integerCocycle_ext target
    (fun k => values k+target (Multiplicative.ofAdd k) adjustment-adjustment)
    (fun k => boundary (lifted k)) (by
      intro k l
      rw [relation,ofAdd_add,map_mul,Module.End.mul_apply]
      simp only [map_sub,map_add]
      abel) (by
      intro k l
      rw [lifted_relation,map_add,equivariant]) (by simpa only [at_one] using generator)
  exact fun k => congrFun equal k

end TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
