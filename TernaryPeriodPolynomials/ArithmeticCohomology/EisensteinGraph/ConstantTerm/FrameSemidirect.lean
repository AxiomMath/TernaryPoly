module

public import Mathlib.GroupTheory.SemidirectProduct
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.Frame

@[expose] public section


/-!
# The level lattice of a radical frame is a semidirect product

For a radical frame `F` and a level `N`, the lattice `u(ℤ²) · {m | A_m ≡ 1 mod N}` is the image of
the semidirect product `Multiplicative (ℤ × ℤ) ⋊ leviLevel N` under an injective homomorphism
`F.latticeHom N`, so that the cohomological results about `L ⋊ M` apply to it.

Written by AxiomCode.
-/

open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm

/-- The integral radical lattice, written multiplicatively. -/
abbrev Lat : Type := Multiplicative (ℤ × ℤ)

theorem intAct_add (A : GLTwo ℤ) (ℓ ℓ' : ℤ × ℤ) :
    intAct A (ℓ + ℓ') = intAct A ℓ + intAct A ℓ' := by
  simp only [intAct, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]
  ext <;> simp <;> ring

theorem intAct_one (ℓ : ℤ × ℤ) : intAct 1 ℓ = ℓ := by
  simp [intAct]

theorem intAct_mul (A B : GLTwo ℤ) (ℓ : ℤ × ℤ) :
    intAct (A * B) ℓ = intAct A (intAct B ℓ) := by
  simp only [intAct, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  ext <;> simp <;> ring

/-- The additive automorphism of `ℤ²` given by an integral invertible matrix. -/
def intActEquiv (A : GLTwo ℤ) : (ℤ × ℤ) ≃+ (ℤ × ℤ) where
  toFun := intAct A
  invFun := intAct A⁻¹
  left_inv ℓ := by rw [← intAct_mul, inv_mul_cancel, intAct_one]
  right_inv ℓ := by rw [← intAct_mul, mul_inv_cancel, intAct_one]
  map_add' := intAct_add A

/-- The Levi action on the multiplicative lattice. -/
def leviAction : GLTwo ℤ →* MulAut Lat where
  toFun A := AddEquiv.toMultiplicative (intActEquiv A)
  map_one' := by
    apply MulEquiv.ext
    intro ℓ
    show Multiplicative.ofAdd (intAct 1 (Multiplicative.toAdd ℓ)) = ℓ
    simp only [intAct_one, ofAdd_toAdd]
  map_mul' A B := by
    apply MulEquiv.ext
    intro ℓ
    show Multiplicative.ofAdd (intAct (A * B) (Multiplicative.toAdd ℓ)) =
      Multiplicative.ofAdd (intAct A (intAct B (Multiplicative.toAdd ℓ)))
    rw [intAct_mul]

namespace RadicalFrame

variable (F : RadicalFrame) (N : ℕ)

/-- The action of the level subgroup of the Levi on the lattice. -/
def latticeAction : F.leviLevel N →* MulAut Lat :=
  leviAction.comp (F.leviMatrix.comp (F.leviLevel N).subtype)

/-- The integral points as a homomorphism on the multiplicative lattice. -/
def integralHom : Lat →* RationalGL3 where
  toFun ℓ := F.integral (Multiplicative.toAdd ℓ)
  map_one' := F.integral_zero
  map_mul' a b := F.integral_add (Multiplicative.toAdd a) (Multiplicative.toAdd b)

/-- The inclusion of the level subgroup of the Levi. -/
def leviLevelHom : F.leviLevel N →* RationalGL3 :=
  F.leviHom.comp (F.leviLevel N).subtype

/-- The map from the semidirect product onto the level lattice. -/
def latticeHom : SemidirectProduct Lat (F.leviLevel N) (F.latticeAction N) →* RationalGL3 :=
  SemidirectProduct.lift (F.integralHom) (F.leviLevelHom N) (by
    intro m
    apply MonoidHom.ext
    intro ℓ
    change F.integral (intAct (F.leviMatrix (m : F.Levi)) (Multiplicative.toAdd ℓ)) =
      F.leviHom (m : F.Levi) * F.integral (Multiplicative.toAdd ℓ) * (F.leviHom (m : F.Levi))⁻¹
    rw [F.levi_mul_integral]
    group)

theorem latticeHom_inl (ℓ : Lat) :
    F.latticeHom N (SemidirectProduct.inl ℓ) = F.integral (Multiplicative.toAdd ℓ) := by
  simp [latticeHom, integralHom]

theorem latticeHom_inr (m : F.leviLevel N) :
    F.latticeHom N (SemidirectProduct.inr m) = F.leviHom (m : F.Levi) := by
  simp [latticeHom, leviLevelHom]

theorem latticeHom_apply (g : SemidirectProduct Lat (F.leviLevel N) (F.latticeAction N)) :
    F.latticeHom N g = F.integral (Multiplicative.toAdd g.left) * F.leviHom (g.right : F.Levi) := by
  have h : g = SemidirectProduct.inl g.left * SemidirectProduct.inr g.right := by
    apply SemidirectProduct.ext <;> simp
  conv_lhs => rw [h]
  rw [map_mul, latticeHom_inl, latticeHom_inr]

theorem latticeHom_injective : Function.Injective (F.latticeHom N) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  rw [latticeHom_apply] at hg
  have hm : F.leviHom (g.right : F.Levi) = F.integral (-Multiplicative.toAdd g.left) := by
    rw [F.integral_neg]
    exact eq_inv_of_mul_eq_one_right hg
  have h1 : g.right = 1 := Subtype.ext (F.disjoint (g.right : F.Levi)
    (((-Multiplicative.toAdd g.left).1 : ℚ), ((-Multiplicative.toAdd g.left).2 : ℚ)) hm)
  rw [h1] at hg
  simp only [Subgroup.coe_one, map_one, mul_one] at hg
  have h2 : F.integral (Multiplicative.toAdd g.left) = F.integral 0 := by
    rw [hg, F.integral_zero]
  have h3 : Multiplicative.toAdd g.left = 0 := by
    have h4 := F.radical_injective h2
    have h5 := congrArg (fun r : Multiplicative (ℚ × ℚ) => Multiplicative.toAdd r) h4
    simp only [toAdd_ofAdd] at h5
    ext
    · simpa using congrArg Prod.fst h5
    · simpa using congrArg Prod.snd h5
  apply SemidirectProduct.ext
  · exact h3
  · exact h1

theorem latticeHom_range : (F.latticeHom N).range = F.lattice N := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    rw [latticeHom_apply]
    exact ⟨Multiplicative.toAdd x.left, x.right, x.right.property, rfl⟩
  · rintro ⟨ℓ, m, hm, rfl⟩
    refine ⟨SemidirectProduct.inl (Multiplicative.ofAdd ℓ) *
      SemidirectProduct.inr ⟨m, hm⟩, ?_⟩
    rw [map_mul, latticeHom_inl, latticeHom_inr]
    rfl

end RadicalFrame

end TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm
