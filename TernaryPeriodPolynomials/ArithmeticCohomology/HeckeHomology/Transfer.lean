module

public import TernaryPeriodPolynomials.GroupCohomology.Homology.NormalDescent

@[expose] public section


/-!
# Transfer in group homology for a (not necessarily normal) finite-index subgroup

Formalized by Claude Sonnet 5.5.

For a finite-index subgroup `N ≤ K` (no normality) and `A : Rep k K` (`k` a field), `tSumR`/`tMapR` is the coset sum
`[v] ↦ ∑_{N x ∈ N\K} [x v]` from `K`-coinvariants to `N`-coinvariants (`tSumR_invariant`: independent of coset representatives
and of the `K`-class).  It is a natural transformation `tNatR : cK ⟶ cN N`, hence a chain map `TYR` on the complexes of
coinvariants of `A ⊗ bar(K)`, and `trR A n : Hₙ(K, A) → Hₙ(N, Res A)` (Mathlib's `groupHomology`) is its transport along `eK`, `eN`.  `trR_cor`: `tr` followed by corestriction is multiplication by the index `|N\K|`.
-/

open CategoryTheory Representation Representation.Coinvariants
open TernaryPeriodPolynomials.Argument.GroupHomology

noncomputable section

universe u

namespace TernaryPeriodPolynomials.Argument.HeckeHomology

variable {k K : Type u} [Field k] [Group K] (N : Subgroup K)
  {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k K V)

/-- Right cosets `N x`. -/
abbrev RC := Quotient (QuotientGroup.rightRel N)

theorem rc_eq_iff (a b : K) : (Quotient.mk (QuotientGroup.rightRel N) a : RC N) = Quotient.mk _ b ↔ b * a⁻¹ ∈ N := by
  rw [Quotient.eq]; exact QuotientGroup.rightRel_apply

/-- Right multiplication on right cosets. -/
def rmul (h : K) : RC N → RC N :=
  Quotient.map' (fun a => a * h) (fun a b hab => by
    rw [QuotientGroup.rightRel_apply] at hab ⊢
    simpa [mul_assoc] using hab)

theorem rmul_mk (h a : K) : rmul N h (Quotient.mk _ a) = Quotient.mk _ (a * h) := rfl

theorem rmul_mul (h h' : K) (x : RC N) : rmul N h' (rmul N h x) = rmul N (h * h') x := by
  induction x using Quotient.inductionOn' with
  | h a => simp [rmul_mk, mul_assoc]

theorem rmul_one (x : RC N) : rmul N 1 x = x := by
  induction x using Quotient.inductionOn' with
  | h a => simp [rmul_mk]

/-- `x ↦ x * h` as an equivalence. -/
def rmulEquiv (h : K) : RC N ≃ RC N where
  toFun := rmul N h
  invFun := rmul N h⁻¹
  left_inv x := by rw [rmul_mul, mul_inv_cancel, rmul_one]
  right_inv x := by rw [rmul_mul, inv_mul_cancel, rmul_one]

/-- The class of `ρ y v` in the `N`-coinvariants depends only on the right coset `N y`. -/
theorem mk_rep_eq {y y' : K} (h : (Quotient.mk (QuotientGroup.rightRel N) y : RC N) = Quotient.mk _ y')
    (v : V) :
    Coinvariants.mk (ρ.comp N.subtype) (ρ y v) = Coinvariants.mk (ρ.comp N.subtype) (ρ y' v) := by
  rw [rc_eq_iff] at h
  have : y' = (y' * y⁻¹) * y := by group
  conv_rhs => rw [this]
  have h2 := Coinvariants.mk_self_apply (ρ.comp N.subtype) ⟨y' * y⁻¹, h⟩ (ρ y v)
  rw [map_mul]
  exact h2.symm

variable [N.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

instance : Fintype (RC N) := inferInstance

/-- The coset-sum `v ↦ ∑_{N x} [x v]`, landing in the `N`-coinvariants. -/
def tSumR : V →ₗ[k] Coinvariants (ρ.comp N.subtype) :=
  ∑ x : RC N, (Coinvariants.mk (ρ.comp N.subtype)) ∘ₗ ρ x.out

theorem tSumR_apply (v : V) :
    tSumR N ρ v = ∑ x : RC N, Coinvariants.mk (ρ.comp N.subtype) (ρ x.out v) := by
  simp [tSumR]

theorem tSumR_invariant (h : K) (v : V) : tSumR N ρ (ρ h v) = tSumR N ρ v := by
  rw [tSumR_apply, tSumR_apply]
  have key : ∀ x : RC N, Coinvariants.mk (ρ.comp N.subtype) (ρ x.out (ρ h v)) =
      Coinvariants.mk (ρ.comp N.subtype) (ρ (rmulEquiv N h x).out v) := by
    intro x
    rw [← Module.End.mul_apply, ← map_mul]
    apply mk_rep_eq
    have h1 : (Quotient.mk (QuotientGroup.rightRel N) (x.out * h) : RC N) = rmulEquiv N h x := by
      have : x = Quotient.mk _ x.out := (Quotient.out_eq x).symm
      conv_rhs => rw [this]
      rfl
    rw [h1]
    exact (Quotient.out_eq _).symm
  simp only [key]
  exact Equiv.sum_comp (rmulEquiv N h) (fun y : RC N => Coinvariants.mk (ρ.comp N.subtype) (ρ y.out v))

/-- The transfer `V_K → V_N`. -/
def tMapR : Coinvariants ρ →ₗ[k] Coinvariants (ρ.comp N.subtype) :=
  Coinvariants.lift ρ (tSumR N ρ) fun h => LinearMap.ext fun v => by
    simp [tSumR_invariant]

theorem tMapR_mk (v : V) : tMapR N ρ (Coinvariants.mk ρ v) = tSumR N ρ v := rfl

theorem qMap_tMapR (v : V) :
    qMap N ρ (tMapR N ρ (Coinvariants.mk ρ v)) =
      (Fintype.card (RC N) : k) • Coinvariants.mk ρ v := by
  rw [tMapR_mk, tSumR_apply, map_sum]
  simp only [qMap_mk, Coinvariants.mk_self_apply, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul k]

/-- The transfer natural transformation `cK ⟶ cN N`. -/
def tNatR : cK (k := k) (K := K) ⟶ cN N where
  app P := ModuleCat.ofHom (tMapR N P.ρ)
  naturality P Q f := ModuleCat.hom_ext (Coinvariants.hom_ext (LinearMap.ext fun v => by
    change tMapR N Q.ρ (Coinvariants.mk _ (f.hom v)) = _
    rw [tMapR_mk, tSumR_apply]
    change _ = Coinvariants.map _ _ _ (tMapR N P.ρ (Coinvariants.mk _ v))
    rw [tMapR_mk, tSumR_apply]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    exact congrArg (Coinvariants.mk (Q.ρ.comp N.subtype)) (Rep.hom_comm_apply f x.out v).symm))

/-- The transfer on the complexes of coinvariants. -/
def TYR (Y : ChainComplex (Rep.{u} k K) ℕ) : CxK Y ⟶ CxN N Y :=
  (NatTrans.mapHomologicalComplex (tNatR N) _).app Y

theorem TYR_QY (Y : ChainComplex (Rep.{u} k K) ℕ) :
    TYR N Y ≫ QY N Y = (Fintype.card (RC N) : k) • 𝟙 _ := by
  refine HomologicalComplex.hom_ext _ _ fun j => ?_
  refine ModuleCat.hom_ext (Coinvariants.hom_ext (LinearMap.ext fun v => ?_))
  change qMap N (Y.X j).ρ (tMapR N (Y.X j).ρ (Coinvariants.mk _ v)) =
    (Fintype.card (RC N) : k) • Coinvariants.mk _ v
  exact qMap_tMapR N (Y.X j).ρ v

/-- **The transfer** `H_n(K, A) → H_n(N, Res A)` for a (not necessarily normal) finite-index subgroup. -/
def trR (A : Rep.{u} k K) (n : ℕ) : groupHomology A n ⟶ groupHomology (Rep.res N.subtype A) n :=
  (eK A n).hom ≫ HomologicalComplex.homologyMap (TYR N (YA A)) n ≫ (eN N A n).inv

/-- Transfer followed by corestriction is multiplication by the index `[K : N]`. -/
theorem trR_cor (A : Rep.{u} k K) (n : ℕ) :
    trR N A n ≫ groupHomology.map N.subtype (𝟙 (Rep.res N.subtype A)) n =
      (Fintype.card (RC N) : k) • 𝟙 _ := by
  have h := cor_comparison N A n
  have h2 : (eN N A n).inv ≫ groupHomology.map N.subtype (𝟙 (Rep.res N.subtype A)) n =
      HomologicalComplex.homologyMap (QY N (YA A)) n ≫ (eK A n).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← h]
    simp
  unfold trR
  simp only [Category.assoc]
  rw [h2, ← Category.assoc (HomologicalComplex.homologyMap (TYR N (YA A)) n),
    ← HomologicalComplex.homologyMap_comp, TYR_QY]
  rw [homologyMap_smul']
  simp

end TernaryPeriodPolynomials.Argument.HeckeHomology
