module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.Duality
public import TernaryPeriodPolynomials.PeriodPolynomial.FareyDuality.FareyComplex

@[expose] public section


/-!
# The dual Farey tree computes group cohomology in degree one

Formalized by Claude Sonnet 5.5.  Context: `ar:eq:facepair`.

For a subgroup `Γ ≤ GL₂(ℤ)` with `FareyData` (free action on triangles) and a complex representation `A`:
* `tri_reach`, `tri_const`: the dual Farey tree is connected;
* `exists_potential`-type facts: `potFn`/`pot`, the normalized potential of an antisymmetric edge cochain (`pot_delta : δ (pot F) = F`,
  `pot_unique`), obtained from the exactness `d1_injective`, `exists_boundary` of the Farey resolution;
* `pot_smul`: twisted equivariance `pot F (γ t) = γ · pot F t + pot F (γ t₀)`; `coc F γ = pot F (γ t₀)`: the actual path-sum cocycle,
  `coc_mul`: it is a crossed homomorphism;
* `cohMap A : C¹(A) → groupCohomology.H1 A`: the class of the path-sum cocycle (Mathlib's `H1π`), with
  `cohMap_eq_zero_iff : cohMap F = 0 ↔ F ∈ range δ`, `cohMap_surjective`, hence
  **`cohIso A : C¹(A) / δ C⁰(A) ≃ₗ H¹(Γ, A)`**;
* `cohMap_natural`: naturality in the coefficient representation (for every morphism `A ⟶ B`, `H¹.map = C1.map`).
The comparison is the actual cocycle map (path sums along the tree), not an abstract isomorphism, and needs no freeness of `Γ` as an
abstract group; only the free action on the (contractible) tree.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNParabolicPD

open TernaryPeriodPolynomials.Argument.FareyTree CategoryTheory TernaryPoly.RankTwoAugmentedFrames
open scoped MonoidAlgebra Classical

section Tree

/-- The dual Farey tree is connected: every triangle is reached from `triPlus` by a path of adjacent triangles. -/
theorem tri_reach (t : Tri) : Relation.ReflTransGen TAdj triPlus t := by
  induction' hr : triRank t using Nat.strong_induction_on with n ih generalizing t
  by_cases hc : Central t
  · rcases (central_iff t).mp hc with rfl | rfl
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single tAdj_triPlus_triMinus
  · obtain ⟨t', hadj, hlt⟩ := rank_P2 hc
    exact (ih (triRank t') (hr ▸ hlt) t' rfl).tail hadj.symm

/-- A function on triangles taking equal values at adjacent triangles is constant. -/
theorem tri_const {V : Type} {P : Tri → V} (h : ∀ q : OTE, P q.1.2 = P q.1.1) (t : Tri) : P t = P triPlus := by
  have := tri_reach t
  induction this with
  | refl => rfl
  | tail _ hadj ih => rw [← ih]; exact h (oteOf _ _ hadj)

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- Evaluation of a function on oriented edges against a rational chain. -/
def evalChain (F : OTE → V) (c : PE) : V := c.coeff.sum fun p r => (r : ℂ) • F p

theorem evalChain_add (F : OTE → V) (x y : PE) : evalChain F (x + y) = evalChain F x + evalChain F y := by
  unfold evalChain
  rw [MonoidAlgebra.coeff_add]
  exact Finsupp.sum_add_index' (fun p => by simp) (fun p r₁ r₂ => by push_cast; rw [add_smul])

theorem evalChain_zero (F : OTE → V) : evalChain F 0 = 0 := by
  simp [evalChain]

theorem evalChain_sub (F : OTE → V) (x y : PE) : evalChain F (x - y) = evalChain F x - evalChain F y := by
  have := evalChain_add F (x - y) y
  rw [sub_add_cancel] at this
  rw [this]; abel

theorem evalChain_single (F : OTE → V) (p : OTE) (r : ℚ) :
    evalChain F (MonoidAlgebra.single p r) = (r : ℂ) • F p := by
  unfold evalChain
  rw [MonoidAlgebra.coeff_single, Finsupp.sum_single_index]
  simp

theorem evalChain_edgeVec (F : OTE → V) (hF : ∀ q : OTE, F q.swap = -F q) (p : OTE) :
    evalChain F (edgeVec p) = F p := by
  have e : edgeVec p = MonoidAlgebra.single p (1 / 2 : ℚ) - MonoidAlgebra.single p.swap (1 / 2 : ℚ) := by
    unfold edgeVec
    rw [smul_sub, MonoidAlgebra.smul_single, MonoidAlgebra.smul_single]
    simp
  rw [e, evalChain_sub, evalChain_single, evalChain_single, hF]
  push_cast
  rw [smul_neg, sub_neg_eq_add, ← add_smul]
  norm_num

/-- A fixed choice of chain `a t` with `d a t = [t] - [triPlus]`. -/
def bd (t : Tri) : P1 := Classical.choose (exists_boundary t)

theorem bd_spec (t : Tri) : d1.hom (bd t) = MonoidAlgebra.single t (1 : ℚ) - MonoidAlgebra.single triPlus 1 :=
  Classical.choose_spec (exists_boundary t)

theorem bd_triPlus : bd triPlus = 0 := by
  apply d1_injective
  rw [bd_spec, map_zero, sub_self]

theorem bd_edge (q : OTE) : ((bd q.1.2 - bd q.1.1 : P1) : PE) = edgeVec q := by
  have h : bd q.1.2 - bd q.1.1 = (⟨edgeVec q, edgeVec_mem q⟩ : P1) := by
    apply d1_injective
    rw [map_sub, bd_spec, bd_spec, d1_apply]
    change _ = dTilde.hom (edgeVec q)
    rw [dTilde_edgeVec]
    abel
  exact congrArg Subtype.val h

/-- The normalized potential of an antisymmetric edge function: `δ (pot F) = F`, `pot F triPlus = 0`. -/
def potFn (F : OTE → V) (t : Tri) : V := evalChain F ((bd t : P1) : PE)

theorem potFn_base (F : OTE → V) : potFn F triPlus = 0 := by
  simp [potFn, bd_triPlus, evalChain_zero]

theorem potFn_delta (F : OTE → V) (hF : ∀ q : OTE, F q.swap = -F q) (q : OTE) :
    potFn F q.1.2 - potFn F q.1.1 = F q := by
  unfold potFn
  rw [← evalChain_sub]
  have : (((bd q.1.2 : P1) : PE) - ((bd q.1.1 : P1) : PE)) = ((bd q.1.2 - bd q.1.1 : P1) : PE) := rfl
  rw [this, bd_edge, evalChain_edgeVec F hF]

/-- Uniqueness of the normalized potential. -/
theorem potFn_unique (F : OTE → V) {P : Tri → V} (hP : ∀ q : OTE, P q.1.2 - P q.1.1 = F q) (h0 : P triPlus = 0)
    (hF : ∀ q : OTE, F q.swap = -F q) (t : Tri) : P t = potFn F t := by
  have : (fun t => P t - potFn F t) triPlus = 0 := by simp [h0, potFn_base]
  have h := tri_const (P := fun t => P t - potFn F t) (fun q => by
    have h1 := hP q
    have h2 := potFn_delta F hF q
    show P q.1.2 - potFn F q.1.2 = P q.1.1 - potFn F q.1.1
    linear_combination (norm := module) h1 - h2) t
  have h' : P t - potFn F t = 0 := h.trans this
  exact sub_eq_zero.mp h'

end Tree


section Group

variable {Γ : Subgroup IntegralGL} {E : Type} [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ Γ E)

/-- The normalized potential of a cochain. -/
def pot (F : C1 ρ) : Tri → E := potFn F.1

theorem pot_base (F : C1 ρ) : pot ρ F triPlus = 0 := potFn_base F.1

theorem pot_delta (F : C1 ρ) (q : OTE) : pot ρ F q.1.2 - pot ρ F q.1.1 = F.1 q := potFn_delta F.1 F.2.2 q

theorem pot_unique (F : C1 ρ) {P : Tri → E} (hP : ∀ q : OTE, P q.1.2 - P q.1.1 = F.1 q) (h0 : P triPlus = 0) (t : Tri) :
    P t = pot ρ F t := potFn_unique F.1 hP h0 F.2.2 t

theorem pot_add (F F' : C1 ρ) (t : Tri) : pot ρ (F + F') t = pot ρ F t + pot ρ F' t :=
  (pot_unique ρ (F + F') (P := fun t => pot ρ F t + pot ρ F' t)
    (fun q => by
      have h1 := pot_delta ρ F q
      have h2 := pot_delta ρ F' q
      show pot ρ F q.1.2 + pot ρ F' q.1.2 - (pot ρ F q.1.1 + pot ρ F' q.1.1) = F.1 q + F'.1 q
      linear_combination (norm := module) h1 + h2)
    (by simp [pot_base]) t).symm

theorem pot_smul_scalar (c : ℂ) (F : C1 ρ) (t : Tri) : pot ρ (c • F) t = c • pot ρ F t :=
  (pot_unique ρ (c • F) (P := fun t => c • pot ρ F t)
    (fun q => by
      have h1 := pot_delta ρ F q
      show c • pot ρ F q.1.2 - c • pot ρ F q.1.1 = c • F.1 q
      rw [← smul_sub, h1])
    (by simp [pot_base]) t).symm

/-- Twisted equivariance of the potential: `pot F (γ t) = γ · pot F t + pot F (γ t₀)`. -/
theorem pot_smul (F : C1 ρ) (γ : Γ) (t : Tri) :
    pot ρ F ((γ : IntegralGL) • t) = ρ γ (pot ρ F t) + pot ρ F ((γ : IntegralGL) • triPlus) := by
  have h := tri_const (P := fun t => pot ρ F ((γ : IntegralGL) • t) - ρ γ (pot ρ F t)) (fun q => by
    have h1 := pot_delta ρ F ((γ : IntegralGL) • q)
    have h2 := pot_delta ρ F q
    have h3 : F.1 ((γ : IntegralGL) • q) = ρ γ (F.1 q) := F.2.1 γ q
    show pot ρ F ((γ : IntegralGL) • q.1.2) - ρ γ (pot ρ F q.1.2) = pot ρ F ((γ : IntegralGL) • q.1.1) - ρ γ (pot ρ F q.1.1)
    have h4 : ρ γ (pot ρ F q.1.2 - pot ρ F q.1.1) = ρ γ (F.1 q) := by rw [h2]
    rw [map_sub] at h4
    change pot ρ F ((γ : IntegralGL) • q.1.2) - pot ρ F ((γ : IntegralGL) • q.1.1) = F.1 ((γ : IntegralGL) • q) at h1
    linear_combination (norm := module) h1 - h4 + h3) t
  simp only [pot_base, map_zero, sub_zero] at h
  rw [← h]; abel

/-- The group cocycle of a cochain: the path sum from the base triangle to `γ · (base triangle)`. -/
def coc (F : C1 ρ) : Γ → E := fun γ => pot ρ F ((γ : IntegralGL) • triPlus)

theorem coc_mul (F : C1 ρ) (γ δ : Γ) : coc ρ F (γ * δ) = ρ γ (coc ρ F δ) + coc ρ F γ := by
  unfold coc
  have : (((γ * δ : Γ) : IntegralGL)) • triPlus = (γ : IntegralGL) • ((δ : IntegralGL) • triPlus) := by
    rw [← mul_smul]; rfl
  rw [this, pot_smul]

/-- `coc` as a linear map. -/
def cocL : C1 ρ →ₗ[ℂ] (Γ → E) where
  toFun F := coc ρ F
  map_add' F F' := by funext γ; simp [coc, pot_add]
  map_smul' c F := by funext γ; simp [coc, pot_smul_scalar]

end Group

section Cohomology

variable {Γ : Subgroup IntegralGL} (A : Rep ℂ Γ)

theorem cocL_mem (F : C1 A.ρ) : cocL A.ρ F ∈ groupCohomology.cocycles₁ A := by
  rw [groupCohomology.mem_cocycles₁_iff]
  intro γ δ
  exact coc_mul A.ρ F γ δ

/-- The cocycle of a cochain, as an element of Mathlib's `cocycles₁`. -/
def cocycleMap : C1 A.ρ →ₗ[ℂ] groupCohomology.cocycles₁ A :=
  LinearMap.codRestrict _ (cocL A.ρ) (cocL_mem A)

/-- **The comparison map** `C¹ → H¹(Γ, A)` (Mathlib's `groupCohomology.H1`): the class of the path-sum cocycle. -/
def cohMap : C1 A.ρ →ₗ[ℂ] groupCohomology.H1 A :=
  (groupCohomology.H1π A).hom.comp (cocycleMap A)

theorem cohMap_apply (F : C1 A.ρ) : cohMap A F = groupCohomology.H1π A (cocycleMap A F) := rfl


theorem cocycleMap_apply (F : C1 A.ρ) (γ : Γ) : (cocycleMap A F : Γ → A) γ = coc A.ρ F γ := rfl

/-- The class of the path-sum cocycle vanishes iff the cochain is a coboundary `δ H`. -/
theorem cohMap_eq_zero_iff (F : C1 A.ρ) : cohMap A F = 0 ↔ F ∈ LinearMap.range (delta A.ρ) := by
  rw [cohMap_apply, groupCohomology.H1π_eq_zero_iff]
  constructor
  · rintro ⟨u, hu⟩
    have hu' : ∀ γ : Γ, coc A.ρ F γ = A.ρ γ u - u := fun γ => by
      have := congrFun hu γ
      simp only [groupCohomology.d₀₁_hom_apply] at this
      exact this.symm
    refine ⟨⟨fun t => pot A.ρ F t + u, ?_⟩, ?_⟩
    · intro γ t
      change pot A.ρ F ((γ : IntegralGL) • t) + u = A.ρ γ (pot A.ρ F t + u)
      rw [pot_smul, map_add]
      have := hu' γ
      unfold coc at this
      rw [this]
      abel
    · apply Subtype.ext
      funext q
      change (pot A.ρ F q.1.2 + u) - (pot A.ρ F q.1.1 + u) = F.1 q
      rw [← pot_delta A.ρ F q]
      abel
  · rintro ⟨H, rfl⟩
    refine ⟨H.1 triPlus, ?_⟩
    funext γ
    simp only [groupCohomology.d₀₁_hom_apply]
    have hP : ∀ t, H.1 t - H.1 triPlus = pot A.ρ (delta A.ρ H) t := fun t =>
      pot_unique A.ρ (delta A.ρ H) (P := fun t => H.1 t - H.1 triPlus) (fun q => by
        change H.1 q.1.2 - H.1 triPlus - (H.1 q.1.1 - H.1 triPlus) = H.1 q.1.2 - H.1 q.1.1
        abel) (by simp) t
    change A.ρ γ (H.1 triPlus) - H.1 triPlus = pot A.ρ (delta A.ρ H) ((γ : IntegralGL) • triPlus)
    rw [← hP]
    have := H.2 γ triPlus
    change H.1 ((γ : IntegralGL) • triPlus) = A.ρ γ (H.1 triPlus) at this
    rw [this]

variable (D : FareyData Γ)

include D in
/-- Every class of `H¹(Γ, A)` is the class of a path-sum cocycle. -/
theorem cohMap_surjective : Function.Surjective (cohMap A) := by
  intro x
  induction x using groupCohomology.H1_induction_on with
  | h f =>
    let S := D.RT
    let Hh : Tri → A := fun x => f (dec S x).2
    have hH : ∀ (γ : Γ) (x : Tri), Hh ((γ : IntegralGL) • x) = A.ρ γ (Hh x) + f γ := by
      intro γ x
      have h : dec S ((γ : IntegralGL) • x) = ((dec S x).1, γ * (dec S x).2) :=
        dec_eq S D.freeT (by simp only [mul_smul, dec_spec]; rfl)
      have hf := (groupCohomology.mem_cocycles₁_iff (A := A) f.1).1 f.2 γ (dec S x).2
      change f (dec S ((γ : IntegralGL) • x)).2 = _
      rw [h]
      exact hf
    let F : OTE → A := fun q => Hh q.1.2 - Hh q.1.1
    have hFeq : ∀ (γ : Γ) (q : OTE), F ((γ : IntegralGL) • q) = A.ρ γ (F q) := by
      intro γ q
      change Hh ((γ : IntegralGL) • q.1.2) - Hh ((γ : IntegralGL) • q.1.1) = A.ρ γ (Hh q.1.2 - Hh q.1.1)
      rw [hH, hH, map_sub]
      abel
    let F' : C1 A.ρ := ⟨F, hFeq, fun q => by
      change Hh q.1.1 - Hh q.1.2 = -(Hh q.1.2 - Hh q.1.1)
      abel⟩
    refine ⟨F', ?_⟩
    rw [cohMap_apply, groupCohomology.H1π_eq_iff]
    refine ⟨Hh triPlus, ?_⟩
    funext γ
    simp only [groupCohomology.d₀₁_hom_apply]
    have hP : ∀ t, Hh t - Hh triPlus = pot A.ρ F' t := fun t =>
      pot_unique A.ρ F' (P := fun t => Hh t - Hh triPlus) (fun q => by
        change Hh q.1.2 - Hh triPlus - (Hh q.1.1 - Hh triPlus) = Hh q.1.2 - Hh q.1.1
        abel) (by simp) t
    have e1 : (cocycleMap A F' : Γ → A) γ = pot A.ρ F' ((γ : IntegralGL) • triPlus) := rfl
    have e2 := hP ((γ : IntegralGL) • triPlus)
    have e3 := hH γ triPlus
    change A.ρ γ (Hh triPlus) - Hh triPlus = ((cocycleMap A F' : Γ → A) - (f : Γ → A)) γ
    rw [Pi.sub_apply, e1, ← e2, e3]
    abel

include D in
/-- **The dual Farey tree computes `H¹(Γ, A)`**: `C¹ / δ C⁰ ≃ H¹(Γ, A)` (path-sum cocycles). -/
def cohIso : (C1 A.ρ ⧸ LinearMap.range (delta A.ρ)) ≃ₗ[ℂ] groupCohomology.H1 A :=
  (Submodule.quotEquivOfEq _ _ (by
      ext F
      rw [LinearMap.mem_ker]
      exact (cohMap_eq_zero_iff A F).symm)).trans
    (LinearMap.quotKerEquivOfSurjective (cohMap A) (cohMap_surjective A D))

end Cohomology

section Natural

variable {Γ : Subgroup IntegralGL} {A B : Rep ℂ Γ}

/-- Push a cochain forward along a morphism of representations. -/
def C1.map (φ : A ⟶ B) : C1 A.ρ →ₗ[ℂ] C1 B.ρ where
  toFun F := ⟨fun q => φ.hom (F.1 q), fun γ q => by
      exact (congrArg φ.hom (F.2.1 γ q)).trans (Rep.hom_comm_apply φ γ (F.1 q)), fun q => by
      change φ.hom (F.1 q.swap) = -φ.hom (F.1 q)
      rw [F.2.2 q, map_neg]⟩
  map_add' F F' := by apply Subtype.ext; funext q; exact map_add _ _ _
  map_smul' c F := by apply Subtype.ext; funext q; exact map_smul _ _ _

theorem pot_map (φ : A ⟶ B) (F : C1 A.ρ) (t : Tri) : pot B.ρ (C1.map φ F) t = φ.hom (pot A.ρ F t) := by
  refine (pot_unique B.ρ (C1.map φ F) (P := fun t => φ.hom (pot A.ρ F t)) (fun q => ?_) (by simp [pot_base]) t).symm
  change φ.hom (pot A.ρ F q.1.2) - φ.hom (pot A.ρ F q.1.1) = φ.hom (F.1 q)
  rw [← map_sub, pot_delta]

/-- **Naturality in the coefficients** of the comparison `C¹ → H¹`. -/
theorem cohMap_natural (φ : A ⟶ B) (F : C1 A.ρ) :
    (groupCohomology.map (MonoidHom.id Γ) φ 1).hom (cohMap A F) = cohMap B (C1.map φ F) := by
  rw [cohMap_apply, cohMap_apply, groupCohomology.H1π_comp_map_apply]
  congr 1
  apply Subtype.ext
  funext γ
  change φ.hom (coc A.ρ F γ) = coc B.ρ (C1.map φ F) γ
  unfold coc
  rw [pot_map]

end Natural


end TernaryPeriodPolynomials.Argument.GammaNParabolicPD
