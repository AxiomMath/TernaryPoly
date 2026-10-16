module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.Transfer

@[expose] public section


/-!
# Hecke operators on group homology and their naturality in the coefficient module

Formalized by Claude Sonnet 5.5.

* `HeckeDatum ι g`: a finite-index subgroup `S ≤ Γ` and `f : S → Γ` with `ι (f s) = g ι(s) g⁻¹` (`ι : Γ → Ĝ`, `g ∈ Ĝ`).
* `heckeOp D M n : Hₙ(Γ, M) → Hₙ(Γ, M)` for a `Ĝ`-representation `M`: the transfer `trR` to `S` (Transfer.lean), the transport `m ↦ g m`
  (`corrMap`, a morphism `Res_S M → Res_f M`) and corestriction `groupHomology.map f`.  On `H₀` this is `[m] ↦ ∑_{S x ∈ S\Γ} [g x m]`,
  a sum over the right cosets `Γ g x` of `Γ g Γ`, i.e. over `Γ\ΓgΓ`.
* `trR_nat`, `eK_nat`, `eN_nat`, `betaA_nat`, `inhomIso_nat`: naturality of the transfer and of the bar-resolution comparisons in the
  coefficient module; `heckeOp_nat`: for a morphism `ψ : M → M'` of `Ĝ`-representations the Hecke operators commute with
  `Hₙ(ψ)`.  Hence the image of `Hₙ(Γ, M) → Hₙ(Γ, M'')` for a morphism of `Ĝ`-modules is Hecke-stable (`range_heckeOp_stable`).
-/

open CategoryTheory Representation Representation.Coinvariants MonoidalCategory
open TernaryPeriodPolynomials.Argument.GroupHomology

noncomputable section

universe u

namespace TernaryPeriodPolynomials.Argument.HeckeHomology

open scoped Classical

variable {k K : Type u} [Field k] [Group K]

/-- `YA` as a functor in `A`. -/
def YAmap {A B : Rep.{u} k K} (φ : A ⟶ B) : YA A ⟶ YA B where
  f n := φ ▷ ((Rep.barComplex k K).X n)
  comm' i j _ := by
    change φ ▷ _ ≫ B ◁ (Rep.barComplex k K).d i j = A ◁ (Rep.barComplex k K).d i j ≫ φ ▷ _
    exact (whisker_exchange _ _).symm

theorem inhomIso_nat {A B : Rep.{u} k K} (φ : A ⟶ B) :
    groupHomology.chainsMap (MonoidHom.id K) φ ≫ (groupHomology.inhomogeneousChainsIso B).hom =
      (groupHomology.inhomogeneousChainsIso A).hom ≫
        ((cK (k := k) (K := K)).mapHomologicalComplex (ComplexShape.down ℕ)).map (YAmap φ) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine groupHomology.inhomogeneousChains.ext fun x => ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun a => ?_)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_ofHom, Finsupp.lsingle_apply]
  have eL := groupHomology.chainsMap_f_single (MonoidHom.id K) φ n x a
  have eR := inhomIso_hom_f_single A n x a
  have eB := inhomIso_hom_f_single B n (MonoidHom.id K ∘ x) (φ.hom a)
  rw [eL, eB]
  change _ = ((((cK (k := k) (K := K)).mapHomologicalComplex (ComplexShape.down ℕ)).map (YAmap φ)).f n).hom
    (((groupHomology.inhomogeneousChainsIso A).hom.f n).hom (Finsupp.single x a))
  rw [eR]
  rfl

variable (N : Subgroup K)

/-- `betaA` with its codomain written as the complex `CxN`. -/
def betaA' (A : Rep.{u} k K) :
    groupHomology.inhomogeneousChains (Rep.res N.subtype A) ⟶ CxN N (YA A) := betaA N A

theorem betaA_nat {A B : Rep.{u} k K} (φ : A ⟶ B) :
    groupHomology.chainsMap (MonoidHom.id N) ((Rep.resFunctor N.subtype).map φ) ≫ betaA' N B =
      betaA' N A ≫ (((cN (k := k) N).mapHomologicalComplex (ComplexShape.down ℕ)).map (YAmap φ)) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine groupHomology.inhomogeneousChains.ext fun x => ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun a => ?_)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_ofHom, Finsupp.lsingle_apply]
  have eL := groupHomology.chainsMap_f_single (A := Rep.res N.subtype A) (B := Rep.res N.subtype B) (MonoidHom.id N) (Rep.resMap N.subtype φ) n x a
  have eB := betaA_single N B n (MonoidHom.id N ∘ x) ((Rep.resMap N.subtype φ).hom a)
  have eA := betaA_single N A n x a
  rw [eL]
  change ((betaA N B).f n).hom (Finsupp.single (MonoidHom.id N ∘ x) ((Rep.resMap N.subtype φ).hom a)) = ((((cN (k := k) N).mapHomologicalComplex (ComplexShape.down ℕ)).map (YAmap φ)).f n).hom
    (((betaA N A).f n).hom (Finsupp.single x a))
  rw [eB, eA]
  rfl

variable [N.FiniteIndex]

theorem eK_nat {A B : Rep.{u} k K} (φ : A ⟶ B) (n : ℕ) :
    groupHomology.map (MonoidHom.id K) φ n ≫ (eK B n).hom =
      (eK A n).hom ≫ HomologicalComplex.homologyMap
        (((cK (k := k) (K := K)).mapHomologicalComplex (ComplexShape.down ℕ)).map (YAmap φ)) n := by
  rw [groupHomologyIso_bar_hom, groupHomologyIso_bar_hom]
  exact (HomologicalComplex.homologyMap_comp (groupHomology.chainsMap (MonoidHom.id K) φ)
      (groupHomology.inhomogeneousChainsIso B).hom n).symm.trans
    ((congrArg (fun c => HomologicalComplex.homologyMap c n) (inhomIso_nat φ)).trans
      (HomologicalComplex.homologyMap_comp (groupHomology.inhomogeneousChainsIso A).hom _ n))

omit [N.FiniteIndex] in
theorem eN_nat {A B : Rep.{u} k K} (φ : A ⟶ B) (n : ℕ) :
    groupHomology.map (MonoidHom.id N) ((Rep.resFunctor N.subtype).map φ) n ≫ (eN N B n).hom =
      (eN N A n).hom ≫ HomologicalComplex.homologyMap
        (((cN (k := k) N).mapHomologicalComplex (ComplexShape.down ℕ)).map (YAmap φ)) n := by
  rw [eN_hom, eN_hom]
  have hb := betaA_nat N φ
  have h1 := congrArg (fun c => HomologicalComplex.homologyMap c n) hb
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h1
  exact h1

theorem TYR_nat {A B : Rep.{u} k K} (φ : A ⟶ B) :
    ((cK (k := k) (K := K)).mapHomologicalComplex (ComplexShape.down ℕ)).map (YAmap φ) ≫ TYR N (YA B) =
      TYR N (YA A) ≫ ((cN (k := k) N).mapHomologicalComplex (ComplexShape.down ℕ)).map (YAmap φ) :=
  (NatTrans.mapHomologicalComplex (tNatR N) (ComplexShape.down ℕ)).naturality (YAmap φ)

/-- **Naturality of the transfer in the coefficient module.** -/
theorem trR_nat {A B : Rep.{u} k K} (φ : A ⟶ B) (n : ℕ) :
    groupHomology.map (MonoidHom.id K) φ n ≫ trR N B n =
      trR N A n ≫ groupHomology.map (MonoidHom.id N) ((Rep.resFunctor N.subtype).map φ) n := by
  have h1 := eK_nat φ n
  have h2 := eN_nat N φ n
  have h3 : (eN N A n).inv ≫ groupHomology.map (MonoidHom.id N) ((Rep.resFunctor N.subtype).map φ) n =
      HomologicalComplex.homologyMap
        (((cN (k := k) N).mapHomologicalComplex (ComplexShape.down ℕ)).map (YAmap φ)) n ≫
        (eN N B n).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← h2]
    simp
  unfold trR
  simp only [Category.assoc]
  rw [h3, ← Category.assoc (HomologicalComplex.homologyMap (TYR N (YA A)) n),
    ← HomologicalComplex.homologyMap_comp, ← TYR_nat N φ, HomologicalComplex.homologyMap_comp]
  rw [← Category.assoc, ← Category.assoc, h1]
  simp [Category.assoc]

/-- Data of a Hecke correspondence `Γ ← S → Γ` of `ι : Γ → Ĝ` and `g ∈ Ĝ`: a finite-index subgroup `S` and
`f : S → Γ` with `ι (f s) = g ι(s) g⁻¹`. -/
structure HeckeDatum {Γ Ĝ : Type} [Group Γ] [Group Ĝ] (ι : Γ →* Ĝ) (g : Ĝ) where
  S : Subgroup Γ
  finiteIndex : S.FiniteIndex
  f : S →* Γ
  hf : ∀ s : S, ι (f s) = g * ι s * g⁻¹

variable {Γ Ĝ : Type} [Group Γ] [Group Ĝ] {ι : Γ →* Ĝ} {g : Ĝ}

/-- The "rational matrix transport" `m ↦ g m`, as a morphism `Res_S M → Res_f M`. -/
def corrMap (D : HeckeDatum ι g) (M : Rep.{0} ℚ Ĝ) :
    Rep.res D.S.subtype (Rep.res ι M) ⟶ Rep.res D.f (Rep.res ι M) :=
  Rep.ofHom ⟨M.ρ g, fun s => by
    ext a
    change M.ρ g (M.ρ (ι s.1) a) = M.ρ (ι (D.f s)) (M.ρ g a)
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, D.hf s]
    congr 1
    group⟩

/-- **The Hecke operator** `[ΓgΓ]` on `Hₙ(Γ, M)`: transfer to `S`, transport by `g`, corestriction along `f`. -/
def heckeOp (D : HeckeDatum ι g) (M : Rep.{0} ℚ Ĝ) (n : ℕ) :
    groupHomology (Rep.res ι M) n ⟶ groupHomology (Rep.res ι M) n :=
  haveI := D.finiteIndex
  trR D.S (Rep.res ι M) n ≫ groupHomology.map D.f (corrMap D M) n

theorem corr_nat (D : HeckeDatum ι g) {M M' : Rep.{0} ℚ Ĝ} (ψ : M ⟶ M') (n : ℕ) :
    groupHomology.map D.f (corrMap D M) n ≫
        groupHomology.map (MonoidHom.id Γ) ((Rep.resFunctor ι).map ψ) n =
      groupHomology.map (MonoidHom.id D.S)
          ((Rep.resFunctor D.S.subtype).map ((Rep.resFunctor ι).map ψ)) n ≫
        groupHomology.map D.f (corrMap D M') n := by
  have hL := groupHomology.map_comp (A := Rep.res D.S.subtype (Rep.res ι M)) (B := Rep.res ι M)
    (C := Rep.res ι M') D.f (MonoidHom.id Γ) (corrMap D M) ((Rep.resFunctor ι).map ψ) n
  have hR := groupHomology.map_comp (A := Rep.res D.S.subtype (Rep.res ι M))
    (B := Rep.res D.S.subtype (Rep.res ι M')) (C := Rep.res ι M') (MonoidHom.id D.S) D.f
    ((Rep.resFunctor D.S.subtype).map ((Rep.resFunctor ι).map ψ)) (corrMap D M') n
  rw [← hL, ← hR]
  refine groupHomology.map_congr rfl ?_ n
  ext a
  exact (Rep.hom_comm_apply ψ g a)

theorem heckeOp_nat (D : HeckeDatum ι g) {M M' : Rep.{0} ℚ Ĝ} (ψ : M ⟶ M') (n : ℕ) :
    heckeOp D M n ≫ groupHomology.map (MonoidHom.id Γ) ((Rep.resFunctor ι).map ψ) n =
      groupHomology.map (MonoidHom.id Γ) ((Rep.resFunctor ι).map ψ) n ≫ heckeOp D M' n := by
  have := D.finiteIndex
  unfold heckeOp
  rw [Category.assoc, corr_nat D ψ n, ← Category.assoc, ← Category.assoc]
  congr 1
  exact (trR_nat D.S ((Rep.resFunctor ι).map ψ) n).symm

/-- The image of `Hₙ(Γ, M) → Hₙ(Γ, M'')` induced by a morphism of `Ĝ`-representations is stable under every Hecke
operator. -/
theorem range_heckeOp_stable (D : HeckeDatum ι g) {M M' : Rep.{0} ℚ Ĝ} (ψ : M ⟶ M') (n : ℕ)
    (x : groupHomology (Rep.res ι M') n)
    (hx : x ∈ LinearMap.range (groupHomology.map (MonoidHom.id Γ) ((Rep.resFunctor ι).map ψ) n).hom) :
    (heckeOp D M' n).hom x ∈
      LinearMap.range (groupHomology.map (MonoidHom.id Γ) ((Rep.resFunctor ι).map ψ) n).hom := by
  obtain ⟨y, rfl⟩ := hx
  have h := congrArg (fun φ => φ.hom y) (heckeOp_nat D ψ n)
  exact ⟨(heckeOp D M n).hom y, h⟩

end TernaryPeriodPolynomials.Argument.HeckeHomology
