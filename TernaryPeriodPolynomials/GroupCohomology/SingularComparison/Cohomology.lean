module

public import TernaryPeriodPolynomials.GroupCohomology.SingularComparison.CohHomotopy
public import TernaryPeriodPolynomials.GroupCohomology.SingularComparison.Conjugation

@[expose] public section


/-!
# Cohomology bridge: invariant homogeneous cochains versus Mathlib's `groupCohomology`

Formalized by Claude Sonnet 5.5.

For a subgroup `Λ ≤ G`, `Inv Λ n` is the space of `Λ`-invariant functions `G^{n+1} → ℂ` (the equivariant
cochains of the homogeneous resolution, `homEquiv`: `Hom_Λ(Res std_n, ℂ) ≃ Inv Λ n`).  `dInv` is the coboundary
`(δF)(x) = F(∂x)` (`dInv_apply`).  The comparison with Mathlib goes through the cochain map
`Theta Λ : Hom(Res std, ℂ) ⟶ inhomogeneousCochains (Rep.trivial ℂ Λ ℂ)`, `F ↦ (y ↦ F(1, y₁, y₁y₂, …))`
(`Theta_apply`), which induces an isomorphism on cohomology because the bar resolution of `Λ` and the
restricted standard resolution of `G` are projective resolutions of the same representation
(`isIso_Theta`, from `CohHomotopy`).  `cohClass Λ j` is the resulting class map from the invariant
`(j+1)`-cocycles `cohCycles Λ j` to `groupCohomology (Rep.trivial ℂ Λ ℂ) (j+1)`: it is surjective
(`cohClass_surjective`) with kernel exactly the coboundaries of invariant cochains (`cohClass_eq_zero_iff`),
and natural in the subgroup (`cohClass_res`: Mathlib's restriction along `Λ' ≤ Λ`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HomologyBridge

open CategoryTheory Representation MonoidalCategory Rep
open TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains (NullChains)
open TernaryPeriodPolynomials.BoundaryDuality.ChainCalculus (Chains leftTranslate)

variable {G : Type} [Group G] (Λ : Subgroup G)

/-- The restriction to `Λ` of the standard resolution of `G`. -/
abbrev Pstd :=
  (Rep.resFunctor Λ.subtype).mapProjectiveResolution (Rep.standardResolution ℂ G)

/-- The chain map from the bar resolution of `Λ` to the restricted standard resolution of `G`. -/
def xi : (Rep.barResolution ℂ Λ).complex ⟶ (Pstd Λ).complex :=
  barMap (k := ℂ) Λ.subtype ≫
    ((Rep.resFunctor Λ.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).map
      (Rep.barComplex.isoStandardComplex ℂ G).hom

theorem xi_aug : (xi Λ).f 0 ≫ (Pstd Λ).π.f 0 = (Rep.barResolution ℂ Λ).π.f 0 := by
  have h := barMap_pi (k := ℂ) Λ
  refine Eq.trans ?_ h
  have e : ((resFunctor Λ.subtype).mapProjectiveResolution (barResolution ℂ G)).π.f 0 =
      (((resFunctor Λ.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (barComplex.isoStandardComplex ℂ G).hom).f 0 ≫ (Pstd Λ).π.f 0 := by
    change (((resFunctor Λ.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).map
        ((barComplex.isoStandardComplex ℂ G).hom ≫ standardComplex.εToSingle₀ ℂ G) ≫
          (HomologicalComplex.singleMapHomologicalComplex (resFunctor Λ.subtype) (ComplexShape.down ℕ) 0).hom.app
              (Rep.trivial ℂ G ℂ)).f 0 = _
    rw [Functor.map_comp]
    rfl
  rw [e]
  rfl

/-- The inhomogeneous cochains versus `Hom(bar resolution, ℂ)`, with the resolution as a
`ProjectiveResolution`. -/
def inhomIso : groupCohomology.inhomogeneousCochains (Rep.trivial ℂ Λ ℂ) ≅
    (Rep.barResolution ℂ Λ).complex.linearYonedaObj ℂ (Rep.trivial ℂ Λ ℂ) :=
  groupCohomology.inhomogeneousCochainsIso (Rep.trivial ℂ Λ ℂ)

/-- The cochain map from `Hom(Res std, ℂ)` to the inhomogeneous cochains of `Λ`. -/
def Theta : ((Pstd Λ).complex.linearYonedaObj ℂ (Rep.trivial ℂ Λ ℂ)) ⟶
    groupCohomology.inhomogeneousCochains (Rep.trivial ℂ Λ ℂ) :=
  yMap (xi Λ) (Rep.trivial ℂ Λ ℂ) ≫ (inhomIso Λ).inv

instance isIso_Theta (n : ℕ) : IsIso (HomologicalComplex.homologyMap (Theta Λ) n) := by
  have h1 := isIso_homologyMap_yMap_res (Rep.barResolution ℂ Λ) (Pstd Λ) (xi Λ) (xi_aug Λ)
    (Rep.trivial ℂ Λ ℂ) n
  have h2 : IsIso (HomologicalComplex.homologyMap (inhomIso Λ).inv n) := inferInstance
  unfold Theta
  rw [HomologicalComplex.homologyMap_comp]
  infer_instance

/-- `Λ`-invariant functions on `(n+1)`-tuples of vertices. -/
def Inv (n : ℕ) : Submodule ℂ ((Fin (n + 1) → G) → ℂ) where
  carrier := {F | ∀ γ ∈ Λ, ∀ x, F (fun i => γ * x i) = F x}
  add_mem' := fun {a b} ha hb γ hγ x => by
    simp only [Pi.add_apply]; rw [ha γ hγ x, hb γ hγ x]
  zero_mem' := fun γ hγ x => rfl
  smul_mem' := fun c a ha γ hγ x => by
    simp only [Pi.smul_apply]; rw [ha γ hγ x]

theorem mem_Inv {n : ℕ} {F : (Fin (n + 1) → G) → ℂ} :
    F ∈ Inv Λ n ↔ ∀ γ ∈ Λ, ∀ x, F (fun i => γ * x i) = F x := Iff.rfl

/-- The `n`-th term of the restricted standard resolution, as the permutation module. -/
abbrev XL (n : ℕ) : Rep ℂ Λ := (Pstd Λ).complex.X n

example (n : ℕ) : (XL Λ n).V = MonoidAlgebra ℂ (Fin (n + 1) → G) := rfl

/-- The value of an equivariant map on the basis vector of a tuple. -/
def evalFun {n : ℕ} (φ : XL Λ n ⟶ Rep.trivial ℂ Λ ℂ) : (Fin (n + 1) → G) → ℂ :=
  fun x => φ.hom (MonoidAlgebra.single x (1 : ℂ))

theorem evalFun_inv {n : ℕ} (φ : XL Λ n ⟶ Rep.trivial ℂ Λ ℂ) : evalFun Λ φ ∈ Inv Λ n := by
  intro γ hγ x
  have h := Rep.hom_comm_apply φ ⟨γ, hγ⟩ (MonoidAlgebra.single x (1 : ℂ))
  have e : (XL Λ n).ρ ⟨γ, hγ⟩ (MonoidAlgebra.single x (1 : ℂ)) =
      MonoidAlgebra.single (fun i => γ * x i) (1 : ℂ) := Xstd_act n γ x 1
  rw [e] at h
  exact h

/-- Evaluation on basis vectors, as a linear map into the invariant functions. -/
def evalInv (n : ℕ) : (XL Λ n ⟶ Rep.trivial ℂ Λ ℂ) →ₗ[ℂ] Inv Λ n where
  toFun φ := ⟨evalFun Λ φ, evalFun_inv Λ φ⟩
  map_add' φ ψ := by
    apply Subtype.ext; funext x; rfl
  map_smul' c φ := by
    apply Subtype.ext; funext x; rfl

theorem lc_actC {n : ℕ} {F : (Fin (n + 1) → G) → ℂ} (hF : F ∈ Inv Λ n) (γ : Λ) (c : Chains G n) :
    Finsupp.linearCombination ℂ F (actC γ.1 n c) = Finsupp.linearCombination ℂ F c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single x r =>
    rw [actC_single]
    simp only [Finsupp.linearCombination_single, smul_eq_mul]
    rw [show (γ.1 • x) = fun i => γ.1 * x i from rfl, hF γ.1 γ.2 x]

/-- Linear combination as a map out of the carrier of the permutation module. -/
def lcMap {n : ℕ} (F : (Fin (n + 1) → G) → ℂ) : ↑(XL Λ n) →ₗ[ℂ] ℂ :=
  Finsupp.linearCombination ℂ F ∘ₗ (toMA (G := G) n).symm.toLinearMap

theorem lcMap_toMA {n : ℕ} (F : (Fin (n + 1) → G) → ℂ) (c : Chains G n) :
    lcMap Λ F (toMA n c) = Finsupp.linearCombination ℂ F c := by
  change Finsupp.linearCombination ℂ F ((toMA (G := G) n).symm (toMA n c)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem lc_equivariant {n : ℕ} {F : (Fin (n + 1) → G) → ℂ} (hF : F ∈ Inv Λ n) (γ : Λ)
    (v : ↑(XL Λ n)) : lcMap Λ F ((XL Λ n).ρ γ v) = lcMap Λ F v := by
  obtain ⟨c, rfl⟩ := (toMA (G := G) n).surjective v
  have e : (XL Λ n).ρ γ (toMA n c) = toMA n (actC γ.1 n c) := (toMA_actC γ.1 n c).symm
  rw [e, lcMap_toMA, lcMap_toMA, lc_actC Λ hF]

/-- The equivariant map determined by an invariant function. -/
def invHom {n : ℕ} (F : Inv Λ n) : XL Λ n ⟶ Rep.trivial ℂ Λ ℂ :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap (ρ := (XL Λ n).ρ)
    (σ := (Rep.trivial ℂ Λ ℂ).ρ) (lcMap Λ F.1) (fun γ v => lc_equivariant Λ F.2 γ v))

theorem evalInv_invHom {n : ℕ} (F : Inv Λ n) : evalInv Λ n (invHom Λ F) = F := by
  apply Subtype.ext; funext x
  change lcMap Λ F.1 (toMA n (Finsupp.single x (1 : ℂ))) = F.1 x
  rw [lcMap_toMA]
  simp

theorem evalInv_injective (n : ℕ) : Function.Injective (evalInv Λ n) := by
  intro φ ψ h
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  have hx : ∀ x : Fin (n + 1) → G,
      φ.hom (toMA n (Finsupp.single x (1 : ℂ))) = ψ.hom (toMA n (Finsupp.single x (1 : ℂ))) := fun x =>
    congrFun (congrArg Subtype.val h) x
  have key : φ.hom.toLinearMap ∘ₗ (toMA (G := G) n).toLinearMap =
      ψ.hom.toLinearMap ∘ₗ (toMA (G := G) n).toLinearMap := by
    apply Finsupp.lhom_ext
    intro x r
    have e : (Finsupp.single x r : Chains G n) = r • Finsupp.single x (1 : ℂ) := by simp
    rw [e, map_smul, map_smul]
    exact congrArg (r • ·) (hx x)
  apply LinearMap.ext
  intro v
  obtain ⟨c, rfl⟩ := (toMA (G := G) n).surjective v
  exact LinearMap.congr_fun key c

/-- Equivariant maps `Res std_n → ℂ` are the invariant functions on `(n+1)`-tuples. -/
def homEquiv (n : ℕ) : (XL Λ n ⟶ Rep.trivial ℂ Λ ℂ) ≃ₗ[ℂ] Inv Λ n :=
  LinearEquiv.ofBijective (evalInv Λ n) ⟨evalInv_injective Λ n, fun F => ⟨invHom Λ F, evalInv_invHom Λ F⟩⟩

/-- The cochain complex `Hom(Res std, ℂ)`. -/
abbrev Kc : CochainComplex (ModuleCat ℂ) ℕ :=
  (Pstd Λ).complex.linearYonedaObj ℂ (Rep.trivial ℂ Λ ℂ)

/-- The short complex around degree `j + 1` of `Hom(Res std, ℂ)`. -/
abbrev Sc (j : ℕ) : ShortComplex (ModuleCat ℂ) := (Kc Λ).sc' j (j + 1) (j + 2)

/-- The identification of the `i`-th term with the invariant functions. -/
def sigmaC (i : ℕ) : Inv Λ i →ₗ[ℂ] ↑((Kc Λ).X i) := (homEquiv Λ i).symm.toLinearMap

theorem sigmaC_surjective (i : ℕ) : Function.Surjective (sigmaC Λ i) :=
  (homEquiv Λ i).symm.surjective

/-- The coboundary on invariant functions. -/
def dInv (i : ℕ) : Inv Λ i →ₗ[ℂ] Inv Λ (i + 1) :=
  (homEquiv Λ (i + 1)).toLinearMap ∘ₗ ((Kc Λ).d i (i + 1)).hom ∘ₗ sigmaC Λ i

theorem sigmaC_d (i : ℕ) (F : Inv Λ i) :
    ((Kc Λ).d i (i + 1)).hom (sigmaC Λ i F) = sigmaC Λ (i + 1) (dInv Λ i F) := by
  exact (LinearEquiv.symm_apply_apply (homEquiv Λ (i + 1)) _).symm

theorem hom_toMA {n : ℕ} (φ : XL Λ n ⟶ Rep.trivial ℂ Λ ℂ) (c : Chains G n) :
    φ.hom (toMA n c) = Finsupp.linearCombination ℂ (evalFun Λ φ) c := by
  have h : φ = invHom Λ (evalInv Λ n φ) := (evalInv_injective Λ n (evalInv_invHom Λ _)).symm
  calc φ.hom (toMA n c) = (invHom Λ (evalInv Λ n φ)).hom (toMA n c) :=
        congrArg (fun ψ => ψ.hom (toMA n c)) h
    _ = lcMap Λ (evalFun Λ φ) (toMA n c) := rfl
    _ = _ := lcMap_toMA Λ _ c

/-- The coboundary is the alternating sum over faces: `(δF)(x) = F(∂ x)`. -/
theorem dInv_apply (i : ℕ) (F : Inv Λ i) (x : Fin (i + 2) → G) :
    (dInv Λ i F).1 x = Finsupp.linearCombination ℂ F.1
      (TernaryPeriodPolynomials.TopVanishing.homogeneousBoundary (i + 1)
        (Finsupp.single x (1 : ℂ))) := by
  set ψ := (homEquiv Λ i).symm F with hψ
  have hF : evalFun Λ ψ = F.1 := by
    have := (homEquiv Λ i).apply_symm_apply F
    exact congrArg Subtype.val this
  change (((Pstd Λ).complex.d (i + 1) i ≫ ψ).hom (MonoidAlgebra.single x (1 : ℂ))) = _
  have e : ((Pstd Λ).complex.d (i + 1) i).hom (MonoidAlgebra.single x (1 : ℂ)) =
      toMA i (TernaryPeriodPolynomials.TopVanishing.homogeneousBoundary (i + 1)
        (Finsupp.single x (1 : ℂ))) := by
    have := toMA_boundary (G := G) i (Finsupp.single x (1 : ℂ))
    exact this
  calc (((Pstd Λ).complex.d (i + 1) i ≫ ψ).hom (MonoidAlgebra.single x (1 : ℂ)))
      = ψ.hom (((Pstd Λ).complex.d (i + 1) i).hom (MonoidAlgebra.single x (1 : ℂ))) := rfl
    _ = ψ.hom (toMA i (TernaryPeriodPolynomials.TopVanishing.homogeneousBoundary (i + 1)
        (Finsupp.single x (1 : ℂ)))) := by rw [e]
    _ = _ := by rw [hom_toMA, hF]

theorem sc_h₁ (j : ℕ) (m : Inv Λ j) : (Sc Λ j).f.hom (sigmaC Λ j m) = sigmaC Λ (j + 1) (dInv Λ j m) :=
  sigmaC_d Λ j m

theorem sc_h₂ (j : ℕ) (m : Inv Λ (j + 1)) :
    (Sc Λ j).g.hom (sigmaC Λ (j + 1) m) = sigmaC Λ (j + 2) (dInv Λ (j + 1) m) :=
  sigmaC_d Λ (j + 1) m

/-- Invariant `(j+1)`-cochains with vanishing coboundary. -/
abbrev cohCycles (j : ℕ) : Submodule ℂ (Inv Λ (j + 1)) :=
  coverCycles (Sc Λ j) (sigmaC Λ (j + 2)) (dInv Λ (j + 1))

theorem mem_cohCycles (j : ℕ) (F : Inv Λ (j + 1)) : F ∈ cohCycles Λ j ↔ dInv Λ (j + 1) F = 0 := by
  change sigmaC Λ (j + 2) (dInv Λ (j + 1) F) = 0 ↔ _
  exact (map_eq_zero_iff _ (homEquiv Λ (j + 2)).symm.injective)

/-- `H^{j+1}` of `Hom(Res std, ℂ)` as the homology of the short complex around it. -/
def cohIso0 (j : ℕ) : (Kc Λ).homology (j + 1) ≅ (Sc Λ j).homology :=
  HomologicalComplex.homologyIsoSc' _ j (j + 1) (j + 2) (CochainComplex.prev_nat_succ j)
    (CochainComplex.next ℕ (j + 1))

/-- The class of an invariant cocycle of degree `j + 1` in Mathlib's `H^{j+1}(Λ, ℂ)`. -/
def cohClass (j : ℕ) : cohCycles Λ j →ₗ[ℂ] groupCohomology (Rep.trivial ℂ Λ ℂ) (j + 1) :=
  ((HomologicalComplex.homologyMap (Theta Λ) (j + 1)).hom ∘ₗ (cohIso0 Λ j).inv.hom) ∘ₗ
    coverClass (sc_h₂ Λ j)

theorem cohClass_surjective (j : ℕ) : Function.Surjective (cohClass Λ j) := by
  intro y
  obtain ⟨z, hz⟩ := coverClass_surjective (sc_h₂ Λ j) (sigmaC_surjective Λ (j + 1))
    ((cohIso0 Λ j).hom.hom ((inv (HomologicalComplex.homologyMap (Theta Λ) (j + 1))).hom y))
  refine ⟨z, ?_⟩
  change (HomologicalComplex.homologyMap (Theta Λ) (j + 1)).hom
    ((cohIso0 Λ j).inv.hom (coverClass (sc_h₂ Λ j) z)) = y
  rw [hz]
  have h1 := Iso.hom_inv_id_apply (cohIso0 Λ j)
    ((inv (HomologicalComplex.homologyMap (Theta Λ) (j + 1))).hom y)
  rw [h1]
  exact Iso.inv_hom_id_apply (asIso (HomologicalComplex.homologyMap (Theta Λ) (j + 1))) y

theorem cohClass_eq_zero_iff (j : ℕ) (F : cohCycles Λ j) :
    cohClass Λ j F = 0 ↔ (F : Inv Λ (j + 1)) ∈ LinearMap.range (dInv Λ j) := by
  have h1 : cohClass Λ j F = 0 ↔ coverClass (sc_h₂ Λ j) F = 0 := by
    change (HomologicalComplex.homologyMap (Theta Λ) (j + 1)).hom
      ((cohIso0 Λ j).inv.hom (coverClass (sc_h₂ Λ j) F)) = 0 ↔ _
    constructor
    · intro h
      have := (ModuleCat.mono_iff_injective (HomologicalComplex.homologyMap (Theta Λ) (j + 1))).mp
        inferInstance (h.trans (map_zero (HomologicalComplex.homologyMap (Theta Λ) (j + 1)).hom).symm)
      exact (ModuleCat.mono_iff_injective (cohIso0 Λ j).inv).mp inferInstance
        (this.trans (map_zero (cohIso0 Λ j).inv.hom).symm)
    · intro h
      rw [h, map_zero, map_zero]
  rw [h1, coverClass_eq_zero_iff (sc_h₁ Λ j) (sc_h₂ Λ j) (sigmaC_surjective Λ j) F]
  have hk : LinearMap.ker (sigmaC Λ (j + 1)) = ⊥ := LinearMap.ker_eq_bot.mpr (homEquiv Λ (j + 1)).symm.injective
  change (F : Inv Λ (j + 1)) ∈ LinearMap.ker (sigmaC Λ (j + 1)) ⊔ LinearMap.range (dInv Λ j) ↔ _
  rw [hk, bot_sup_eq]

theorem xi_single {n : ℕ} (y : Fin n → Λ) :
    ((xi Λ).f n).hom (Finsupp.single y (MonoidAlgebra.single (1 : Λ) (1 : ℂ))) =
      MonoidAlgebra.single (Fin.partialProd (fun i => (y i : G))) (1 : ℂ) := by
  have h1 := barTerm_single (k := ℂ) Λ.subtype n y 1 1
  have h2 := diagonalSuccIsoFree_inv_single_single (k := ℂ) (G := G) n (fun i => (y i : G)) 1 1
  change (((Rep.barComplex.isoStandardComplex ℂ G).hom.f n)).hom
    ((barTerm (k := ℂ) Λ.subtype n).hom (Finsupp.single y (MonoidAlgebra.single (1 : Λ) (1 : ℂ)))) = _
  rw [h1]
  simp only [map_one]
  have h3 : ((Rep.barComplex.isoStandardComplex ℂ G).hom.f n).hom
      (Finsupp.single (Λ.subtype ∘ y) (MonoidAlgebra.single (1 : G) (1 : ℂ))) =
      (diagonalSuccIsoFree ℂ G n).inv.hom
        (Finsupp.single (fun i => (y i : G)) (MonoidAlgebra.single (1 : G) (1 : ℂ))) := rfl
  rw [h3, h2, one_smul]

theorem Theta_apply {n : ℕ} (φ : XL Λ n ⟶ Rep.trivial ℂ Λ ℂ) (y : Fin n → Λ) :
    ((Theta Λ).f n).hom φ y = evalFun Λ φ (Fin.partialProd (fun i => (y i : G))) := by
  have e : ((Theta Λ).f n).hom φ y =
      φ.hom (((xi Λ).f n).hom (Finsupp.single y (MonoidAlgebra.single (1 : Λ) (1 : ℂ)))) := rfl
  rw [e, xi_single]
  rfl

section Restriction

variable {Λ' : Subgroup G} {Λ : Subgroup G}

theorem Inv_mono (h : Λ' ≤ Λ) (i : ℕ) : Inv Λ i ≤ Inv Λ' i :=
  fun _ hF γ hγ x => hF γ (h hγ) x

/-- Invariant functions for `Λ` are invariant for `Λ' ≤ Λ`. -/
def restrInv (h : Λ' ≤ Λ) (i : ℕ) : Inv Λ i →ₗ[ℂ] Inv Λ' i :=
  Submodule.inclusion (Inv_mono h i)

theorem restrInv_val (h : Λ' ≤ Λ) (i : ℕ) (F : Inv Λ i) : (restrInv h i F).1 = F.1 := rfl

theorem dInv_restr (h : Λ' ≤ Λ) (i : ℕ) (F : Inv Λ i) :
    dInv Λ' i (restrInv h i F) = restrInv h (i + 1) (dInv Λ i F) := by
  apply Subtype.ext; funext x
  rw [dInv_apply]
  change _ = (dInv Λ i F).1 x
  rw [dInv_apply]
  rfl

/-- The restriction `Hom_Λ(-, ℂ) → Hom_Λ'(-, ℂ)` in degree `i`. -/
def Rc (h : Λ' ≤ Λ) (i : ℕ) : (Kc Λ).X i ⟶ (Kc Λ').X i :=
  ModuleCat.ofHom (sigmaC Λ' i ∘ₗ restrInv h i ∘ₗ (homEquiv Λ i).toLinearMap)

theorem Rc_sigma (h : Λ' ≤ Λ) (i : ℕ) (F : Inv Λ i) :
    (Rc h i).hom (sigmaC Λ i F) = sigmaC Λ' i (restrInv h i F) := by
  change sigmaC Λ' i (restrInv h i ((homEquiv Λ i) ((homEquiv Λ i).symm F))) = _
  rw [LinearEquiv.apply_symm_apply]

/-- The restriction cochain map. -/
def RcMap (h : Λ' ≤ Λ) : Kc Λ ⟶ Kc Λ' where
  f i := Rc h i
  comm' i j hij := by
    have hj : j = i + 1 := by simpa using hij.symm
    subst hj
    refine ModuleCat.hom_ext (LinearMap.ext fun ψ => ?_)
    obtain ⟨F, rfl⟩ := sigmaC_surjective Λ i ψ
    change ((Kc Λ').d i (i + 1)).hom ((Rc h i).hom (sigmaC Λ i F)) =
      (Rc h (i + 1)).hom (((Kc Λ).d i (i + 1)).hom (sigmaC Λ i F))
    rw [Rc_sigma, sigmaC_d, sigmaC_d, Rc_sigma, dInv_restr]

theorem evalFun_sigmaC (i : ℕ) (F : Inv Λ i) : evalFun Λ (sigmaC Λ i F) = F.1 :=
  congrArg Subtype.val ((homEquiv Λ i).apply_symm_apply F)

/-- The identity intertwiner for restriction of the trivial representations. -/
def phiCoh (h : Λ' ≤ Λ) : Rep.res (Subgroup.inclusion h) (Rep.trivial ℂ Λ ℂ) ⟶ Rep.trivial ℂ Λ' ℂ :=
  𝟙 _

theorem Theta_res (h : Λ' ≤ Λ) (n : ℕ) :
    (Theta Λ).f n ≫ (groupCohomology.cochainsMap (Subgroup.inclusion h) (phiCoh h)).f n =
      (RcMap h).f n ≫ (Theta Λ').f n := by
  refine ModuleCat.hom_ext (LinearMap.ext fun ψ => ?_)
  obtain ⟨F, rfl⟩ := sigmaC_surjective Λ n ψ
  funext y
  have e1 : ((groupCohomology.cochainsMap (Subgroup.inclusion h) (phiCoh h)).f n).hom
      (((Theta Λ).f n).hom (sigmaC Λ n F)) y =
      ((Theta Λ).f n).hom (sigmaC Λ n F) (Subgroup.inclusion h ∘ y) := rfl
  have e2 : ((RcMap h).f n ≫ (Theta Λ').f n).hom (sigmaC Λ n F) y =
      ((Theta Λ').f n).hom ((Rc h n).hom (sigmaC Λ n F)) y := rfl
  change ((groupCohomology.cochainsMap (Subgroup.inclusion h) (phiCoh h)).f n).hom
      (((Theta Λ).f n).hom (sigmaC Λ n F)) y = _
  rw [e1, e2]
  refine (Theta_apply Λ (sigmaC Λ n F) _).trans (Eq.trans ?_
    (Theta_apply Λ' ((Rc h n).hom (sigmaC Λ n F)) y).symm)
  rw [Rc_sigma, evalFun_sigmaC, evalFun_sigmaC]
  rfl

end Restriction

theorem homologyMap_homologyIsoSc'_up {K L : CochainComplex (ModuleCat ℂ) ℕ} (f : K ⟶ L) (j : ℕ) :
    HomologicalComplex.homologyMap f (j + 1) ≫
        (L.homologyIsoSc' j (j + 1) (j + 2) (CochainComplex.prev_nat_succ j)
          (CochainComplex.next ℕ (j + 1))).hom =
      (K.homologyIsoSc' j (j + 1) (j + 2) (CochainComplex.prev_nat_succ j)
          (CochainComplex.next ℕ (j + 1))).hom ≫
        ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor' (ModuleCat ℂ)
          (ComplexShape.up ℕ) j (j + 1) (j + 2)).map f) :=
  (HomologicalComplex.homologyFunctorIso' (ModuleCat ℂ) (ComplexShape.up ℕ) j (j + 1) (j + 2)
    (CochainComplex.prev_nat_succ j) (CochainComplex.next ℕ (j + 1))).hom.naturality f

theorem homologyIsoSc'_up_inv_natural {K L : CochainComplex (ModuleCat ℂ) ℕ} (f : K ⟶ L) (j : ℕ) :
    (K.homologyIsoSc' j (j + 1) (j + 2) (CochainComplex.prev_nat_succ j)
          (CochainComplex.next ℕ (j + 1))).inv ≫ HomologicalComplex.homologyMap f (j + 1) =
      ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor' (ModuleCat ℂ)
          (ComplexShape.up ℕ) j (j + 1) (j + 2)).map f) ≫
        (L.homologyIsoSc' j (j + 1) (j + 2) (CochainComplex.prev_nat_succ j)
          (CochainComplex.next ℕ (j + 1))).inv := by
  calc _ = (K.homologyIsoSc' j (j + 1) (j + 2) (CochainComplex.prev_nat_succ j)
          (CochainComplex.next ℕ (j + 1))).inv ≫ (HomologicalComplex.homologyMap f (j + 1) ≫
          (L.homologyIsoSc' j (j + 1) (j + 2) (CochainComplex.prev_nat_succ j)
          (CochainComplex.next ℕ (j + 1))).hom) ≫ (L.homologyIsoSc' j (j + 1) (j + 2)
          (CochainComplex.prev_nat_succ j) (CochainComplex.next ℕ (j + 1))).inv := by simp
    _ = _ := by rw [homologyMap_homologyIsoSc'_up f j]; simp

section ResNat

variable {Λ' : Subgroup G} {Λ : Subgroup G}

/-- The morphism of short complexes induced by restriction. -/
def ScR (h : Λ' ≤ Λ) (j : ℕ) : Sc Λ j ⟶ Sc Λ' j :=
  (HomologicalComplex.shortComplexFunctor' (ModuleCat ℂ) (ComplexShape.up ℕ) j (j + 1) (j + 2)).map
    (RcMap h)

theorem restrInv_mem_cohCycles (h : Λ' ≤ Λ) (j : ℕ) (F : cohCycles Λ j) :
    restrInv h (j + 1) F.1 ∈ cohCycles Λ' j := by
  rw [mem_cohCycles, dInv_restr, (mem_cohCycles Λ j F.1).mp F.2, map_zero]

theorem cohClass_res (h : Λ' ≤ Λ) (j : ℕ) (F : cohCycles Λ j) :
    (groupCohomology.map (Subgroup.inclusion h) (phiCoh h) (j + 1)).hom (cohClass Λ j F) =
      cohClass Λ' j ⟨restrInv h (j + 1) F.1, restrInv_mem_cohCycles h j F⟩ := by
  have hn0 : Theta Λ ≫ groupCohomology.cochainsMap (Subgroup.inclusion h) (phiCoh h) =
      RcMap h ≫ Theta Λ' := HomologicalComplex.hom_ext _ _ (fun n => Theta_res h n)
  have hn := congrArg (fun φ => HomologicalComplex.homologyMap φ (j + 1)) hn0
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hn
  have hcov := coverClass_natural (ScR h j) (σ₂ := sigmaC Λ (j + 1))
    (σ₂' := sigmaC Λ' (j + 1) ∘ₗ restrInv h (j + 1))
    (σ₃ := sigmaC Λ (j + 2)) (σ₃' := sigmaC Λ' (j + 2) ∘ₗ restrInv h (j + 2))
    (d₂ := dInv Λ (j + 1))
    (fun m => Rc_sigma h (j + 1) m) (fun m => Rc_sigma h (j + 2) m)
    (sc_h₂ Λ j)
    (fun m => by
      change (Sc Λ' j).g.hom (sigmaC Λ' (j + 1) (restrInv h (j + 1) m)) =
        sigmaC Λ' (j + 2) (restrInv h (j + 2) (dInv Λ (j + 1) m))
      rw [← dInv_restr]
      exact sc_h₂ Λ' j _) F
  have hiso := congrArg (fun t => t.hom (coverClass (sc_h₂ Λ j) F))
    (homologyIsoSc'_up_inv_natural (RcMap h) j)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hiso
  have hn' : (groupCohomology.map (Subgroup.inclusion h) (phiCoh h) (j + 1)).hom
      ((HomologicalComplex.homologyMap (Theta Λ) (j + 1)).hom
        ((cohIso0 Λ j).inv.hom (coverClass (sc_h₂ Λ j) F))) =
      (HomologicalComplex.homologyMap (Theta Λ') (j + 1)).hom
        ((HomologicalComplex.homologyMap (RcMap h) (j + 1)).hom
          ((cohIso0 Λ j).inv.hom (coverClass (sc_h₂ Λ j) F))) :=
    congrArg (fun t => t.hom ((cohIso0 Λ j).inv.hom (coverClass (sc_h₂ Λ j) F))) hn
  change (groupCohomology.map (Subgroup.inclusion h) (phiCoh h) (j + 1)).hom
      ((HomologicalComplex.homologyMap (Theta Λ) (j + 1)).hom
        ((cohIso0 Λ j).inv.hom (coverClass (sc_h₂ Λ j) F))) = _
  rw [hn']
  rw [show (HomologicalComplex.homologyMap (RcMap h) (j + 1)).hom
      ((cohIso0 Λ j).inv.hom (coverClass (sc_h₂ Λ j) F)) =
      (cohIso0 Λ' j).inv.hom ((ShortComplex.homologyMap (ScR h j)).hom
        (coverClass (sc_h₂ Λ j) F)) from hiso, hcov]
  rfl

end ResNat

end TernaryPeriodPolynomials.Argument.HomologyBridge
