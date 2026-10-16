module

public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.Ext
public import Mathlib.RepresentationTheory.Homological.Resolution
public import TernaryPeriodPolynomials.Topology.TopHomology.CycleSpan
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.Order.Fin.SuccAboveOrderIso

@[expose] public section


/-!
# From a one-dimensional top cohomology of a complex of representations to a fundamental cycle

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.TopHomology

theorem dependent_of_homology_iso (K : CochainComplex (ModuleCat.{0} ℚ) ℕ)
    (h : Nonempty (K.homology 4 ≅ ModuleCat.of ℚ ℚ)) (c₁ c₂ : K.X 4)
    (h₁ : (K.d 4 5).hom c₁ = 0) (h₂ : (K.d 4 5).hom c₂ = 0) :
    ∃ (a b : ℚ), (a ≠ 0 ∨ b ≠ 0) ∧ ∃ η : K.X 3, (K.d 3 4).hom η = a • c₁ + b • c₂ := by
  obtain ⟨h⟩ := h
  let S := K.sc' 3 4 5
  let iso : S.moduleCatLeftHomologyData.H ≅ ModuleCat.of ℚ ℚ :=
    S.moduleCatLeftHomologyData.homologyIso.symm ≪≫
      (K.homologyIsoSc' 3 4 5 (by simp) (by simp)).symm ≪≫ h
  let e := iso.toLinearEquiv
  let x₁ : LinearMap.ker S.g.hom := ⟨c₁, h₁⟩
  let x₂ : LinearMap.ker S.g.hom := ⟨c₂, h₂⟩
  let q₁ : S.moduleCatLeftHomologyData.H := Submodule.Quotient.mk x₁
  let q₂ : S.moduleCatLeftHomologyData.H := Submodule.Quotient.mk x₂
  have key : ∀ a b : ℚ, a • q₁ + b • q₂ = 0 → ∃ η : K.X 3, (K.d 3 4).hom η = a • c₁ + b • c₂ := by
    intro a b hab
    have hmem : a • x₁ + b • x₂ ∈ LinearMap.range S.moduleCatToCycles := by
      have hab' : (a • (Submodule.Quotient.mk x₁ :
          LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) +
          b • Submodule.Quotient.mk x₂) = 0 := hab
      have : (Submodule.Quotient.mk (a • x₁ + b • x₂) :
          LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) = 0 := by
        rw [Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul]
        exact hab'
      exact (Submodule.Quotient.mk_eq_zero _).mp this
    obtain ⟨η, hη⟩ := hmem
    refine ⟨η, ?_⟩
    have := congrArg Subtype.val hη
    exact this
  by_cases hr : e q₁ = 0 ∧ e q₂ = 0
  · refine ⟨1, 0, Or.inl one_ne_zero, key 1 0 ?_⟩
    have : q₁ = 0 := e.injective (by simpa using hr.1)
    simp [this]
  · refine ⟨e q₂, -(e q₁), ?_, key _ _ ?_⟩
    · by_contra hcon
      push Not at hcon
      exact hr ⟨by simpa using hcon.2, hcon.1⟩
    · apply e.injective
      simp only [map_add, map_smul, smul_eq_mul, map_zero]
      ring

section Class

variable (K : CochainComplex (ModuleCat.{0} ℚ) ℕ) (h : K.homology 4 ≅ ModuleCat.of ℚ ℚ)

/-- The linear equivalence between the quotient `ker / range` computing `H⁴` and `ℚ`. -/
def classEquiv : (K.sc' 3 4 5).moduleCatLeftHomologyData.H ≃ₗ[ℚ] ℚ :=
  ((K.sc' 3 4 5).moduleCatLeftHomologyData.homologyIso.symm ≪≫
    (K.homologyIsoSc' 3 4 5 (by simp) (by simp)).symm ≪≫ h).toLinearEquiv

/-- The class in `ℚ` of a degree-four cocycle. -/
def cocycleClass (φ : K.X 4) (hφ : (K.d 4 5).hom φ = 0) : ℚ :=
  classEquiv K h (Submodule.Quotient.mk (⟨φ, hφ⟩ : LinearMap.ker (K.sc' 3 4 5).g.hom))

theorem cocycleClass_eq_zero_iff (φ : K.X 4) (hφ : (K.d 4 5).hom φ = 0) :
    cocycleClass K h φ hφ = 0 ↔ ∃ η : K.X 3, (K.d 3 4).hom η = φ := by
  unfold cocycleClass
  refine (LinearEquiv.map_eq_zero_iff _).trans ?_
  refine (Submodule.Quotient.mk_eq_zero (LinearMap.range (K.sc' 3 4 5).moduleCatToCycles)).trans ?_
  constructor
  · rintro ⟨η, hη⟩
    exact ⟨η, congrArg Subtype.val hη⟩
  · rintro ⟨η, hη⟩
    exact ⟨η, Subtype.ext hη⟩

theorem cocycleClass_add (φ ψ : K.X 4) (hφ : (K.d 4 5).hom φ = 0) (hψ : (K.d 4 5).hom ψ = 0)
    (hs : (K.d 4 5).hom (φ + ψ) = 0) :
    cocycleClass K h (φ + ψ) hs = cocycleClass K h φ hφ + cocycleClass K h ψ hψ := by
  unfold cocycleClass
  exact (congrArg (classEquiv K h)
    (Submodule.Quotient.mk_add (LinearMap.range (K.sc' 3 4 5).moduleCatToCycles)
      (x := (⟨φ, hφ⟩ : LinearMap.ker (K.sc' 3 4 5).g.hom)) (y := ⟨ψ, hψ⟩))).trans
    (map_add _ _ _)

theorem cocycleClass_smul (a : ℚ) (φ : K.X 4) (hφ : (K.d 4 5).hom φ = 0)
    (hs : (K.d 4 5).hom (a • φ) = 0) :
    cocycleClass K h (a • φ) hs = a * cocycleClass K h φ hφ := by
  unfold cocycleClass
  exact (congrArg (classEquiv K h)
    (Submodule.Quotient.mk_smul (LinearMap.range (K.sc' 3 4 5).moduleCatToCycles) a
      (⟨φ, hφ⟩ : LinearMap.ker (K.sc' 3 4 5).g.hom))).trans (map_smul _ _ _)

theorem cocycleClass_congr {φ φ' : K.X 4} (hφ : (K.d 4 5).hom φ = 0) (hφ' : (K.d 4 5).hom φ' = 0)
    (e : φ = φ') : cocycleClass K h φ hφ = cocycleClass K h φ' hφ' := by
  subst e
  rfl

/-- A nonzero class is represented by a cocycle that is not a coboundary. -/
theorem exists_noncoboundary : ∃ (φ : K.X 4) (hφ : (K.d 4 5).hom φ = 0), cocycleClass K h φ hφ ≠ 0 := by
  obtain ⟨q, hq⟩ := (classEquiv K h).surjective 1
  induction q using Submodule.Quotient.induction_on with
  | H x =>
    refine ⟨x.1, x.2, ?_⟩
    change classEquiv K h (Submodule.Quotient.mk x) ≠ 0
    rw [hq]
    exact one_ne_zero

end Class

section Coinv

variable {Γ : Type} [Group Γ]

/-- The coinvariants of a complex of representations. -/
def coinvD (P : ChainComplex (Rep.{0} ℚ Γ) ℕ) (i j : ℕ) :
    (P.X i).ρ.Coinvariants →ₗ[ℚ] (P.X j).ρ.Coinvariants :=
  Representation.Coinvariants.map _ _ (P.d i j).hom

/-- Morphisms into a trivial representation are linear forms on the coinvariants. -/
def coinvHom (X : Rep.{0} ℚ Γ) (W : Type) [AddCommGroup W] [Module ℚ W] :
    (X ⟶ Rep.trivial ℚ Γ W) ≃ₗ[ℚ] (X.ρ.Coinvariants →ₗ[ℚ] W) where
  toFun c := Representation.Coinvariants.lift X.ρ c.hom.toLinearMap (fun g => by
    ext x
    simpa using Rep.hom_comm_apply c g x)
  invFun φ := Rep.ofHom ⟨φ ∘ₗ Representation.Coinvariants.mk X.ρ, fun g => by
    ext x
    simp⟩
  map_add' c c' := by
    apply Representation.Coinvariants.hom_ext
    rfl
  map_smul' a c := by
    apply Representation.Coinvariants.hom_ext
    rfl
  left_inv c := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    rfl
  right_inv φ := by
    apply Representation.Coinvariants.hom_ext
    rfl

theorem coinvHom_apply_mk (X : Rep.{0} ℚ Γ) (W : Type) [AddCommGroup W] [Module ℚ W]
    (c : X ⟶ Rep.trivial ℚ Γ W) (x : X) :
    coinvHom X W c (Representation.Coinvariants.mk X.ρ x) = c.hom x := rfl

theorem coinvHom_comp {X Y : Rep.{0} ℚ Γ} (f : X ⟶ Y) (W : Type) [AddCommGroup W] [Module ℚ W]
    (c : Y ⟶ Rep.trivial ℚ Γ W) :
    coinvHom X W (f ≫ c) = coinvHom Y W c ∘ₗ Representation.Coinvariants.map _ _ f.hom := by
  apply Representation.Coinvariants.hom_ext
  rfl

theorem cohomologyAtMostOne_coinv (P : ChainComplex (Rep.{0} ℚ Γ) ℕ)
    (h : Nonempty ((P.linearYonedaObj ℚ (Rep.trivial ℚ Γ ℚ)).homology 4 ≅ ModuleCat.of ℚ ℚ)) :
    CohomologyAtMostOne (coinvD P 5 4) (coinvD P 4 3) := by
  intro φ₁ φ₂ hφ₁ hφ₂
  set K := P.linearYonedaObj ℚ (Rep.trivial ℚ Γ ℚ) with hK
  have hd : ∀ (c : P.X 4 ⟶ Rep.trivial ℚ Γ ℚ), (K.d 4 5).hom c = P.d 5 4 ≫ c := fun c => rfl
  have hd' : ∀ (c : P.X 3 ⟶ Rep.trivial ℚ Γ ℚ), (K.d 3 4).hom c = P.d 4 3 ≫ c := fun c => rfl
  have hcoc : ∀ φ : (P.X 4).ρ.Coinvariants →ₗ[ℚ] ℚ, φ ∘ₗ coinvD P 5 4 = 0 →
      (K.d 4 5).hom ((coinvHom (P.X 4) ℚ).symm φ) = 0 := by
    intro φ hφ
    rw [hd]
    have h0 : coinvHom (P.X 5) ℚ (P.d 5 4 ≫ (coinvHom (P.X 4) ℚ).symm φ) = 0 := by
      rw [coinvHom_comp, LinearEquiv.apply_symm_apply]
      exact hφ
    exact (coinvHom (P.X 5) ℚ).injective (h0.trans (map_zero _).symm)
  obtain ⟨a, b, hab, η, hη⟩ := dependent_of_homology_iso K h _ _ (hcoc φ₁ hφ₁) (hcoc φ₂ hφ₂)
  refine ⟨a, b, coinvHom (P.X 3) ℚ (η : P.X 3 ⟶ Rep.trivial ℚ Γ ℚ), hab, ?_⟩
  let η' : P.X 3 ⟶ Rep.trivial ℚ Γ ℚ := η
  have hη' : P.d 4 3 ≫ η' = a • (coinvHom (P.X 4) ℚ).symm φ₁ + b • (coinvHom (P.X 4) ℚ).symm φ₂ := hη
  have := congrArg (coinvHom (P.X 4) ℚ) hη'
  rw [coinvHom_comp, map_add, map_smul, map_smul, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply] at this
  exact this.symm

/-- **A fundamental cycle.** If the top cohomology of `Hom(P, ℚ)` (trivial coefficients) is
one-dimensional, the coinvariants of `P` in degree four carry a cycle `ω` such that every cocycle
with trivial coefficients in any `ℚ`-vector space vanishing on `ω` is a coboundary. -/
theorem exists_fundamental_cycle (P : ChainComplex (Rep.{0} ℚ Γ) ℕ)
    (h : Nonempty ((P.linearYonedaObj ℚ (Rep.trivial ℚ Γ ℚ)).homology 4 ≅ ModuleCat.of ℚ ℚ)) :
    ∃ ω : (P.X 4).ρ.Coinvariants, coinvD P 4 3 ω = 0 ∧
      (∀ z : (P.X 4).ρ.Coinvariants, coinvD P 4 3 z = 0 →
        ∃ c : ℚ, z - c • ω ∈ LinearMap.range (coinvD P 5 4)) ∧
      ∀ (W : Type) [AddCommGroup W] [Module ℚ W] (c : P.X 4 ⟶ Rep.trivial ℚ Γ W),
        P.d 5 4 ≫ c = 0 → coinvHom (P.X 4) W c ω = 0 →
        ∃ η : P.X 3 ⟶ Rep.trivial ℚ Γ W, c = P.d 4 3 ≫ η := by
  obtain ⟨ω, hω, hspan⟩ := exists_cycle_span (cohomologyAtMostOne_coinv P h)
  refine ⟨ω, hω, hspan, fun W _ _ c hc hcω => ?_⟩
  have hφ : coinvHom (P.X 4) W c ∘ₗ coinvD P 5 4 = 0 := by
    have h1 := coinvHom_comp (P.d 5 4) W c
    rw [hc, map_zero] at h1
    exact h1.symm
  obtain ⟨η', hη'⟩ := cocycle_eq_comp_of_apply_eq_zero hspan (coinvHom (P.X 4) W c) hφ hcω
  refine ⟨(coinvHom (P.X 3) W).symm η', ?_⟩
  apply (coinvHom (P.X 4) W).injective
  rw [coinvHom_comp, LinearEquiv.apply_symm_apply]
  exact hη'

/-- **Normalization of the fundamental cycle.** Any two linear functionals on the degree-four cocycles
that kill coboundaries are proportional once the first factors through `H⁴ ≅ ℚ`: the class map
`cocycleClass` is a nonzero rational multiple of the evaluation on a spanning cycle `ω`. -/
theorem fundamental_cycle_normalization (P : ChainComplex (Rep.{0} ℚ Γ) ℕ)
    (geo : (P.linearYonedaObj ℚ (Rep.trivial ℚ Γ ℚ)).homology 4 ≅ ModuleCat.of ℚ ℚ)
    (ω : (P.X 4).ρ.Coinvariants)
    (hspan : ∀ (c : P.X 4 ⟶ Rep.trivial ℚ Γ ℚ), P.d 5 4 ≫ c = 0 →
      coinvHom (P.X 4) ℚ c ω = 0 → ∃ η : P.X 3 ⟶ Rep.trivial ℚ Γ ℚ, c = P.d 4 3 ≫ η) :
    ∃ lam : ℚ, lam ≠ 0 ∧ ∀ (c : P.X 4 ⟶ Rep.trivial ℚ Γ ℚ) (hc : P.d 5 4 ≫ c = 0),
      cocycleClass (P.linearYonedaObj ℚ (Rep.trivial ℚ Γ ℚ)) geo c hc =
        lam * coinvHom (P.X 4) ℚ c ω := by
  obtain ⟨φ₀, hφ₀, hne⟩ := exists_noncoboundary _ geo
  let φ₀' : P.X 4 ⟶ Rep.trivial ℚ Γ ℚ := φ₀
  have hb : coinvHom (P.X 4) ℚ φ₀' ω ≠ 0 := by
    intro h0
    obtain ⟨η, hη⟩ := hspan φ₀' hφ₀ h0
    exact hne ((cocycleClass_eq_zero_iff _ geo φ₀ hφ₀).mpr ⟨η, hη.symm⟩)
  refine ⟨cocycleClass _ geo φ₀ hφ₀ / coinvHom (P.X 4) ℚ φ₀' ω, ?_, ?_⟩
  · exact div_ne_zero hne hb
  · intro c hc
    set a : ℚ := coinvHom (P.X 4) ℚ c ω / coinvHom (P.X 4) ℚ φ₀' ω with ha
    let ψ : P.X 4 ⟶ Rep.trivial ℚ Γ ℚ := c - a • φ₀'
    have hψ : P.d 5 4 ≫ ψ = 0 := by
      have e1 : P.d 5 4 ≫ ψ = P.d 5 4 ≫ c - a • (P.d 5 4 ≫ φ₀') := by
        simp only [ψ, Preadditive.comp_sub, Linear.comp_smul]
      rw [e1, hc]
      have : P.d 5 4 ≫ φ₀' = 0 := hφ₀
      rw [this]
      simp
    have hψω : coinvHom (P.X 4) ℚ ψ ω = 0 := by
      have : coinvHom (P.X 4) ℚ ψ ω = coinvHom (P.X 4) ℚ c ω - a * coinvHom (P.X 4) ℚ φ₀' ω := by
        simp only [ψ, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [this, ha, div_mul_cancel₀ _ hb, sub_self]
    obtain ⟨η, hη⟩ := hspan ψ hψ hψω
    have hψ0 : cocycleClass _ geo ψ hψ = 0 :=
      (cocycleClass_eq_zero_iff _ geo ψ hψ).mpr ⟨η, hη.symm⟩
    have hcψ : c = ψ + a • φ₀' := (sub_add_cancel c (a • φ₀')).symm
    have hs : ((P.linearYonedaObj ℚ (Rep.trivial ℚ Γ ℚ)).d 4 5).hom (a • φ₀') = 0 := by
      have : P.d 5 4 ≫ φ₀' = 0 := hφ₀
      change P.d 5 4 ≫ (a • φ₀') = 0
      rw [Linear.comp_smul, this, smul_zero]
    have hsum : ((P.linearYonedaObj ℚ (Rep.trivial ℚ Γ ℚ)).d 4 5).hom (ψ + a • φ₀') = 0 := by
      rw [← hcψ]; exact hc
    have h1 := cocycleClass_congr _ geo hc hsum hcψ
    have h2 := cocycleClass_add _ geo ψ (a • φ₀') hψ hs hsum
    have h3 : cocycleClass _ geo (a • φ₀') hs = a * cocycleClass _ geo φ₀ hφ₀ :=
      cocycleClass_smul _ geo a φ₀ hφ₀ hs
    refine h1.trans (h2.trans ?_)
    rw [hψ0, zero_add, h3, ha]
    field_simp

end Coinv

end TernaryPeriodPolynomials.Argument.TopHomology
