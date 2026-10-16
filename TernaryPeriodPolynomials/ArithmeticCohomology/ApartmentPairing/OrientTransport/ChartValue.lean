module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.LocalEval
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.CrossRelation
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Localize

@[expose] public section


/-!
# Orientation transport: the local pairing model in `ℝ⁵`

Coordinates for the local statement of Lemma 3.3 (G3): `prodEL : ℝ³ × ℝ² ≃ₗ ℝ⁵`, the projections `piE`, `rhoE`, the compact
convex neighbourhood `Nset = {‖π x‖ ≤ 1/4, ‖ρ x‖ ≤ 1/4}` of the origin and the two open sets `UA = {‖ρ x‖ > 1/4}`,
`UB = {‖π x‖ > 1/4}` with `Nsetᶜ = UA ∪ UB`.  For Thom cochains `y₀` of `ℝ³` and `θ₀` of `ℝ²` (`ThomPair`: radius `1/4`),
`yE = y₀ ∘ π_#` and `thE = θ₀ ∘ ρ_#` are cocycles of `ℝ⁵` killing the simplices in `UB`, resp. `UA`, and
`Pair = capPairF 2 3 yE thE` is the Alexander-Whitney pairing `y ∘ (θ ∩ -)`; it kills the chains over `UA`, over `UB`
and boundaries (`Pair_UA`, `Pair_UB`, `Pair_boundary`), and takes the value `lamPos · lam2` on the product simplex
`σ₀` of `LocalEval` (`Pair_sigma5`; `σ₀` is a chain of the triad but its boundary is not carried by `UA`, `UB`; see
`Staircase` for the chain that is).  `sigma5_facet_far` records that the facets of `σ₀` avoid `Nset`.

Formalized by Claude Sonnet 5.5.
-/

open SphereOddDegree SphereOddDegree.AlexanderWhitney SphereOddDegree.AffineBarycentricSubdivision
open CategoryTheory
open TernaryPeriodPolynomials.Argument.Lemma33.Locality
open TernaryPeriodPolynomials.Argument.Lemma33.Orient
open TernaryPoly.SingularLocalCap TernaryPoly TernaryPoly.EuclideanLocalHomology TernaryPoly.ContractibleSingularHomology TernaryPoly.RationalRelativeSingular

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport

/-- `ℝ³ × ℝ² ≃ ℝ⁵` as a linear equivalence (concatenation of coordinates). -/
def prodEL : (R3 × R2) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 5) where
  toFun p := WithLp.toLp 2 ![p.1 0, p.1 1, p.1 2, p.2 0, p.2 1]
  invFun v := (WithLp.toLp 2 ![v 0, v 1, v 2], WithLp.toLp 2 ![v 3, v 4])
  map_add' p q := by
    apply PiLp.ext; intro i; fin_cases i <;> rfl
  map_smul' c p := by
    apply PiLp.ext; intro i; fin_cases i <;> rfl
  left_inv p := by
    apply Prod.ext
    · apply PiLp.ext; intro i; fin_cases i <;> rfl
    · apply PiLp.ext; intro i; fin_cases i <;> rfl
  right_inv v := by
    apply PiLp.ext; intro i; fin_cases i <;> rfl

/-- The projection `ℝ⁵ → ℝ³` onto the first three coordinates. -/
def piE : EuclideanSpace ℝ (Fin 5) →ₗ[ℝ] R3 := (LinearMap.fst ℝ R3 R2).comp prodEL.symm.toLinearMap

/-- The projection `ℝ⁵ → ℝ²` onto the last two coordinates. -/
def rhoE : EuclideanSpace ℝ (Fin 5) →ₗ[ℝ] R2 := (LinearMap.snd ℝ R3 R2).comp prodEL.symm.toLinearMap

theorem piE_cont : Continuous piE := LinearMap.continuous_of_finiteDimensional _
theorem rhoE_cont : Continuous rhoE := LinearMap.continuous_of_finiteDimensional _

theorem piE_prodEL (p : R3 × R2) : piE (prodEL p) = p.1 := by simp [piE]
theorem rhoE_prodEL (p : R3 × R2) : rhoE (prodEL p) = p.2 := by simp [rhoE]

/-- The morphism of spaces `ℝ⁵ → ℝ³`. -/
def piEHom : TopCat.of (EuclideanSpace ℝ (Fin 5)) ⟶ TopCat.of R3 := TopCat.ofHom ⟨piE, piE_cont⟩

/-- The morphism of spaces `ℝ⁵ → ℝ²`. -/
def rhoEHom : TopCat.of (EuclideanSpace ℝ (Fin 5)) ⟶ TopCat.of R2 := TopCat.ofHom ⟨rhoE, rhoE_cont⟩

/-- The product simplex `σ₀` in the coordinates of `ℝ⁵`. -/
def sigma5V : Fin (5 + 1) → EuclideanSpace ℝ (Fin 5) := fun j => prodEL (sigma0V j)

theorem pi_back_sigma5 :
    pushSimplex piEHom 3 (backSimplex (TopCat.of (EuclideanSpace ℝ (Fin 5))) 2 3 (affSimp (2 + 3) sigma5V)) =
      affSimp 3 tetraV := by
  rw [backSimplex_affSimp]
  have := pushSimplex_affSimp (V := EuclideanSpace ℝ (Fin 5)) (W := R3) piE piE_cont 3
    (fun i => sigma5V ⟨i.val + 2, by omega⟩)
  refine this.trans ?_
  congr 1
  funext i
  fin_cases i <;> simp [sigma5V, sigma0V, piE_prodEL]

theorem rho_front_sigma5 :
    pushSimplex rhoEHom 2 (frontSimplex (TopCat.of (EuclideanSpace ℝ (Fin 5))) 2 3 (affSimp (2 + 3) sigma5V)) =
      affSimp 2 rtri := by
  rw [frontSimplex_affSimp]
  have := pushSimplex_affSimp (V := EuclideanSpace ℝ (Fin 5)) (W := R2) rhoE rhoE_cont 2
    (fun i => sigma5V (Fin.castLE (by omega) i))
  refine this.trans ?_
  congr 1
  funext i
  fin_cases i <;> simp [sigma5V, sigma0V, rhoE_prodEL]

@[simp] theorem piE_apply0 (x : EuclideanSpace ℝ (Fin 5)) : piE x 0 = x 0 := rfl
@[simp] theorem piE_apply1 (x : EuclideanSpace ℝ (Fin 5)) : piE x 1 = x 1 := rfl
@[simp] theorem piE_apply2 (x : EuclideanSpace ℝ (Fin 5)) : piE x 2 = x 2 := rfl
@[simp] theorem rhoE_apply0 (x : EuclideanSpace ℝ (Fin 5)) : rhoE x 0 = x 3 := rfl
@[simp] theorem rhoE_apply1 (x : EuclideanSpace ℝ (Fin 5)) : rhoE x 1 = x 4 := rfl

theorem norm_piE_sq (x : EuclideanSpace ℝ (Fin 5)) : ‖piE x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_three]

theorem norm_rhoE_sq (x : EuclideanSpace ℝ (Fin 5)) : ‖rhoE x‖ ^ 2 = x 3 ^ 2 + x 4 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_two]

/-- The compact convex neighbourhood `N'` of the origin: both components of norm at most `1/4`. -/
def Nset : Set (EuclideanSpace ℝ (Fin 5)) := {x | ‖piE x‖ ≤ 1 / 4 ∧ ‖rhoE x‖ ≤ 1 / 4}

theorem facet_far (a0 a1 a2 a3 a4 : ℝ) (x : EuclideanSpace ℝ (Fin 5))
    (hlin : a0 * x 0 + a1 * x 1 + a2 * x 2 + a3 * x 3 + a4 * x 4 = -1 / 6)
    (hℓ : a0 ^ 2 + a1 ^ 2 + a2 ^ 2 + a3 ^ 2 + a4 ^ 2 < 2 / 9) : x ∉ Nset := by
  rintro ⟨h1, h2⟩
  have e1 : ‖piE x‖ ^ 2 ≤ (1 / 4) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have e2 : ‖rhoE x‖ ^ 2 ≤ (1 / 4) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  rw [norm_piE_sq] at e1
  rw [norm_rhoE_sq] at e2
  have hsum : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2 ≤ 1 / 8 := by nlinarith
  have hcs : (a0 * x 0 + a1 * x 1 + a2 * x 2 + a3 * x 3 + a4 * x 4) ^ 2 ≤
      (a0 ^ 2 + a1 ^ 2 + a2 ^ 2 + a3 ^ 2 + a4 ^ 2) * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2) := by
    nlinarith [sq_nonneg (a0 * x 1 - a1 * x 0), sq_nonneg (a0 * x 2 - a2 * x 0), sq_nonneg (a0 * x 3 - a3 * x 0),
      sq_nonneg (a0 * x 4 - a4 * x 0), sq_nonneg (a1 * x 2 - a2 * x 1), sq_nonneg (a1 * x 3 - a3 * x 1),
      sq_nonneg (a1 * x 4 - a4 * x 1), sq_nonneg (a2 * x 3 - a3 * x 2), sq_nonneg (a2 * x 4 - a4 * x 2),
      sq_nonneg (a3 * x 4 - a4 * x 3)]
  rw [hlin] at hcs
  have hpos : 0 ≤ a0 ^ 2 + a1 ^ 2 + a2 ^ 2 + a3 ^ 2 + a4 ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hsum hpos]

theorem sigma5_facet_far (i : Fin 6) (t : Delta 4) :
    affMapN 4 (fun j => sigma5V (i.succAbove j)) t ∉ Nset := by
  have hs : ∑ j, t.weights j = 1 := t.total_of_fintype
  rw [Fin.sum_univ_five] at hs
  fin_cases i
  · refine facet_far (-1 / 24) (1 / 8) (-1 / 24) (5 / 18) (-1 / 18) _ ?_ (by norm_num)
    simp [affMapN, Fin.sum_univ_five, sigma5V, sigma0V, prodEL, tetraV, rref, rv, mk3, rtri, rt, mk2,
      Fin.succAbove]
    linear_combination (-1 / 6) * hs
  · refine facet_far (-1 / 24) (1 / 8) (-1 / 24) (-1 / 18) (5 / 18) _ ?_ (by norm_num)
    simp [affMapN, Fin.sum_univ_five, sigma5V, sigma0V, prodEL, tetraV, rref, rv, mk3, rtri, rt, mk2,
      Fin.succAbove]
    linear_combination (-1 / 6) * hs
  · refine facet_far (-1 / 24) (1 / 8) (-1 / 24) (-1 / 18) (-1 / 18) _ ?_ (by norm_num)
    simp [affMapN, Fin.sum_univ_five, sigma5V, sigma0V, prodEL, tetraV, rref, rv, mk3, rtri, rt, mk2,
      Fin.succAbove]
    linear_combination (-1 / 6) * hs
  · refine facet_far (5 / 24) (-1 / 8) (-1 / 24) (-1 / 18) (-1 / 18) _ ?_ (by norm_num)
    simp [affMapN, Fin.sum_univ_five, sigma5V, sigma0V, prodEL, tetraV, rref, rv, mk3, rtri, rt, mk2,
      Fin.succAbove]
    linear_combination (-1 / 6) * hs
  · refine facet_far (-1 / 24) (-1 / 8) (5 / 24) (-1 / 18) (-1 / 18) _ ?_ (by norm_num)
    simp [affMapN, Fin.sum_univ_five, sigma5V, sigma0V, prodEL, tetraV, rref, rv, mk3, rtri, rt, mk2,
      Fin.succAbove]
    linear_combination (-1 / 6) * hs
  · refine facet_far (-1 / 24) (-1 / 8) (-1 / 24) (-1 / 18) (-1 / 18) _ ?_ (by norm_num)
    simp [affMapN, Fin.sum_univ_five, sigma5V, sigma0V, prodEL, tetraV, rref, rv, mk3, rtri, rt, mk2,
      Fin.succAbove]
    linear_combination (-1 / 6) * hs

open TernaryPoly in
theorem sigma5_boundary_mem :
    (singularBoundary ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) 4).hom
        (chainGenerator ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) 5 (affSimp 5 sigma5V)) ∈
      subChainSubmodule ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) Nsetᶜ 4 :=
  boundary_affSimp_mem _ 4 sigma5V (fun k t => sigma5_facet_far k t)

/-- The open set where the `ℝ²`-component has norm `> 1/4`. -/
def UA : Set (EuclideanSpace ℝ (Fin 5)) := {x | 1 / 4 < ‖rhoE x‖}

/-- The open set where the `ℝ³`-component has norm `> 1/4`. -/
def UB : Set (EuclideanSpace ℝ (Fin 5)) := {x | 1 / 4 < ‖piE x‖}

theorem Nset_compl : Nsetᶜ = UA ∪ UB := by
  ext x
  simp only [Nset, UA, UB, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_union, not_and_or, not_le]
  tauto

theorem isOpen_UA : IsOpen UA := isOpen_lt continuous_const (continuous_norm.comp rhoE_cont)
theorem isOpen_UB : IsOpen UB := isOpen_lt continuous_const (continuous_norm.comp piE_cont)

section Pairing

variable (y₀ : (chains R3).X 3 →ₗ[ℚ] ℚ) (θ₀ : (chains R2).X 2 →ₗ[ℚ] ℚ)

/-- The scalar 3-cochain `y₀ ∘ π_#` of `ℝ⁵`. -/
def yE : singularChainGroup ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) 3 →ₗ[ℚ] ℚ :=
  y₀.comp (singularChainMap ℚ piEHom 3).hom

/-- The scalar 2-cochain `θ₀ ∘ ρ_#` of `ℝ⁵`. -/
def thE : singularChainGroup ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) 2 →ₗ[ℚ] ℚ :=
  θ₀.comp (singularChainMap ℚ rhoEHom 2).hom

/-- The Alexander-Whitney pairing `y ∘ (θ ∩ -)` of the two pulled-back Thom cochains, on 5-chains of `ℝ⁵`. -/
def Pair : singularChainGroup ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) (2 + 3) →ₗ[ℚ] ℚ :=
  capPairF (TopCat.of (EuclideanSpace ℝ (Fin 5))) (ModuleCat.of ℚ ℚ) 2 3 (yE y₀) (thE θ₀)

/-- The Thom conditions (radius `1/4`) on a pair of cochains of `ℝ³` and `ℝ²`. -/
structure ThomPair : Prop where
  y_cocycle : ∀ e : (chains R3).X 4, y₀ (((chains R3).d 4 3).hom e) = 0
  y_vanish : ∀ τ : singularSimplices (TopCat.of R3) 3, IsSubordinate {v : R3 | 1 / 4 < ‖v‖} τ →
    y₀ (chainGenerator ℚ (TopCat.of R3) 3 τ) = 0
  y_deg : ∀ c : (chains R3).X 3, ((chains R3).d 3 2).hom c ∈
      subChainSubmodule ℚ (TopCat.of R3) {v : R3 | 1 / 4 < ‖v‖} 2 →
    ∃ h : ((localChains 3).d 3 2).hom ((locR3.f 3).hom c) = 0, y₀ c = degR3 c h
  t_cocycle : ∀ e : (chains R2).X 3, θ₀ (((chains R2).d 3 2).hom e) = 0
  t_vanish : ∀ τ : singularSimplices (TopCat.of R2) 2, IsSubordinate {v : R2 | 1 / 4 < ‖v‖} τ →
    θ₀ (chainGenerator ℚ (TopCat.of R2) 2 τ) = 0
  t_deg : ∀ c : (chains R2).X 2, ((chains R2).d 2 1).hom c ∈
      subChainSubmodule ℚ (TopCat.of R2) {v : R2 | 1 / 4 < ‖v‖} 1 →
    ∃ h : ((localChains 2).d 2 1).hom ((locR2.f 2).hom c) = 0, θ₀ c = degR2 c h

variable {y₀ θ₀}

theorem yE_cocycle (H : ThomPair y₀ θ₀) (e : singularChainGroup ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) 4) :
    yE y₀ ((singularBoundary ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) 3).hom e) = 0 := by
  unfold yE
  rw [LinearMap.comp_apply]
  have h1 := singularChainMap_boundary_apply ℚ piEHom 3 e
  have h2 : (singularChainMap ℚ piEHom 3).hom ((singularBoundary ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) 3).hom e) =
      (singularBoundary ℚ (TopCat.of R3) 3).hom ((singularChainMap ℚ piEHom 4).hom e) := h1.symm
  rw [h2]
  exact H.y_cocycle _

theorem thE_cocycle (H : ThomPair y₀ θ₀) (e : singularChainGroup ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) 3) :
    thE θ₀ ((singularBoundary ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) 2).hom e) = 0 := by
  unfold thE
  rw [LinearMap.comp_apply]
  have h1 := singularChainMap_boundary_apply ℚ rhoEHom 2 e
  have h2 : (singularChainMap ℚ rhoEHom 2).hom ((singularBoundary ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) 2).hom e) =
      (singularBoundary ℚ (TopCat.of R2) 2).hom ((singularChainMap ℚ rhoEHom 3).hom e) := h1.symm
  rw [h2]
  exact H.t_cocycle _

theorem thE_vanish (H : ThomPair y₀ θ₀) (τ : singularSimplices (TopCat.of (EuclideanSpace ℝ (Fin 5))) 2)
    (hτ : IsSubordinate UA τ) : thE θ₀ (chainGenerator ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) 2 τ) = 0 := by
  unfold thE
  rw [LinearMap.comp_apply, singularChainMap_generator]
  apply H.t_vanish
  rw [isSubordinate_pushSimplex_iff]
  exact hτ

theorem yE_vanish (H : ThomPair y₀ θ₀) (τ : singularSimplices (TopCat.of (EuclideanSpace ℝ (Fin 5))) 3)
    (hτ : IsSubordinate UB τ) : yE y₀ (chainGenerator ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) 3 τ) = 0 := by
  unfold yE
  rw [LinearMap.comp_apply, singularChainMap_generator]
  apply H.y_vanish
  rw [isSubordinate_pushSimplex_iff]
  exact hτ

theorem Pair_UA (H : ThomPair y₀ θ₀) {c : singularChainGroup ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) (2 + 3)}
    (hc : c ∈ subChainSubmodule ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) UA (2 + 3)) : Pair y₀ θ₀ c = 0 :=
  capPairF_eq_zero_of_front (TopCat.of (EuclideanSpace ℝ (Fin 5))) (ModuleCat.of ℚ ℚ) 2 3 (yE y₀) (thE θ₀)
    (fun τ hτ => thE_vanish H τ hτ) hc

theorem Pair_UB (H : ThomPair y₀ θ₀) {c : singularChainGroup ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) (2 + 3)}
    (hc : c ∈ subChainSubmodule ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) UB (2 + 3)) : Pair y₀ θ₀ c = 0 :=
  capPairF_eq_zero_of_back (TopCat.of (EuclideanSpace ℝ (Fin 5))) (ModuleCat.of ℚ ℚ) 2 3 (yE y₀) (thE θ₀)
    (fun τ hτ => yE_vanish H τ hτ) hc

theorem Pair_boundary (H : ThomPair y₀ θ₀)
    (u : singularChainGroup ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) (2 + 3 + 1)) :
    Pair y₀ θ₀ ((singularBoundary ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) (2 + 3)).hom u) = 0 := by
  have h := capPairF_leibniz (TopCat.of (EuclideanSpace ℝ (Fin 5))) (ModuleCat.of ℚ ℚ) 2 3 (yE y₀)
    (yE_cocycle H) (thE θ₀) u
  have h0 : (thE θ₀).comp (singularBoundary ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) 2).hom = 0 := by
    apply LinearMap.ext
    intro e
    exact thE_cocycle H e
  rw [h0] at h
  have hz : capPairF (TopCat.of (EuclideanSpace ℝ (Fin 5))) (ModuleCat.of ℚ ℚ) (2 + 1) 3 (yE y₀)
      (0 : singularChainGroup ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) (2 + 1) →ₗ[ℚ] ℚ) = 0 := by
    apply scalarChain_ext
    intro σ
    rw [capPairF_generator]
    simp
  rw [hz] at h
  exact h.symm.trans (by simp)

theorem unit_subset_quarter3 : {v : R3 | 1 < ‖v‖} ⊆ {v : R3 | 1 / 4 < ‖v‖} := by
  intro v hv
  have h1 : (1 : ℝ) < ‖v‖ := hv
  show (1 / 4 : ℝ) < ‖v‖
  linarith

theorem unit_subset_quarter2 : {v : R2 | 1 < ‖v‖} ⊆ {v : R2 | 1 / 4 < ‖v‖} := by
  intro v hv
  have h1 : (1 : ℝ) < ‖v‖ := hv
  show (1 / 4 : ℝ) < ‖v‖
  linarith

theorem ThomPair.y_deg1 (H : ThomPair y₀ θ₀) (c : (chains R3).X 3)
    (hc : ((chains R3).d 3 2).hom c ∈ subChainSubmodule ℚ (TopCat.of R3) {v : R3 | 1 < ‖v‖} 2) :
    ∃ h : ((localChains 3).d 3 2).hom ((locR3.f 3).hom c) = 0, y₀ c = degR3 c h :=
  H.y_deg c (subChainSubmodule_mono unit_subset_quarter3 2 hc)

theorem ThomPair.t_deg1 (H : ThomPair y₀ θ₀) (c : (chains R2).X 2)
    (hc : ((chains R2).d 2 1).hom c ∈ subChainSubmodule ℚ (TopCat.of R2) {v : R2 | 1 < ‖v‖} 1) :
    ∃ h : ((localChains 2).d 2 1).hom ((locR2.f 2).hom c) = 0, θ₀ c = degR2 c h :=
  H.t_deg c (subChainSubmodule_mono unit_subset_quarter2 1 hc)

/-- **The pairing of the Thom cochains on the product simplex**: `lamPos · lam2`. -/
theorem Pair_sigma5 (H : ThomPair y₀ θ₀) :
    Pair y₀ θ₀ (chainGenerator ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) (2 + 3) (affSimp (2 + 3) sigma5V)) =
      lamPos * lam2 := by
  unfold Pair
  rw [capPairF_generator]
  show yE y₀ _ * thE θ₀ _ = _
  unfold yE thE
  rw [LinearMap.comp_apply, LinearMap.comp_apply, singularChainMap_generator, singularChainMap_generator,
    pi_back_sigma5, rho_front_sigma5]
  rw [thom3_tetra y₀ H.y_deg1, thom2_tri θ₀ H.t_deg1]

end Pairing

end TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport
