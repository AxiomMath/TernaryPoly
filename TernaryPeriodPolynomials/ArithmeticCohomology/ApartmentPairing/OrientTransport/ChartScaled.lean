module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.ChartOriented

@[expose] public section


/-!
# The chart-level value for unit Thom cochains and arbitrary radii

`Lsc η δ` is the diagonal dilation of `ℝ⁵ = ℝ³ × ℝ²` by `(4η)⁻¹` on the first and `(4δ)⁻¹` on the second factor.  It carries the
radii `(η, δ)` to `(1/4, 1/4)`.  `chart_scaled` is the value of the pairing of the pulled-back unit Thom cochains
`y₁ ∘ (η⁻¹ π f)_#`, `θ₁ ∘ (δ⁻¹ ρ f)_#` on a chain `cc` of a space `X` mapping to `ℝ⁵` by `f`: when `(Lsc ∘ f)_# cc` has class the
library local generator at the origin, `d₅ · ⟨y, θ⟩(cc) = lamPos · lam2`.

Formalized by Claude Sonnet 5.5.
-/

open SphereOddDegree SphereOddDegree.AlexanderWhitney SphereOddDegree.AffineBarycentricSubdivision
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open TernaryPeriodPolynomials.Argument.Lemma33.Locality
open TernaryPeriodPolynomials.Argument.Lemma33.Orient
open TernaryPoly TernaryPoly.EuclideanLocalHomology TernaryPoly.ContractibleSingularHomology
  TernaryPoly.RationalRelativeSingular TernaryPoly.RationalManifoldCompact TernaryPoly.EuclideanCompactClasses
  TernaryPoly.RationalLocalOrientation TernaryPoly.EuclideanOrientationScalar
open TernaryPoly.SingularLocalCap.Descent TernaryPoly.SingularLocalCap

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport

local notation "X5" => TopCat.of (EuclideanSpace ℝ (Fin 5))

/-- The diagonal dilation of `ℝ⁵` by `a` on the `ℝ³` factor and `b` on the `ℝ²` factor, as a linear map. -/
def LscL (a b : ℝ) : EuclideanSpace ℝ (Fin 5) →ₗ[ℝ] EuclideanSpace ℝ (Fin 5) :=
  prodEL.toLinearMap ∘ₗ ((a • LinearMap.id : R3 →ₗ[ℝ] R3).prodMap (b • LinearMap.id : R2 →ₗ[ℝ] R2)) ∘ₗ
    prodEL.symm.toLinearMap

theorem piE_LscL (a b : ℝ) (x : EuclideanSpace ℝ (Fin 5)) : piE (LscL a b x) = a • piE x := by
  simp [LscL, piE]

theorem rhoE_LscL (a b : ℝ) (x : EuclideanSpace ℝ (Fin 5)) : rhoE (LscL a b x) = b • rhoE x := by
  simp [LscL, rhoE]

/-- The dilation of `ℝ⁵` carrying the radii `(η, δ)` to `(1/4, 1/4)`. -/
def Lsc (η δ : ℝ) : X5 ⟶ X5 :=
  TopCat.ofHom ⟨LscL ((4 * η)⁻¹) ((4 * δ)⁻¹), LinearMap.continuous_of_finiteDimensional _⟩

theorem piE_Lsc (η δ : ℝ) (x : EuclideanSpace ℝ (Fin 5)) :
    piE ((Lsc η δ).hom x) = (4 * η)⁻¹ • piE x := piE_LscL _ _ x

theorem rhoE_Lsc (η δ : ℝ) (x : EuclideanSpace ℝ (Fin 5)) :
    rhoE ((Lsc η δ).hom x) = (4 * δ)⁻¹ • rhoE x := rhoE_LscL _ _ x

theorem Lsc_preimage_UA {δ : ℝ} (hδ : 0 < δ) (η : ℝ) :
    (Lsc η δ).hom ⁻¹' UA = {x : EuclideanSpace ℝ (Fin 5) | δ < ‖rhoE x‖} := by
  ext x
  change 1 / 4 < ‖rhoE ((Lsc η δ).hom x)‖ ↔ δ < ‖rhoE x‖
  rw [rhoE_Lsc, norm_smul, norm_inv, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * δ)]
  rw [inv_mul_eq_div, lt_div_iff₀ (by positivity)]
  constructor <;> intro h <;> linarith

theorem Lsc_preimage_UB {η : ℝ} (hη : 0 < η) (δ : ℝ) :
    (Lsc η δ).hom ⁻¹' UB = {x : EuclideanSpace ℝ (Fin 5) | η < ‖piE x‖} := by
  ext x
  change 1 / 4 < ‖piE ((Lsc η δ).hom x)‖ ↔ η < ‖piE x‖
  rw [piE_Lsc, norm_smul, norm_inv, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * η)]
  rw [inv_mul_eq_div, lt_div_iff₀ (by positivity)]
  constructor <;> intro h <;> linarith

theorem Lsc_pi {η : ℝ} (hη : 0 < η) (δ : ℝ) :
    Lsc η δ ≫ piEHom ≫ scale3 4 = piEHom ≫ scale3 η⁻¹ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change (4 : ℝ) • piE ((Lsc η δ).hom x) = η⁻¹ • piE x
  rw [piE_Lsc, smul_smul]
  congr 1
  field_simp

theorem Lsc_rho (η : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Lsc η δ ≫ rhoEHom ≫ scale2 4 = rhoEHom ≫ scale2 δ⁻¹ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change (4 : ℝ) • rhoE ((Lsc η δ).hom x) = δ⁻¹ • rhoE x
  rw [rhoE_Lsc, smul_smul]
  congr 1
  field_simp

theorem scaled_boundary_mem {X : TopCat.{0}} (f : X ⟶ X5) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    {cc : singularChainGroup ℚ X (3 + 2)}
    (hcc : (singularBoundary ℚ X 4).hom cc ∈
      subChainSubmodule ℚ X (f.hom ⁻¹' {x : EuclideanSpace ℝ (Fin 5) | δ < ‖rhoE x‖}) 4 ⊔
        subChainSubmodule ℚ X (f.hom ⁻¹' {x : EuclideanSpace ℝ (Fin 5) | η < ‖piE x‖}) 4) :
    (singularBoundary ℚ X 4).hom cc ∈
      subChainSubmodule ℚ X ((f ≫ Lsc η δ).hom ⁻¹' UA) 4 ⊔
        subChainSubmodule ℚ X ((f ≫ Lsc η δ).hom ⁻¹' UB) 4 := by
  have h1 : (f ≫ Lsc η δ).hom ⁻¹' UA = f.hom ⁻¹' {x : EuclideanSpace ℝ (Fin 5) | δ < ‖rhoE x‖} := by
    rw [← Lsc_preimage_UA hδ η]; rfl
  have h2 : (f ≫ Lsc η δ).hom ⁻¹' UB = f.hom ⁻¹' {x : EuclideanSpace ℝ (Fin 5) | η < ‖piE x‖} := by
    rw [← Lsc_preimage_UB hη δ]; rfl
  rw [h1, h2]
  exact hcc

variable (y₁ : (chains R3).X 3 →ₗ[ℚ] ℚ) (θ₁ : (chains R2).X 2 →ₗ[ℚ] ℚ)

/-- **The chart-level value for unit Thom cochains.**  `y₁`, `θ₁` are Thom cochains of radius `1`; for a chain `cc` of `X`
with `∂ cc` over `{δ < ‖ρ f‖}` and `{η < ‖π f‖}` such that the dilated pushforward `((f ≫ Lsc η δ)_# cc)` has class the library
local generator at the origin, `d₅ · ⟨y₁ ∘ (η⁻¹ π f)_#, θ₁ ∘ (δ⁻¹ ρ f)_#⟩(cc) = lamPos · lam2`. -/
theorem chart_scaled
    (hy₁d : ∀ e : (chains R3).X 4, y₁ (((chains R3).d 4 3).hom e) = 0)
    (hy₁v : ∀ τ : singularSimplices (TopCat.of R3) 3, IsSubordinate {v : R3 | 1 < ‖v‖} τ →
      y₁ (chainGenerator ℚ (TopCat.of R3) 3 τ) = 0)
    (hy₁c : ∀ c : (chains R3).X 3, ((chains R3).d 3 2).hom c ∈
        subChainSubmodule ℚ (TopCat.of R3) {v : R3 | 1 < ‖v‖} 2 →
      ∃ h : ((localChains 3).d 3 2).hom ((locR3.f 3).hom c) = 0, y₁ c = degR3 c h)
    (hθ₁d : ∀ e : (chains R2).X 3, θ₁ (((chains R2).d 3 2).hom e) = 0)
    (hθ₁v : ∀ τ : singularSimplices (TopCat.of R2) 2, IsSubordinate {v : R2 | 1 < ‖v‖} τ →
      θ₁ (chainGenerator ℚ (TopCat.of R2) 2 τ) = 0)
    (hθ₁c : ∀ c : (chains R2).X 2, ((chains R2).d 2 1).hom c ∈
        subChainSubmodule ℚ (TopCat.of R2) {v : R2 | 1 < ‖v‖} 1 →
      ∃ h : ((localChains 2).d 2 1).hom ((locR2.f 2).hom c) = 0, θ₁ c = degR2 c h)
    {X : TopCat.{0}} (f : X ⟶ X5) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (cc : singularChainGroup ℚ X (3 + 2))
    (hcc : (singularBoundary ℚ X 4).hom cc ∈
      subChainSubmodule ℚ X (f.hom ⁻¹' {x : EuclideanSpace ℝ (Fin 5) | δ < ‖rhoE x‖}) 4 ⊔
        subChainSubmodule ℚ X (f.hom ⁻¹' {x : EuclideanSpace ℝ (Fin 5) | η < ‖piE x‖}) 4)
    (hpt : homologyMap (supportPointMap (Nset : Set (EuclideanSpace ℝ (Fin 5))) 0 zero_mem_Nset) (3 + 2)
      (relCls ((singularChainMap ℚ (f ≫ Lsc η δ) (3 + 2)).hom cc)
        (relCls_mem_of_sup (push_boundary_mem (f ≫ Lsc η δ) cc (scaled_boundary_mem f hη hδ hcc)))) =
      localGenerator 3 0) :
    d5 * capPairF X (ModuleCat.of ℚ ℚ) 2 3
      (y₁.comp (singularChainMap ℚ (f ≫ piEHom ≫ scale3 η⁻¹) 3).hom)
      (θ₁.comp (singularChainMap ℚ (f ≫ rhoEHom ≫ scale2 δ⁻¹) 2).hom) cc = lamPos * lam2 := by
  have H := thomPair_scale y₁ θ₁ hy₁d hy₁v hy₁c hθ₁d hθ₁v hθ₁c
  have key := chart_pair_oriented H (f ≫ Lsc η δ) cc (scaled_boundary_mem f hη hδ hcc) hpt
  have e1 : (yE (y₁.comp (singularChainMap ℚ (scale3 4) 3).hom)).comp
      (singularChainMap ℚ (f ≫ Lsc η δ) 3).hom =
      y₁.comp (singularChainMap ℚ (f ≫ piEHom ≫ scale3 η⁻¹) 3).hom := by
    unfold yE
    rw [← Lsc_pi hη δ]
    simp only [← Category.assoc, singularChainMap_comp]
    rfl
  have e2 : (thE (θ₁.comp (singularChainMap ℚ (scale2 4) 2).hom)).comp
      (singularChainMap ℚ (f ≫ Lsc η δ) 2).hom =
      θ₁.comp (singularChainMap ℚ (f ≫ rhoEHom ≫ scale2 δ⁻¹) 2).hom := by
    unfold thE
    rw [← Lsc_rho η hδ]
    simp only [← Category.assoc, singularChainMap_comp]
    rfl
  rw [e1, e2] at key
  exact key

end TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport
