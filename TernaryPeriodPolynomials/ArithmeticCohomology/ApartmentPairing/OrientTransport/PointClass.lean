module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.LocalClass
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.ChartScaled
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.ChartChange
public import TernaryPeriodPolynomials.GroupCohomology.Relative.CapConnectingAlgebra

@[expose] public section


/-!
# Point classes of chains

* `rcls_eq_of_decomp`: two chains whose difference is a chain over `S` plus a boundary have the same class in `H(X, S)`.
* `relCls_point`: the point restriction of `relCls` (on `Nset`) is the class `rcls` at the origin.
* `Lsc_pointClass`: the dilation `Lsc` carries a chain with local class the library generator at the origin to one with the
  same property.

Formalized by Claude Sonnet 5.5.
-/

open SphereOddDegree SphereOddDegree.AlexanderWhitney SphereOddDegree.AffineBarycentricSubdivision
open CategoryTheory CategoryTheory.Limits HomologicalComplex TopologicalSpace
open TernaryPeriodPolynomials.Argument.Lemma33.Locality
open TernaryPeriodPolynomials.Argument.Lemma33.Orient
open TernaryPoly TernaryPoly.EuclideanLocalHomology TernaryPoly.ContractibleSingularHomology
  TernaryPoly.RationalRelativeSingular TernaryPoly.RationalManifoldCompact
  TernaryPoly.RationalLocalChartHomology TernaryPoly.RationalRelativeExcision TernaryPoly.RationalLocalMap
  TernaryPoly.RationalSingularAugmentation TernaryPoly.RationalLocalOrientation
open TernaryPoly.SingularLocalCap.Descent

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport

/-- Two chains differing by a chain over `S` and a boundary have the same class in `H(X, S)`. -/
theorem rcls_eq_of_decomp {X : TopCat.{0}} (S : Set X) (n : ℕ) (c c' : singularChainGroup ℚ X (n + 1))
    (h : (singularBoundary ℚ X n).hom c ∈ subChainSubmodule ℚ X S n)
    (h' : (singularBoundary ℚ X n).hom c' ∈ subChainSubmodule ℚ X S n)
    (w : singularChainGroup ℚ X (n + 1)) (hw : w ∈ subChainSubmodule ℚ X S (n + 1))
    (u : singularChainGroup ℚ X (n + 2))
    (hc : c = c' + w + (singularBoundary ℚ X (n + 1)).hom u) :
    rcls (X := X) S n c h = rcls (X := X) S n c' h' := by
  unfold rcls
  apply TernaryPoly.RelativeCapConnecting.chainClass_eq_of_boundary (relativeChains S) (n + 1) _ _
    ((cokernel.π (RationalRelativeSingular.inclusion S)).f (n + 2) u)
  have hd := ConcreteCategory.congr_hom
    ((cokernel.π (RationalRelativeSingular.inclusion S)).comm (n + 2) (n + 1)) u
  have hw0 : (cokernel.π (RationalRelativeSingular.inclusion S)).f (n + 1) w = 0 :=
    (rel_proj_eq_zero_iff S (n + 1) w).mpr hw
  have hsub : (cokernel.π (RationalRelativeSingular.inclusion S)).f (n + 1) c -
      (cokernel.π (RationalRelativeSingular.inclusion S)).f (n + 1) c' =
      (cokernel.π (RationalRelativeSingular.inclusion S)).f (n + 1) w +
      (cokernel.π (RationalRelativeSingular.inclusion S)).f (n + 1) ((singularBoundary ℚ X (n + 1)).hom u) := by
    rw [← map_sub, ← map_add, hc]
    congr 1
    abel
  change ((relativeChains S).d (n + 2) (n + 1)).hom
      ((cokernel.π (RationalRelativeSingular.inclusion S)).f (n + 2) u) =
    (cokernel.π (RationalRelativeSingular.inclusion S)).f (n + 1) c -
      (cokernel.π (RationalRelativeSingular.inclusion S)).f (n + 1) c'
  rw [hsub, hw0, zero_add]
  exact hd


/-- The diagonal matrix `diag(a, a, a, b, b)`. -/
def Dmat (a b : ℝ) : Matrix (Fin 5) (Fin 5) ℝ := Matrix.diagonal ![a, a, a, b, b]

theorem det_Dmat (a b : ℝ) : (Dmat a b).det = a ^ 3 * b ^ 2 := by
  simp [Dmat, Matrix.det_diagonal, Fin.prod_univ_succ]
  ring

/-- The diagonal dilation as an element of the general linear group. -/
def Dgl (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : Matrix.GeneralLinearGroup (Fin 5) ℝ :=
  Matrix.GeneralLinearGroup.mk'' (Dmat a b) (by
    rw [det_Dmat]
    exact isUnit_iff_ne_zero.mpr (by positivity))

theorem Dgl_det_pos (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    0 < (Matrix.GeneralLinearGroup.det (Dgl a b ha hb) : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  change 0 < (Dmat a b).det
  rw [det_Dmat]
  positivity

theorem LscL_eq_linE (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (x : EuclideanSpace ℝ (Fin 5)) :
    LscL a b x = linE (Dgl a b ha hb) x := by
  apply PiLp.ext
  intro i
  fin_cases i
  all_goals simp [LscL, linE, Dgl, Dmat, prodEL, Matrix.mulVec, dotProduct, Matrix.diagonal_apply]


theorem relativeMap_congr {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (S : Set X) (T : Set Y)
    (f g : C(X, Y)) (hfg : f = g) (hf : Set.MapsTo f S T) (hg : Set.MapsTo g S T) :
    relativeMap f S T hf = relativeMap g S T hg := by
  subst hfg; rfl

theorem Lsc_hom_eq {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    (Lsc η δ).hom = linE (Dgl ((4 * η)⁻¹) ((4 * δ)⁻¹) (by positivity) (by positivity)) :=
  ContinuousMap.ext fun x => LscL_eq_linE _ _ (by positivity) (by positivity) x

theorem Lsc_zero (η δ : ℝ) : (Lsc η δ).hom 0 = 0 := by
  change LscL _ _ 0 = 0
  exact map_zero _

/-- **The dilation preserves the library generator at the origin.** -/
theorem Lsc_pointClass {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (c : singularChainGroup ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) (4 + 1))
    (h0 : (singularBoundary ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) 4).hom c ∈
      subChainSubmodule ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 5))) 4)
    (h0' : (singularBoundary ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) 4).hom
      ((singularChainMap ℚ (Lsc η δ) (4 + 1)).hom c) ∈
      subChainSubmodule ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 5))) 4)
    (hpt : rcls (X := TopCat.of (EuclideanSpace ℝ (Fin 5))) ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 5))) 4 c h0 =
      localGenerator 3 0) :
    rcls (X := TopCat.of (EuclideanSpace ℝ (Fin 5))) ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 5))) 4
      ((singularChainMap ℚ (Lsc η δ) (4 + 1)).hom c) h0' = localGenerator 3 0 := by
  have hm : Set.MapsTo (Lsc η δ).hom ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 5)))
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 5))) := by
    intro z hz hz0
    apply hz
    have := linE_injective (Dgl ((4 * η)⁻¹) ((4 * δ)⁻¹) (by positivity) (by positivity))
    apply this
    rw [← Lsc_hom_eq hη hδ]
    rw [Lsc_zero]
    exact hz0
  have h1 := rcls_map (X := TopCat.of (EuclideanSpace ℝ (Fin 5))) (Y := TopCat.of (EuclideanSpace ℝ (Fin 5)))
    (Lsc η δ) _ _ hm 4 c h0 h0'
  rw [← h1, hpt]
  have hlin : Set.MapsTo (linE (Dgl ((4 * η)⁻¹) ((4 * δ)⁻¹) (by positivity) (by positivity)))
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 5))) ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 5))) := by
    rw [← Lsc_hom_eq hη hδ]; exact hm
  rw [relativeMap_congr _ _ _ _ (Lsc_hom_eq hη hδ) hm hlin]
  exact linE_generator' (Dgl_det_pos _ _ (by positivity) (by positivity)) 0 0 (by
    rw [← Lsc_hom_eq hη hδ]; exact Lsc_zero η δ) hlin


theorem rcls_congr {X : TopCat.{0}} (S : Set X) (n : ℕ) (c c' : singularChainGroup ℚ X (n + 1))
    (hcc : c = c')
    (h : (singularBoundary ℚ X n).hom c ∈ subChainSubmodule ℚ X S n)
    (h' : (singularBoundary ℚ X n).hom c' ∈ subChainSubmodule ℚ X S n) :
    rcls (X := X) S n c h = rcls (X := X) S n c' h' := by
  subst hcc; rfl

theorem compl_Nset_sub_punct : (Nset : Set (EuclideanSpace ℝ (Fin 5)))ᶜ ⊆ ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 5))) := by
  intro x hx h0
  apply hx
  rw [Set.mem_singleton_iff.mp h0]
  exact zero_mem_Nset

/-- The point restriction of the class on `Nset` is the local class at the origin. -/
theorem relCls_point (c : singularChainGroup ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) (3 + 2))
    (h : (singularBoundary ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) (3 + 2 - 1)).hom c ∈
      subChainSubmodule ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) (Nset : Set (TopCat.of (EuclideanSpace ℝ (Fin 5))))ᶜ (3 + 2 - 1))
    (h0 : (singularBoundary ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) 4).hom c ∈
      subChainSubmodule ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 5))) 4) :
    homologyMap (supportPointMap (Nset : Set (EuclideanSpace ℝ (Fin 5))) 0 zero_mem_Nset) (3 + 2)
      (relCls c h) =
    rcls (X := TopCat.of (EuclideanSpace ℝ (Fin 5))) ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 5))) 4 c h0 := by
  have h1 := rcls_map (X := TopCat.of (EuclideanSpace ℝ (Fin 5))) (Y := TopCat.of (EuclideanSpace ℝ (Fin 5)))
    (𝟙 _) ((Nset : Set (EuclideanSpace ℝ (Fin 5)))ᶜ) ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 5)))
    (fun z hz => compl_Nset_sub_punct hz) 4 c h (by
      rw [show (singularChainMap ℚ (𝟙 (TopCat.of (EuclideanSpace ℝ (Fin 5)))) (4 + 1)).hom c = c from
        congrArg (fun F => F.hom c) (singularChainMap_id ℚ _ _)]
      exact h0)
  refine h1.trans ?_
  exact rcls_congr _ _ _ _ (congrArg (fun F => F.hom c) (singularChainMap_id ℚ _ _)) _ _


/-- The Thom conditions of radius `1` on a pair of cochains of `ℝ³` and `ℝ²`. -/
structure UnitThom (y₁ : (chains R3).X 3 →ₗ[ℚ] ℚ) (θ₁ : (chains R2).X 2 →ₗ[ℚ] ℚ) : Prop where
  y_cocycle : ∀ e : (chains R3).X 4, y₁ (((chains R3).d 4 3).hom e) = 0
  y_vanish : ∀ τ : singularSimplices (TopCat.of R3) 3, IsSubordinate {v : R3 | 1 < ‖v‖} τ →
    y₁ (chainGenerator ℚ (TopCat.of R3) 3 τ) = 0
  y_deg : ∀ c : (chains R3).X 3, ((chains R3).d 3 2).hom c ∈
      subChainSubmodule ℚ (TopCat.of R3) {v : R3 | 1 < ‖v‖} 2 →
    ∃ h : ((EuclideanLocalHomology.localChains 3).d 3 2).hom ((locR3.f 3).hom c) = 0, y₁ c = degR3 c h
  t_cocycle : ∀ e : (chains R2).X 3, θ₁ (((chains R2).d 3 2).hom e) = 0
  t_vanish : ∀ τ : singularSimplices (TopCat.of R2) 2, IsSubordinate {v : R2 | 1 < ‖v‖} τ →
    θ₁ (chainGenerator ℚ (TopCat.of R2) 2 τ) = 0
  t_deg : ∀ c : (chains R2).X 2, ((chains R2).d 2 1).hom c ∈
      subChainSubmodule ℚ (TopCat.of R2) {v : R2 | 1 < ‖v‖} 1 →
    ∃ h : ((EuclideanLocalHomology.localChains 2).d 2 1).hom ((locR2.f 2).hom c) = 0, θ₁ c = degR2 c h

/-- **The oriented chart-level value, with the orientation read at the origin of the unscaled chart.** -/
theorem chart_scaled_pt {y₁ : (chains R3).X 3 →ₗ[ℚ] ℚ} {θ₁ : (chains R2).X 2 →ₗ[ℚ] ℚ} (T : UnitThom y₁ θ₁)
    {X : TopCat.{0}} (f : X ⟶ TopCat.of (EuclideanSpace ℝ (Fin 5))) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (cc : singularChainGroup ℚ X (3 + 2))
    (hcc : (singularBoundary ℚ X 4).hom cc ∈
      subChainSubmodule ℚ X (f.hom ⁻¹' {x : EuclideanSpace ℝ (Fin 5) | δ < ‖rhoE x‖}) 4 ⊔
        subChainSubmodule ℚ X (f.hom ⁻¹' {x : EuclideanSpace ℝ (Fin 5) | η < ‖piE x‖}) 4)
    (h0 : (singularBoundary ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) 4).hom
      ((singularChainMap ℚ f (4 + 1)).hom cc) ∈
      subChainSubmodule ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 5))) 4)
    (hpt : rcls (X := TopCat.of (EuclideanSpace ℝ (Fin 5))) ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 5))) 4
      ((singularChainMap ℚ f (4 + 1)).hom cc) h0 = localGenerator 3 0) :
    d5 * capPairF X (ModuleCat.of ℚ ℚ) 2 3
      (y₁.comp (singularChainMap ℚ (f ≫ piEHom ≫ scale3 η⁻¹) 3).hom)
      (θ₁.comp (singularChainMap ℚ (f ≫ rhoEHom ≫ scale2 δ⁻¹) 2).hom) cc = lamPos * lam2 := by
  have hb := relCls_mem_of_sup (push_boundary_mem (f ≫ Lsc η δ) cc (scaled_boundary_mem f hη hδ hcc))
  have hb0 : (singularBoundary ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) 4).hom
      ((singularChainMap ℚ (f ≫ Lsc η δ) (4 + 1)).hom cc) ∈
      subChainSubmodule ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 5))) 4 :=
    subChainSubmodule_mono compl_Nset_sub_punct 4 hb
  refine chart_scaled y₁ θ₁ T.y_cocycle T.y_vanish T.y_deg T.t_cocycle T.t_vanish T.t_deg f hη hδ cc hcc ?_
  rw [relCls_point _ hb hb0]
  have hcomp : (singularChainMap ℚ (f ≫ Lsc η δ) (4 + 1)).hom cc =
      (singularChainMap ℚ (Lsc η δ) (4 + 1)).hom ((singularChainMap ℚ f (4 + 1)).hom cc) := by
    rw [singularChainMap_comp]; rfl
  rw [rcls_congr _ _ _ _ hcomp hb0 (by rw [← hcomp]; exact hb0)]
  exact Lsc_pointClass hη hδ _ h0 _ hpt

end TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport
