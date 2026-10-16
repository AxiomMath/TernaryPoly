module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.ChartTheorem

@[expose] public section


/-!
# Naturality of the cap pairing and the chart-level value for a chain of an arbitrary chart

`capPairF_natural`: the pairing `y ∘ (f ∩ -)` of two pulled-back cochains evaluated on a chain equals the pairing of the
original cochains on the pushed-forward chain.  Together with `chart_value` this gives the value of the pairing of the
pulled-back Thom cochains on a chain of any space `X` mapping to `ℝ⁵`: `chart_pair_value`.

Formalized by Claude Sonnet 5.5.
-/

open SphereOddDegree SphereOddDegree.AlexanderWhitney SphereOddDegree.AffineBarycentricSubdivision
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open TernaryPeriodPolynomials.Argument.Lemma33.Locality
open TernaryPeriodPolynomials.Argument.Lemma33.Orient
open TernaryPoly TernaryPoly.EuclideanLocalHomology TernaryPoly.ContractibleSingularHomology
  TernaryPoly.RationalRelativeSingular TernaryPoly.RationalManifoldCompact
open TernaryPoly.SingularLocalCap.Descent TernaryPoly.SingularLocalCap

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport

local notation "X5" => TopCat.of (EuclideanSpace ℝ (Fin 5))

/-- **Naturality of the cap pairing.** -/
theorem capPairF_natural {X Y : TopCat.{0}} (g : X ⟶ Y) (a b : ℕ)
    (y : singularChainGroup ℚ Y b →ₗ[ℚ] ℚ) (f : singularChainGroup ℚ Y a →ₗ[ℚ] ℚ)
    (c : singularChainGroup ℚ X (a + b)) :
    capPairF Y (ModuleCat.of ℚ ℚ) a b y f ((singularChainMap ℚ g (a + b)).hom c) =
      capPairF X (ModuleCat.of ℚ ℚ) a b (y.comp (singularChainMap ℚ g b).hom)
        (f.comp (singularChainMap ℚ g a).hom) c := by
  have : (capPairF Y (ModuleCat.of ℚ ℚ) a b y f).comp (singularChainMap ℚ g (a + b)).hom =
      capPairF X (ModuleCat.of ℚ ℚ) a b (y.comp (singularChainMap ℚ g b).hom)
        (f.comp (singularChainMap ℚ g a).hom) := by
    apply scalarChain_ext
    intro σ
    rw [LinearMap.comp_apply, singularChainMap_generator, capPairF_generator, capPairF_generator,
      LinearMap.comp_apply, LinearMap.comp_apply, singularChainMap_generator, singularChainMap_generator]
    have h1 : backSimplex Y a b (pushSimplex g (a + b) σ) = pushSimplex g b (backSimplex X a b σ) :=
      (backSimplex_naturality g a b σ).symm
    have h2 : frontSimplex Y a b (pushSimplex g (a + b) σ) = pushSimplex g a (frontSimplex X a b σ) :=
      (frontSimplex_naturality g a b σ).symm
    rw [h1, h2]
  exact congrArg (fun L => L c) this

variable {y₀ : (chains R3).X 3 →ₗ[ℚ] ℚ} {θ₀ : (chains R2).X 2 →ₗ[ℚ] ℚ}

/-- The pushforward of a chain of `X` whose boundary lies over the preimages of `UA` and `UB` has boundary over `UA`, `UB`. -/
theorem push_boundary_mem {X : TopCat.{0}} (F : X ⟶ X5) (cc : singularChainGroup ℚ X (3 + 2))
    (hcc : (singularBoundary ℚ X 4).hom cc ∈
      subChainSubmodule ℚ X (F.hom ⁻¹' UA) 4 ⊔ subChainSubmodule ℚ X (F.hom ⁻¹' UB) 4) :
    (singularBoundary ℚ X5 4).hom ((singularChainMap ℚ F (3 + 2)).hom cc) ∈
      subChainSubmodule ℚ X5 UA 4 ⊔ subChainSubmodule ℚ X5 UB 4 := by
  have h1 := singularChainMap_boundary_apply ℚ F 4 cc
  have h2 : (singularBoundary ℚ X5 4).hom ((singularChainMap ℚ F (3 + 2)).hom cc) =
      (singularChainMap ℚ F 4).hom ((singularBoundary ℚ X 4).hom cc) := h1
  rw [h2]
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hcc
  rw [← hab, map_add]
  exact Submodule.add_mem_sup (singularChainMap_mem_sub F UA 4 ha) (singularChainMap_mem_sub F UB 4 hb)

/-- **The chart-level value of the pulled-back Thom pairing.**  For a continuous map `F : X ⟶ ℝ⁵` and a 5-chain `cc` of `X`
whose boundary lies over `F⁻¹ UA` and `F⁻¹ UB`, if `d₅ · [F_# cc] = q · [stair]` in `H₅(ℝ⁵, ℝ⁵ ∖ Nset)` then
`d₅ · ⟨y₀ ∘ (π F)_#, θ₀ ∘ (ρ F)_#⟩(cc) = q · lamPos · lam2`. -/
theorem chart_pair_value (H : ThomPair y₀ θ₀) {X : TopCat.{0}} (F : X ⟶ X5) (cc : singularChainGroup ℚ X (3 + 2))
    (hcc : (singularBoundary ℚ X 4).hom cc ∈
      subChainSubmodule ℚ X (F.hom ⁻¹' UA) 4 ⊔ subChainSubmodule ℚ X (F.hom ⁻¹' UB) 4)
    (d5 q : ℚ)
    (e : d5 • relCls ((singularChainMap ℚ F (3 + 2)).hom cc)
        (relCls_mem_of_sup (push_boundary_mem F cc hcc)) =
      q • relCls stair (relCls_mem_of_sup stair_boundary_mem)) :
    d5 * capPairF X (ModuleCat.of ℚ ℚ) 2 3 ((yE y₀).comp (singularChainMap ℚ F 3).hom)
      ((thE θ₀).comp (singularChainMap ℚ F 2).hom) cc = q * (lamPos * lam2) := by
  rw [← capPairF_natural F 2 3 (yE y₀) (thE θ₀) cc]
  exact chart_value H _ (push_boundary_mem F cc hcc) d5 q e

end TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport
