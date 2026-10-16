module

public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.MayerVietorisMaps

@[expose] public section


noncomputable section
namespace TernaryPoly.EquivariantSingularMayerVietoris
open Module CategoryTheory FreeActionLinearization EquivariantSingularResolution EquivariantSingularSmall
open SphereOddDegree SphereOddDegree.AffineBarycentricSubdivision TopologicalSpace
open scoped Classical

variable (G : Type) [Group G] (E : TopCat.{0}) [MulAction G E] [ContinuousConstSMul G E]

/-- For a group action, forward invariance of a simplex predicate is equivalent to invariance in both directions. -/
theorem invariant_predicate_iff (n : ℕ) (P : SingularSimplex E n → Prop)
    (hP : ∀ (g : G) (σ : SingularSimplex E n), P σ → P (g • σ))
    (g : G) (σ : SingularSimplex E n) : P (g • σ) ↔ P σ := by
  constructor
  · intro h
    simpa only [inv_smul_smul] using hP g⁻¹ (g • σ) h
  · exact hP g σ

/-- The scalar coordinate-keep projection is equivariant whenever its actual simplex predicate is invariant. -/
theorem keepHom_equivariant (n : ℕ) (P : SingularSimplex E n → Prop)
    (hP : ∀ (g : G) (σ : SingularSimplex E n), P σ → P (g • σ)) (g : G) :
    (keepHom ℚ E P).hom.comp (chainAction G E n g) =
      (chainAction G E n g).comp (keepHom ℚ E P).hom := by
  apply (generatorBasis E n).ext
  intro σ
  change (keepHom ℚ E P).hom (chainAction G E n g (generatorBasis E n σ)) =
    chainAction G E n g ((keepHom ℚ E P).hom (generatorBasis E n σ))
  rw [generatorBasis_apply, chainAction_generator, keepHom_generator, keepHom_generator]
  by_cases hσ : P σ
  · rw [ite_eq_left hσ, ite_eq_left ((invariant_predicate_iff G E n P hP g σ).mpr hσ), chainAction_generator]
  · rw [ite_eq_right hσ, ite_eq_right (fun h => hσ ((invariant_predicate_iff G E n P hP g σ).mp h)), map_zero]

/-- Elementwise equivariance of the actual coordinate-keep projection. -/
theorem keepHom_smul (n : ℕ) (P : SingularSimplex E n → Prop)
    (hP : ∀ (g : G) (σ : SingularSimplex E n), P σ → P (g • σ))
    (g : G) (c : (underlyingChains E).X n) :
    (keepHom ℚ E P).hom (chainAction G E n g c) =
      chainAction G E n g ((keepHom ℚ E P).hom c) :=
  LinearMap.congr_fun (keepHom_equivariant G E n P hP g) c

variable (U V : Opens E) (hU : InvariantSet G E (U : Set E)) (hV : InvariantSet G E (V : Set E))
  (hUV : U ⊔ V = ⊤)

include hU hV in
/-- The exact right-only routing predicate is invariant under the actual deck action. -/
theorem subVnotU_invariant (n : ℕ) (g : G) (σ : SingularSimplex E n)
    (hσ : IsSubVnotU U V σ) : IsSubVnotU U V (g • σ) := by
  exact ⟨subordinate_invariant G E (V : Set E) hV n g σ hσ.1,
    fun h => hσ.2 ((invariant_predicate_iff G E n (IsSubordinate (U : Set E))
      (subordinate_invariant G E (U : Set E) hU n) g σ).mp h)⟩

/-- The literal scalar left routing map lifts to an equivariant map of actual small-chain degrees. -/
def routeLeft (n : ℕ) : (coverChains G E U V hU hV hUV).X n ⟶ (leftChains G E U hU).X n :=
  Rep.ofHom ⟨(routeU ℚ U V hUV n).hom, fun g => by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact keepHom_smul G E n (IsSubordinate (U : Set E)) (subordinate_invariant G E _ hU n) g c.val⟩

/-- The literal scalar right-only routing map lifts to an equivariant map. -/
def routeRight (n : ℕ) : (coverChains G E U V hU hV hUV).X n ⟶ (rightChains G E V hV).X n :=
  Rep.ofHom ⟨(routeV ℚ U V hUV n).hom, fun g => by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact keepHom_smul G E n (IsSubVnotU U V) (subVnotU_invariant G E U V hU hV n) g c.val⟩

/-- The actual right-chain projection to intersection chains is equivariant. -/
def projectRightToInter (n : ℕ) : (rightChains G E V hV).X n ⟶ (interChains G E U V hU hV).X n :=
  Rep.ofHom ⟨(projVtoUV ℚ U V n).hom, fun g => by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact keepHom_smul G E n (IsSubordinate (U : Set E)) (subordinate_invariant G E _ hU n) g c.val⟩

end TernaryPoly.EquivariantSingularMayerVietoris
