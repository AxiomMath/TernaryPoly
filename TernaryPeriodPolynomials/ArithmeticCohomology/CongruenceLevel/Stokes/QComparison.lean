module

public import Mathlib

@[expose] public section


/-!
# Group cohomology of a complex representation and of its underlying rational representation

Formalized by Claude Sonnet 5.5.

For a complex representation `ρ` of a group `H` on `V` (with a compatible `ℚ`-structure) let `qRepG ρ` be the underlying rational representation.  The
2-cocycles and 2-coboundaries of `Rep.of ρ` and of `qRepG ρ` are the same sets of functions `H × H → V`, so `qH2 : H²(H, ρ) →+ H²(H, qRepG ρ)`, `[z] ↦ [z]`, is
a well-defined bijective additive map (`qH2_π`, `qH2_bijective`), natural in the group (`qH2_map`): it commutes with the maps `groupCohomology.map` induced by group
homomorphisms with the identity coefficient comparison.
-/

open CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

section QComparison

variable {H : Type} [Group H] {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ H V)

/-- The rational representation underlying a complex representation. -/
def qReprG : Representation ℚ H V where
  toFun γ := (ρ γ).restrictScalars ℚ
  map_one' := by ext v; simp
  map_mul' a b := by ext v; simp

/-- The rational representation underlying a complex representation, as an object of `Rep ℚ H`. -/
def qRepG : Rep.{0} ℚ H := Rep.of (qReprG ρ)

/-- A complex 2-cocycle is a rational 2-cocycle. -/
def qCoc (z : groupCohomology.cocycles₂ (Rep.of ρ)) : groupCohomology.cocycles₂ (qRepG ρ) :=
  ⟨z.1, (groupCohomology.mem_cocycles₂_iff _).2 ((groupCohomology.mem_cocycles₂_iff z.1).1 z.2)⟩

theorem qCoc_apply (z : groupCohomology.cocycles₂ (Rep.of ρ)) (x : H × H) : (qCoc ρ z).1 x = z.1 x := rfl

/-- A complex 2-coboundary is a rational 2-coboundary. -/
theorem qCob_mem {f : H × H → V} (hf : f ∈ groupCohomology.coboundaries₂ (Rep.of ρ)) :
    f ∈ groupCohomology.coboundaries₂ (qRepG ρ) := by
  obtain ⟨b, hb⟩ := hf
  refine ⟨b, ?_⟩
  funext x
  exact congrFun hb x

theorem qCob_mem' {f : H × H → V} (hf : f ∈ groupCohomology.coboundaries₂ (qRepG ρ)) :
    f ∈ groupCohomology.coboundaries₂ (Rep.of ρ) := by
  obtain ⟨b, hb⟩ := hf
  refine ⟨b, ?_⟩
  funext x
  exact congrFun hb x

/-- The additive map on cocycles. -/
def qCocAdd : groupCohomology.cocycles₂ (Rep.of ρ) →+ groupCohomology.cocycles₂ (qRepG ρ) where
  toFun := qCoc ρ
  map_zero' := rfl
  map_add' _ _ := rfl

theorem qH2_ker (x : groupCohomology.cocycles₂ (Rep.of ρ))
    (hx : (groupCohomology.H2π (Rep.of ρ)) x = 0) : (groupCohomology.H2π (qRepG ρ)) (qCoc ρ x) = 0 := by
  rw [groupCohomology.H2π_eq_zero_iff] at hx ⊢
  exact qCob_mem ρ hx

open Classical in
/-- **The comparison of `H²` of a complex representation with `H²` of its underlying rational representation.** -/
def qH2 : groupCohomology.H2 (Rep.of ρ) →+ groupCohomology.H2 (qRepG ρ) :=
  AddMonoidHom.liftOfRightInverse
    (groupCohomology.H2π (Rep.of ρ)).hom.toAddMonoidHom
    (Function.surjInv ((ModuleCat.epi_iff_surjective (groupCohomology.H2π (Rep.of ρ))).1 inferInstance))
    (Function.rightInverse_surjInv _)
    ⟨((groupCohomology.H2π (qRepG ρ)).hom.toAddMonoidHom).comp (qCocAdd ρ), by
      intro x hx
      exact qH2_ker ρ x hx⟩

theorem qH2_π (z : groupCohomology.cocycles₂ (Rep.of ρ)) :
    qH2 ρ (groupCohomology.H2π (Rep.of ρ) z) = groupCohomology.H2π (qRepG ρ) (qCoc ρ z) := by
  unfold qH2
  exact AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ z

/-- A rational 2-cocycle is a complex 2-cocycle. -/
def qCoc' (z : groupCohomology.cocycles₂ (qRepG ρ)) : groupCohomology.cocycles₂ (Rep.of ρ) :=
  ⟨z.1, (groupCohomology.mem_cocycles₂_iff _).2 ((groupCohomology.mem_cocycles₂_iff z.1).1 z.2)⟩

theorem qH2_surjective : Function.Surjective (qH2 ρ) := by
  intro y
  induction y using groupCohomology.H2_induction_on with
  | h w =>
    refine ⟨groupCohomology.H2π (Rep.of ρ) (qCoc' ρ w), ?_⟩
    rw [qH2_π]
    rfl

theorem qH2_injective : Function.Injective (qH2 ρ) := by
  intro x y hxy
  induction x using groupCohomology.H2_induction_on with
  | h z =>
    induction y using groupCohomology.H2_induction_on with
    | h z' =>
      rw [qH2_π, qH2_π, groupCohomology.H2π_eq_iff] at hxy
      rw [groupCohomology.H2π_eq_iff]
      exact qCob_mem' ρ hxy

theorem qH2_bijective : Function.Bijective (qH2 ρ) := ⟨qH2_injective ρ, qH2_surjective ρ⟩

/-- **Naturality of the comparison in the group**: it commutes with the maps of group cohomology induced by group homomorphisms. -/
theorem qH2_map {K : Type} [Group K] (α : K →* H) (x : groupCohomology.H2 (Rep.of ρ)) :
    qH2 (ρ.comp α) ((groupCohomology.map α (𝟙 (Rep.res α (Rep.of ρ))) 2).hom x) =
      (groupCohomology.map α (𝟙 (Rep.res α (qRepG ρ))) 2).hom (qH2 ρ x) := by
  induction x using groupCohomology.H2_induction_on with
  | h z =>
    have h1 : (groupCohomology.map α (𝟙 (Rep.res α (Rep.of ρ))) 2).hom (groupCohomology.H2π (Rep.of ρ) z) =
        groupCohomology.H2π (Rep.of (ρ.comp α))
          (groupCohomology.mapCocycles₂ α (𝟙 (Rep.res α (Rep.of ρ))) z) :=
      groupCohomology.H2π_comp_map_apply α (𝟙 _) z
    have h2 : (groupCohomology.map α (𝟙 (Rep.res α (qRepG ρ))) 2).hom
          (groupCohomology.H2π (qRepG ρ) (qCoc ρ z)) =
        groupCohomology.H2π (qRepG (ρ.comp α))
          (groupCohomology.mapCocycles₂ α (𝟙 (Rep.res α (qRepG ρ))) (qCoc ρ z)) :=
      groupCohomology.H2π_comp_map_apply α (𝟙 _) (qCoc ρ z)
    rw [qH2_π ρ z, h1, h2, qH2_π]
    rfl

end QComparison

end TernaryPeriodPolynomials.Argument.GammaNStokes
