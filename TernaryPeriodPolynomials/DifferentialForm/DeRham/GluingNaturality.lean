module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.GluingCohomology

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothDeRhamGluing
open Set SmoothLocalDeRham SmoothCoveringDeRham SymmetricSpaceCovering CategoryTheory
open scoped ContDiff Topology

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {ρ : Representation ℝ DeckGroup F} {U V U' V' : Set OrbitSpace}

theorem restrictEquivariant_trans {A B C : Set OrbitSpace} (hAB : A ⊆ B) (hBC : B ⊆ C)
    (n : ℕ) (w : EquivariantForm ρ C n) :
    restrictEquivariant ρ hAB n (restrictEquivariant ρ hBC n w) =
      restrictEquivariant ρ (hAB.trans hBC) n w := by
  apply Subtype.ext
  apply Form.ext
  intro x hx
  rw [restrictEquivariant_apply ρ _ _ hx, restrictEquivariant_apply ρ _ _ hx,
    restrictEquivariant_apply ρ _ _ (liftedDomain_mono hAB hx)]

variable (ρ) (hU : IsOpen U) (hV : IsOpen V) (hU' : IsOpen U') (hV' : IsOpen V')
  (hUU' : U ⊆ U') (hVV' : V ⊆ V')

def ordinaryPairRestriction : ordinaryPairComplex ρ hU' hV' ⟶ ordinaryPairComplex ρ hU hV :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom
    ((restrictEquivariant ρ hUU' n).prodMap (restrictEquivariant ρ hVV' n))) (by
      intro n
      simp only [ordinaryPairComplex, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro p
      exact Prod.ext (restrictEquivariant_d ρ hU' hU hUU' p.1).symm
        (restrictEquivariant_d ρ hV' hV hVV' p.2).symm)

/-- The ordinary Mayer-Vietoris short exact complexes are contravariantly natural for actual
inclusions of pairs of quotient opens. -/
def ordinarySequenceRestriction : ordinarySequence ρ hU' hV' ⟶ ordinarySequence ρ hU hV where
  τ₁ := restrictionChainMap ρ (hU'.union hV') (hU.union hV) (union_subset_union hUU' hVV')
  τ₂ := ordinaryPairRestriction ρ hU hV hU' hV' hUU' hVV'
  τ₃ := restrictionChainMap ρ (hU'.inter hV') (hU.inter hV) (inter_subset_inter hUU' hVV')
  comm₁₂ := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro w
    change EquivariantForm ρ (U' ∪ V') n at w
    apply Prod.ext
    · change restrictEquivariant ρ subset_union_left n
        (restrictEquivariant ρ (union_subset_union hUU' hVV') n w) =
        restrictEquivariant ρ hUU' n (restrictEquivariant ρ subset_union_left n w)
      rw [restrictEquivariant_trans, restrictEquivariant_trans]
    · change restrictEquivariant ρ subset_union_right n
        (restrictEquivariant ρ (union_subset_union hUU' hVV') n w) =
        restrictEquivariant ρ hVV' n (restrictEquivariant ρ subset_union_right n w)
      rw [restrictEquivariant_trans, restrictEquivariant_trans]
  comm₂₃ := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro p
    change EquivariantForm ρ U' n × EquivariantForm ρ V' n at p
    change restrictEquivariant ρ inter_subset_left n (restrictEquivariant ρ hUU' n p.1) -
      restrictEquivariant ρ inter_subset_right n (restrictEquivariant ρ hVV' n p.2) =
      restrictEquivariant ρ (inter_subset_inter hUU' hVV') n
        (restrictEquivariant ρ inter_subset_left n p.1 - restrictEquivariant ρ inter_subset_right n p.2)
    rw [map_sub, restrictEquivariant_trans, restrictEquivariant_trans,
      restrictEquivariant_trans, restrictEquivariant_trans]

/-- Naturality of the actual ordinary connecting homomorphism under restriction of open pairs. -/
theorem ordinaryConnecting_natural (n : ℕ) :
    ordinaryConnecting ρ hU' hV' n ≫
      HomologicalComplex.homologyMap
        (restrictionChainMap ρ (hU'.union hV') (hU.union hV) (union_subset_union hUU' hVV')) (n + 1) =
      HomologicalComplex.homologyMap
        (restrictionChainMap ρ (hU'.inter hV') (hU.inter hV) (inter_subset_inter hUU' hVV')) n ≫
        ordinaryConnecting ρ hU hV n :=
  HomologicalComplex.HomologySequence.δ_naturality
    (ordinarySequenceRestriction ρ hU hV hU' hV' hUU' hVV')
    (ordinarySequence_shortExact ρ hU' hV') (ordinarySequence_shortExact ρ hU hV) n (n + 1) rfl

end TernaryPoly.SmoothDeRhamGluing
