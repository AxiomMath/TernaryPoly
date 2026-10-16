module

public import Mathlib

@[expose] public section


/-!
# Comparing the coinvariants of a tensored bar resolution with those of a relatively projective one

Formalized by Claude Sonnet 5.5.

* `A ⊗ -` preserves projective objects of `Rep ℚ G` (`tensorLeft_preservesProjective`, because its right adjoint
  `Hom_ℚ(A, -)` preserves epimorphisms: `ihom_preservesEpi`), and quasi-isomorphisms (`quasiIso_tensorLeft`).
* `tensorResolution A P` is the projective resolution `A ⊗ P_• → A ⊗ Z` obtained from a projective resolution `P → Z`;
  `tensorResolution'` does the same for a resolution `K → 1` of the trivial representation *whose tensor products with `A`
  are projective*, without `K` itself being projective.
* `isIso_homologyMap_tensorComparison`: for such a `K` and a chain map `ξ : std → K` over `1`, the map induced on
  `(A ⊗ -)_G`-complexes is a quasi-isomorphism.  Hence `Hₙ(G, A)` may be computed from `(A ⊗ K_•)_G`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GroupHomologyDescent

open CategoryTheory MonoidalCategory Limits

variable {G : Type} [Group G]

/-- The internal hom `Hom_ℚ(A, -)` preserves epimorphisms of representations over a field. -/
instance ihom_preservesEpi (A : Rep ℚ G) : (ihom A).PreservesEpimorphisms where
  preserves {X Y} f hf := by
    rw [Rep.epi_iff_surjective] at hf ⊢
    intro h
    obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective f.hom.toLinearMap
      (LinearMap.range_eq_top.mpr hf)
    let h' : ↑A →ₗ[ℚ] ↑Y := h
    refine ⟨(s ∘ₗ h' : ↑A →ₗ[ℚ] ↑X), ?_⟩
    have key : (f.hom.toLinearMap ∘ₗ (s ∘ₗ h') : ↑A →ₗ[ℚ] ↑Y) = h' := by
      rw [← LinearMap.comp_assoc, hs]
      rfl
    exact key

/-- `A ⊗ -` preserves projective objects in `Rep ℚ G`. -/
instance tensorLeft_preservesProjective (A : Rep ℚ G) :
    (tensorLeft A).PreservesProjectiveObjects :=
  Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms (ihom.adjunction A)

/-- A chain map between projective resolutions over the identity is a homotopy equivalence. -/
def resHomotopyEquiv' {X : Rep ℚ G} (P Q : ProjectiveResolution X) (φ : P.complex ⟶ Q.complex)
    (hφ : φ.f 0 ≫ Q.π.f 0 = P.π.f 0) : HomotopyEquiv P.complex Q.complex where
  hom := φ
  inv := ProjectiveResolution.lift (𝟙 X) Q P
  homotopyHomInvId := by
    have hφ' : φ ≫ Q.π = P.π := by
      refine HomologicalComplex.to_single_hom_ext ?_
      simpa using hφ
    refine ProjectiveResolution.liftHomotopy (𝟙 X) _ _ ?_ ?_
    · rw [Category.assoc, ProjectiveResolution.lift_commutes, ← Category.assoc, hφ']
    · simp
  homotopyInvHomId := by
    have hφ' : φ ≫ Q.π = P.π := by
      refine HomologicalComplex.to_single_hom_ext ?_
      simpa using hφ
    refine ProjectiveResolution.liftHomotopy (𝟙 X) _ _ ?_ ?_
    · rw [Category.assoc, hφ', ProjectiveResolution.lift_commutes]
    · simp

/-- The functor `A ⊗ -` on `Rep ℚ G` preserves quasi-isomorphisms of chain complexes. -/
theorem quasiIso_tensorLeft (A : Rep ℚ G) {X Y : ChainComplex (Rep ℚ G) ℕ} (f : X ⟶ Y) [QuasiIso f] :
    QuasiIso (((tensorLeft A).mapHomologicalComplex (ComplexShape.down ℕ)).map f) := by
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ (forget₂ (Rep ℚ G) (ModuleCat ℚ))]
  have h1 : QuasiIso (((forget₂ (Rep ℚ G) (ModuleCat ℚ)).mapHomologicalComplex (ComplexShape.down ℕ)).map f) := by
    rw [HomologicalComplex.quasiIso_map_iff_of_preservesHomology]
    infer_instance
  have h2 : QuasiIso (((tensorLeft ((forget₂ (Rep ℚ G) (ModuleCat ℚ)).obj A)).mapHomologicalComplex
      (ComplexShape.down ℕ)).map (((forget₂ (Rep ℚ G) (ModuleCat ℚ)).mapHomologicalComplex
        (ComplexShape.down ℕ)).map f)) :=
    by have := h1; infer_instance
  exact h2


open Rep in
/-- Tensoring a projective resolution of `Z` with `A` gives a projective resolution of `A ⊗ Z`. -/
def tensorResolution (A : Rep ℚ G) {Z : Rep ℚ G} (P : ProjectiveResolution Z) :
    ProjectiveResolution (A ⊗ Z) where
  complex := ((tensorLeft A).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  projective n := (tensorLeft A).projective_obj_of_projective (P.projective n)
  π := ((tensorLeft A).mapHomologicalComplex (ComplexShape.down ℕ)).map P.π ≫
    (HomologicalComplex.singleMapHomologicalComplex (tensorLeft A) (ComplexShape.down ℕ) 0).hom.app Z
  quasiIso := by
    have := quasiIso_tensorLeft A P.π
    infer_instance


/-- A projective resolution of `A ⊗ 1` from a resolution `K → 1` with `A ⊗ K_q` projective. -/
def tensorResolution' (A : Rep ℚ G) (K : ChainComplex (Rep ℚ G) ℕ)
    (εK : K ⟶ (ChainComplex.single₀ (Rep ℚ G)).obj (Rep.trivial ℚ G ℚ)) [QuasiIso εK]
    (hK : ∀ q, Projective (A ⊗ K.X q)) : ProjectiveResolution (A ⊗ Rep.trivial ℚ G ℚ) where
  complex := ((tensorLeft A).mapHomologicalComplex (ComplexShape.down ℕ)).obj K
  projective := hK
  π := ((tensorLeft A).mapHomologicalComplex (ComplexShape.down ℕ)).map εK ≫
    (HomologicalComplex.singleMapHomologicalComplex (tensorLeft A) (ComplexShape.down ℕ) 0).hom.app
      (Rep.trivial ℚ G ℚ)
  quasiIso := by
    have := quasiIso_tensorLeft A εK
    infer_instance

/-- **Comparison.**  If `K → 1` is a resolution of the trivial representation with all `A ⊗ K_q` projective and
`ξ : std → K` is a chain map over `1`, then `(A ⊗ ξ)_G` is a quasi-isomorphism on the complexes of coinvariants. -/
theorem isIso_homologyMap_tensorComparison (A : Rep ℚ G) (K : ChainComplex (Rep ℚ G) ℕ)
    (εK : K ⟶ (ChainComplex.single₀ (Rep ℚ G)).obj (Rep.trivial ℚ G ℚ)) [QuasiIso εK]
    (ξ : Rep.standardComplex ℚ G ⟶ K) (hξ : ξ ≫ εK = Rep.standardComplex.εToSingle₀ ℚ G)
    (hK : ∀ q, Projective (A ⊗ K.X q)) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (((Rep.coinvariantsFunctor ℚ G).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (((tensorLeft A).mapHomologicalComplex (ComplexShape.down ℕ)).map ξ)) n) := by
  let R1 := tensorResolution A (Rep.standardResolution ℚ G)
  let R2 := tensorResolution' A K εK hK
  let φ : R1.complex ⟶ R2.complex := ((tensorLeft A).mapHomologicalComplex (ComplexShape.down ℕ)).map ξ
  have hφ : φ.f 0 ≫ R2.π.f 0 = R1.π.f 0 := by
    have h : φ ≫ R2.π = R1.π := by
      simp only [R1, R2, φ, tensorResolution, tensorResolution', Rep.standardResolution]
      rw [← Category.assoc, ← Functor.map_comp, hξ]
    exact congrArg (fun ψ => ψ.f 0) h
  let e := resHomotopyEquiv' R1 R2 φ hφ
  have := (Functor.mapHomotopyEquiv (Rep.coinvariantsFunctor ℚ G) e).quasiIsoAt_hom n
  exact (quasiIsoAt_iff_isIso_homologyMap _ n).mp this

end TernaryPeriodPolynomials.Argument.GroupHomologyDescent
