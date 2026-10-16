module

public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.MayerVietorisCochains

@[expose] public section


noncomputable section
namespace TernaryPoly.EquivariantSingularMayerVietoris
open CategoryTheory Limits HomologicalComplex EquivariantSingularSmall

variable {G : Type} [Group G]

/-- Genuine Hom pullback preserves the identity. -/
theorem homPullback_id (C : ChainComplex (Rep ℚ G) ℕ) (W : Rep.{0} ℚ G) :
    homPullback (𝟙 C) W = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro n
  ext c
  change C.X n ⟶ W at c
  change (𝟙 (C.X n)) ≫ c = c
  exact Category.id_comp c

/-- Genuine Hom pullback sends the zero map to zero. -/
theorem homPullback_zero (C D : ChainComplex (Rep ℚ G) ℕ) (W : Rep.{0} ℚ G) :
    homPullback (0 : C ⟶ D) W = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  ext c
  change D.X n ⟶ W at c
  change (0 : C.X n ⟶ D.X n) ≫ c = 0
  simp only [zero_comp]

/-- Genuine Hom pullback is additive in the actual chain map. -/
theorem homPullback_add {C D : ChainComplex (Rep ℚ G) ℕ} (f g : C ⟶ D) (W : Rep.{0} ℚ G) :
    homPullback (f + g) W = homPullback f W + homPullback g W := by
  apply HomologicalComplex.hom_ext
  intro n
  ext c
  change D.X n ⟶ W at c
  change (f.f n + g.f n) ≫ c = f.f n ≫ c + g.f n ≫ c
  exact Preadditive.add_comp (C.X n) (D.X n) W (f.f n) (g.f n) c

/-- Genuine Hom cochains of a biproduct are the biproduct of actual Hom cochains. -/
def homBiprodIso (C D : ChainComplex (Rep ℚ G) ℕ) (W : Rep.{0} ℚ G) :
    homCochains (C ⊞ D) W ≅ homCochains C W ⊞ homCochains D W where
  hom := biprod.lift (homPullback biprod.inl W) (homPullback biprod.inr W)
  inv := biprod.desc (homPullback biprod.fst W) (homPullback biprod.snd W)
  hom_inv_id := by
    rw [biprod.lift_desc, ← homPullback_comp, ← homPullback_comp, ← homPullback_add,
      biprod.total, homPullback_id]
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
      simp only [Category.assoc, biprod.lift_fst, biprod.lift_snd,
        biprod.inl_desc_assoc, biprod.inr_desc_assoc, ← homPullback_comp,
        biprod.inl_fst, biprod.inr_snd, biprod.inl_snd, biprod.inr_fst,
        homPullback_id, homPullback_zero, Category.comp_id]

/-- Under the genuine biproduct identification, Hom of a sum map is the pair of restrictions. -/
theorem homBiprodIso_restriction {C D K : ChainComplex (Rep ℚ G) ℕ} (a : C ⟶ K) (b : D ⟶ K)
    (W : Rep.{0} ℚ G) :
    homPullback (biprod.desc a b) W ≫ (homBiprodIso C D W).hom =
      biprod.lift (homPullback a W) (homPullback b W) := by
  apply biprod.hom_ext <;>
    simp only [Category.assoc, homBiprodIso, biprod.lift_fst, biprod.lift_snd,
      ← homPullback_comp, biprod.inl_desc, biprod.inr_desc]

/-- Genuine Hom pullback preserves additive inverses. -/
theorem homPullback_neg {C D : ChainComplex (Rep ℚ G) ℕ} (f : C ⟶ D) (W : Rep.{0} ℚ G) :
    homPullback (-f) W = -homPullback f W := by
  apply HomologicalComplex.hom_ext
  intro n
  ext c
  change D.X n ⟶ W at c
  change (-f.f n) ≫ c = -(f.f n ≫ c)
  exact Preadditive.neg_comp _ _

/-- Under the actual biproduct comparison, a signed chain inclusion yields difference restriction. -/
theorem homBiprodIso_difference {C D K : ChainComplex (Rep ℚ G) ℕ} (a : K ⟶ C) (b : K ⟶ D)
    (W : Rep.{0} ℚ G) :
    (homBiprodIso C D W).inv ≫ homPullback (biprod.lift a (-b)) W =
      biprod.desc (homPullback a W) (-homPullback b W) := by
  apply biprod.hom_ext' <;>
    simp only [homBiprodIso, biprod.inl_desc_assoc, biprod.inr_desc_assoc,
      ← homPullback_comp, biprod.lift_fst, biprod.lift_snd, homPullback_neg,
      biprod.inl_desc, biprod.inr_desc]

/-- Genuine Hom sends an actual chain isomorphism to its actual contravariant cochain isomorphism. -/
def homIso {C D : ChainComplex (Rep ℚ G) ℕ} (e : C ≅ D) (W : Rep.{0} ℚ G) :
    homCochains D W ≅ homCochains C W where
  hom := homPullback e.hom W
  inv := homPullback e.inv W
  hom_inv_id := by rw [← homPullback_comp, e.inv_hom_id, homPullback_id]
  inv_hom_id := by rw [← homPullback_comp, e.hom_inv_id, homPullback_id]

end TernaryPoly.EquivariantSingularMayerVietoris
