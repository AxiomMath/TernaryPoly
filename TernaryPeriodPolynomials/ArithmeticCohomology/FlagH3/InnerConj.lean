module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.Algebra.Homology.Opposite
public import TernaryPeriodPolynomials.GroupCohomology.Homology.BarMaps

@[expose] public section



/-!
# Inner automorphisms act trivially on group cohomology, in every degree

Formalized by Claude Sonnet 5.5.

For `g ∈ G` and `A : Rep k G`, `conjBack g A : Res_{c_g} A ⟶ A` is `ρ(g⁻¹)`, and `map_conj_self` states that the induced map `groupCohomology.map (c_g) (conjBack g A) n` on `Hⁿ(G, A)` is the identity
for every `n` (Mathlib has this in no degree; `GammaNStokes/ConjInvariance.h2Map_conj_self` is degree two).  Proof: the chain map `conjBar` of the bar resolution
`[x₁|…|xₙ] ↦ g⁻¹ [g x₁ g⁻¹|…|g xₙ g⁻¹]` (built from `barMap (c_g)` and `ρ(g⁻¹)`) lifts the identity of `k`, so it is homotopic to the identity (`ProjectiveResolution.liftHomotopy`), and `Hom(conjBar, A)`
is the cochain map of `(c_g, ρ(g⁻¹))` (`cochainsMap_conj`).
-/

noncomputable section

universe u

namespace TernaryPeriodPolynomials.Argument.FlagH3

open CategoryTheory Rep Finsupp
open TernaryPeriodPolynomials.Argument.GroupHomology

variable {k G : Type u} [CommRing k] [Group G] (g : G)

/-- Conjugation by `g` as a group homomorphism. -/
abbrev conjHom : G →* G := (MulAut.conj g).toMonoidHom

/-- `ρ(g⁻¹)`, as a morphism from the representation twisted by conjugation by `g` back to the representation. -/
def conjBack (V : Rep k G) : (resFunctor (conjHom g)).obj V ⟶ V :=
  Rep.ofHom
    { toFun := fun v => V.ρ g⁻¹ v
      map_add' := fun _ _ => map_add _ _ _
      map_smul' := fun _ _ => map_smul _ _ _
      isIntertwining' := fun x => by
        ext v
        change V.ρ g⁻¹ (V.ρ (g * x * g⁻¹) v) = V.ρ x (V.ρ g⁻¹ v)
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 2
        group }

theorem conjBack_natural {V W : Rep k G} (ψ : V ⟶ W) :
    (resFunctor (conjHom g)).map ψ ≫ conjBack g W = conjBack g V ≫ ψ := by
  ext v
  exact (Rep.hom_comm_apply ψ g⁻¹ v).symm


/-- The chain map of the bar complex `[x₁|…|xₙ] ↦ g⁻¹ [g x₁ g⁻¹|…|g xₙ g⁻¹]`. -/
def conjBar : barComplex k G ⟶ barComplex k G where
  f n := (barMap (k := k) (conjHom g)).f n ≫ conjBack g _
  comm' := by
    rintro i j (rfl : j + 1 = i)
    have h1 := (barMap (k := k) (conjHom g)).comm (j + 1) j
    have h2 := conjBack_natural g (k := k) ((barComplex k G).d (j + 1) j)
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun t => (barMap (k := k) (conjHom g)).f (j + 1) ≫ t) h2.symm).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun t => t ≫ conjBack g ((barComplex k G).X j)) h1).trans ?_
    exact Category.assoc _ _ _

theorem conjBar_aug :
    (conjBar (k := k) g).f 0 ≫ (barResolution k G).π.f 0 = (barResolution k G).π.f 0 := by
  refine free_ext _ _ _ _ _ fun x => ?_
  have h2 := barPi_f_zero (k := k) (G := G) x 1 1
  refine Eq.trans ?_ h2.symm
  have e1 : ((conjBar (k := k) g).f 0).hom (single x (MonoidAlgebra.single 1 1)) =
      single (conjHom g ∘ x) (MonoidAlgebra.single (g⁻¹ * (g * 1 * g⁻¹)) 1) := by
    change (conjBack g _).hom ((barTerm (k := k) (conjHom g) 0).hom (single x (MonoidAlgebra.single 1 1))) = _
    rw [barTerm_single]
    exact Representation.free_single_single _ _ _ _
  exact (congrArg (fun v => ((barResolution k G).π.f 0).hom v) e1).trans (barPi_f_zero _ _ _)


/-- `conjBar` is homotopic to the identity (comparison theorem). -/
def conjBarHomotopy : Homotopy (conjBar (k := k) g) (𝟙 (barComplex k G)) := by
  have hc : conjBar (k := k) g ≫ (barResolution k G).π = (barResolution k G).π := by
    refine HomologicalComplex.to_single_hom_ext ?_
    exact conjBar_aug (k := k) g
  refine ProjectiveResolution.liftHomotopy (𝟙 _) (P := barResolution k G) (Q := barResolution k G)
    (conjBar (k := k) g) (𝟙 _) ?_ ?_
  · exact hc.trans (by rw [CategoryTheory.Functor.map_id, Category.comp_id])
  · exact (Category.id_comp _).trans (by rw [CategoryTheory.Functor.map_id, Category.comp_id])

/-- Precomposition with a chain map: `Hom(Q, A) ⟶ Hom(P, A)`. -/
def yMap {P Q : ChainComplex (Rep k G) ℕ} (φ : P ⟶ Q) (A : Rep k G) :
    Q.linearYonedaObj k A ⟶ P.linearYonedaObj k A :=
  (HomologicalComplex.unopFunctor _ _).map
    ((((linearYoneda k (Rep k G)).obj A).rightOp.mapHomologicalComplex (ComplexShape.down ℕ)).map φ).op

theorem yMap_apply {P Q : ChainComplex (Rep k G) ℕ} (φ : P ⟶ Q) (A : Rep k G) (n : ℕ)
    (f : Q.X n ⟶ A) : ((yMap φ A).f n).hom f = φ.f n ≫ f := rfl

theorem yMap_id {P : ChainComplex (Rep k G) ℕ} (A : Rep k G) : yMap (𝟙 P) A = 𝟙 _ := by
  unfold yMap
  simp
  rfl

theorem homologyMap_yMap_conjBar (A : Rep k G) (n : ℕ) :
    HomologicalComplex.homologyMap (yMap (conjBar (k := k) g) A) n = 𝟙 _ := by
  have h : Homotopy (yMap (conjBar (k := k) g) A) (yMap (𝟙 (barComplex k G)) A) :=
    (Functor.mapHomotopy (((linearYoneda k (Rep k G)).obj A).rightOp) (conjBarHomotopy (k := k) g)).unop
  rw [h.homologyMap_eq n, yMap_id]
  simp


omit [Group G] in
theorem inhomIso_hom_apply [Group G] (A : Rep k G) (n : ℕ) (c : (Fin n → G) → A) (x : Fin n → G) :
    ((ModuleCat.Hom.hom ((groupCohomology.inhomogeneousCochainsIso A).hom.f n)) c).hom
      (single x (MonoidAlgebra.single 1 1)) = c x := by
  change (Rep.freeLiftLEquiv k G (Fin n → G) A) ((Rep.freeLiftLEquiv k G (Fin n → G) A).symm c) x = c x
  simp

theorem hom_single_single {α : Type u} {A : Rep k G} (H : free k G α ⟶ A) (y : α) (h : G) :
    H.hom (single y (MonoidAlgebra.single h 1)) = A.ρ h (H.hom (single y (MonoidAlgebra.single 1 1))) := by
  have := Rep.hom_comm_apply H h (single y (MonoidAlgebra.single 1 1))
  have e : (free k G α).ρ h (single y (MonoidAlgebra.single 1 1)) = single y (MonoidAlgebra.single h 1) := by
    simp
  rw [e] at this
  exact this

theorem conjBar_basis (n : ℕ) (x : Fin n → G) :
    ((conjBar (k := k) g).f n).hom (single x (MonoidAlgebra.single 1 1)) =
      single (conjHom g ∘ x) (MonoidAlgebra.single g⁻¹ 1) := by
  change (conjBack g _).hom ((barTerm (k := k) (conjHom g) n).hom (single x (MonoidAlgebra.single 1 1))) = _
  rw [barTerm_single]
  refine (Representation.free_single_single _ _ _ _).trans ?_
  simp

theorem conjBar_comp_basis {A : Rep k G} (n : ℕ) (x : Fin n → G) (H : (barComplex k G).X n ⟶ A) :
    ((conjBar (k := k) g).f n ≫ H).hom (single x (MonoidAlgebra.single 1 1)) =
      A.ρ g⁻¹ (H.hom (single (conjHom g ∘ x) (MonoidAlgebra.single 1 1))) := by
  rw [Rep.hom_comp, Representation.IntertwiningMap.comp_apply, conjBar_basis]
  exact hom_single_single (k := k) (α := Fin n → G) (A := A) H _ _

theorem cochainsMap_conj (A : Rep k G) :
    (groupCohomology.inhomogeneousCochainsIso A).hom ≫ yMap (conjBar (k := k) g) A =
      groupCohomology.cochainsMap (conjHom g) (conjBack g A) ≫ (groupCohomology.inhomogeneousCochainsIso A).hom := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun c => ?_)
  refine Rep.free_ext _ _ _ _ _ fun x => ?_
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [inhomIso_hom_apply]
  refine (conjBar_comp_basis g n x _).trans ?_
  rw [inhomIso_hom_apply]
  rfl


/-- **Inner automorphisms act trivially on group cohomology in every degree**: conjugation by `g` combined with `ρ(g⁻¹)` on the coefficients induces the identity on `Hⁿ(G, A)`. -/
theorem map_conj_self (A : Rep k G) (n : ℕ) :
    groupCohomology.map (conjHom g) (conjBack g A) n = 𝟙 (groupCohomology A n) := by
  have h : groupCohomology.cochainsMap (conjHom g) (conjBack g A) =
      (groupCohomology.inhomogeneousCochainsIso A).hom ≫ yMap (conjBar (k := k) g) A ≫
        (groupCohomology.inhomogeneousCochainsIso A).inv := by
    rw [← Category.assoc, cochainsMap_conj, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  unfold groupCohomology.map
  rw [h, HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp,
    homologyMap_yMap_conjBar, Category.id_comp, ← HomologicalComplex.homologyMap_comp]
  simp [groupCohomology]

end TernaryPeriodPolynomials.Argument.FlagH3
