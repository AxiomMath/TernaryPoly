module

public import TernaryPeriodPolynomials.Topology.Euclidean.Local.Isotopy

@[expose] public section


noncomputable section
namespace TernaryPoly.EuclideanLocalHomology
open CategoryTheory Limits HomologicalComplex ContractibleSingularHomology
open RationalRelativeSingular RationalSingularAugmentation
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The actual pair map at a point for an injective Euclidean continuous map. -/
def pointLocalMap (f : C(E,E)) (hf : Function.Injective f) (x : E) :
    localChainsAt d x ⟶ localChainsAt d (f x) :=
  relativeMap f {x}ᶜ {f x}ᶜ (fun z hz => by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, hf.eq_iff] using hz)

/-- Translation turns the literal point-local map into its actual centered pair map. -/
theorem pointLocalMap_translation (f : C(E,E)) (hf : Function.Injective f) (x : E) :
    pointLocalMap f hf x ≫ (translateLocalIso d (f x)).hom =
      (translateLocalIso d x).hom ≫
        relativeMap (centeredMap f x) ({0}ᶜ : Set E) ({0}ᶜ : Set E)
          (centeredMap_punctured f x hf) := by
  simp only [pointLocalMap, translateLocalIso, relativeHomeomorphIso_hom]
  apply (cancel_epi (cokernel.π (inclusion ({x}ᶜ : Set E)))).mp
  simp only [relativeMap, cokernel.map, cokernel.π_desc_assoc, cokernel.π_desc, Category.assoc]
  rw [← Category.assoc, ← chainMap_comp, ← Category.assoc, ← chainMap_comp]
  congr 2
  ext z
  simp [centeredMap, Homeomorph.subRight_apply]

/-- Isotopies through injective maps preserve the canonical translation identification of
actual local homology, at every point and in every degree at least two. -/
theorem pointLocalMap_homology_translation (f : C(E,E)) (hf : Function.Injective f)
    (H : ContinuousMap.Homotopy (ContinuousMap.id E) f)
    (hH : ∀ t, Function.Injective (fun z => H (t,z))) (x : E) (k : ℕ) (hk : k ≠ 0) :
    homologyMap (pointLocalMap f hf x) (k+1) ≫
        (translateLocalHomologyIso d (f x) (k+1)).hom =
      (translateLocalHomologyIso d x (k+1)).hom := by
  change homologyMap _ _ ≫ homologyMap _ _ = homologyMap _ _
  rw [← homologyMap_comp, pointLocalMap_translation, homologyMap_comp,
    centered_localHomologyMap_eq_id f x hf H hH k hk, Category.comp_id]

/-- A fixed nonzero generator in Euclidean top local homology, translated to each point. -/
def localGenerator (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+2))) :
    (localChainsAt (n+2) x).homology (n+2) :=
  (localTopAtIso n x).inv (1 : ℚ)

/-- The chosen Euclidean local generator is nonzero. -/
theorem localGenerator_ne_zero (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+2))) :
    localGenerator n x ≠ 0 := by
  intro h
  have h' := congrArg (fun z => (localTopAtIso n x).hom z) h
  simp [localGenerator] at h'

/-- An actual isotopy preserves the chosen nonzero local generators at all points. -/
theorem pointLocalMap_generator (n : ℕ)
    (f : C(EuclideanSpace ℝ (Fin (n+2)),EuclideanSpace ℝ (Fin (n+2))))
    (hf : Function.Injective f) (H : ContinuousMap.Homotopy (ContinuousMap.id _) f)
    (hH : ∀ t, Function.Injective (fun z => H (t,z))) (x : EuclideanSpace ℝ (Fin (n+2))) :
    homologyMap (pointLocalMap f hf x) (n+2) (localGenerator n x) =
      localGenerator n (f x) := by
  apply (ModuleCat.mono_iff_injective (localTopAtIso n (f x)).hom).mp inferInstance
  have h := pointLocalMap_homology_translation f hf H hH x (n+1) (by omega)
  have hh := congrArg (fun a => a ≫ (localTopIso n).hom) h
  have hv := congrArg (fun a => a (localGenerator n x)) hh
  simpa [localGenerator, localTopAtIso, Category.assoc] using hv

end TernaryPoly.EuclideanLocalHomology
