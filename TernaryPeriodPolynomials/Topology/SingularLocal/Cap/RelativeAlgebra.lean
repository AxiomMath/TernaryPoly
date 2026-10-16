module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.Homology
public import TernaryPeriodPolynomials.GroupCohomology.Relative.ChainSequence
public import TernaryPeriodPolynomials.GroupCohomology.Relative.CochainSequence

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCap.RelativeAlgebra
open CategoryTheory Limits HomologicalComplex

variable {K L : ChainComplex (ModuleCat.{0} ℚ) ℕ} (i : K ⟶ L)

/-- Evaluation of the genuine relative cokernel is the actual degreewise cokernel. -/
def cokernelDegreeIso (n : ℕ) : (cokernel i).X n ≅ cokernel (i.f n) :=
  PreservesCokernel.iso (eval (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) n) i

/-- The actual relative projection commutes with its degreewise cokernel comparison. -/
theorem projection_degreeIso (n : ℕ) :
    (cokernel.π i).f n ≫ (cokernelDegreeIso i n).hom = cokernel.π (i.f n) :=
  PreservesCokernel.π_iso_hom (eval (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) n) i

/-- Every chain in the genuine cokernel complex has an absolute-chain representative. -/
theorem projection_surjective (n : ℕ) : Function.Surjective ((cokernel.π i).f n) :=
  (ModuleCat.epi_iff_surjective _).mp inferInstance

/-- Descend an actual linear chain operation through the genuine relative cokernel. -/
def descend (n : ℕ) (M : ModuleCat.{0} ℚ) (f : L.X n →ₗ[ℚ] M)
    (hf : ∀ x, f (i.f n x) = 0) : (cokernel i).X n →ₗ[ℚ] M :=
  ((cokernelDegreeIso i n).hom ≫ cokernel.desc (i.f n) (ModuleCat.ofHom f)
    (by ext x; exact hf x)).hom

/-- The descended operation agrees exactly with its prescribed formula on representatives. -/
theorem descend_projection (n : ℕ) (M : ModuleCat.{0} ℚ) (f : L.X n →ₗ[ℚ] M)
    (hf : ∀ x, f (i.f n x) = 0) (x : L.X n) :
    descend i n M f hf ((cokernel.π i).f n x) = f x := by
  have h : (cokernel.π i).f n ≫ ModuleCat.ofHom (descend i n M f hf) = ModuleCat.ofHom f := by
    change (cokernel.π i).f n ≫ ((cokernelDegreeIso i n).hom ≫ _) = _
    rw [← Category.assoc, projection_degreeIso, cokernel.π_desc]
  exact congrArg (fun g => g x) h

/-- A bilinear chain operation descends through the actual cokernel in its second argument. -/
def descendBilinear (n : ℕ) (W M : ModuleCat.{0} ℚ) (β : W →ₗ[ℚ] L.X n →ₗ[ℚ] M)
    (hβ : ∀ w x, β w (i.f n x) = 0) : W →ₗ[ℚ] (cokernel i).X n →ₗ[ℚ] M where
  toFun w := descend i n M (β w) (hβ w)
  map_add' w w' := by
    ext z
    obtain ⟨x,rfl⟩ := projection_surjective i n z
    erw [LinearMap.add_apply, descend_projection, descend_projection, descend_projection]
    exact LinearMap.congr_fun (map_add β w w') x
  map_smul' r w := by
    ext z
    obtain ⟨x,rfl⟩ := projection_surjective i n z
    erw [LinearMap.smul_apply, descend_projection, descend_projection]
    exact LinearMap.congr_fun (map_smul β r w) x

/-- Zero of an actual relative chain means membership in the actual subspace image. -/
theorem projection_zero_iff (n : ℕ) (x : L.X n) :
    (cokernel.π i).f n x = 0 ↔ ∃ y, i.f n y = x := by
  have h := (ShortComplex.mk (i.f n) (cokernel.π (i.f n)) (cokernel.condition _)).exact_of_g_is_cokernel
    (cokernelIsCokernel (i.f n))
  have he := h.moduleCat_range_eq_ker
  have hp := congrArg (fun f => f x) (projection_degreeIso i n)
  change (cokernelDegreeIso i n).hom ((cokernel.π i).f n x) = cokernel.π (i.f n) x at hp
  constructor
  · intro hx
    have hh : x ∈ LinearMap.ker (cokernel.π (i.f n)).hom := by
      change cokernel.π (i.f n) x = 0
      rw [← hp,hx,map_zero]
    rw [← he] at hh
    exact hh
  · rintro ⟨y,rfl⟩
    exact congrArg (fun f => f y) (HomologicalComplex.congr_hom (cokernel.condition i) n)

end TernaryPoly.SingularLocalCap.RelativeAlgebra
