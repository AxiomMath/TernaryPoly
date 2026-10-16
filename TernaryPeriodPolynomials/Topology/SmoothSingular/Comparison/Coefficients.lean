module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Comparison.DeRham

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularComparison
open CategoryTheory SmoothLocalDeRham SmoothCoveringDeRham
open scoped Topology
variable {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Actual continuous linear postcomposition of coefficients of smooth chart forms. -/
def deRhamCoefficientForm (L : F →L[ℝ] G) (s : Set E) (n : ℕ) :
    Form (F := F) s n →ₗ[ℝ] Form (F := G) s n where
  toFun w := ⟨coefficientRaw L w, coefficientRaw_smooth L (Form.smooth w), by
    intro x hx
    simp only [coefficientRaw, Form.outside w hx, map_zero]⟩
  map_add' w z := by
    apply Form.ext
    intro x hx
    exact map_add (coefficientFormMap L n) _ _
  map_smul' r w := by
    apply Form.ext
    intro x hx
    exact map_smul (coefficientFormMap L n) r _

/-- Coefficient postcomposition commutes with the actual exterior derivative. -/
theorem deRhamCoefficientForm_d (L : F →L[ℝ] G) {s : Set E} (hs : IsOpen s)
    (n : ℕ) (w : Form (F := F) s n) :
    deRhamCoefficientForm L s (n+1) (d hs n w) =
      d hs n (deRhamCoefficientForm L s n w) := by
  apply Form.ext
  intro x hx
  rw [d_apply hs _ hx]
  change coefficientFormMap L (n+1) ((d hs n w : RawForm E F (n+1)) x) =
    extDeriv (coefficientRaw L w) x
  rw [d_apply hs _ hx]
  exact (extDeriv_coefficientRaw L
    (((Form.smooth w).contDiffAt (hs.mem_nhds hx)).differentiableAt (by simp))).symm

/-- The genuine cochain map induced by a continuous real-linear coefficient map. -/
def deRhamCoefficient (L : F →L[ℝ] G) {s : Set E} (hs : IsOpen s) :
    complex (F := F) hs ⟶ complex (F := G) hs :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (deRhamCoefficientForm L s n)) (fun n => by
    rw [deRham_d, deRham_d]
    apply ModuleCat.hom_ext
    exact LinearMap.ext (fun w => (deRhamCoefficientForm_d L hs n w).symm))

/-- The coefficient map sends the constant section c to the constant section L(c). -/
theorem deRhamCoefficient_constant (L : F →L[ℝ] G) (s : Set E) (c : F) :
    deRhamCoefficientForm L s 0 (deRhamConstant s c) = deRhamConstant s (L c) := by
  apply Form.ext
  intro x hx
  change coefficientFormMap L 0 ((constant s c : RawForm E F 0) x) =
    (constant s (L c) : RawForm E G 0) x
  simp only [constant, ofFunction_apply _ _ hx]
  ext v
  rfl

/-- Actual coefficient maps commute with the canonical smooth augmentation. -/
theorem deRhamAugmentation_coefficient (L : F →L[ℝ] G) {s : Set E} (hs : IsOpen s) :
    deRhamAugmentation (F := F) hs ≫ deRhamCoefficient L hs =
      (CochainComplex.single₀ (ModuleCat ℝ)).map (ModuleCat.ofHom L.toLinearMap) ≫
        deRhamAugmentation (F := G) hs := by
  apply (CochainComplex.fromSingle₀Equiv (complex (F := G) hs) (ModuleCat.of ℝ F)).injective
  apply Subtype.ext
  change ModuleCat.ofHom (deRhamConstant (F := F) s) ≫
      ModuleCat.ofHom (deRhamCoefficientForm L s 0) =
    ModuleCat.ofHom L.toLinearMap ≫ ModuleCat.ofHom (deRhamConstant (F := G) s)
  apply ModuleCat.hom_ext
  exact LinearMap.ext (deRhamCoefficient_constant L s)

/-- Literal coefficient maps and restrictions commute, including arbitrary deck transition maps. -/
theorem deRhamCoefficient_restrict (L : F →L[ℝ] G) {s t : Set E}
    (hs : IsOpen s) (ht : IsOpen t) (hts : t ⊆ s) :
    deRhamCoefficient L hs ≫ deRhamRestriction hs ht hts =
      deRhamRestriction hs ht hts ≫ deRhamCoefficient L ht := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro w
  change Form (F := F) s n at w
  apply Form.ext
  intro x hx
  change (restrictTo hts n (deRhamCoefficientForm L s n w) : RawForm E G n) x =
    coefficientFormMap L n ((restrictTo hts n w : RawForm E F n) x)
  rw [restrictTo_apply hts _ hx, restrictTo_apply hts _ hx]
  rfl

end TernaryPoly.SmoothSingularComparison
