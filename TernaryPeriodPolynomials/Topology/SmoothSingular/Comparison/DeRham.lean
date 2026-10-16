module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Comparison.Resolution
public import TernaryPeriodPolynomials.Topology.SmoothLocal.DeRhamRestriction
public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.Operations

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularComparison
open CategoryTheory Limits HomologicalComplex Set
open SmoothLocalDeRham SmoothCoveringDeRham

variable {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The chart-complex differential is literally the proved exterior differential. -/
theorem deRham_d {s : Set E} (hs : IsOpen s) (n : ℕ) :
    (complex (F := F) hs).d n (n+1) = ModuleCat.ofHom (d hs n) :=
  by
    unfold complex
    exact CochainComplex.of_d (fun i => ModuleCat.of ℝ (Form (F := F) s i))
      (fun i => ModuleCat.ofHom (d hs i)) n

/-- The literal constant coefficient zero-forms, with their real-linear structure. -/
def deRhamConstant (s : Set E) : F →ₗ[ℝ] Form (F := F) s 0 where
  toFun := constant s
  map_add' a b := by
    apply Form.ext
    intro x hx
    simp only [constant, ofFunction_apply _ _ hx, AddMemClass.coe_add, Pi.add_apply]
    exact map_add zeroEquiv a b
  map_smul' r a := by
    apply Form.ext
    intro x hx
    simp [constant, ofFunction_apply, hx]

/-- Constant zero-forms are closed on every open chart, without connectedness assumptions. -/
theorem deRhamConstant_closed {s : Set E} (hs : IsOpen s) :
    (d (F := F) hs 0).comp (deRhamConstant s) = 0 := by
  apply LinearMap.ext
  intro c
  apply Form.ext
  intro x hx
  change (d hs 0 (ofFunction (fun _ => c) contDiffOn_const) : RawForm E F 1) x = 0
  rw [d_ofFunction hs _ _ hx, fderiv_fun_const]
  exact map_zero oneEquiv

/-- Constants inject on each nonempty chart. -/
theorem deRhamConstant_injective {s : Set E} (hne : s.Nonempty) :
    Function.Injective (deRhamConstant (F := F) s) := by
  obtain ⟨x, hx⟩ := hne
  intro c e h
  have he := congrArg (fun w : Form (F := F) s 0 => (w : RawForm E F 0) x) h
  change (constant s c : RawForm E F 0) x = (constant s e : RawForm E F 0) x at he
  simp only [constant, ofFunction_apply _ _ hx] at he
  exact zeroEquiv.injective he

/-- On a connected chart, the kernel of the actual first derivative consists exactly of constants. -/
theorem deRhamConstant_exact {s : Set E} (hs : IsOpen s) (hc : IsPreconnected s) :
    LinearMap.range (deRhamConstant (F := F) s) = LinearMap.ker (d hs 0) := by
  ext w
  constructor
  · rintro ⟨c, rfl⟩
    exact LinearMap.congr_fun (deRhamConstant_closed hs) c
  · intro hw
    obtain ⟨c, hc⟩ := (closed_zero_iff_constant hs hc w).mp hw
    exact ⟨c, hc.symm⟩

/-- The canonical chain-level augmentation of smooth de Rham forms by constant coefficients. -/
def deRhamAugmentation {s : Set E} (hs : IsOpen s) :
    (CochainComplex.single₀ (ModuleCat ℝ)).obj (ModuleCat.of ℝ F) ⟶ complex (F := F) hs :=
  augmentation (ModuleCat.ofHom (deRhamConstant s))
    (by apply ModuleCat.hom_ext; exact deRhamConstant_closed hs)

/-- The actual smooth de Rham complex is exact in every positive degree on convex charts. -/
theorem deRham_exactAt [FiniteDimensional ℝ E] [CompleteSpace F]
    {s : Set E} (hs : IsOpen s) (hc : Convex ℝ s) (n : ℕ) :
    (complex (F := F) hs).ExactAt (n+1) := by
  rw [exactAt_iff' _ n (n+1) (n+2) (by simp) (by simp)]
  apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
  change LinearMap.range ((complex (F := F) hs).d n (n+1)).hom =
    LinearMap.ker ((complex (F := F) hs).d (n+1) ((n+1)+1)).hom
  rw [deRham_d, deRham_d]
  exact range_d_eq_ker_d (F := F) hs hc n

/-- Local Poincare and actual degree-zero constants prove this local augmentation is a
quasi-isomorphism; no abstract comparison hypothesis is used. -/
theorem deRhamAugmentation_quasiIso [FiniteDimensional ℝ E] [CompleteSpace F]
    {s : Set E} (hs : IsOpen s) (hc : Convex ℝ s) (hne : s.Nonempty) :
    QuasiIso (deRhamAugmentation (F := F) hs) := by
  have : Mono (ModuleCat.ofHom (deRhamConstant (F := F) s)) :=
    (ModuleCat.mono_iff_injective _).mpr (deRhamConstant_injective hne)
  unfold deRhamAugmentation
  refine @augmentation_quasiIso ℝ _ (complex (F := F) hs) (ModuleCat.of ℝ F)
    (ModuleCat.ofHom (deRhamConstant (F := F) s)) _ ?_ this ?_
  · apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
    change LinearMap.range (deRhamConstant (F := F) s) =
      LinearMap.ker ((complex (F := F) hs).d 0 (0+1)).hom
    rw [deRham_d]
    exact deRhamConstant_exact (F := F) hs hc.isPreconnected
  · exact deRham_exactAt (F := F) hs hc

/-- Actual chart restriction as a real cochain map. -/
def deRhamRestriction {s t : Set E} (hs : IsOpen s) (ht : IsOpen t) (hts : t ⊆ s) :
    complex (F := F) hs ⟶ complex (F := F) ht :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (restrictTo hts n)) (fun n => by
    rw [deRham_d, deRham_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro w
    exact (restrictTo_d (F := F) hs ht hts w).symm)

/-- Restriction preserves literal constant zero-forms. -/
theorem deRhamConstant_restrict {s t : Set E} (hts : t ⊆ s) (c : F) :
    restrictTo hts 0 (deRhamConstant s c) = deRhamConstant t c := by
  apply Form.ext
  intro x hx
  rw [restrictTo_apply hts _ hx]
  change (constant s c : RawForm E F 0) x = (constant t c : RawForm E F 0) x
  simp [constant, hts hx, hx]

/-- The local augmentation square commutes for the actual restriction maps. -/
theorem deRhamAugmentation_restrict {s t : Set E} (hs : IsOpen s) (ht : IsOpen t)
    (hts : t ⊆ s) :
    deRhamAugmentation (F := F) hs ≫ deRhamRestriction hs ht hts =
      deRhamAugmentation (F := F) ht := by
  apply (CochainComplex.fromSingle₀Equiv (complex (F := F) ht) (ModuleCat.of ℝ F)).injective
  apply Subtype.ext
  change (deRhamAugmentation hs).f 0 ≫ (deRhamRestriction hs ht hts).f 0 =
    (deRhamAugmentation ht).f 0
  change ModuleCat.ofHom (deRhamConstant (F := F) s) ≫
    ModuleCat.ofHom (restrictTo hts 0) = ModuleCat.ofHom (deRhamConstant (F := F) t)
  apply ModuleCat.hom_ext
  exact LinearMap.ext (deRhamConstant_restrict (F := F) hts)

end TernaryPoly.SmoothSingularComparison
