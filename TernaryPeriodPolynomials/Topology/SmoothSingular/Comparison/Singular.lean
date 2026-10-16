module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Comparison.SingularAugmentation

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularComparison
open CategoryTheory Limits HomologicalComplex

/-- Genuine real singular cochains, as Hom on the actual Mathlib singular chains. -/
abbrev realSingularCochains (X : TopCat.{0}) (F : ModuleCat.{0} ℝ) :
    CochainComplex (ModuleCat.{0} ℝ) ℕ := realHomComplex (realSingularChains X) F

/-- The literal constant singular zero-cochain: multiply the scalar coefficient sum by c. -/
def singularConstant (X : TopCat.{0}) (F : ModuleCat.{0} ℝ) :
    F →ₗ[ℝ] ((realSingularChains X).X 0 →ₗ[ℝ] F) where
  toFun c := (realSingularSum X).hom.smulRight c
  map_add' c e := by ext x; exact smul_add _ c e
  map_smul' r c := by ext x; exact smul_comm _ r c

/-- Every constant singular zero-cochain is closed, by the actual augmented chain identity. -/
theorem singularConstant_closed (X : TopCat.{0}) (F : ModuleCat.{0} ℝ) :
    (homDifferential (realSingularChains X) F 0).comp (singularConstant X F) = 0 := by
  apply LinearMap.ext
  intro c
  apply LinearMap.ext
  intro x
  have h := congrArg (fun f => f x) (realSingularSum_boundary X)
  change realSingularSum X ((realSingularChains X).d 1 0 x) = 0 at h
  change (realSingularSum X ((realSingularChains X).d 1 0 x)) • c = 0
  rw [h, zero_smul]

/-- Constant singular cochains inject whenever the space is nonempty. -/
theorem singularConstant_injective (X : TopCat.{0}) (F : ModuleCat.{0} ℝ) [Nonempty X] :
    Function.Injective (singularConstant X F) := by
  obtain ⟨x, hx⟩ := realSingularSum_surjective X 1
  intro c e h
  have hh := LinearMap.congr_fun h x
  change (realSingularSum X x) • c = (realSingularSum X x) • e at hh
  simpa only [hx, one_smul] using hh

/-- Actual closed singular zero-cochains on a path-connected space are precisely constants. -/
theorem singularConstant_exact (X : TopCat.{0}) (F : ModuleCat.{0} ℝ) [PathConnectedSpace X] :
    LinearMap.range (singularConstant X F) =
      LinearMap.ker (homDifferential (realSingularChains X) F 0) := by
  ext φ
  constructor
  · rintro ⟨c, rfl⟩
    exact LinearMap.congr_fun (singularConstant_closed X F) c
  · intro hφ
    change φ.comp ((realSingularChains X).d 1 0).hom = 0 at hφ
    obtain ⟨ψ, hψ⟩ := factor_of_ker_le (realSingularSum X).hom φ (by
      intro x hx
      rw [← realSingularSum_exact X] at hx
      obtain ⟨y, rfl⟩ := hx
      exact LinearMap.congr_fun hφ y)
    refine ⟨ψ 1, ?_⟩
    apply LinearMap.ext
    intro x
    change (realSingularSum X x) • ψ 1 = φ x
    calc
      _ = ψ (realSingularSum X x) := by simpa using (map_smul ψ (realSingularSum X x) 1).symm
      _ = φ x := LinearMap.congr_fun hψ x

/-- The actual constant-to-singular cochain augmentation. -/
def singularAugmentation (X : TopCat.{0}) (F : ModuleCat.{0} ℝ) :
    (CochainComplex.single₀ (ModuleCat ℝ)).obj F ⟶ realSingularCochains X F :=
  augmentation (ModuleCat.ofHom (singularConstant X F)) (by
    rw [realHom_d]
    apply ModuleCat.hom_ext
    exact singularConstant_closed X F)

/-- The actual real singular augmentation is a quasi-isomorphism on a contractible space,
for every real coefficient module. -/
theorem singularAugmentation_quasiIso (X : TopCat.{0}) (F : ModuleCat.{0} ℝ)
    [ContractibleSpace X] : QuasiIso (singularAugmentation X F) := by
  have hm : Mono (ModuleCat.ofHom (singularConstant X F)) :=
    (ModuleCat.mono_iff_injective _).mpr (singularConstant_injective X F)
  unfold singularAugmentation
  refine @augmentation_quasiIso ℝ _ (realSingularCochains X F) F _ _ ?_ hm ?_
  · apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
    change LinearMap.range (singularConstant X F) =
      LinearMap.ker ((realHomComplex (realSingularChains X) F).d 0 (0+1)).hom
    rw [realHom_d]
    exact singularConstant_exact X F
  · intro n
    exact realHom_exactAt _ _ n (realSingularChains_exactAt X n)

/-- Actual pullback of real singular cochains by a continuous map. -/
abbrev singularPullback {X Y : TopCat.{0}} (f : X ⟶ Y) (F : ModuleCat.{0} ℝ) :
    realSingularCochains Y F ⟶ realSingularCochains X F :=
  realHomPullback (realSingularChainMap f) F

/-- The constant augmentation commutes with genuine continuous pullback. -/
theorem singularAugmentation_pullback {X Y : TopCat.{0}} (f : X ⟶ Y) (F : ModuleCat.{0} ℝ) :
    singularAugmentation Y F ≫ singularPullback f F = singularAugmentation X F := by
  apply (CochainComplex.fromSingle₀Equiv (realSingularCochains X F) F).injective
  apply Subtype.ext
  change ModuleCat.ofHom (singularConstant Y F) ≫
    (realHomPullback (realSingularChainMap f) F).f 0 = ModuleCat.ofHom (singularConstant X F)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  apply LinearMap.ext
  intro x
  exact congrArg (fun r : ℝ => r • c)
    (congrArg (fun g => g x) (realSingularSum_natural f))

/-- The constant augmentation commutes with actual real-linear coefficient postcomposition. -/
theorem singularAugmentation_coefficient (X : TopCat.{0}) {F G : ModuleCat.{0} ℝ} (f : F ⟶ G) :
    singularAugmentation X F ≫ realHomCoefficient (realSingularChains X) f =
      (CochainComplex.single₀ (ModuleCat ℝ)).map f ≫ singularAugmentation X G := by
  apply (CochainComplex.fromSingle₀Equiv (realSingularCochains X G) F).injective
  apply Subtype.ext
  change ModuleCat.ofHom (singularConstant X F) ≫
      (realHomCoefficient (realSingularChains X) f).f 0 = f ≫ ModuleCat.ofHom (singularConstant X G)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  apply LinearMap.ext
  intro x
  exact map_smul f.hom (realSingularSum X x) c

end TernaryPoly.SmoothSingularComparison
