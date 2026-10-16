module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Comparison.Resolution
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Module.Projective

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularComparison
open CategoryTheory Limits HomologicalComplex

/-- Over the reals, any linear map killing a kernel factors through the given linear map.
The extension is used only to prove exactness; the comparison maps remain canonical. -/
theorem factor_of_ker_le {A B F : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup F] [Module ℝ A] [Module ℝ B] [Module ℝ F]
    (g : A →ₗ[ℝ] B) (φ : A →ₗ[ℝ] F) (h : g.ker ≤ φ.ker) :
    ∃ ψ : B →ₗ[ℝ] F, ψ.comp g = φ := by
  obtain ⟨r, hr⟩ := g.rangeRestrict.exists_rightInverse_of_surjective g.range_rangeRestrict
  obtain ⟨ψ, hψ⟩ := (φ.comp r).exists_extend
  refine ⟨ψ, ?_⟩
  apply LinearMap.ext
  intro x
  have hrg : g (r (g.rangeRestrict x)) = g x := by
    exact congrArg Subtype.val (LinearMap.congr_fun hr (g.rangeRestrict x))
  have hk : x - r (g.rangeRestrict x) ∈ g.ker := by
    change g (x - r (g.rangeRestrict x)) = 0
    rw [map_sub, hrg, sub_self]
  have hv : φ x = φ (r (g.rangeRestrict x)) := by
    exact sub_eq_zero.mp ((map_sub φ _ _).symm.trans (h hk))
  exact (LinearMap.congr_fun hψ (g.rangeRestrict x)).trans hv.symm

/-- Actual real-valued Hom differential, defined by precomposition with the genuine boundary. -/
def homDifferential (K : ChainComplex (ModuleCat ℝ) ℕ) (F : ModuleCat ℝ) (n : ℕ) :
    (K.X n →ₗ[ℝ] F) →ₗ[ℝ] (K.X (n+1) →ₗ[ℝ] F) where
  toFun φ := φ.comp (K.d (n+1) n).hom
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The Hom differential squares to zero by the actual chain identity. -/
theorem homDifferential_squared (K : ChainComplex (ModuleCat ℝ) ℕ) (F : ModuleCat ℝ)
    (n : ℕ) : (homDifferential K F (n+1)).comp (homDifferential K F n) = 0 := by
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro c
  have h := congrArg (fun f => f c) (K.d_comp_d (n+2) (n+1) n)
  change K.d (n+1) n (K.d (n+2) (n+1) c) = 0 at h
  change φ (K.d (n+1) n (K.d (n+2) (n+1) c)) = 0
  rw [h, map_zero]

/-- The genuine real Hom cochain complex. -/
def realHomComplex (K : ChainComplex (ModuleCat ℝ) ℕ) (F : ModuleCat ℝ) :
    CochainComplex (ModuleCat ℝ) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of ℝ (K.X n →ₗ[ℝ] F))
    (fun n => ModuleCat.ofHom (homDifferential K F n)) (fun n => by
      apply ModuleCat.hom_ext
      exact homDifferential_squared K F n)

/-- The literal Hom differential in consecutive degrees. -/
theorem realHom_d (K : ChainComplex (ModuleCat ℝ) ℕ) (F : ModuleCat ℝ) (n : ℕ) :
    (realHomComplex K F).d n (n+1) = ModuleCat.ofHom (homDifferential K F n) :=
  by
    unfold realHomComplex
    exact CochainComplex.of_d (fun i => ModuleCat.of ℝ (K.X i →ₗ[ℝ] F))
      (fun i => ModuleCat.ofHom (homDifferential K F i)) n

/-- A closed Hom cochain factors across the previous boundary whenever the chain complex is
exact there. This works for arbitrary real coefficient spaces, without finite dimension. -/
theorem realHom_exactAt (K : ChainComplex (ModuleCat ℝ) ℕ) (F : ModuleCat ℝ)
    (n : ℕ) (hex : K.ExactAt (n+1)) : (realHomComplex K F).ExactAt (n+1) := by
  rw [exactAt_iff' _ (n+2) (n+1) n (by simp) (by simp)] at hex
  have hx := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp hex
  change LinearMap.range (K.d (n+2) (n+1)).hom = LinearMap.ker (K.d (n+1) n).hom at hx
  rw [exactAt_iff' _ n (n+1) (n+2) (by simp) (by simp)]
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro φ hφ
  change K.X (n+1) →ₗ[ℝ] F at φ
  change (realHomComplex K F).d (n+1) ((n+1)+1) φ = 0 at hφ
  rw [realHom_d] at hφ
  change φ.comp (K.d (n+2) (n+1)).hom = 0 at hφ
  obtain ⟨ψ, hψ⟩ := factor_of_ker_le (A := K.X (n+1)) (B := K.X n) (F := F)
    (K.d (n+1) n).hom φ (by
    intro x hxx
    have hmem : x ∈ LinearMap.range (K.d (n+2) (n+1)).hom := by
      rw [hx]
      exact hxx
    obtain ⟨y, rfl⟩ := hmem
    exact LinearMap.congr_fun hφ y)
  refine ⟨ψ, ?_⟩
  change (realHomComplex K F).d n (n+1) ψ = φ
  rw [realHom_d]
  exact hψ

/-- A chain map acts on real Hom cochains by literal precomposition. -/
def realHomPullback {K L : ChainComplex (ModuleCat ℝ) ℕ} (f : K ⟶ L)
    (F : ModuleCat ℝ) : realHomComplex L F ⟶ realHomComplex K F :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom
    { toFun := fun φ => φ.comp (f.f n).hom
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }) (fun n => by
    rw [realHom_d, realHom_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro c
    change L.X n →ₗ[ℝ] F at φ
    exact congrArg (fun x => φ x) (congrArg (fun g => g c) (f.comm (n+1) n)).symm)

/-- Coefficient maps act on real Hom cochains by literal postcomposition. -/
def realHomCoefficient (K : ChainComplex (ModuleCat ℝ) ℕ) {F G : ModuleCat ℝ}
    (f : F ⟶ G) : realHomComplex K F ⟶ realHomComplex K G :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom
    { toFun := fun φ => f.hom.comp φ
      map_add' := fun _ _ => by ext x; exact map_add f.hom _ _
      map_smul' := fun r φ => by ext x; exact map_smul f.hom r _ }) (fun _ => by
    rw [realHom_d, realHom_d]
    apply ModuleCat.hom_ext
    rfl)

/-- Real coefficient postcomposition and actual chain pullback commute. -/
theorem realHomPullback_coefficient {K L : ChainComplex (ModuleCat ℝ) ℕ}
    (f : K ⟶ L) {F G : ModuleCat ℝ} (g : F ⟶ G) :
    realHomPullback f F ≫ realHomCoefficient K g =
      realHomCoefficient L g ≫ realHomPullback f G := by
  ext n φ
  rfl

end TernaryPoly.SmoothSingularComparison
