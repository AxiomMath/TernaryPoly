module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCohomology.TopCohomologyGrid
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

@[expose] public section


open CategoryTheory CategoryTheory.Limits

noncomputable section
namespace TernaryPoly.LatticeTopCohomology
open IntegerGridExactness

theorem d₂_injective : Function.Injective d₂.hom := by
  intro x y h
  apply grid₀.injective
  apply IntegerGridTopInjective.boundary₂_injective
  rw [← grid_d₂, ← grid_d₂, h]

theorem range_d₂_eq_ker_d₁ : d₂.hom.toLinearMap.range = d₁.hom.toLinearMap.ker := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    apply grid₀.injective
    change grid₀ (d₁.hom (d₂.hom y)) = grid₀ 0
    rw [grid_d₁, grid_d₂, boundary₁_boundary₂, map_zero]
  · intro hx
    have hg : grid₁ x ∈ LinearMap.ker boundary₁ := by
      have hx' : d₁.hom x = 0 := hx
      rw [LinearMap.mem_ker, ← grid_d₁, hx', map_zero]
    rw [ker_boundary₁_eq_range_boundary₂] at hg
    obtain ⟨y, hy⟩ := hg
    refine ⟨grid₀.symm y, ?_⟩
    apply grid₁.injective
    change grid₁ (d₂.hom (grid₀.symm y)) = grid₁ x
    rw [grid_d₂, LinearEquiv.apply_symm_apply, hy]

theorem range_d₁_eq_ker_augmentation :
    d₁.hom.toLinearMap.range = augmentationHom.hom.toLinearMap.ker := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change augmentationHom.hom (d₁.hom y) = 0
    rw [grid_augmentation, grid_d₁, augmentation_boundary₁]
  · intro hx
    have hg : grid₀ x ∈ LinearMap.ker augmentation := by
      rw [LinearMap.mem_ker, ← grid_augmentation]
      exact hx
    rw [ker_augmentation_eq_range_boundary₁] at hg
    obtain ⟨y, hy⟩ := hg
    refine ⟨grid₁.symm y, ?_⟩
    apply grid₀.injective
    change grid₀ (d₁.hom (grid₁.symm y)) = grid₀ x
    rw [grid_d₁, LinearEquiv.apply_symm_apply, hy]

theorem augmentation_surjective : Function.Surjective augmentationHom.hom := by
  intro r
  exact ⟨MonoidAlgebra.single 1 r, augmentationHom_single 1 r⟩

theorem rep_exact (S : ShortComplex (Rep ℚ Lattice))
    (h : S.f.hom.toLinearMap.range = S.g.hom.toLinearMap.ker) : S.Exact := by
  apply (forget₂ (Rep ℚ Lattice) (ModuleCat ℚ)).reflects_exact_of_faithful S
  apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
  exact h

abbrev PZero := Rep.free ℚ Lattice PEmpty

theorem pZero_isZero : IsZero PZero := by
  rw [IsZero.iff_id_eq_zero]
  apply Rep.free_ext ℚ Lattice PZero
  intro i
  exact PEmpty.elim i

/-- The rank-one, rank-two, rank-one free lattice resolution, zero above degree two. -/
def objects : ℕ → Rep ℚ Lattice
  | 0 => P₀
  | 1 => P₁
  | 2 => P₂
  | _ + 3 => PZero

def differential : (n : ℕ) → objects (n+1) ⟶ objects n
  | 0 => d₁
  | 1 => d₂
  | _ + 2 => 0

theorem differential_squared (n : ℕ) : differential (n+1) ≫ differential n = 0 := by
  rcases n with _ | _ | n
  · exact d₂_d₁
  · exact zero_comp
  · exact zero_comp

def complex : ChainComplex (Rep ℚ Lattice) ℕ :=
  ChainComplex.of objects differential differential_squared

def augmentation : complex ⟶ (ChainComplex.single₀ (Rep ℚ Lattice)).obj Trivial :=
  (complex.toSingle₀Equiv Trivial).symm ⟨augmentationHom, d₁_augmentation⟩

theorem complex_exact_succ (n : ℕ) : complex.ExactAt (n+1) := by
  apply (HomologicalComplex.exactAt_iff' complex (n+2) (n+1) n (by simp) (by simp)).mpr
  rcases n with _ | _ | n
  · apply rep_exact
    exact range_d₂_eq_ker_d₁
  · apply rep_exact
    change LinearMap.range (0 : PZero →ₗ[ℚ] P₂) = LinearMap.ker d₂.hom.toLinearMap
    rw [LinearMap.range_zero, LinearMap.ker_eq_bot.mpr d₂_injective]
  · apply ShortComplex.exact_of_isZero_X₂
    exact pZero_isZero

instance augmentation_epi : Epi augmentationHom :=
  (Rep.epi_iff_surjective augmentationHom).mpr augmentation_surjective

/-- The actual square-grid chain complex is a projective resolution of the trivial module. -/
def resolution : ProjectiveResolution Trivial where
  complex := complex
  projective n := by
    rcases n with _ | _ | _ | n
    · exact Rep.leftRegular_projective
    · exact Rep.free_projective
    · exact Rep.leftRegular_projective
    · exact Rep.free_projective
  π := augmentation
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · constructor
        · apply rep_exact
          exact range_d₁_eq_ker_augmentation
        · exact augmentation_epi
      all_goals rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact complex_exact_succ n
      · apply ChainComplex.exactAt_succ_single_obj⟩

end TernaryPoly.LatticeTopCohomology
