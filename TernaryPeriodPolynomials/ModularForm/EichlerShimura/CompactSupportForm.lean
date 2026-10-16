module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.CompactSupport.Surgery
public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.CompactSupport.Compact

@[expose] public section


/-!
# Step 1: a primitive whose differential has compact support modulo `Γ`

Unconditional Eichler--Shimura route.
Let `Γ` be a finite-index subgroup of `SL(2, ℤ)` with `-1 ∉ Γ`, `ρ : Γ →* End_ℝ W` a finite
dimensional representation and `c` a `1`-cocycle of `Γ` in `W` which is a coboundary at every
parabolic element.  Then there is a smooth `φ : ℂ → W` on the upper half plane `U` with
`φ (γ z) = ρ γ (φ z) + c γ`, whose differential `fderiv ℝ φ` (a smooth closed `Γ`-equivariant
`W`-valued `1`-form) vanishes outside the `Γ`-translates of one compact subset of `U`
(`exists_compactSupport_primitive`).  Its period cocycle `γ ↦ φ (γ z₀) - φ z₀` equals `c`
plus a coboundary.  The matrix version for `W = EuclideanSpace ℂ (Fin d)` is
`exists_compactSupport_primitive_matrix`.

Proof: start with the equivariant primitive `φ₀` of the partition of unity
(`Partition.exists_equivariant_primitive`) and subtract the equivariant correction of `CuspData.corr`,
which equals `φ₀ + v g₀` on the height-two horoball at every cusp representative `g₀`, so that
`φ₀ - corr` is locally constant there.  Parabolicity is used only through `exists_cusp_vector`.

Formalized by Claude Sonnet 5.5.
-/

open UpperHalfPlane ModularGroup Complex
open scoped Modular MatrixGroups ContDiff

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ESFoundations.CompactSupport

open TernaryPeriodPolynomials.Argument.ESFoundations
open TernaryPeriodPolynomials.Argument.ESFoundations.Partition
open TernaryPeriodPolynomials.Argument.ESFoundations.HodgePair (U isOpen_U)

variable {Γ : Subgroup SL(2, ℤ)} {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- **Step 1.** A cocycle that is a coboundary on the parabolic elements has an equivariant smooth
primitive whose differential is supported in the `Γ`-translates of a compact subset of `U`. -/
theorem exists_compactSupport_primitive [Γ.FiniteIndex] [FiniteDimensional ℝ W]
    (hneg : (-1 : SL(2, ℤ)) ∉ Γ) (ρ : Γ →* (W →ₗ[ℝ] W)) (c : Γ → W)
    (hc : ∀ δ γ : Γ, c (δ * γ) = c δ + ρ δ (c γ))
    (hpar : ∀ γ : Γ, IsParabolicElt γ.1 → ∃ u : W, c γ = ρ γ u - u) :
    ∃ φ : ℂ → W, ContDiffOn ℝ ∞ φ U ∧
      (∀ δ : Γ, ∀ z ∈ U, φ (mob (δ : SL(2, ℤ)) z) = ρ δ (φ z) + c δ) ∧
      ∃ K : Set ℂ, IsCompact K ∧ K ⊆ U ∧
        ∀ z ∈ U, (∀ γ : Γ, mob (γ : SL(2, ℤ)) z ∉ K) → fderiv ℝ φ z = 0 := by
  obtain ⟨D⟩ := exists_cuspData hneg ρ c hc hpar
  obtain ⟨φ₀, hφ₀, hφ₀eq⟩ := exists_equivariant_primitive Γ (fun δ => ρ δ) c hc
  obtain ⟨K, hK, hKU, hKcov⟩ := exists_compact_height_two_complex Γ
  refine ⟨fun z => φ₀ z - D.corr φ₀ z, hφ₀.sub (D.contDiffOn_corr φ₀ hφ₀), ?_, K, hK, hKU, ?_⟩
  · intro δ z hz
    simp only
    rw [hφ₀eq δ z hz, D.corr_mob φ₀ δ hz, map_sub]
    abel
  · intro z hz hzK
    -- a point at which some horoball has height above two
    have hex : ∃ g : SL(2, ℤ), 2 < (mob g⁻¹ z).im := by
      by_contra hno
      push Not at hno
      obtain ⟨γ, hγ⟩ := hKcov z hz hno
      exact hzK γ hγ
    obtain ⟨g, hg⟩ := hex
    obtain ⟨g₀, hg₀, γ', hγ', hs⟩ := D.cover g
    -- `γ' z` lies in the height-two horoball at `g₀`
    have hdeep : 2 < (mob g₀⁻¹ (mob γ' z)).im := by
      have e : mob g₀⁻¹ (mob γ' z) = mob (g₀⁻¹ * γ' * g) (mob g⁻¹ z) := by
        rw [← mob_mul, ← mob_mul]; congr 1; group
      rw [e, im_mob_of_lowerLeft hs (mob_mem _ _)]
      exact hg
    -- the open set on which `γ' u` stays deep
    have hopen : IsOpen (U ∩ (fun u => (mob g₀⁻¹ (mob γ' u)).im) ⁻¹' Set.Ioi 2) := by
      refine ContinuousOn.isOpen_inter_preimage ?_ isOpen_U isOpen_Ioi
      exact (Complex.imCLM.continuous.comp_continuousOn
        ((contDiffOn_mob (n := 1) g₀⁻¹).continuousOn.comp (contDiffOn_mob (n := 1) γ').continuousOn (mapsTo_mob _)))
    have hzmem : z ∈ U ∩ (fun u => (mob g₀⁻¹ (mob γ' u)).im) ⁻¹' Set.Ioi 2 := ⟨hz, hdeep⟩
    have hconst : ∀ u ∈ U ∩ (fun u => (mob g₀⁻¹ (mob γ' u)).im) ⁻¹' Set.Ioi 2,
        φ₀ u - D.corr φ₀ u = ρ ⟨γ', hγ'⟩⁻¹ (-D.v g₀ - c ⟨γ', hγ'⟩) := by
      rintro u ⟨hu, hu2⟩
      have hdu : 2 < (mob g₀⁻¹ (mob γ' u)).im := hu2
      have h1 := D.corr_deep φ₀ hφ₀eq hg₀ (mob_mem γ' u) hdu
      have h2 := hφ₀eq ⟨γ', hγ'⟩ u hu
      have h3 : (ρ ⟨γ', hγ'⟩⁻¹) (ρ ⟨γ', hγ'⟩ (φ₀ u - D.corr φ₀ u)) = φ₀ u - D.corr φ₀ u := by
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      have h4 : ρ ⟨γ', hγ'⟩ (φ₀ u - D.corr φ₀ u) = -D.v g₀ - c ⟨γ', hγ'⟩ := by
        rw [map_sub, ← D.corr_mob φ₀ ⟨γ', hγ'⟩ hu]
        have : φ₀ (mob γ' u) - D.corr φ₀ (mob γ' u) = -D.v g₀ := by
          rw [h1]; abel
        have h5 : ρ ⟨γ', hγ'⟩ (φ₀ u) = φ₀ (mob γ' u) - c ⟨γ', hγ'⟩ := by
          rw [h2]; abel
        rw [h5, sub_right_comm, this]
      rw [← h3, h4]
    have hev : (fun u => φ₀ u - D.corr φ₀ u) =ᶠ[nhds z]
        fun _ => ρ ⟨γ', hγ'⟩⁻¹ (-D.v g₀ - c ⟨γ', hγ'⟩) :=
      Filter.eventuallyEq_of_mem (hopen.mem_nhds hzmem) hconst
    rw [hev.fderiv_eq]
    exact fderiv_const_apply _


/-- A complex matrix representation acting on `EuclideanSpace ℂ (Fin d)`, as a real representation. -/
def matrixRep {d : ℕ} (ρ : Γ →* Matrix (Fin d) (Fin d) ℂ) :
    Γ →* (EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin d)) where
  toFun γ := (Matrix.toEuclideanLin (ρ γ)).restrictScalars ℝ
  map_one' := by
    ext v i
    simp
  map_mul' a b := by
    ext v i
    simp [Matrix.mulVec_mulVec]

theorem matrixRep_apply {d : ℕ} (ρ : Γ →* Matrix (Fin d) (Fin d) ℂ) (γ : Γ)
    (v : EuclideanSpace ℂ (Fin d)) : matrixRep ρ γ v = Matrix.toEuclideanLin (ρ γ) v := rfl

/-- **Step 1, matrix form**: `W = EuclideanSpace ℂ (Fin d)` with `ρ` acting through
`Matrix.toEuclideanLin`. -/
theorem exists_compactSupport_primitive_matrix {d : ℕ} [Γ.FiniteIndex]
    (hneg : (-1 : SL(2, ℤ)) ∉ Γ) (ρ : Γ →* Matrix (Fin d) (Fin d) ℂ)
    (c : Γ → EuclideanSpace ℂ (Fin d))
    (hc : ∀ δ γ : Γ, c (δ * γ) = c δ + Matrix.toEuclideanLin (ρ δ) (c γ))
    (hpar : ∀ γ : Γ, IsParabolicElt γ.1 → ∃ u : EuclideanSpace ℂ (Fin d),
      c γ = Matrix.toEuclideanLin (ρ γ) u - u) :
    ∃ φ : ℂ → EuclideanSpace ℂ (Fin d), ContDiffOn ℝ ∞ φ U ∧
      (∀ δ : Γ, ∀ z ∈ U, φ (mob (δ : SL(2, ℤ)) z) = Matrix.toEuclideanLin (ρ δ) (φ z) + c δ) ∧
      ∃ K : Set ℂ, IsCompact K ∧ K ⊆ U ∧
        ∀ z ∈ U, (∀ γ : Γ, mob (γ : SL(2, ℤ)) z ∉ K) → fderiv ℝ φ z = 0 :=
  exists_compactSupport_primitive hneg (matrixRep ρ) c hc hpar

end TernaryPeriodPolynomials.Argument.ESFoundations.CompactSupport
