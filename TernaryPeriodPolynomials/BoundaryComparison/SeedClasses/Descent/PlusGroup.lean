module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.StabilizerSplitting
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.FlagBlocks
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.StabilizerActions
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.PlaneRep

@[expose] public section


/-!
# The determinant-one part of the identity-plane stabilizer as a plane parabolic group

`Λ₀ = flagArithmeticStabilizer .plane 1` is the library's arithmetic stabilizer of the identity plane,
the group `ℤ² ⋊ GL₂(ℤ)` of matrices `[[m, b], [0, 1]]` (`identityPlane_stabilizer_exists_blocks`).
Its determinant-one part `Λ₀⁺ = ℤ² ⋊ SL₂(ℤ)` acts holomorphically on the plane face; this module
makes it a split extension `ℤ² → Λ₀⁺ → SL₂(ℤ)` (`plusExtension`, `plusSplitting`), gives it the
plane-parabolic data of de Rham construction (`plusPlaneData`), and proves that D's
coefficient representation `rhoC` is the restriction of the library's coefficient representation
`identityPlaneCoefficientRep` (`plusPlaneData_rhoC`). This is the transport step (S4c, item 1) from
the de Rham class of the seed (Lemma C.3, `ar:lem:seed`, of
the paper) to the library's stratum cohomology.

Written by Claude Opus 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3

/-- The library's arithmetic stabilizer `Λ₀` of the identity plane. -/
abbrev Lam0 : Subgroup RationalGL3 :=
  flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3))

/-- `SL₂(ℤ)` inside `GL₂(ℤ)`. -/
abbrev SL2Z : Subgroup (GeneralLinearGroup (Fin 2) ℤ) :=
  (GeneralLinearGroup.det : GeneralLinearGroup (Fin 2) ℤ →* ℤˣ).ker

/-- `Λ₀⁺ = ℤ² ⋊ SL₂(ℤ)`. -/
abbrev Lam0Plus : Subgroup Lam0 := SL2Z.comap identityPlaneLeviProjection

/-- Every element of `Λ₀` is `[[m, b], [0, 1]]` with `m` its Levi projection. -/
theorem lam0_entries (g : Lam0) :
    (g : RationalGL3).val 2 0 = 0 ∧ (g : RationalGL3).val 2 1 = 0 ∧ (g : RationalGL3).val 2 2 = 1 ∧
      ∀ i j : Fin 2, (((identityPlaneLeviProjection g : GeneralLinearGroup (Fin 2) ℤ) :
        Matrix (Fin 2) (Fin 2) ℤ) i j : ℚ) = (g : RationalGL3).val i.castSucc j.castSucc := by
  obtain ⟨a, b, m, hg⟩ := identityPlane_stabilizer_exists_blocks g
  have hm := identityPlaneLeviProjection_blocks g a b m hg
  have hv : (g : RationalGL3).val =
      !![((m : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℚ), (m : Matrix (Fin 2) (Fin 2) ℤ) 0 1, a;
        (m : Matrix (Fin 2) (Fin 2) ℤ) 1 0, (m : Matrix (Fin 2) (Fin 2) ℤ) 1 1, b; 0, 0, 1] := by
    rw [hg]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [planeUnipotent, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three]
  refine ⟨by rw [hv]; rfl, by rw [hv]; rfl, by rw [hv]; rfl, fun i j => ?_⟩
  rw [hm, hv]
  fin_cases i <;> fin_cases j <;> rfl

/-- The radical lattice inside `Λ₀⁺`. -/
def plusInl : RadicalLattice →* Lam0Plus :=
  identityPlaneRadicalInclusion.codRestrict _ (fun r => by
    show identityPlaneLeviProjection (identityPlaneRadicalInclusion r) ∈ SL2Z
    rw [identityPlaneLeviProjection_radical]
    exact one_mem _)

/-- The Levi projection `Λ₀⁺ → SL₂(ℤ)`. -/
def plusProj : Lam0Plus →* SL2Z :=
  (identityPlaneLeviProjection.comp Lam0Plus.subtype).codRestrict _ (fun g => g.property)

/-- The Levi section `SL₂(ℤ) → Λ₀⁺`. -/
def plusSection : SL2Z →* Lam0Plus :=
  (identityPlaneLeviSection.comp SL2Z.subtype).codRestrict _ (fun m => by
    show identityPlaneLeviProjection (identityPlaneLeviSection m) ∈ SL2Z
    rw [identityPlaneLeviProjection_section]
    exact m.property)

theorem plusProj_section (m : SL2Z) : plusProj (plusSection m) = m := by
  apply Subtype.ext
  exact identityPlaneLeviProjection_section m

/-- The split extension `ℤ² → Λ₀⁺ → SL₂(ℤ)`. -/
def plusExtension : GroupExtension RadicalLattice Lam0Plus SL2Z where
  inl := plusInl
  rightHom := plusProj
  inl_injective := fun a b h =>
    identityPlaneRadicalInclusion_injective (congrArg (fun x : Lam0Plus => (x : Lam0)) h)
  range_inl_eq_ker_rightHom := by
    ext g
    constructor
    · rintro ⟨r, rfl⟩
      apply Subtype.ext
      exact identityPlaneLeviProjection_radical r
    · intro hg
      have hker : (g : Lam0) ∈ identityPlaneLeviProjection.ker :=
        congrArg Subtype.val (MonoidHom.mem_ker.mp hg)
      rw [← identityPlaneRadical_range] at hker
      obtain ⟨r, hr⟩ := hker
      exact ⟨r, Subtype.ext hr⟩
  rightHom_surjective := fun m => ⟨plusSection m, plusProj_section m⟩

/-- The Levi splitting of `Λ₀⁺`. -/
def plusSplitting : plusExtension.Splitting :=
  ⟨plusSection, plusProj_section⟩

/-! ### Plane-parabolic data and the coefficient representation -/

/-- The real Levi block of an element of `Λ₀⁺`. -/
def plusLam : Lam0Plus →* GeneralLinearGroup (Fin 2) ℝ :=
  (GeneralLinearGroup.map (Int.castRingHom ℝ)).comp (identityPlaneLeviProjection.comp Lam0Plus.subtype)

/-- The real radical column of an element of `Λ₀⁺`. -/
def plusW (g : Lam0Plus) : Fin 2 → ℝ :=
  ![(((g : Lam0) : RationalGL3).val 0 2 : ℝ), (((g : Lam0) : RationalGL3).val 1 2 : ℝ)]

private theorem plusLam_entry (g : Lam0Plus) (i j : Fin 2) :
    ((plusLam g : GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j =
      ((((g : Lam0) : RationalGL3).val i.castSucc j.castSucc : ℚ) : ℝ) := by
  have h := (lam0_entries (g : Lam0)).2.2.2 i j
  rw [← h]
  simp [plusLam, GeneralLinearGroup.map_apply]

/-- The real matrix of an element of `Λ₀⁺` is `[[λ, w], [0, 1]]`. -/
theorem plus_matrix (g : Lam0Plus) :
    (((g : Lam0) : RationalGL3).val).map (algebraMap ℚ ℝ) =
      parabolicMatrix ((plusLam g : GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
        (plusW g) := by
  obtain ⟨h20, h21, h22, -⟩ := lam0_entries (g : Lam0)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [parabolicMatrix, plusLam_entry, plusW, h20, h21, h22, Matrix.map_apply]

theorem plusW_mul (g h : Lam0Plus) :
    plusW (g * h) = plusW g +
      ((plusLam g : GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).mulVec (plusW h) := by
  obtain ⟨-, -, hh22, -⟩ := lam0_entries (h : Lam0)
  have hval : (((g * h : Lam0Plus) : Lam0) : RationalGL3).val =
      (((g : Lam0) : RationalGL3).val) * (((h : Lam0) : RationalGL3).val) := rfl
  funext i
  fin_cases i
  · simp only [plusW, Matrix.mulVec, dotProduct, Fin.sum_univ_two, plusLam_entry, hval,
      Matrix.mul_apply, Fin.sum_univ_three, hh22, Matrix.cons_val_zero, Matrix.cons_val_one,
      Pi.add_apply, Fin.zero_eta, Fin.isValue, Fin.castSucc_zero, Fin.castSucc_one]
    push_cast
    ring
  · simp only [plusW, Matrix.mulVec, dotProduct, Fin.sum_univ_two, plusLam_entry, hval,
      Matrix.mul_apply, Fin.sum_univ_three, hh22, Matrix.cons_val_zero, Matrix.cons_val_one,
      Pi.add_apply, Fin.mk_one, Fin.isValue, Fin.castSucc_zero, Fin.castSucc_one]
    push_cast
    ring

/-- `Λ₀⁺` as a plane parabolic group `PlaneData`). -/
def plusPlaneData : PlaneData Lam0Plus where
  lam := plusLam
  w := plusW
  det_one g := by
    have hdet : GeneralLinearGroup.det (identityPlaneLeviProjection (g : Lam0)) = 1 := g.property
    simp only [plusLam, MonoidHom.comp_apply, Subgroup.coe_subtype]
    rw [GeneralLinearGroup.map_det, hdet, map_one]
  w_mul := plusW_mul

/-- D's embedding `σ` of `Λ₀⁺` into `GL₃(ℝ)` is the real image of the rational matrix. -/
theorem plusPlaneData_sigma (g : Lam0Plus) :
    plusPlaneData.sigma g = GeneralLinearGroup.map (algebraMap ℚ ℝ) ((g : Lam0) : RationalGL3) := by
  apply Units.ext
  change parabolicMatrix ((plusLam g : GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
    (plusW g) = (((g : Lam0) : RationalGL3).val).map (algebraMap ℚ ℝ)
  exact (plus_matrix g).symm

/-- D's coefficient representation of `Λ₀⁺` is the restriction of the library's coefficient
representation of `Λ₀` (trivial character). -/
theorem plusPlaneData_rhoC (n : ℕ) (g : Lam0Plus) :
    plusPlaneData.rhoC n g = (identityPlaneCoefficientRep n).ρ (g : Lam0) := by
  change GeneralEisenstein.realCoefficient n (plusPlaneData.sigma g) =
    rationalCoefficientComponent n trivialCharacter ((g : Lam0) : RationalGL3)
  rw [plusPlaneData_sigma]
  change _ = componentCharacter trivialCharacter _ • GeneralEisenstein.realCoefficient n _
  have h1 : componentCharacter trivialCharacter
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) ((g : Lam0) : RationalGL3)) = 1 := rfl
  rw [h1, one_smul]

end TernaryPeriodPolynomials.Argument.SeedC3S4c
