module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.PlusGroup
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.StabilizerEdge

@[expose] public section


/-!
# The determinant-one part of the good-line stabilizer as a split extension (line mirror of `SeedC3S4c.PlusGroup`, first half)

`Λ₁ = {Q(3b, m, 1)} = flagArithmeticStabilizer .line ⟨e₃⟩` is the library's arithmetic stabilizer of the good line (`ℤ² ⋊ GL₂(ℤ)`, radical lattice `3ℤ²`).
Its determinant-one part `Λ₁⁺ = ℤ² ⋊ SL₂(ℤ)` (`Lam1Plus`) is a split extension (`linePlusExtension`, `linePlusSplitting`); `lam1_entries` gives the block shape
`[[m, 0], [c, 1]]` of its elements.

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c (SL2Z)

/-- The library's arithmetic stabilizer `Λ₁` of the good line. -/
abbrev Lam1 : Subgroup RationalGL3 :=
  flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine)

/-- `Λ₁⁺ = ℤ² ⋊ SL₂(ℤ)`. -/
abbrev Lam1Plus : Subgroup Lam1 := SL2Z.comap goodLineLeviProjection

/-- Every element of `Λ₁` is `[[m, 0], [c, 1]]` with `m` its Levi projection. -/
theorem lam1_entries (g : Lam1) :
    (g : RationalGL3).val 0 2 = 0 ∧ (g : RationalGL3).val 1 2 = 0 ∧ (g : RationalGL3).val 2 2 = 1 ∧
      ∀ i j : Fin 2, (((goodLineLeviProjection g : GeneralLinearGroup (Fin 2) ℤ) :
        Matrix (Fin 2) (Fin 2) ℤ) i j : ℚ) = (g : RationalGL3).val i.castSucc j.castSucc := by
  obtain ⟨a, b, m, hg⟩ := goodLine_stabilizer_exists_blocks g
  have hm := goodLineLeviProjection_blocks g a b m hg
  have hv : (g : RationalGL3).val =
      !![((m : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℚ), (m : Matrix (Fin 2) (Fin 2) ℤ) 0 1, 0;
        (m : Matrix (Fin 2) (Fin 2) ℤ) 1 0, (m : Matrix (Fin 2) (Fin 2) ℤ) 1 1, 0;
        3 * a, 3 * b, 1] := by
    rw [hg]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lowerPlaneUnipotent, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three]
  refine ⟨by rw [hv]; rfl, by rw [hv]; rfl, by rw [hv]; rfl, fun i j => ?_⟩
  rw [hm, hv]
  fin_cases i <;> fin_cases j <;> rfl

/-- The radical lattice inside `Λ₁⁺`. -/
def linePlusInl : RadicalLattice →* Lam1Plus :=
  goodLineRadicalInclusion.codRestrict _ (fun r => by
    show goodLineLeviProjection (goodLineRadicalInclusion r) ∈ SL2Z
    rw [goodLineLeviProjection_radical]
    exact one_mem _)

/-- The Levi projection `Λ₁⁺ → SL₂(ℤ)` (as a subgroup of `GL₂(ℤ)`). -/
def linePlusProj : Lam1Plus →* SL2Z :=
  (goodLineLeviProjection.comp Lam1Plus.subtype).codRestrict _ (fun g => g.property)

/-- The Levi section `SL₂(ℤ) → Λ₁⁺`. -/
def linePlusSection : SL2Z →* Lam1Plus :=
  (goodLineLeviSection.comp SL2Z.subtype).codRestrict _ (fun m => by
    show goodLineLeviProjection (goodLineLeviSection m) ∈ SL2Z
    rw [goodLineLeviProjection_section]
    exact m.property)

theorem linePlusProj_section (m : SL2Z) : linePlusProj (linePlusSection m) = m := by
  apply Subtype.ext
  exact goodLineLeviProjection_section m

/-- The split extension `ℤ² → Λ₁⁺ → SL₂(ℤ)`. -/
def linePlusExtension : GroupExtension RadicalLattice Lam1Plus SL2Z where
  inl := linePlusInl
  rightHom := linePlusProj
  inl_injective := fun a b h =>
    goodLineRadicalInclusion_injective (congrArg (fun x : Lam1Plus => (x : Lam1)) h)
  range_inl_eq_ker_rightHom := by
    ext g
    constructor
    · rintro ⟨r, rfl⟩
      apply Subtype.ext
      exact goodLineLeviProjection_radical r
    · intro hg
      have hker : (g : Lam1) ∈ goodLineLeviProjection.ker :=
        congrArg Subtype.val (MonoidHom.mem_ker.mp hg)
      rw [← goodLineRadical_range] at hker
      obtain ⟨r, hr⟩ := hker
      exact ⟨r, Subtype.ext hr⟩
  rightHom_surjective := fun m => ⟨linePlusSection m, linePlusProj_section m⟩

/-- The Levi splitting of `Λ₁⁺`. -/
def linePlusSplitting : linePlusExtension.Splitting :=
  ⟨linePlusSection, linePlusProj_section⟩

end TernaryPeriodPolynomials.Argument.LineSeed
