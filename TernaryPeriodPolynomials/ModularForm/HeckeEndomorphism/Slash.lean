module

public import TernaryPeriodPolynomials.ModularForm.HeckeEndomorphism.Cosets

@[expose] public section

noncomputable section
open Matrix UpperHalfPlane
open scoped MatrixGroups ModularForm
namespace TernaryPoly.BinaryCuspHeckeEndomorphism
open BinaryModularSymbol (GL2)
open BinaryRationalHeckeArithmetic BinaryRationalHeckePrime BinaryCuspPeriod

/-- An actual integral rational matrix of determinant one belongs to the full real modular group. -/
theorem realify_mem_SL2Z (g : Gamma) (hg : g.val.val.det = 1) : realify g.val ∈ 𝒮ℒ := by
  obtain ⟨h,rfl⟩ := integralEquiv.surjective g
  have hh : h.val.det = 1 := by
    apply Int.cast_injective (α := ℚ)
    change (Int.castRingHom ℚ) h.val.det = 1
    rw [(Int.castRingHom ℚ).map_det]
    exact hg
  refine ⟨⟨h.val,hh⟩,?_⟩
  apply Units.ext
  ext i j
  change (h.val i j : ℝ) = ((h.val i j : ℚ) : ℝ)
  simp

/-- The rational image of an actual integral special-linear matrix. -/
def gamma (g : SL(2, ℤ)) : Gamma := integralEquiv g.toGL

@[simp] theorem realify_gamma (g : SL(2, ℤ)) :
    realify (gamma g).val = Matrix.SpecialLinearGroup.mapGL ℝ g := by
  apply Units.ext
  ext i j
  change (((g.val i j : ℤ) : ℚ) : ℝ) = (g.val i j : ℝ)
  simp

@[simp] theorem det_gamma (g : SL(2, ℤ)) : (gamma g).val.val.det = 1 := by
  have he := (Int.castRingHom ℚ).map_det g.val
  rw [g.property,map_one] at he
  exact he.symm

/-- The finite sum of literal real slash transforms by the upper prime representatives. -/
def slashSum {d : ℕ} (p : ℕ) [Fact p.Prime] (f : Forms d) : ℍ → ℂ :=
  ∑ i : PrimeIndex p, (f : ℍ → ℂ) ∣[(d : ℤ)+2] realify (upper p i)

/-- Exact left-coset permutation proves invariance under every element of SL2Z. -/
theorem slashSum_invariant {d : ℕ} (p : ℕ) [Fact p.Prime] (f : Forms d) (g : SL(2, ℤ)) :
    slashSum p f ∣[(d : ℤ)+2] g = slashSum p f := by
  rw [slashSum,SlashAction.sum_slash]
  have ht (i : PrimeIndex p) :
      ((f : ℍ → ℂ) ∣[(d : ℤ)+2] realify (upper p i)) ∣[(d : ℤ)+2] g =
        (f : ℍ → ℂ) ∣[(d : ℤ)+2] realify (upper p (reindex p (gamma g) i)) := by
    have hreal : Matrix.SpecialLinearGroup.toGL
        ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) g) = realify (gamma g).val :=
      (realify_gamma g).symm
    rw [ModularForm.SL_slash,hreal,←SlashAction.slash_mul,←map_mul,factor_spec,map_mul,
      SlashAction.slash_mul]
    rw [SlashInvariantFormClass.slash_action_eq f (realify (factor p (gamma g) i).val)
      (realify_mem_SL2Z _ (by rw [factor_det,det_gamma]))]
  simp_rw [ht]
  exact (reindexEquiv p (gamma g)).sum_comp
    (fun i : PrimeIndex p => (f : ℍ → ℂ) ∣[(d : ℤ)+2] realify (upper p i))

end TernaryPoly.BinaryCuspHeckeEndomorphism
