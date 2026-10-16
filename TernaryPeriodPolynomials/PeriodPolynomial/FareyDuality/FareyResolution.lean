module

public import TernaryPeriodPolynomials.PeriodPolynomial.FareyDuality.FareyComplex
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic

@[expose] public section


/-!
# The dual Farey tree is a projective resolution of the trivial `GL₂(ℤ)`-representation

Formalized by Claude Sonnet 5.5.

`farComplex` is the two-term complex `P1 → P0` (degrees `1, 0`) of `FareyComplex`; `farPi` its augmentation to the trivial
representation; `farPi_quasiIso` follows from the exactness `d1_injective`, `exists_d1_preimage`, `epsMap_surjective`
(the same recipe as Mathlib's `Rep.FiniteCyclicGroup.resolution_quasiIso`); `farResolution` is the resulting
`ProjectiveResolution (Rep.trivial ℚ GL₂(ℤ) ℚ)`.  Consequently `groupHomologyFarey` computes `Hₙ(GL₂(ℤ), M)` as the homology of
`(M ⊗ P_•)_Γ`, and `Hₙ` vanishes for `n ≥ 2` (`isZero_groupHomology_two_le`): `GL₂(ℤ)` has rational cohomological
dimension one.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FareyTree

open CategoryTheory CategoryTheory.Limits Representation Rep TernaryPoly.RankTwoAugmentedFrames
open ZeroObject

/-- The terms of the two-term complex. -/
def farX : ℕ → Rep ℚ IntegralGL
  | 0 => P0
  | 1 => P1
  | _ + 2 => 0

/-- The differentials of the two-term complex. -/
def farD : ∀ n : ℕ, farX (n + 1) ⟶ farX n
  | 0 => d1
  | _ + 1 => 0

/-- The two-term complex `P1 → P0` of the dual Farey tree, in degrees `1, 0`. -/
def farComplex : ChainComplex (Rep ℚ IntegralGL) ℕ :=
  ChainComplex.of farX farD (fun n => by
    cases n with
    | zero => exact zero_comp
    | succ n => exact zero_comp)

theorem eps_d1_comp : d1 ≫ epsMap = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro a
  exact eps_d1 a

/-- The augmentation of the two-term complex. -/
def farPi : farComplex ⟶ (ChainComplex.single₀ (Rep ℚ IntegralGL)).obj (Rep.trivial ℚ IntegralGL ℚ) :=
  ((ChainComplex.toSingle₀Equiv farComplex _)).symm ⟨epsMap, by
    simp only [farComplex]
    exact eps_d1_comp⟩

instance farProjective (n : ℕ) : Projective (farComplex.X n) := by
  change Projective (farX n)
  match n with
  | 0 => exact inferInstanceAs (Projective P0)
  | 1 => exact inferInstanceAs (Projective P1)
  | n + 2 => exact (isZero_zero (Rep ℚ IntegralGL)).projective

theorem farPi_f_zero : farPi.f 0 = epsMap := by
  rfl

theorem farPi_quasiIso : QuasiIso farPi where
  quasiIsoAt m := by
    induction m with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros' _ rfl rfl rfl]
      constructor
      · apply (forget₂ _ (ModuleCat ℚ)).reflects_exact_of_faithful
        rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
        ext c
        change c ∈ LinearMap.range d1.hom.toLinearMap ↔ c ∈ LinearMap.ker epsMap.hom.toLinearMap
        constructor
        · rintro ⟨a, rfl⟩
          exact eps_d1 a
        · intro hc
          exact exists_d1_preimage c hc
      · rw [Rep.epi_iff_surjective]
        exact epsMap_surjective
    | succ m _ =>
      rw [quasiIsoAt_iff_exactAt' (hL := ChainComplex.exactAt_succ_single_obj ..),
        HomologicalComplex.exactAt_iff' _ (m + 2) (m + 1) m (by simp) (by simp)]
      cases m with
      | zero =>
        have h21 : (HomologicalComplex.sc' farComplex (0 + 2) (0 + 1) 0).f = 0 :=
          ChainComplex.of_d farX farD 1
        rw [ShortComplex.exact_iff_mono _ h21]
        change Mono (farComplex.d 1 0)
        have h10 : farComplex.d 1 0 = d1 := ChainComplex.of_d farX farD 0
        rw [h10]
        exact (Rep.mono_iff_injective d1).mpr d1_injective
      | succ m =>
        apply ShortComplex.exact_of_isZero_X₂
        exact isZero_zero (Rep ℚ IntegralGL)

/-- The dual Farey tree as a projective resolution of the trivial representation of `GL₂(ℤ)` over `ℚ`. -/
def farResolution : ProjectiveResolution (Rep.trivial ℚ IntegralGL ℚ) where
  complex := farComplex
  projective := farProjective
  π := farPi
  quasiIso := farPi_quasiIso

/-- Group homology of `GL₂(ℤ)` computed by the dual Farey tree. -/
def groupHomologyFarey (M : Rep ℚ IntegralGL) (n : ℕ) :
    groupHomology M n ≅ (farResolution.complex.coinvariantsTensorObj M).homology n :=
  groupHomologyIso M n farResolution

/-- **`GL₂(ℤ)` has rational cohomological dimension one**: `Hₙ(GL₂(ℤ), M) = 0` for `n ≥ 2`. -/
theorem isZero_groupHomology_two_le (M : Rep ℚ IntegralGL) (n : ℕ) :
    IsZero (groupHomology M (n + 2)) := by
  refine IsZero.of_iso ?_ (groupHomologyFarey M (n + 2))
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ (n + 3) (n + 2) (n + 1) (by simp) (by simp)]
  apply ShortComplex.exact_of_isZero_X₂
  exact Functor.map_isZero ((Rep.coinvariantsTensor ℚ IntegralGL).obj M) (isZero_zero (Rep ℚ IntegralGL))

end TernaryPeriodPolynomials.Argument.FareyTree
