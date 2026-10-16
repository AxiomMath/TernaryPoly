module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.CellExact

@[expose] public section


/-!
# The cellular permutation complex as a projective resolution

`Γ(6)` acts freely on the cells of every grade (`six_cancel`), so each `cellRep n` is projective
(`cellRep_projective`).  The augmentation `cellAug : cellPermComplex ⟶ single₀ ℚ` (`cellAug0`, the sum of the
signs `epsQ` of the vertices) is a quasi-isomorphism by the rational exactness of `CellExact`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical Pointwise

namespace TernaryPeriodPolynomials.Argument.Lemma33.Retract

open CategoryTheory Finsupp GeneralEisenstein TernaryPoly TernaryPoly.EquivariantSingularResolution
  TernaryPoly.SymmetricSpaceRationalGluing TernaryPoly.IntegralGL3Congruence
  TernaryPoly.SingularLocalHomology TernaryPoly.SymmetricSpaceBordifiedPrincipalSix
  TernaryPeriodPolynomials.FreeResolution
  TernaryPeriodPolynomials.TopVanishing


theorem six_cancel (g h : principalSix) (C : Cell) (hC : g • C = h • C) : g = h := by
  have hs : (h⁻¹ * g) • C = C := by rw [mul_smul, hC, inv_smul_smul]
  have h1 : levelOfSix (h⁻¹ * g) = 1 := Cell.free _ C hs
  have h2 : h⁻¹ * g = 1 := by
    apply Subtype.ext
    have := congrArg levelLift h1
    rw [levelLift_levelOfSix] at this
    exact this.trans (map_one _)
  exact (inv_mul_eq_one.mp h2).symm

instance (n : ℕ) : IsCancelSMul principalSix (Graded n) where
  left_cancel' a _ _ h := MulAction.injective a h
  right_cancel' a b c h := six_cancel a b c.1 (congrArg Subtype.val h)

instance cellRep_projective (n : ℕ) : Projective (cellRep n) :=
  TernaryPoly.FreeActionLinearization.permutation_projective ℚ principalSix (Graded n)

/-- The augmentation of the cells of grade zero. -/
def cellAug0 : cellRep 0 ⟶ Rep.trivial ℚ principalSix ℚ :=
  permHomTo _ augQ (fun g C => by
    rw [augQ_single, augQ_single]
    change epsQ (levelOfSix g • C.1) = _
    rw [epsQ_smul]
    rfl)

theorem cellAug0_hom (z : MonoidAlgebra ℚ (Graded 0)) :
    (cellAug0).hom z = augQ (MonoidAlgebra.coeffLinearEquiv ℚ z) := rfl

theorem cellAug0_cellD (z : MonoidAlgebra ℚ (Graded 1)) : cellAug0.hom ((cellD 0).hom z) = 0 := by
  rw [cellD_hom_apply, cellAug0_hom, LinearEquiv.apply_symm_apply]
  exact LinearMap.congr_fun augQ_dLin _

theorem cellAug_comm : cellPermComplex.d 1 0 ≫ cellAug0 = 0 := by
  rw [cellPerm_d]
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  exact cellAug0_cellD z

/-- The augmentation of the cellular permutation complex to the trivial representation. -/
def cellAug : cellPermComplex ⟶ (ChainComplex.single₀ (Rep ℚ principalSix)).obj
    (Rep.trivial ℚ principalSix ℚ) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨cellAug0, cellAug_comm⟩

theorem cellAug0_exact_aux (x : MonoidAlgebra ℚ (Graded 0)) (hx : cellAug0.hom x = 0) :
    ∃ y : MonoidAlgebra ℚ (Graded 1), (cellD 0).hom y = x := by
  rw [cellAug0_hom] at hx
  obtain ⟨y, hy⟩ := exact_zero _ hx
  refine ⟨(MonoidAlgebra.coeffLinearEquiv ℚ).symm y, ?_⟩
  rw [cellD_hom_apply, LinearEquiv.apply_symm_apply, hy, LinearEquiv.symm_apply_apply]

theorem cellAug0_exact : (ShortComplex.mk (cellPermComplex.d 1 0) cellAug0 cellAug_comm).Exact := by
  apply (ShortComplex.exact_map_iff_of_faithful _
    (forget₂ (Rep ℚ principalSix) (ModuleCat ℚ))).mp
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  obtain ⟨y, hy⟩ := cellAug0_exact_aux x hx
  refine ⟨y, ?_⟩
  change ((forget₂ (Rep ℚ principalSix) (ModuleCat ℚ)).map (cellPermComplex.d 1 0)).hom y = x
  rw [cellPerm_d]
  exact hy

theorem cellAug0_surj (q : ℚ) : ∃ x : MonoidAlgebra ℚ (Graded 0), cellAug0.hom x = q := by
  obtain ⟨C, hC⟩ := augQ_surj
  refine ⟨(MonoidAlgebra.coeffLinearEquiv ℚ).symm (single C (q / epsQ C.1)), ?_⟩
  rw [cellAug0_hom, LinearEquiv.apply_symm_apply]
  have e : (single C (q / epsQ C.1) : Graded 0 →₀ ℚ) = (q / epsQ C.1) • single C 1 := by simp
  rw [e, map_smul, augQ_single, smul_eq_mul, div_mul_cancel₀ _ hC]

instance cellAug0_epi : Epi cellAug0 := by
  apply (forget₂ (Rep ℚ principalSix) (ModuleCat ℚ)).epi_of_epi_map
  rw [ModuleCat.epi_iff_surjective]
  intro q
  exact cellAug0_surj q

instance cellAug_quasiIso : QuasiIso cellAug := by
  constructor
  intro n
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · exact ⟨cellAug0_exact, cellAug0_epi⟩
    all_goals rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt']
    · exact cellPerm_exactAt n
    · exact ChainComplex.exactAt_succ_single_obj _ _

/-- The augmented cellular permutation complex is a projective resolution of the trivial representation. -/
def cellResolution : ProjectiveResolution (Rep.trivial ℚ principalSix ℚ) where
  complex := cellPermComplex
  projective n := cellRep_projective n
  π := cellAug
  quasiIso := cellAug_quasiIso

end TernaryPeriodPolynomials.Argument.Lemma33.Retract
