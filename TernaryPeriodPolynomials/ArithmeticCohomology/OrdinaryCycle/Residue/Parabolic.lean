module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Residue.ParabolicSubstitution

@[expose] public section


open MvPolynomial
open scoped DirectSum
noncomputable section
namespace TernaryPoly.OrdinaryResidueParabolic
open PolynomialGLAction SinglePole SinglePoleCoordinate OrdinaryResidueSupport
attribute [local instance] Classical.propDecidable

/-- A normal other than a=0 cannot be transported to a=0 by this block parabolic. -/
theorem transformed_normal_ne (g : GL3) (lam : ℚˣ) (u : Fin 2 → ℚ) (C : GL2)
    (hg : g.val = blockMatrix lam u C) (H J : SinglePole.Normal) (c : ℚ)
    (hc : substitute (g⁻¹ : GL3) (denominator H) = MvPolynomial.C c * denominator J)
    (hH : H ≠ axis 0) : J ≠ axis 0 := by
  intro hJ
  subst J
  have he := congrArg (substitute (g : Mat3)) hc
  have hi : (g⁻¹).val * g.val = 1 := g.inv_val
  rw [←AlgHom.comp_apply,substitute_comp,hi,substitute_one,AlgHom.id_apply] at he
  rw [map_mul,denominator_axis,map_mul,substitute_X_zero g lam u C hg] at he
  simp only [substitute,bind₁_C_right] at he
  apply hH
  apply ((denominator_dvd_iff (axis 0) H).mp ?_).symm
  apply (denominator_axis_dvd_iff 0 (denominator H)).mpr
  rw [he]
  exact ⟨MvPolynomial.C c * MvPolynomial.C (axisScale 0) * MvPolynomial.C (lam : ℚ),by ring⟩

/-- The exact chosen-normal scaling cancels lambda and leaves only the inverse Levi determinant. -/
theorem scaledRestriction_transformed (n : ℕ) (g : GL3) (lam : ℚˣ) (u : Fin 2 → ℚ) (C : GL2)
    (hg : g.val = blockMatrix lam u C) (p : V (n+1)) :
    scaledRestriction n 0 (transformedNumerator n (-1) g ((lam : ℚ)⁻¹) p) =
      C.val.det⁻¹ • homogeneousBinarySubstitute (n+1) (C⁻¹).val (scaledRestriction n 0 p) := by
  apply Subtype.ext
  change (axisScale 0)⁻¹ • restrict 0
    (determinantCharacter (-1) g • ((lam : ℚ)⁻¹)⁻¹ • substitute (g⁻¹ : GL3) p.val) =
    C.val.det⁻¹ • binarySubstitute (C⁻¹).val ((axisScale 0)⁻¹ • restrict 0 p.val)
  rw [map_smul,map_smul,inv_inv,restrict_substitute_inverse g lam u C hg,map_smul]
  rw [smul_smul (determinantCharacter (-1) g),determinant_residue_scalar g lam u C hg]
  exact smul_comm _ _ _

/-- Literal a=0 component, retained as a linear map to use the actual direct-sum universal property. -/
def zeroCoordinate (n : ℕ) : Residues n →ₗ[ℚ] BinaryV (n+1) :=
  (literalFiberMap n 0).comp (SinglePoleSupport.component n (axis 0))

/-- Every actual residue transforms on a=0 by det(C) inverse and C inverse substitution. -/
theorem coordinateTuple_action (n : ℕ) (g : GL3) (lam : ℚˣ) (u : Fin 2 → ℚ) (C : GL2)
    (hg : g.val = blockMatrix lam u C) (r : Residues n) :
    coordinateTuple n (residueAction n (-1) g r) 0 =
      C.val.det⁻¹ • homogeneousBinarySubstitute (n+1) (C⁻¹).val (coordinateTuple n r 0) := by
  have he : (zeroCoordinate n).comp (residueAction n (-1) g) =
      (C.val.det⁻¹ • homogeneousBinarySubstitute (n+1) (C⁻¹).val).comp (zeroCoordinate n) := by
    apply DirectSum.linearMap_ext
    intro H
    apply LinearMap.ext
    intro z
    obtain ⟨p,rfl⟩ := (numeratorRelations n H).mkQ_surjective z
    change literalFiberMap n 0 ((residueAction n (-1) g
      (DirectSum.lof ℚ SinglePole.Normal (ResidueFiber n) H ((numeratorRelations n H).mkQ p))) (axis 0)) =
      C.val.det⁻¹ • homogeneousBinarySubstitute (n+1) (C⁻¹).val
        (literalFiberMap n 0 ((DirectSum.lof ℚ SinglePole.Normal (ResidueFiber n) H
          ((numeratorRelations n H).mkQ p)) (axis 0)))
    by_cases hH : H = axis 0
    · subst H
      rw [residueAction_lof n (-1) g (axis 0) (axis 0) ((lam : ℚ)⁻¹)
        (substitute_inverse_denominator g lam u C hg)]
      rw [DirectSum.lof_apply,DirectSum.lof_apply,literalFiberMap_mk,literalFiberMap_mk]
      exact scaledRestriction_transformed n g lam u C hg p
    · obtain ⟨J,c,_hc,hc⟩ := transformed_denominator_exists g H
      rw [residueAction_lof n (-1) g H J c hc]
      have hJ := transformed_normal_ne g lam u C hg H J c hc hH
      have hzJ : (DirectSum.lof ℚ SinglePole.Normal (ResidueFiber n) J
          ((numeratorRelations n J).mkQ (transformedNumerator n (-1) g c p))) (axis 0) = 0 :=
        DirectSum.of_eq_of_ne _ _ _ hJ.symm
      have hzH : (DirectSum.lof ℚ SinglePole.Normal (ResidueFiber n) H
          ((numeratorRelations n H).mkQ p)) (axis 0) = 0 :=
        DirectSum.of_eq_of_ne _ _ _ (Ne.symm hH)
      rw [hzJ,hzH,map_zero,map_zero,smul_zero]
  exact LinearMap.congr_fun he r

/-- The same literal block-parabolic law holds for actual single-pole rational coefficients. -/
theorem coordinateResidue_action (n : ℕ) (g : GL3) (lam : ℚˣ) (u : Fin 2 → ℚ) (C : GL2)
    (hg : g.val = blockMatrix lam u C) (x : singlePole n) :
    coordinateResidue n 0 (singlePoleAction n (-1) g x) =
      C.val.det⁻¹ • homogeneousBinarySubstitute (n+1) (C⁻¹).val (coordinateResidue n 0 x) := by
  change coordinateTuple n (residue n (singlePoleAction n (-1) g x)) 0 = _
  rw [←residue_equivariant]
  exact coordinateTuple_action n g lam u C hg (residue n x)

end TernaryPoly.OrdinaryResidueParabolic
