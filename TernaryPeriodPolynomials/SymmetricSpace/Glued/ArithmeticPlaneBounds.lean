module

public import TernaryPeriodPolynomials.SymmetricSpace.Glued.ArithmeticPlaneModels

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceGluedArithmetic
open Matrix SymmetricSpacePositive SymmetricSpaceParabolicCoordinates SymmetricSpaceFlagCoordinates
open SymmetricSpaceBorelCorner SymmetricSpaceRationalGluing SymmetricSpacePlaneBordification

/-- The actual affine plane equation bounds its two translation entries. -/
theorem block_translation_bound (F H M : ℝ) (hF : 0≤F) (hH : 0≤H) (_hM : 0≤M)
    (A : Mat2) (u v w : Vec2) (f : ℝ) (hf : f≠0)
    (hA : ∀ i j,|A i j|≤H) (hfb : |f|≤F) (hv : ∀ i,|v i|≤M) (hw : ∀ i,|w i|≤M)
    (he : transformedUnipotent A u f v=w) : ∀ i,|u i|≤F*M+2*H*M := by
  intro i
  have hi := congrArg (fun z : Vec2 => z i) he
  simp [transformedUnipotent,smul_eq_mul,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at hi
  have hi' : A i 0*v 0+A i 1*v 1+u i=f*w i := by
    have hh := congrArg (fun z : ℝ => f*z) hi
    simpa only [←mul_assoc,mul_inv_cancel₀ hf,one_mul,add_zero] using hh
  have hui : u i=f*w i-(A i 0*v 0+A i 1*v 1) := by linarith
  calc
    |u i|=|f*w i-(A i 0*v 0+A i 1*v 1)| := congrArg abs hui
    _ ≤ |f*w i|+|A i 0*v 0+A i 1*v 1| := abs_sub _ _
    _ ≤ |f*w i|+(|A i 0*v 0|+|A i 1*v 1|) := add_le_add le_rfl (abs_add_le _ _)
    _ ≤ F*M+(H*M+H*M) := by
      simp only [abs_mul]
      exact add_le_add (mul_le_mul hfb (hw i) (abs_nonneg _) hF)
        (add_le_add (mul_le_mul (hA i 0) (hv 0) (abs_nonneg _) hH)
          (mul_le_mul (hA i 1) (hv 1) (abs_nonneg _) hH))
    _ = F*M+2*H*M := by ring

/-- All actual plane transition matrices in a bounded corner box have uniformly bounded entries.
The second root may vanish, and the first root has no imposed positive lower bound. -/
theorem real_plane_entry_bound (d : ℕ) (hd : d≠0) (D M : ℝ) (hD : 0<D) (hM : 1≤M) :
    ∃ R : ℝ,∀ (r : PlaneGroup) (p : domain r.val),HasIntegralDenominator d r.val →
      |r.val.val.det|≤D → (∀ i,|p.val.1 i|≤M) →
      (∀ i,|(transition r.val p).val.1 i|≤M) → p.val.2.1.val≤M →
      (transition r.val p).val.2.1.val≤M → ∀ i j,|r.val.val i j|≤R := by
  obtain ⟨B,hB,hdiag⟩ := real_borel_diagonal_bound d hd D hD
  obtain ⟨RB,hRB⟩ := borel_entries_bound B M hB hM
  obtain ⟨F,E,hF,hE,hFE⟩ := plane_scalar_det_bounds d hd D hD
  let δ : ℝ := 1/(d : ℝ)
  have hδ : 0<δ := one_div_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hd)
  obtain ⟨RA,hRA⟩ := binary_shape_siegel_bound δ E M hδ hE.le hM
  let H := max 1 RA
  let U := F*M+2*H*M
  let R := max RB (max H (max F U))
  have hH : 0≤H := zero_le_one.trans (le_max_left _ _)
  have hM0 : 0≤M := zero_le_one.trans hM
  have hHR : H≤R := (le_max_left _ _).trans (le_max_right _ _)
  have hFR : F≤R := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hUR : U≤R := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨R,?_⟩
  intro r p hden hdet hp hq htp htq
  by_cases h10 : r.val.val 1 0=0
  · have hborel : r.val∈borelStabilizer :=
      (mem_borelStabilizer_iff r.val).mpr ⟨h10,(mem_planeStabilizer_iff r.val).mp r.property⟩
    have hh := hRB ⟨r.val,hborel⟩ p.val (transition r.val p).val
      (hdiag ⟨r.val,hborel⟩ hden hdet) hp hq (transition_borel ⟨r.val,hborel⟩ p).symm
    exact fun i j => (hh i j).trans (le_max_left _ _)
  · have hpos : 0<p.val.2.1.val := by
      rcases ((mem_domain_iff r.val p.val).mp p.property).1 with h|h
      · exact h
      · exact False.elim (h10 ((SymmetricSpaceLineBordification.mem_lineStabilizer_iff r.val).mp h).1)
    have hqpos : 0<(transition r.val p).val.2.1.val := (transition_pos1_iff r.val p).mpr hpos
    let P := planeParametersHom r
    have h10eq : r.val.val 1 0=P.A.val 1 0 := by rw [planeParameters_matrix]; rfl
    have hclower : δ≤|P.A.val 1 0| :=
      real_denominator_lower_bound d hd _ (h10eq ▸ h10) (by simpa only [h10eq] using hden 1 0)
    have he := plane_overlap_relation r p hpos
    have hshape := congrArg (fun z : PlaneBordification => z.2.1.val) he
    change binaryNormalize (shapeMatrix ((transition r.val p).val.1 0) (transition r.val p).val.2.1.val)=
      binaryNormalize (P.A.val*binaryNormalize (shapeMatrix (p.val.1 0) p.val.2.1.val)*star P.A.val) at hshape
    obtain ⟨hf,hdetA⟩ := hFE r hden hdet
    have hAB : ∀ i j,|P.A.val i j|≤H := fun i j =>
      (hRA P.A (p.val.1 0) ((transition r.val p).val.1 0) p.val.2.1.val
        (transition r.val p).val.2.1.val hpos hqpos hclower hdetA (hp 0) (hq 0) htp htq
        hshape.symm i j).trans (le_max_right _ _)
    have hv (i : Fin 2) : |(![p.val.1 2,p.val.1 1] : Vec2) i|≤M := by
      fin_cases i
      · exact hp 2
      · exact hp 1
    have hw (i : Fin 2) : |(![(transition r.val p).val.1 2,(transition r.val p).val.1 1] : Vec2) i|≤M := by
      fin_cases i
      · exact hq 2
      · exact hq 1
    have hu : ∀ i,|P.u i|≤U := block_translation_bound F H M hF.le hH hM0 P.A.val P.u
      _ _ P.d.val P.d.ne_zero hAB hf hv hw (congrArg (fun z : PlaneBordification => z.1) he).symm
    rw [planeParameters_matrix]
    intro i j
    fin_cases i <;> fin_cases j
    · exact (hAB 0 0).trans hHR
    · exact (hAB 0 1).trans hHR
    · exact (hu 0).trans hUR
    · exact (hAB 1 0).trans hHR
    · exact (hAB 1 1).trans hHR
    · exact (hu 1).trans hUR
    · change |(0 : ℝ)|≤R
      simpa only [abs_zero] using hH.trans hHR
    · change |(0 : ℝ)|≤R
      simpa only [abs_zero] using hH.trans hHR
    · exact hf.trans hFR

end TernaryPoly.SymmetricSpaceGluedArithmetic
