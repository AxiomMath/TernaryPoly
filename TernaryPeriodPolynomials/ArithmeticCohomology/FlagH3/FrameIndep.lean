module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagH3.FlagCoords
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagH3.Independence

@[expose] public section



/-!
# `λ_F` and `G_F` do not depend on the choice of the frame `g` with `flagOf g = F`

Formalized by Claude Sonnet 5.5.

`flagDataAt F g hg` is the flag datum on the stabilizer of `F`, computed with the Heisenberg coordinates (entries of `g γ g⁻¹`) of a frame `g` with `flagOf g = F`.  Two frames `g`, `g'` of the same flag differ by an upper
triangular matrix `β = g' g⁻¹` of determinant `1`; the two coordinate systems are related by `a' = e₁e₂ a`, `b' = e₂e₃ b`, `c' = e₁e₃ c + s a + t b` (`frame_rel`), so the Heisenberg cocycles are cohomologous
(`theta_change`) and the functionals agree (`flagDataAt_lam_indep`).  Hence `flagLam F` and `flagGen F` (defined with `Classical.choose`) are the same for every frame (`flagLam_frame`, `flagGen_frame`).
-/

open CategoryTheory MonoidalCategory
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FlagH3

open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg (flagGroup flag_entries)
open TernaryPeriodPolynomials.Argument.GammaNFacesFull (lineBorel)
open TernaryPeriodPolynomials.Argument.SeedC3S4c (planeBorel)
open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

/-- The isomorphism from the flag group `Γ(6) ∩ g⁻¹Bg` to the stabilizer of `F`, when `flagOf g = F`. -/
def stabCongr (F : Flag) (g : SL(3, ℤ)) (hg : flagOf g = F) :
    ↥(gammaNBAt 6 g) ≃* ↥(MulAction.stabilizer Γ6 F) :=
  (flagStabEquiv g).trans (MulEquiv.subgroupCongr (by rw [hg]))

theorem stabCongr_val (F : Flag) (g : SL(3, ℤ)) (hg : flagOf g = F) (p : ↥(gammaNBAt 6 g)) :
    (gammaSixEquiv.symm ((stabCongr F g hg p : ↥(MulAction.stabilizer Γ6 F)) : Γ6)).1 = p.1 := by
  subst hg
  have : ((stabCongr (flagOf g) g rfl p : ↥(MulAction.stabilizer Γ6 (flagOf g))) : Γ6) = flagEmb g p := rfl
  rw [this]
  simp [flagEmb]


/-- The flag datum on the stabilizer of `F`, computed with the coordinates of a frame `g` with `flagOf g = F`. -/
def flagDataAt (F : Flag) (g : SL(3, ℤ)) (hg : flagOf g = F) : FlagCohomDatum ↥(MulAction.stabilizer Γ6 F) :=
  ((flagCoords g).ofMulEquiv (stabCongr F g hg)).flagData
    (mapEquivExt (flagExt g) (stabCongr F g hg) (MulEquiv.refl _)) (stabCongr F g hg (flagX g))
    (stabCongr F g hg (flagY g)) 6 6 (by norm_num) (by norm_num)
    (by simpa [HeisCoords.ofMulEquiv] using (flagX_coords g).1)
    (by simpa [HeisCoords.ofMulEquiv] using (flagX_coords g).2.1)
    (by simpa [HeisCoords.ofMulEquiv] using (flagX_coords g).2.2)
    (by simpa [HeisCoords.ofMulEquiv] using (flagY_coords g).1)
    (by simpa [HeisCoords.ofMulEquiv] using (flagY_coords g).2.1)
    (by simpa [HeisCoords.ofMulEquiv] using (flagY_coords g).2.2)

/-- The matrix `g q g⁻¹` of a stabilizer element, for a frame `g` of `F`. -/
def frameMat (F : Flag) (g : SL(3, ℤ)) (γ : ↥(MulAction.stabilizer Γ6 F)) : SL(3, ℤ) :=
  g * (gammaSixEquiv.symm γ.1).1 * g⁻¹

theorem frameMat_coords (F : Flag) (g : SL(3, ℤ)) (hg : flagOf g = F) (γ : ↥(MulAction.stabilizer Γ6 F)) :
    ((flagCoords g).ofMulEquiv (stabCongr F g hg)).a γ = (frameMat F g γ : Matrix (Fin 3) (Fin 3) ℤ) 0 1 ∧
    ((flagCoords g).ofMulEquiv (stabCongr F g hg)).b γ = (frameMat F g γ : Matrix (Fin 3) (Fin 3) ℤ) 1 2 ∧
    ((flagCoords g).ofMulEquiv (stabCongr F g hg)).c γ = (frameMat F g γ : Matrix (Fin 3) (Fin 3) ℤ) 0 2 := by
  have h := stabCongr_val F g hg ((stabCongr F g hg).symm γ)
  rw [MulEquiv.apply_symm_apply] at h
  refine ⟨?_, ?_, ?_⟩ <;> simp [HeisCoords.ofMulEquiv, flagCoords, conjB, frameMat, h]


theorem frameMat_mem (F : Flag) (g : SL(3, ℤ)) (hg : flagOf g = F) (γ : ↥(MulAction.stabilizer Γ6 F)) :
    frameMat F g γ ∈ flagGroup 6 := by
  have h := stabCongr_val F g hg ((stabCongr F g hg).symm γ)
  rw [MulEquiv.apply_symm_apply] at h
  have := conjB_mem g ((stabCongr F g hg).symm γ)
  unfold conjB at this
  rw [← h] at this
  exact this

/-- Two frames of the same flag differ by an upper triangular matrix. -/
theorem frame_borel (g g' : SL(3, ℤ)) (h : flagOf g = flagOf g') :
    (g' * g⁻¹ : SL(3, ℤ)) ∈ lineBorel ∧ (g' * g⁻¹ : SL(3, ℤ)) ∈ planeBorel := by
  have h1 : lineOf g = lineOf g' := congrArg (fun F : Flag => F.val.1) h
  have h2 : planeOf g = planeOf g' := congrArg (fun F : Flag => F.val.2) h
  exact ⟨(lineOf_eq_iff g g').1 h1, (planeOf_eq_iff g g').1 h2⟩


theorem frame_rel (F : Flag) (g g' : SL(3, ℤ)) (hg : flagOf g = F) (hg' : flagOf g' = F) :
    ∃ α β s t : ℤ, α * α = 1 ∧ β * β = 1 ∧ ∀ γ : ↥(MulAction.stabilizer Γ6 F),
      (frameMat F g' γ : Matrix (Fin 3) (Fin 3) ℤ) 0 1 = α * (frameMat F g γ : Matrix (Fin 3) (Fin 3) ℤ) 0 1 ∧
      (frameMat F g' γ : Matrix (Fin 3) (Fin 3) ℤ) 1 2 = β * (frameMat F g γ : Matrix (Fin 3) (Fin 3) ℤ) 1 2 ∧
      (frameMat F g' γ : Matrix (Fin 3) (Fin 3) ℤ) 0 2 = α * β * (frameMat F g γ : Matrix (Fin 3) (Fin 3) ℤ) 0 2 +
        s * (frameMat F g γ : Matrix (Fin 3) (Fin 3) ℤ) 0 1 + t * (frameMat F g γ : Matrix (Fin 3) (Fin 3) ℤ) 1 2 := by
  set B0 : Matrix (Fin 3) (Fin 3) ℤ := ((g' * g⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) with hB0
  obtain ⟨⟨b10, b20⟩, ⟨-, b21⟩⟩ := frame_borel g g' (hg.trans hg'.symm)
  have hdet : B0.det = 1 := (g' * g⁻¹ : SL(3, ℤ)).2
  have b10' : B0 1 0 = 0 := b10
  have b21' : B0 2 1 = 0 := b21
  have b20' : B0 2 0 = 0 := b20
  rw [Matrix.det_fin_three, b10', b20', b21'] at hdet
  have pr : B0 0 0 * B0 1 1 * B0 2 2 = 1 := by linear_combination hdet
  obtain ⟨u1, u2, u3⟩ := unit_sq pr
  refine ⟨B0 0 0 * B0 1 1, B0 1 1 * B0 2 2, -B0 1 2, B0 2 2 * B0 0 1, ?_, ?_, fun γ => ?_⟩
  · linear_combination (B0 0 0 * B0 0 0) * u2 + u1
  · linear_combination (B0 1 1 * B0 1 1) * u3 + u2
  set M : Matrix (Fin 3) (Fin 3) ℤ := (frameMat F g γ : Matrix (Fin 3) (Fin 3) ℤ) with hM
  set M' : Matrix (Fin 3) (Fin 3) ℤ := (frameMat F g' γ : Matrix (Fin 3) (Fin 3) ℤ) with hM'
  obtain ⟨m00, m11, m22, -⟩ := flag_entries (by norm_num : 3 ≤ 6) (frameMat_mem F g hg γ)
  obtain ⟨-, m10, m20, m21⟩ := frameMat_mem F g hg γ
  obtain ⟨n00, n11, n22, -⟩ := flag_entries (by norm_num : 3 ≤ 6) (frameMat_mem F g' hg' γ)
  obtain ⟨-, n10, n20, n21⟩ := frameMat_mem F g' hg' γ
  have hrel : M' * B0 = B0 * M := by
    have : frameMat F g' γ * (g' * g⁻¹) = (g' * g⁻¹) * frameMat F g γ := by
      simp only [frameMat]
      group
    exact congrArg (fun X : SL(3, ℤ) => (X : Matrix (Fin 3) (Fin 3) ℤ)) this
  have e01 := congrFun (congrFun hrel 0) 1
  have e12 := congrFun (congrFun hrel 1) 2
  have e02 := congrFun (congrFun hrel 0) 2
  simp only [Matrix.mul_apply, Fin.sum_univ_three] at e01 e12 e02
  have n00' : M' 0 0 = 1 := n00
  have n11' : M' 1 1 = 1 := n11
  have n10' : M' 1 0 = 0 := n10
  have m11' : M 1 1 = 1 := m11
  have m22' : M 2 2 = 1 := m22
  have m21' : M 2 1 = 0 := m21
  simp only [n00', n11', n10', m11', m22', m21', b10', b21', one_mul, zero_mul, mul_zero, add_zero, zero_add,
    mul_one] at e01 e12 e02
  have Ea : M' 0 1 * B0 1 1 = B0 0 0 * M 0 1 := by linear_combination e01
  have Eb : M' 1 2 * B0 2 2 = B0 1 1 * M 1 2 := by linear_combination e12
  have Ec : M' 0 2 * B0 2 2 = B0 0 0 * M 0 2 + B0 0 1 * M 1 2 - M' 0 1 * B0 1 2 := by linear_combination e02
  exact unit_coords pr Ea Eb Ec

/-- **The flag functional does not depend on the frame**: for two frames `g`, `g'` of the same complete flag `F`, the evaluation functionals `λ_F` of `flagDataAt` coincide. -/
theorem flagDataAt_lam_indep (F : Flag) (g g' : SL(3, ℤ)) (hg : flagOf g = F) (hg' : flagOf g' = F) :
    (flagDataAt F g hg).lam = (flagDataAt F g' hg').lam := by
  obtain ⟨α, β, s, t, hα, hβ, hrel⟩ := frame_rel F g g' hg hg'
  unfold flagDataAt
  refine HeisCoords.flagData_lam_eq _ _ α β s t hα hβ ?_ ?_ ?_ _ _ _ _ _ _ 6 6 6 6 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) _ _ _ _ _ _ _ _ _ _ _ _ rfl
  · intro γ
    rw [(frameMat_coords F g' hg' γ).1, (frameMat_coords F g hg γ).1]
    exact (hrel γ).1
  · intro γ
    rw [(frameMat_coords F g' hg' γ).2.1, (frameMat_coords F g hg γ).2.1]
    exact (hrel γ).2.1
  · intro γ
    rw [(frameMat_coords F g' hg' γ).2.2, (frameMat_coords F g hg γ).2.2, (frameMat_coords F g hg γ).1,
      (frameMat_coords F g hg γ).2.1]
    exact (hrel γ).2.2

theorem flagDataAt_self (g : SL(3, ℤ)) : (flagDataAt (flagOf g) g rfl).lam = (flagStabData g).lam :=
  FlagCohomDatum.lam_eq_of_z (flagDataAt (flagOf g) g rfl) (flagStabData g) rfl

theorem cast_lam_eq (g0 : SL(3, ℤ)) (F : Flag) (h : flagOf g0 = F) :
    (h ▸ flagStabData g0 : FlagCohomDatum ↥(MulAction.stabilizer Γ6 F)).lam = (flagDataAt F g0 h).lam := by
  subst h
  exact (flagDataAt_self g0).symm

/-- Independence of the choice of frame, for the datum used throughout: `flagStabDataOf F` has the same functional as the datum computed with any frame. -/
theorem flagStabDataOf_lam_eq (F : Flag) (g : SL(3, ℤ)) (hg : flagOf g = F) :
    (flagStabDataOf F).lam = (flagDataAt F g hg).lam :=
  (cast_lam_eq _ F (Classical.choose_spec (exists_flagOf F))).trans
    (flagDataAt_lam_indep F _ g (Classical.choose_spec (exists_flagOf F)) hg)

namespace FlagCohomDatum

theorem gen_eq_of_lam_eq {B : Type} [Group B] (D D' : FlagCohomDatum B) (h : D.lam = D'.lam) : D.gen = D'.gen :=
  D'.gen_unique (by rw [← h]; exact D.lam_gen) D'.lam_gen

end FlagCohomDatum

/-- **`λ_F` is independent of the frame**: for any `g` with `flagOf g = F`, the functional `flagLam F` is the functional of the datum computed in the coordinates of `g`. -/
theorem flagLam_frame (F : Flag) (g : SL(3, ℤ)) (hg : flagOf g = F) :
    flagLam F = (flagDataAt F g hg).lam ∘ₗ (resTrivialEquiv Γ6 (MulAction.stabilizer Γ6 F) 3).toLinearMap := by
  unfold flagLam
  rw [flagStabDataOf_lam_eq F g hg]

/-- **`G_F` is independent of the frame**. -/
theorem flagGen_frame (F : Flag) (g : SL(3, ℤ)) (hg : flagOf g = F) :
    flagGen F = (resTrivialEquiv Γ6 (MulAction.stabilizer Γ6 F) 3).symm (flagDataAt F g hg).gen := by
  unfold flagGen
  rw [FlagCohomDatum.gen_eq_of_lam_eq _ (flagDataAt F g hg) (flagStabDataOf_lam_eq F g hg)]

end TernaryPeriodPolynomials.Argument.FlagH3
