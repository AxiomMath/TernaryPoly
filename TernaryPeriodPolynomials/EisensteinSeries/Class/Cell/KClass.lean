module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Cell.KNeg
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Cusp.TransGen
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Cusp.ConstantTerm
public import TernaryPeriodPolynomials.EisensteinSeries.Class.AntiHol

@[expose] public section


/-!
# The class of the series at a cusp, restricted to the face of another cusp

Paper: "the same
letters for the rational conjugates".

For `3 ≤ N`, `4 ≤ n`, `h, h' ∈ SL₃(ℤ)` and `k = h' h⁻¹`: the class of the pullback to the boundary model
of the cusp `h⁻¹Ph` of the (holomorphic) series at the cusp `h'⁻¹Ph'` is the class of the transport
(`conjP N h`, `ρ(h⁻¹)`) of the **cell form** `cellForm N k n f`: zero if no `k γ` lies in `P(ℤ)`
(the cusps `h` and `h'` are not in the same orbit), the seed of `f|A` if `k γ = [[A, w], [0, 1]]`, and
the conjugate seed of `(f|A)^*` if `k γ = [[A', w], [0, -1]]` (finite reflection).

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open MvPolynomial
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.SeedC3S4c
  TernaryPeriodPolynomials.Argument.SeedC3.Psi TernaryPoly.SmoothLocalDeRham
  TernaryPoly.SmoothCoveringDeRham
  TernaryPeriodPolynomials.Argument.Statements.EisensteinClass
  TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4

section CellForm

variable (N : ℕ) [NeZero N] (k : SL(3, ℤ)) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

open Classical in
/-- **The cell form**: the seed of `f|A` (cell with bottom entry `1`), the conjugate seed of `(f|A)^*`
(cell with bottom entry `-1`), or `0` (no cell). -/
def cellForm : ZigZag.invClosed isOpen_faceSet (gammaNPlaneData N).action
    ((gammaNPlaneData N).rhoR n) :=
  if hc : ∃ c : Ck N k, IsCellK N k c then
    if h22 : ((cellMat N k hc.choose : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = 1 then
      cuspSeedInv (gammaNPlaneData N) (gammaNPlaneData_lam_mem N)
        (f := cuspSlash N n (leviBlock (cellMat N k hc.choose)
          (cellMat_mem_planeStab N k hc.choose_spec h22)) f)
    else
      cuspSeedConjInv (gammaNPlaneData N) (gammaNPlaneData_lam_mem N)
        (f := fStarGen (leviGroup N) (leviGroup_J_stable N)
          (cuspSlash N n (leviBlock (cellMat N k hc.choose * rPrime)
            (cellMat_mul_rPrime_mem N k hc.choose_spec
              ((cell_entry_pm_one N k hc.choose_spec).resolve_left h22))) f))
  else 0

/-- **The torus average of `ι^*E − cellForm` vanishes.** -/
theorem avInv_sub_cellForm (hN : 3 ≤ N) (hn : 4 ≤ n) :
    avInv n (latticeData_gammaN N) (faceSeriesK N k n f hn - cellForm N k n f) = 0 := by
  classical
  unfold cellForm
  by_cases hc : ∃ c : Ck N k, IsCellK N k c
  · rw [dite_eq_left hc]
    by_cases h22 : ((cellMat N k hc.choose : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = 1
    · rw [dite_eq_left h22]
      refine avInv_sub_zero_of_cell N k n f hn _ ?_
      intro y hy i j m
      have h2 := PlaneData.toPoly_d_etaForm (cuspH (leviGroup N) n
        (cuspSlash N n (leviBlock (cellMat N k hc.choose)
          (cellMat_mem_planeStab N k hc.choose_spec h22)) f)) n
        (cuspH_holo (leviGroup N) n (cuspSlash N n (leviBlock (cellMat N k hc.choose)
          (cellMat_mem_planeStab N k hc.choose_spec h22)) f)) hy i j
      rw [cell_pos_coeff N k n f hN hc.choose_spec h22 (ptOf_mem hy)]
      exact congrArg (·.coeff m) h2
    · rw [dite_eq_right h22]
      refine avInv_sub_zero_of_cell N k n f hn _ ?_
      intro y hy i j m
      rw [toPoly_cuspSeedConjInv n (gammaNPlaneData N) (gammaNPlaneData_lam_mem N) _ hy i j,
        cell_neg_coeff N k n f hN hc.choose_spec
          ((cell_entry_pm_one N k hc.choose_spec).resolve_left h22) (ptOf_mem hy)]
  · rw [dite_eq_right hc]
    have hnone : ∀ c : Ck N k, ¬ IsCellK N k c := fun c hc' => hc ⟨c, hc'⟩
    have := avInv_sub_zero_of_cell N k n f hn 0 (fun y hy i j m => by
      rw [cellCoeffK_eq_zero N k n f hnone]
      simp)
    simpa using this

end CellForm

section Transport

variable (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (hn : 4 ≤ n)
  (h h' : SL(3, ℤ))

/-- **The class of the series at the cusp `h'`, restricted to the face of the cusp `h`, is the class of
the transported cell form** (`3 ≤ N`, `4 ≤ n`; `conjP N h`, `ρ(h⁻¹)`; `k = h' h⁻¹`). -/
theorem faceClass_eq_cell (hN : 3 ≤ N) :
    ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (cuspFaceAction N h)
        (rhoAt N h n)
        (cuspFaceForm N h (planeEisensteinAtComponents false (CuspData.ofSL h') (gammaN N)
          (leviGroup N) n f hn (leviInCusp_gammaN N h'))) =
      ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (cuspFaceAction N h)
        (rhoAt N h n) (twInv (intertwines_rhoAt N n h)
          (comapAt N n h (cellForm N (h' * h⁻¹) n f))) := by
  have hT := intertwines_rhoAt N n h
  have e : cuspFaceForm N h (planeEisensteinAtComponents false (CuspData.ofSL h') (gammaN N)
      (leviGroup N) n f hn (leviInCusp_gammaN N h')) =
      twInv hT (comapAt N n h (faceSeriesK N (h' * h⁻¹) n f hn)) :=
    Subtype.ext (cuspFaceForm_eq_twist_gen N n f hn h h')
  rw [e]
  have h0 : ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty
      (cuspFaceAction N h) ((planeDataComap (gammaNPlaneData N) (conjP N h).toMonoidHom).rhoR n)
      (comapAt N n h (faceSeriesK N (h' * h⁻¹) n f hn - cellForm N (h' * h⁻¹) n f)) = 0 :=
    deRhamClass_comapInv_eq_zero (gammaNPlaneData N) (conjP N h).toMonoidHom n
      (latticeData_gammaN N) (Nat.cast_ne_zero.mpr (NeZero.ne N)) (conjP N h).surjective _
      (avInv_sub_cellForm N (h' * h⁻¹) n f hN hn)
  have h1 := deRhamClass_twist_eq_zero convex_faceSet faceSet_nonempty hT _ h0
  have h2 : twInv hT (comapAt N n h (faceSeriesK N (h' * h⁻¹) n f hn -
      cellForm N (h' * h⁻¹) n f)) =
      twInv hT (comapAt N n h (faceSeriesK N (h' * h⁻¹) n f hn)) -
        twInv hT (comapAt N n h (cellForm N (h' * h⁻¹) n f)) := by
    rw [comapAt_sub, twInv_sub]
  rw [h2] at h1
  have h3 := (ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty
    (cuspFaceAction N h) (rhoAt N h n)).map_sub
    (twInv hT (comapAt N n h (faceSeriesK N (h' * h⁻¹) n f hn)))
    (twInv hT (comapAt N n h (cellForm N (h' * h⁻¹) n f)))
  exact sub_eq_zero.1 (h3.symm.trans h1)

end Transport

section Values

variable (N : ℕ) [NeZero N] (k : SL(3, ℤ)) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))

open Classical in
omit [NeZero N] in
theorem cellForm_none (hnone : ∀ c : Ck N k, ¬ IsCellK N k c) : cellForm N k n f = 0 := by
  have hc : ¬ ∃ c : Ck N k, IsCellK N k c := fun ⟨c, hc'⟩ => hnone c hc'
  unfold cellForm
  rw [dite_eq_right hc]

omit [NeZero N] in
theorem cellForm_pos (hN : 3 ≤ N) {c₀ : Ck N k} (hc : IsCellK N k c₀)
    (h22 : ((cellMat N k c₀ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = 1) :
    cellForm N k n f = cuspSeedInv (gammaNPlaneData N) (gammaNPlaneData_lam_mem N)
      (f := cuspSlash N n (leviBlock (cellMat N k c₀) (cellMat_mem_planeStab N k hc h22)) f) := by
  classical
  have hex : ∃ c : Ck N k, IsCellK N k c := ⟨c₀, hc⟩
  have hceq : hex.choose = c₀ := IsCellK_unique N k hN hex.choose_spec hc
  have h22' : ((cellMat N k hex.choose : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = 1 := by
    rw [hceq]; exact h22
  unfold cellForm
  rw [dite_eq_left hex, dite_eq_left h22']
  have key : ∀ (c₁ : Ck N k) (hc₁ : IsCellK N k c₁)
      (h₁ : ((cellMat N k c₁ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = 1), c₁ = c₀ →
      cuspSeedInv (gammaNPlaneData N) (gammaNPlaneData_lam_mem N)
        (f := cuspSlash N n (leviBlock (cellMat N k c₁) (cellMat_mem_planeStab N k hc₁ h₁)) f) =
      cuspSeedInv (gammaNPlaneData N) (gammaNPlaneData_lam_mem N)
        (f := cuspSlash N n (leviBlock (cellMat N k c₀) (cellMat_mem_planeStab N k hc h22)) f) := by
    intro c₁ hc₁ h₁ hcc
    subst hcc
    rfl
  exact key _ hex.choose_spec h22' hceq

omit [NeZero N] in
theorem cellForm_neg (hN : 3 ≤ N) {c₀ : Ck N k} (hc : IsCellK N k c₀)
    (h22 : ((cellMat N k c₀ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = -1) :
    cellForm N k n f = cuspSeedConjInv (gammaNPlaneData N) (gammaNPlaneData_lam_mem N)
      (f := fStarGen (leviGroup N) (leviGroup_J_stable N)
        (cuspSlash N n (leviBlock (cellMat N k c₀ * rPrime)
          (cellMat_mul_rPrime_mem N k hc h22)) f)) := by
  classical
  have hex : ∃ c : Ck N k, IsCellK N k c := ⟨c₀, hc⟩
  have hceq : hex.choose = c₀ := IsCellK_unique N k hN hex.choose_spec hc
  have h22' : ((cellMat N k hex.choose : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = -1 := by
    rw [hceq]; exact h22
  have hne : ¬ ((cellMat N k hex.choose : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = 1 := by
    rw [h22']; norm_num
  unfold cellForm
  rw [dite_eq_left hex, dite_eq_right hne]
  have key : ∀ (c₁ : Ck N k) (hc₁ : IsCellK N k c₁)
      (h₁ : ((cellMat N k c₁ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = -1), c₁ = c₀ →
      cuspSeedConjInv (gammaNPlaneData N) (gammaNPlaneData_lam_mem N)
        (f := fStarGen (leviGroup N) (leviGroup_J_stable N)
          (cuspSlash N n (leviBlock (cellMat N k c₁ * rPrime)
            (cellMat_mul_rPrime_mem N k hc₁ h₁)) f)) =
      cuspSeedConjInv (gammaNPlaneData N) (gammaNPlaneData_lam_mem N)
        (f := fStarGen (leviGroup N) (leviGroup_J_stable N)
          (cuspSlash N n (leviBlock (cellMat N k c₀ * rPrime)
            (cellMat_mul_rPrime_mem N k hc h22)) f)) := by
    intro c₁ hc₁ h₁ hcc
    subst hcc
    rfl
  exact key _ hex.choose_spec h22' hceq

end Values

section FaceValues

variable (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (hn : 4 ≤ n)
  (h h' : SL(3, ℤ))

/-- **Value: the cusps `h` and `h'` are not in the same orbit** (no `k γ` lies in `P(ℤ)`,
`k = h' h⁻¹`): the restriction of the series at `h'` to the face of `h` has zero class. -/
theorem faceClass_none (hN : 3 ≤ N) (hnone : ∀ c : Ck N (h' * h⁻¹), ¬ IsCellK N (h' * h⁻¹) c) :
    ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (cuspFaceAction N h)
        (rhoAt N h n)
        (cuspFaceForm N h (planeEisensteinAtComponents false (CuspData.ofSL h') (gammaN N)
          (leviGroup N) n f hn (leviInCusp_gammaN N h'))) = 0 := by
  rw [faceClass_eq_cell N n f hn h h' hN, cellForm_none N (h' * h⁻¹) n f hnone]
  have : twInv (intertwines_rhoAt N n h) (comapAt N n h
      (0 : ZigZag.invClosed isOpen_faceSet (gammaNPlaneData N).action
        ((gammaNPlaneData N).rhoR n))) = 0 := by
    apply Subtype.ext
    exact map_zero (ZigZag.twForm (rhoOfSL n h⁻¹) 2)
  rw [this, _root_.map_zero]

/-- **Value: the cell is a positive reflection-free element** (`k γ = [[A, w], [0, 1]]`): the class is
the transported seed of `f|A`. -/
theorem faceClass_pos (hN : 3 ≤ N) {c₀ : Ck N (h' * h⁻¹)} (hc : IsCellK N (h' * h⁻¹) c₀)
    (h22 : ((cellMat N (h' * h⁻¹) c₀ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = 1) :
    ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (cuspFaceAction N h)
        (rhoAt N h n)
        (cuspFaceForm N h (planeEisensteinAtComponents false (CuspData.ofSL h') (gammaN N)
          (leviGroup N) n f hn (leviInCusp_gammaN N h'))) =
      ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (cuspFaceAction N h)
        (rhoAt N h n) (cuspSeedAt N n (cuspSlash N n (leviBlock (cellMat N (h' * h⁻¹) c₀)
          (cellMat_mem_planeStab N (h' * h⁻¹) hc h22)) f) h) := by
  rw [faceClass_eq_cell N n f hn h h' hN, cellForm_pos N (h' * h⁻¹) n f hN hc h22]
  rfl

/-- **Value: the cell has Levi determinant `-1`** (`k γ = [[A', w], [0, -1]] = M diag(1,-1,-1)`): the
class is the transported conjugate seed of `(f|A)^*`. -/
theorem faceClass_neg (hN : 3 ≤ N) {c₀ : Ck N (h' * h⁻¹)} (hc : IsCellK N (h' * h⁻¹) c₀)
    (h22 : ((cellMat N (h' * h⁻¹) c₀ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = -1) :
    ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (cuspFaceAction N h)
        (rhoAt N h n)
        (cuspFaceForm N h (planeEisensteinAtComponents false (CuspData.ofSL h') (gammaN N)
          (leviGroup N) n f hn (leviInCusp_gammaN N h'))) =
      ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (cuspFaceAction N h)
        (rhoAt N h n) (cuspSeedConjAt N n
          (fStarGen (leviGroup N) (leviGroup_J_stable N)
            (cuspSlash N n (leviBlock (cellMat N (h' * h⁻¹) c₀ * rPrime)
              (cellMat_mul_rPrime_mem N (h' * h⁻¹) hc h22)) f)) h) := by
  rw [faceClass_eq_cell N n f hn h h' hN, cellForm_neg N (h' * h⁻¹) n f hN hc h22]
  rfl

end FaceValues

end TernaryPeriodPolynomials.Argument.EisensteinClass
