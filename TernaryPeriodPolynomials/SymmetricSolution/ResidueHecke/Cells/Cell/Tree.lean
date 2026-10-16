module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Cell.Sign
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.EpsGL
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.CellResolution

@[expose] public section


/-!
# Lemma B.1, boundary route: the `GL₃(ℤ)`-equivariant oriented cell complex (without augmentation)

`RGX n` is the representation of `GL₃(ℤ)` on the free `ℚ`-module on the cells of grade `n`, in which `g` sends the
oriented cell `T` (oriented by the label order of its lines) to `cellSign g T` times the oriented cell `g T`.
The boundary of the library (`dLin`, signs `insSignQ`) is `GL₃(ℤ)`-equivariant (`incQ_equiv`), `RG` is the resulting
chain complex, and on `Γ(6)` it is the cellular permutation complex of the library (`RG_resIso`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Pointwise Classical

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open CategoryTheory Finsupp TernaryPeriodPolynomials.FreeResolution
  TernaryPeriodPolynomials.TopVanishing GeneralEisenstein
  TernaryPeriodPolynomials.Argument.Lemma33.Retract

/-! ### The boundary coefficients -/

theorem mem_nbrs' {T : Finset Line} {w : Line} (h : w ∈ nbrs T) :
    Spans T ∧ w ∉ T ∧ IsSimplex (insert w T) := by
  by_cases hT : Spans T
  · exact ⟨hT, (mem_nbrs hT w).mp h⟩
  · rw [nbrs_of_not_spans hT] at h
    exact absurd h (Finset.notMem_empty w)

theorem insert_inj_of_notMem {T : Finset Line} {w w' : Line} (hw : w ∉ T) (_hw' : w' ∉ T)
    (h : insert w T = insert w' T) : w = w' := by
  have : w ∈ insert w' T := h ▸ Finset.mem_insert_self w T
  rcases Finset.mem_insert.mp this with h1 | h1
  · exact h1
  · exact absurd h1 hw

theorem coboundaryOfQ_apply (T S : Finset Line) :
    coboundaryOfQ T S =
      if h : ∃ w ∈ nbrs T, S = insert w T then insSignQ T h.choose else 0 := by
  unfold coboundaryOfQ
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases h : ∃ w ∈ nbrs T, S = insert w T
  · rw [dite_eq_left h]
    obtain ⟨w0, hw0, hS⟩ := h
    have hc := (⟨w0, hw0, hS⟩ : ∃ w ∈ nbrs T, S = insert w T).choose_spec
    have hch : (⟨w0, hw0, hS⟩ : ∃ w ∈ nbrs T, S = insert w T).choose = w0 :=
      insert_inj_of_notMem (mem_nbrs' hc.1).2.1 (mem_nbrs' hw0).2.1 (hc.2.symm.trans hS)
    rw [hch, Finset.sum_eq_single w0]
    · rw [ite_eq_left hS.symm]
    · intro w hw hne
      rw [ite_eq_right]
      intro hwS
      exact hne (insert_inj_of_notMem (mem_nbrs' hw).2.1 (mem_nbrs' hw0).2.1 (hwS.trans hS))
    · intro hnot
      exact absurd hw0 hnot
  · rw [dite_eq_right h]
    refine Finset.sum_eq_zero fun w hw => ?_
    rw [ite_eq_right]
    intro hwS
    exact h ⟨w, hw, hwS.symm⟩

theorem incQ_eq (C D : Cell) :
    incQ C D = if h : ∃ w ∈ nbrs C.val, D.val = insert w C.val then insSignQ C.val h.choose else 0 :=
  coboundaryOfQ_apply C.val D.val

/-- **Equivariance of the boundary coefficients under `GL₃(ℤ)`.** -/
theorem incQ_equiv (g : IntegralGL3) (C D : Cell) :
    cellSign g C.val * incQ (glCell g C) (glCell g D) = cellSign g D.val * incQ C D := by
  rw [incQ_eq, incQ_eq]
  by_cases h : ∃ w ∈ nbrs C.val, D.val = insert w C.val
  · obtain ⟨w, hw, hD⟩ := h
    have hw' : g • w ∈ nbrs (glCell g C).val := by
      rw [glCell_val, nbrs_smul_gl]
      exact Finset.smul_mem_smul_finset hw
    have hD' : (glCell g D).val = insert (g • w) (glCell g C).val := by
      rw [glCell_val, glCell_val, hD, Finset.smul_finset_insert]
    have h' : ∃ w ∈ nbrs (glCell g C).val, (glCell g D).val = insert w (glCell g C).val :=
      ⟨g • w, hw', hD'⟩
    rw [dite_eq_left h', dite_eq_left ⟨w, hw, hD⟩]
    have hc := (⟨w, hw, hD⟩ : ∃ w ∈ nbrs C.val, D.val = insert w C.val).choose_spec
    have hch : (⟨w, hw, hD⟩ : ∃ w ∈ nbrs C.val, D.val = insert w C.val).choose = w :=
      insert_inj_of_notMem (mem_nbrs' hc.1).2.1 (mem_nbrs' hw).2.1 (hc.2.symm.trans hD)
    have hc' := h'.choose_spec
    have hch' : h'.choose = g • w := by
      refine insert_inj_of_notMem (mem_nbrs' hc'.1).2.1 (mem_nbrs' hw').2.1 ?_
      rw [← hc'.2, hD']
    rw [hch, hch']
    have hwC : w ∉ C.val := (mem_nbrs' hw).2.1
    have hinj : Set.InjOn Line.label ((insert w C.val : Finset Line) : Set Line) := by
      rw [← hD]; exact D.isCell.2.label_injOn
    have hginj : Set.InjOn Line.label ((g • insert w C.val : Finset Line) : Set Line) := by
      rw [← hD]; exact (glCell g D).isCell.2.label_injOn
    have key := insSignQ_cellSign g C.val w hwC hinj hginj
    rw [hD, glCell_val]
    rw [mul_comm (cellSign g (insert w C.val)), ← key]
  · have h' : ¬ ∃ w ∈ nbrs (glCell g C).val, (glCell g D).val = insert w (glCell g C).val := by
      rintro ⟨w', hw', hD'⟩
      rw [glCell_val, nbrs_smul_gl] at hw'
      obtain ⟨w, hw, rfl⟩ := Finset.mem_smul_finset.mp hw'
      apply h
      refine ⟨w, hw, ?_⟩
      rw [glCell_val, glCell_val, ← Finset.smul_finset_insert] at hD'
      exact MulAction.injective g hD'
    rw [dite_eq_right h, dite_eq_right h']
    simp

/-! ### The twisted representation -/

/-- The action of `GL₃(ℤ)` on the cells of grade `n` (without signs). -/
def glGraded (n : ℕ) (g : IntegralGL3) (C : Graded n) : Graded n :=
  ⟨glCell g C.1, by rw [grade_glCell]; exact C.2⟩

@[simp] theorem glGraded_val (n : ℕ) (g : IntegralGL3) (C : Graded n) :
    (glGraded n g C).1 = glCell g C.1 := rfl

theorem glGraded_one (n : ℕ) (C : Graded n) : glGraded n 1 C = C := Subtype.ext (glCell_one C.1)

theorem glGraded_mul (n : ℕ) (g h : IntegralGL3) (C : Graded n) :
    glGraded n (g * h) C = glGraded n g (glGraded n h C) := Subtype.ext (glCell_mul g h C.1)

theorem glGraded_injective (n : ℕ) (g : IntegralGL3) : Function.Injective (glGraded n g) := by
  intro C D h
  exact Subtype.ext (glCell_injective g (congrArg Subtype.val h))

theorem glGraded_surj (n : ℕ) (g : IntegralGL3) (E : Graded n) : ∃ D, glGraded n g D = E :=
  ⟨glGraded n g⁻¹ E, by rw [← glGraded_mul, mul_inv_cancel, glGraded_one]⟩

theorem cellSign_cell_mul (g h : IntegralGL3) (C : Cell) :
    cellSign (g * h) C.val = cellSign g (h • C.val) * cellSign h C.val :=
  cellSign_mul g h C.isCell.2.label_injOn (glCell h C).isCell.2.label_injOn
    (glCell (g * h) C).isCell.2.label_injOn

/-- The twisted action of `g` on the free module on cells of grade `n`. -/
def twistLin (n : ℕ) (g : IntegralGL3) : (Graded n →₀ ℚ) →ₗ[ℚ] (Graded n →₀ ℚ) :=
  linearCombination ℚ (fun C : Graded n => cellSign g C.1.val • single (glGraded n g C) (1 : ℚ))

theorem twistLin_single (n : ℕ) (g : IntegralGL3) (C : Graded n) (a : ℚ) :
    twistLin n g (single C a) = single (glGraded n g C) (cellSign g C.1.val * a) := by
  rw [twistLin, linearCombination_single, Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul,
    smul_eq_mul, mul_one, mul_comm]

theorem twistLin_one (n : ℕ) : twistLin n 1 = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro C a
  rw [twistLin_single, glGraded_one, cellSign_one, one_mul]
  rfl

theorem twistLin_mul (n : ℕ) (g h : IntegralGL3) :
    twistLin n (g * h) = twistLin n g ∘ₗ twistLin n h := by
  apply Finsupp.lhom_ext
  intro C a
  rw [LinearMap.comp_apply, twistLin_single, twistLin_single, twistLin_single, glGraded_mul,
    cellSign_cell_mul]
  congr 1
  simp only [glGraded_val, glCell_val]
  ring

/-- The twisted representation of `GL₃(ℤ)` on the free module on the cells of grade `n`. -/
def twistRep (n : ℕ) : Representation ℚ IntegralGL3 (Graded n →₀ ℚ) where
  toFun g := twistLin n g
  map_one' := twistLin_one n
  map_mul' g h := by rw [Module.End.mul_eq_comp]; exact twistLin_mul n g h

/-- The representation of `GL₃(ℤ)` on the oriented cells of grade `n`. -/
def RGX (n : ℕ) : Rep.{0} ℚ IntegralGL3 := Rep.of (twistRep n)

theorem twistLin_apply (n : ℕ) (g : IntegralGL3) (z : Graded n →₀ ℚ) (D : Graded n) :
    twistLin n g z (glGraded n g D) = cellSign g D.1.val * z D := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, mul_add]
  | single C a =>
    rw [twistLin_single, Finsupp.single_apply, Finsupp.single_apply]
    by_cases h : C = D
    · subst h; simp
    · rw [ite_eq_right h, ite_eq_right (fun e => h (glGraded_injective n g e)), mul_zero]

theorem dLin_single (n : ℕ) (C : Graded (n + 1)) (a : ℚ) : dLin n (single C a) = a • dGr n C := by
  rw [dLin, linearCombination_single]

theorem dLin_twist (n : ℕ) (g : IntegralGL3) (z : Graded (n + 1) →₀ ℚ) :
    dLin n (twistLin (n + 1) g z) = twistLin n g (dLin n z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single C a =>
    ext E
    obtain ⟨D, rfl⟩ := glGraded_surj n g E
    rw [twistLin_single, dLin_single, dLin_single, twistLin_apply, Finsupp.smul_apply,
      Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, dGr_apply, dGr_apply]
    have := incQ_equiv g C.1 D.1
    simp only [glGraded_val]
    calc cellSign g C.1.val * a * incQ (glCell g C.1) (glCell g D.1)
        = a * (cellSign g C.1.val * incQ (glCell g C.1) (glCell g D.1)) := by ring
      _ = a * (cellSign g D.1.val * incQ C.1 D.1) := by rw [this]
      _ = _ := by ring

/-- The boundary of the oriented cell complex. -/
def dRG (n : ℕ) : RGX (n + 1) ⟶ RGX n :=
  Rep.ofHom ⟨dLin n, fun g => by
    apply LinearMap.ext
    intro v
    exact dLin_twist n g v⟩

theorem dRG_hom (n : ℕ) (z : Graded (n + 1) →₀ ℚ) : (dRG n).hom z = dLin n z := rfl

/-- The `GL₃(ℤ)`-equivariant oriented cell complex of the well-rounded retract. -/
def RG : ChainComplex (Rep.{0} ℚ IntegralGL3) ℕ :=
  ChainComplex.of RGX dRG (fun n => by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro z
    change dLin n (dLin (n + 1) z) = 0
    exact LinearMap.congr_fun (dLin_dLin n) z)

theorem RG_d (n : ℕ) : RG.d (n + 1) n = dRG n := ChainComplex.of_d _ _ _

/-! ### Restriction to `Γ(6)` -/

theorem cellSign_six (γ : TernaryPoly.IntegralGL3Congruence.principalSix) (T : Finset Line) :
    cellSign (γ : IntegralGL3) T = 1 :=
  cellSign_of_label _ (fun a => by
    have := label_level_smul (levelOfSix γ) a
    rwa [level_smul, levelLift_levelOfSix] at this) _

theorem glGraded_six (n : ℕ) (γ : TernaryPoly.IntegralGL3Congruence.principalSix) (C : Graded n) :
    glGraded n (γ : IntegralGL3) C = γ • C := Subtype.ext (glCell_six γ C.1)

/-- On `Γ(6)` the oriented cell representation is the permutation representation on cells. -/
def RG_resX (n : ℕ) : (Rep.resFunctor TernaryPoly.IntegralGL3Congruence.principalSix.subtype).obj (RGX n) ≅
    cellRep n :=
  Rep.mkIso (.mk (MonoidAlgebra.coeffLinearEquiv ℚ).symm fun γ => by
    refine Finsupp.lhom_ext fun C a => ?_
    change (MonoidAlgebra.coeffLinearEquiv ℚ).symm (twistLin n (γ : IntegralGL3) (single C a)) =
      (Representation.ofMulAction ℚ _ (Graded n) γ)
        ((MonoidAlgebra.coeffLinearEquiv ℚ).symm (single C a))
    have e1 : (MonoidAlgebra.coeffLinearEquiv ℚ).symm (single C a) = MonoidAlgebra.single C a := rfl
    rw [e1, Representation.ofMulAction_single, twistLin_single, cellSign_six, glGraded_six, one_mul]
    rfl)

/-- `RG` restricted to `Γ(6)`. -/
abbrev RGres : ChainComplex (Rep.{0} ℚ TernaryPoly.IntegralGL3Congruence.principalSix) ℕ :=
  ((Rep.resFunctor TernaryPoly.IntegralGL3Congruence.principalSix.subtype).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj RG

theorem RG_resX_comm (j : ℕ) :
    (RG_resX (j + 1)).hom ≫ cellD j =
      (Rep.resFunctor TernaryPoly.IntegralGL3Congruence.principalSix.subtype).map (dRG j) ≫
        (RG_resX j).hom := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  change (MonoidAlgebra.coeffLinearEquiv ℚ).symm (dLin j (MonoidAlgebra.coeffLinearEquiv ℚ
      ((MonoidAlgebra.coeffLinearEquiv ℚ).symm z))) = (MonoidAlgebra.coeffLinearEquiv ℚ).symm (dLin j z)
  exact congrArg (fun w => (MonoidAlgebra.coeffLinearEquiv ℚ).symm (dLin j w))
    (LinearEquiv.apply_symm_apply (MonoidAlgebra.coeffLinearEquiv ℚ) (z : Graded (j + 1) →₀ ℚ))

/-- **The restriction of the oriented cell complex to `Γ(6)` is the cellular permutation complex.** -/
def RG_resIso : RGres ≅ cellPermComplex :=
  HomologicalComplex.Hom.isoOfComponents RG_resX (fun i j hij => by
    obtain rfl : j + 1 = i := hij
    rw [cellPerm_d]
    change (RG_resX (j + 1)).hom ≫ cellD j =
      (Rep.resFunctor TernaryPoly.IntegralGL3Congruence.principalSix.subtype).map (RG.d (j + 1) j) ≫
        (RG_resX j).hom
    rw [RG_d]
    exact RG_resX_comm j)

/-! ### The augmentation -/

theorem augQ_single' (C : Graded 0) (a : ℚ) : augQ (single C a) = a * epsQ C.1 := by
  rw [← Finsupp.smul_single_one, map_smul, augQ_single, smul_eq_mul]

theorem augQ_twist (g : IntegralGL3) (z : Graded 0 →₀ ℚ) : augQ (twistLin 0 g z) = augQ z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single C a =>
    rw [twistLin_single, augQ_single', augQ_single']
    have h := epsQ_equiv g C.1 C.2
    rw [glGraded_val]
    calc cellSign g C.1.val * a * epsQ (glCell g C.1) = a * (epsQ (glCell g C.1) * cellSign g C.1.val) := by
          ring
      _ = a * epsQ C.1 := by rw [h]

/-- The augmentation of the oriented cell complex to the trivial representation. -/
def RG_aug0 : RGX 0 ⟶ Rep.trivial ℚ IntegralGL3 ℚ :=
  Rep.ofHom ⟨augQ, fun g => by
    apply LinearMap.ext
    intro z
    exact augQ_twist g z⟩

theorem RG_aug_comm : RG.d 1 0 ≫ RG_aug0 = 0 := by
  rw [RG_d]
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  exact LinearMap.congr_fun augQ_dLin z

/-- The augmentation of the oriented cell complex. -/
def RG_aug : RG ⟶ (ChainComplex.single₀ (Rep.{0} ℚ IntegralGL3)).obj (Rep.trivial ℚ IntegralGL3 ℚ) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨RG_aug0, RG_aug_comm⟩

end TernaryPeriodPolynomials.Argument.AppendixBResidue
