module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Cell.Tree
public import TernaryPeriodPolynomials.PeriodPolynomial.FareyDuality.PermProjective

@[expose] public section


/-!
# Lemma B.1, boundary route: the oriented cell complex restricted to a subgroup is a projective resolution

Cells have finite stabilizers in `GL₃(ℤ)` (`finite_stab_lines`), so each oriented-cell representation restricted to a
subgroup `H` is a retract of the permutation representation on the double cover `OSet n` of oriented cells and is
projective (`RGX_res_projective`).  The augmented complex restricted to `H` is acyclic (`RGH_quasiIso`, from the
rational exactness of the library's cell complex), hence `RG_projRes H` is a projective resolution of the trivial
representation of `H`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Pointwise Classical

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open CategoryTheory Finsupp TernaryPeriodPolynomials.FreeResolution
  TernaryPeriodPolynomials.TopVanishing GeneralEisenstein
  TernaryPeriodPolynomials.Argument.Lemma33.Retract

/-- The stabilizer of a set of lines that spans is finite. -/
theorem finite_stab_lines (T : Finset Line) (hT : Spans T) :
    Finite {g : IntegralGL3 // g • T = T} := by
  obtain ⟨a, ha, b, hb, c, hc, habc⟩ := hT
  set xa : Vec := Quotient.out a with hxa
  set xb : Vec := Quotient.out b with hxb
  set xc : Vec := Quotient.out c with hxc
  have hdet : det3v xa xb xc ≠ 0 := by
    have := (Line.indep_mk xa xb xc).mp
    rw [hxa, hxb, hxc]
    refine (Line.indep_mk _ _ _).mp ?_
    rw [Line.mk_out, Line.mk_out, Line.mk_out]
    exact habc
  have hmem : ∀ (g : {g : IntegralGL3 // g • T = T}) (t : Line), t ∈ T → g.1 • t ∈ T := by
    intro g t ht
    have := Finset.smul_mem_smul_finset (a := g.1) ht
    rwa [g.2] at this
  let sg : {g : IntegralGL3 // g • T = T} → Line → Bool := fun g t =>
    decide (mv g.1 (Quotient.out t) = Quotient.out (g.1 • t))
  let F : {g : IntegralGL3 // g • T = T} → (T × Bool) × (T × Bool) × (T × Bool) := fun g =>
    ((⟨g.1 • a, hmem g a ha⟩, sg g a), (⟨g.1 • b, hmem g b hb⟩, sg g b),
      (⟨g.1 • c, hmem g c hc⟩, sg g c))
  have hvec : ∀ (g : {g : IntegralGL3 // g • T = T}) (t : Line),
      mv g.1 (Quotient.out t) = if sg g t = true then Quotient.out (g.1 • t) else -Quotient.out (g.1 • t) := by
    intro g t
    have h1 : Line.mk (mv g.1 (Quotient.out t)) = g.1 • t := by
      rw [← smul_mk, Line.mk_out]
    have h2 := Line.mk_eq_mk.mp (h1.trans (Line.mk_out (g.1 • t)).symm)
    by_cases h : mv g.1 (Quotient.out t) = Quotient.out (g.1 • t)
    · have : sg g t = true := by simp [sg, h]
      rw [ite_eq_left this, h]
    · have : sg g t = false := by simp [sg, h]
      rw [this]
      simp only [Bool.false_eq_true, ite_false]
      rcases h2 with h2 | h2
      · exact absurd h2.symm h
      · rw [h2, neg_neg]
  have hinj : Function.Injective F := by
    intro g g' hgg
    simp only [F, Prod.mk.injEq, Subtype.mk.injEq] at hgg
    obtain ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩, ⟨hc1, hc2⟩⟩ := hgg
    have hfix : ∀ (t : Line), g.1 • t = g'.1 • t → sg g t = sg g' t →
        mv g.1 (Quotient.out t) = mv g'.1 (Quotient.out t) := by
      intro t h1 h2
      rw [hvec g t, hvec g' t, h2, h1]
    have e1 := hfix a ha1 ha2
    have e2 := hfix b hb1 hb2
    have e3 := hfix c hc1 hc2
    have key : g.1⁻¹ * g'.1 = 1 := by
      refine eq_one_of_fix3 _ hdet ?_ ?_ ?_
      · rw [mv_mul, ← e1, mv_inv_mv]
      · rw [mv_mul, ← e2, mv_inv_mv]
      · rw [mv_mul, ← e3, mv_inv_mv]
    apply Subtype.ext
    exact (inv_mul_eq_one.mp key)
  exact Finite.of_injective F hinj

theorem cellSign_sq (g : IntegralGL3) (T : Finset Line) : cellSign g T * cellSign g T = 1 := by
  unfold cellSign
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun z _ => ?_
  induction z using Sym2.ind with
  | h a b =>
    simp only [Sym2.lift_mk]
    exact pairSign_sq g a b

theorem cellSign_pm (g : IntegralGL3) (T : Finset Line) : cellSign g T = 1 ∨ cellSign g T = -1 :=
  mul_self_eq_one_iff.mp (cellSign_sq g T)

/-- The double cover of the oriented cells: a cell together with a sign. -/
abbrev OSet (n : ℕ) : Type := {p : Graded n × ℚ // p.2 = 1 ∨ p.2 = -1}

instance (n : ℕ) : MulAction IntegralGL3 (OSet n) where
  smul g p := ⟨(glGraded n g p.1.1, cellSign g p.1.1.1.val * p.1.2), by
    rcases cellSign_pm g p.1.1.1.val with h | h <;> rcases p.2 with h' | h' <;> simp [h, h']⟩
  one_smul p := Subtype.ext (Prod.ext (glGraded_one n p.1.1) (by
    change cellSign 1 p.1.1.1.val * p.1.2 = p.1.2
    rw [cellSign_one, one_mul]))
  mul_smul g h p := Subtype.ext (Prod.ext (glGraded_mul n g h p.1.1) (by
    change cellSign (g * h) p.1.1.1.val * p.1.2 =
      cellSign g (glGraded n h p.1.1).1.val * (cellSign h p.1.1.1.val * p.1.2)
    rw [cellSign_cell_mul]
    simp only [glGraded_val, glCell_val]
    ring))

theorem OSet_smul_val (n : ℕ) (g : IntegralGL3) (p : OSet n) :
    (g • p).1 = (glGraded n g p.1.1, cellSign g p.1.1.1.val * p.1.2) := rfl

/-- The cell with sign `+1`. -/
def oneO (n : ℕ) (C : Graded n) : OSet n := ⟨(C, 1), Or.inl rfl⟩

/-- The cell with sign `-1`. -/
def negO (n : ℕ) (C : Graded n) : OSet n := ⟨(C, -1), Or.inr rfl⟩

theorem smul_oneO_pos {n : ℕ} {g : IntegralGL3} {C : Graded n} (h : cellSign g C.1.val = 1) :
    g • oneO n C = oneO n (glGraded n g C) :=
  Subtype.ext (Prod.ext rfl (by
    change cellSign g C.1.val * 1 = 1
    rw [h, one_mul]))

theorem smul_oneO_neg {n : ℕ} {g : IntegralGL3} {C : Graded n} (h : cellSign g C.1.val = -1) :
    g • oneO n C = negO n (glGraded n g C) :=
  Subtype.ext (Prod.ext rfl (by
    change cellSign g C.1.val * 1 = -1
    rw [h, mul_one]))

theorem smul_negO_pos {n : ℕ} {g : IntegralGL3} {C : Graded n} (h : cellSign g C.1.val = 1) :
    g • negO n C = negO n (glGraded n g C) :=
  Subtype.ext (Prod.ext rfl (by
    change cellSign g C.1.val * (-1) = -1
    rw [h, one_mul]))

theorem smul_negO_neg {n : ℕ} {g : IntegralGL3} {C : Graded n} (h : cellSign g C.1.val = -1) :
    g • negO n C = oneO n (glGraded n g C) :=
  Subtype.ext (Prod.ext rfl (by
    change cellSign g C.1.val * (-1) = 1
    rw [h]; norm_num))

theorem finite_stab_OSet (n : ℕ) (H : Subgroup IntegralGL3) (p : OSet n) :
    Finite (MulAction.stabilizer H p) := by
  have hfin := finite_stab_lines p.1.1.1.val p.1.1.1.isCell.1
  refine Finite.of_injective (fun h : MulAction.stabilizer H p =>
    (⟨(h.1.1 : IntegralGL3), ?_⟩ : {g : IntegralGL3 // g • p.1.1.1.val = p.1.1.1.val})) ?_
  · have h1 : (h.1 • p).1.1 = p.1.1 := by rw [MulAction.mem_stabilizer_iff.mp h.2]
    have h2 := congrArg (fun C : Graded n => C.1.val) h1
    exact h2
  · intro h h' hh
    beta_reduce at hh
    have h1 : h.1.1 = h'.1.1 := Subtype.mk.inj hh
    exact Subtype.ext (Subtype.ext h1)

/-- The oriented cell representation restricted to a subgroup. -/
abbrev RGXres (H : Subgroup IntegralGL3) (n : ℕ) : Rep.{0} ℚ H := (Rep.resFunctor H.subtype).obj (RGX n)

/-- The map forgetting the double cover: `(C, q) ↦ q • C`. -/
def piO (H : Subgroup IntegralGL3) (n : ℕ) : Rep.ofMulAction ℚ H (OSet n) ⟶ RGXres H n :=
  permHomTo _ (linearCombination ℚ (fun p : OSet n => p.1.2 • single p.1.1 (1 : ℚ))) (fun h p => by
    change linearCombination ℚ (fun p : OSet n => p.1.2 • single p.1.1 (1 : ℚ)) (single (h.1 • p) 1) =
      twistLin n h.1 (linearCombination ℚ (fun p : OSet n => p.1.2 • single p.1.1 (1 : ℚ)) (single p 1))
    simp only [linearCombination_single, one_smul, OSet_smul_val]
    rw [map_smul, twistLin_single, Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, smul_eq_mul,
      mul_one, mul_one, mul_comm])

/-- The section: `C ↦ ½ ((C, +) - (C, -))`. -/
def secLin (n : ℕ) : (Graded n →₀ ℚ) →ₗ[ℚ] (OSet n →₀ ℚ) :=
  linearCombination ℚ (fun C : Graded n => (1 / 2 : ℚ) • (single (oneO n C) (1 : ℚ) - single (negO n C) 1))

theorem secLin_single (n : ℕ) (C : Graded n) (a : ℚ) :
    secLin n (single C a) = a • ((1 / 2 : ℚ) • (single (oneO n C) (1 : ℚ) - single (negO n C) 1)) := by
  rw [← Finsupp.smul_single_one, map_smul, secLin, linearCombination_single, one_smul]

theorem secLin_equiv (n : ℕ) (g : IntegralGL3) (z : Graded n →₀ ℚ) :
    secLin n (twistLin n g z) = Finsupp.lmapDomain ℚ ℚ (g • ·) (secLin n z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single C a =>
    rw [twistLin_single, secLin_single, secLin_single, map_smul, map_smul, map_sub,
      Finsupp.lmapDomain_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.mapDomain_single]
    rcases cellSign_pm g C.1.val with h | h
    · rw [smul_oneO_pos h, smul_negO_pos h, h]
      simp
    · rw [smul_oneO_neg h, smul_negO_neg h, h]
      module

/-- The section of `piO`. -/
def iotaO (H : Subgroup IntegralGL3) (n : ℕ) : RGXres H n ⟶ Rep.ofMulAction ℚ H (OSet n) :=
  Rep.ofHom ⟨(MonoidAlgebra.coeffLinearEquiv ℚ).symm.toLinearMap ∘ₗ secLin n, fun h => by
    apply LinearMap.ext
    intro z
    change (MonoidAlgebra.coeffLinearEquiv ℚ).symm (secLin n (twistLin n h.1 z)) =
      (Representation.ofMulAction ℚ H (OSet n) h) ((MonoidAlgebra.coeffLinearEquiv ℚ).symm (secLin n z))
    exact congrArg (MonoidAlgebra.coeffLinearEquiv ℚ).symm (secLin_equiv n h.1 (z : Graded n →₀ ℚ))⟩

theorem iotaO_piO (H : Subgroup IntegralGL3) (n : ℕ) : iotaO H n ≫ piO H n = 𝟙 _ := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  change linearCombination ℚ (fun p : OSet n => p.1.2 • single p.1.1 (1 : ℚ))
    ((MonoidAlgebra.coeffLinearEquiv ℚ) ((MonoidAlgebra.coeffLinearEquiv ℚ).symm (secLin n z))) = z
  rw [LinearEquiv.apply_symm_apply]
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single C a =>
    rw [secLin_single, map_smul, map_smul, map_sub, linearCombination_single, linearCombination_single]
    simp [oneO, negO, Finsupp.smul_single]
    rw [← Finsupp.single_add]
    congr 1
    ring

instance RGXres_projective (H : Subgroup IntegralGL3) (n : ℕ) : Projective (RGXres H n) := by
  have : Projective (Rep.ofMulAction ℚ H (OSet n)) :=
    TernaryPeriodPolynomials.Argument.BinaryDuality.ofMulAction_projective
      (fun p => finite_stab_OSet n H p)
  exact (⟨iotaO H n, piO H n, iotaO_piO H n⟩ : Retract (RGXres H n) (Rep.ofMulAction ℚ H (OSet n))).projective

/-! ### The resolution -/

/-- The oriented cell complex restricted to a subgroup. -/
abbrev RGH (H : Subgroup IntegralGL3) : ChainComplex (Rep.{0} ℚ H) ℕ :=
  ((Rep.resFunctor H.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj RG

theorem RGH_d (H : Subgroup IntegralGL3) (n : ℕ) :
    (RGH H).d (n + 1) n = (Rep.resFunctor H.subtype).map (dRG n) := by
  change (Rep.resFunctor H.subtype).map (RG.d (n + 1) n) = _
  rw [RG_d]
  rfl

/-- The augmentation of the restricted complex. -/
def RGH_aug0 (H : Subgroup IntegralGL3) : (RGH H).X 0 ⟶ Rep.trivial ℚ H ℚ :=
  Rep.ofHom ⟨augQ, fun h => by
    apply LinearMap.ext
    intro z
    exact augQ_twist h.1 z⟩

theorem RGH_aug_comm (H : Subgroup IntegralGL3) : (RGH H).d 1 0 ≫ RGH_aug0 H = 0 := by
  rw [RGH_d]
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  exact LinearMap.congr_fun augQ_dLin z

/-- The augmentation of the restricted oriented cell complex. -/
def RGH_aug (H : Subgroup IntegralGL3) :
    RGH H ⟶ (ChainComplex.single₀ (Rep.{0} ℚ H)).obj (Rep.trivial ℚ H ℚ) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨RGH_aug0 H, RGH_aug_comm H⟩

theorem RGH_exactAt (H : Subgroup IntegralGL3) (n : ℕ) : (RGH H).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  apply (ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep ℚ H) (ModuleCat ℚ))).mp
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hx1 : dLin n (x : Graded (n + 1) →₀ ℚ) = 0 := by
    have := hx
    change ((forget₂ (Rep ℚ H) (ModuleCat ℚ)).map ((RGH H).d (n + 1) n)).hom x = 0 at this
    rw [RGH_d] at this
    exact this
  obtain ⟨y, hy⟩ := exact_succ n _ hx1
  refine ⟨y, ?_⟩
  change ((forget₂ (Rep ℚ H) (ModuleCat ℚ)).map ((RGH H).d (n + 2) (n + 1))).hom y = x
  rw [RGH_d]
  exact hy

theorem RGH_aug0_exact (H : Subgroup IntegralGL3) :
    (ShortComplex.mk ((RGH H).d 1 0) (RGH_aug0 H) (RGH_aug_comm H)).Exact := by
  apply (ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep ℚ H) (ModuleCat ℚ))).mp
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hx1 : augQ (x : Graded 0 →₀ ℚ) = 0 := hx
  obtain ⟨y, hy⟩ := exact_zero _ hx1
  refine ⟨y, ?_⟩
  change ((forget₂ (Rep ℚ H) (ModuleCat ℚ)).map ((RGH H).d 1 0)).hom y = x
  rw [RGH_d]
  exact hy

instance RGH_aug0_epi (H : Subgroup IntegralGL3) : Epi (RGH_aug0 H) := by
  apply (forget₂ (Rep ℚ H) (ModuleCat ℚ)).epi_of_epi_map
  rw [ModuleCat.epi_iff_surjective]
  intro q
  obtain ⟨C, hC⟩ := augQ_surj
  let q' : ℚ := q
  refine ⟨single C (q' / epsQ C.1), ?_⟩
  change augQ (single C (q' / epsQ C.1)) = q'
  rw [augQ_single', div_mul_cancel₀ _ hC]

instance RGH_quasiIso (H : Subgroup IntegralGL3) : QuasiIso (RGH_aug H) := by
  constructor
  intro n
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · exact ⟨RGH_aug0_exact H, RGH_aug0_epi H⟩
    all_goals rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt']
    · exact RGH_exactAt H n
    · exact ChainComplex.exactAt_succ_single_obj _ _

/-- **The oriented cell complex is a projective resolution of the trivial representation of any subgroup of
`GL₃(ℤ)`.** -/
def RG_projRes (H : Subgroup IntegralGL3) : ProjectiveResolution (Rep.trivial ℚ H ℚ) where
  complex := RGH H
  projective n := RGXres_projective H n
  π := RGH_aug H
  quasiIso := RGH_quasiIso H

/-- The augmentation of `Γ(6)`-restricted oriented cells is the augmentation of the cellular permutation complex. -/
theorem RG_resX_aug :
    (RG_resX 0).hom ≫ cellAug0 = RGH_aug0 TernaryPoly.IntegralGL3Congruence.principalSix := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  change augQ ((MonoidAlgebra.coeffLinearEquiv ℚ) ((MonoidAlgebra.coeffLinearEquiv ℚ).symm z)) = augQ z
  exact congrArg augQ (LinearEquiv.apply_symm_apply (MonoidAlgebra.coeffLinearEquiv ℚ) (z : Graded 0 →₀ ℚ))

end TernaryPeriodPolynomials.Argument.AppendixBResidue
