module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.PieceK
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Printed.Integrand

@[expose] public section


/-!
# Every cusp: the congruence cells, the support, and the integrand on a cell

Formalized by Claude Sonnet 5.5.

`pieceFinK k o = (r_o₁ + NẐ) × (r_o₂ + NẐ)` for a free orbit `o` of `qActK N k`; `FzK` is the integrand at `(σ, w) ↦ φ(w₀⁻¹u(σ,w) · (1, ι(k⁻¹)))`
in the face coordinates; `FzK_on_piece` identifies it on the cell with `PhiQ0 N k`, the summand of `lineA1K N k`.
-/

open Matrix GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument.IntegralReduction
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.SeedC3S4c
  TernaryPeriodPolynomials.Argument.EisensteinDual TernaryPeriodPolynomials.Argument.GammaNFaces

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

variable (N : ℕ) [NeZero N] (k : SL(3, ℤ))

/-- The free orbits of the line radical lattice at the cusp `k`. -/
abbrev FreeOrbK : Type := {o : Quotient (qActK N k).orbSetoid // (qActK N k).r0Q o ≠ 0}

/-- The coset of the representative of a free orbit. -/
def orbCosetK (o : FreeOrbK N k) : Ck N k := Quotient.out o.1

/-- The rational point of a free orbit. -/
def orbPtK (o : FreeOrbK N k) : ℚ × ℚ := ptCk N k (orbCosetK N k o)

/-- The congruence cell of a free orbit. -/
def pieceFinK (o : FreeOrbK N k) : Set (FiniteAdeles × FiniteAdeles) :=
  latCoset N (algebraMap ℚ FiniteAdeles (orbPtK N k o).1) ×ˢ latCoset N (algebraMap ℚ FiniteAdeles (orbPtK N k o).2)

theorem pieceFinK_measurable (o : FreeOrbK N k) : MeasurableSet (pieceFinK N k o) :=
  (latCoset_measurable N _).prod (latCoset_measurable N _)

theorem volume_pieceFinK (o : FreeOrbK N k) :
    (finiteMeasure.prod finiteMeasure) (pieceFinK N k o) = (N : ENNReal)⁻¹ * (N : ENNReal)⁻¹ := by
  unfold pieceFinK
  rw [Measure.prod_prod, finiteMeasure_latCoset, finiteMeasure_latCoset, finiteMeasure_latSet]

theorem real_pieceFinK (o : FreeOrbK N k) :
    (finiteMeasure.prod finiteMeasure).real (pieceFinK N k o) = ((N : ℝ) ^ 2)⁻¹ := by
  unfold Measure.real
  rw [volume_pieceFinK, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  ring

theorem orbCosetK_r0 (o : FreeOrbK N k) : cuspRow (gammaN N) (CuspData.ofSL k).r (orbCosetK N k o) 0 ≠ 0 := by
  have := o.2
  rw [QAct.r0Q_out] at this
  exact this

omit [NeZero N] in
theorem orbit_of_pt_shiftK (hN : 3 ≤ N) {c c' : Ck N k}
    (h0 : cuspRow (gammaN N) (CuspData.ofSL k).r c 0 ≠ 0) (h0' : cuspRow (gammaN N) (CuspData.ofSL k).r c' 0 ≠ 0)
    (m : Fin 2 → ℤ) (h : ptCk N k c' = ((ptCk N k c).1 + N * m 0, (ptCk N k c).2 + N * m 1)) :
    ∃ ℓ : Fin 2 → ℤ, cmulR N k (latQ N ℓ) c = c' := by
  have := orbit_of_pt_shift_elt_K N k hN (a := Quotient.out c) (a' := Quotient.out c')
    ((cuspRow_ne_zero_iffK N k c).1 h0) ((cuspRow_ne_zero_iffK N k c').1 h0') m
    (by rw [← ptCk_out, ← ptCk_out]; exact h)
  rw [Quotient.out_eq, Quotient.out_eq] at this
  exact ⟨_, this⟩

/-- **Distinct free orbits give disjoint cells.** -/
theorem pieceFinK_disjoint (hN : 3 ≤ N) : Pairwise (Function.onFun Disjoint (pieceFinK N k)) := by
  intro o o' hne
  rw [Function.onFun, Set.disjoint_left]
  rintro σ ⟨h1, h2⟩ ⟨h1', h2'⟩
  apply hne
  have e1 := latSet_sub N ((mem_latCoset N).1 h1') ((mem_latCoset N).1 h1)
  have e2 := latSet_sub N ((mem_latCoset N).1 h2') ((mem_latCoset N).1 h2)
  have d1 : σ.1 - algebraMap ℚ FiniteAdeles (orbPtK N k o').1 - (σ.1 - algebraMap ℚ FiniteAdeles (orbPtK N k o).1) =
      algebraMap ℚ FiniteAdeles ((orbPtK N k o).1 - (orbPtK N k o').1) := by rw [map_sub]; ring
  have d2 : σ.2 - algebraMap ℚ FiniteAdeles (orbPtK N k o').2 - (σ.2 - algebraMap ℚ FiniteAdeles (orbPtK N k o).2) =
      algebraMap ℚ FiniteAdeles ((orbPtK N k o).2 - (orbPtK N k o').2) := by rw [map_sub]; ring
  rw [d1] at e1
  rw [d2] at e2
  obtain ⟨z1, hz1⟩ := rat_in_lat N e1
  obtain ⟨z2, hz2⟩ := rat_in_lat N e2
  obtain ⟨ℓ, hℓ⟩ := orbit_of_pt_shiftK N k hN (c := orbCosetK N k o) (c' := orbCosetK N k o') (orbCosetK_r0 N k o)
    (orbCosetK_r0 N k o') ![-z1, -z2] (by
      unfold orbPtK at hz1 hz2
      ext
      · simp only [Matrix.cons_val_zero]; push_cast; linarith
      · simp only [Matrix.cons_val_one]; push_cast; linarith)
  have hrel : (qActK N k).OrbRel (orbCosetK N k o) (orbCosetK N k o') := ⟨ℓ, hℓ⟩
  have h1 : Quotient.mk (qActK N k).orbSetoid (orbCosetK N k o) = o.1 := Quotient.out_eq o.1
  have h2 : Quotient.mk (qActK N k).orbSetoid (orbCosetK N k o') = o'.1 := Quotient.out_eq o'.1
  exact Subtype.ext (by rw [← h1, ← h2]; exact Quotient.sound hrel)

/-- **The support of the finite part lies in the congruence cells.** -/
theorem exists_orbit_of_decompK (σ : FiniteAdeles × FiniteAdeles)
    (h : ∃ π κ, IsDecomp N (gFin σ * kInvFin k) π κ) : ∃ o : FreeOrbK N k, σ ∈ pieceFinK N k o := by
  obtain ⟨r0, hr0⟩ := exists_rat_sub_mem_lat N σ.1
  obtain ⟨r1, hr1⟩ := exists_rat_sub_mem_lat N σ.2
  set a : FiniteAdeles × FiniteAdeles := (algebraMap ℚ FiniteAdeles r0, algebraMap ℚ FiniteAdeles r1) with ha
  obtain ⟨κ, hκ, he⟩ := gFin_add_lat N a (σ - a) hr0 hr1
  rw [add_sub_cancel] at he
  obtain ⟨κ', hκ', e'⟩ := kInvFin_conj N k hκ
  have h' : ∃ π κ, IsDecomp N (gFin a * kInvFin k) π κ := by
    rw [he, mul_assoc, e', ← mul_assoc] at h
    exact (exists_decomp_mul_ker N (g := gFin a * kInvFin k) (κ' := κ') hκ').1 h
  obtain ⟨A, hAk, hA0, hAr⟩ := exists_elt_of_decompK N k (r0, r1) h'
  set b : SL(3, ℤ) := k⁻¹ * A with hb
  have hbN : b ∈ gammaN N := by
    have := (gammaN_normal N).conj_mem (A * k⁻¹) hAk k⁻¹
    simpa [hb, mul_assoc] using this
  have hkb : k * b = A := by rw [hb]; group
  set c : Ck N k := Quotient.mk _ (⟨b, hbN⟩ : ↥(gammaN N)) with hc
  have hrow : ∀ j, cuspRow (gammaN N) (CuspData.ofSL k).r c j = ((k * b : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 j := by
    intro j
    rw [hc, cuspRow_mk_eq N k ⟨b, hbN⟩ j]
  have hptc : ptCk N k c = (r0, r1) := by
    rw [← hAr, ← hkb]
    unfold ptCk slRowPt rowPt
    rw [hrow, hrow, hrow]
  have hfree : (qActK N k).r0Q (Quotient.mk (qActK N k).orbSetoid c) ≠ 0 := by
    show cuspRow (gammaN N) (CuspData.ofSL k).r c 0 ≠ 0
    rw [hrow, hkb]; exact hA0
  set o : FreeOrbK N k := ⟨Quotient.mk _ c, hfree⟩ with ho
  refine ⟨o, ?_⟩
  have hrel : (qActK N k).OrbRel (orbCosetK N k o) c := by
    have : Quotient.mk (qActK N k).orbSetoid (orbCosetK N k o) = Quotient.mk (qActK N k).orbSetoid c :=
      Quotient.out_eq o.1
    exact Quotient.exact this
  obtain ⟨ℓ, hℓ⟩ := hrel
  have hpt := ptCk_latQ N k ℓ (orbCosetK N k o) (orbCosetK_r0 N k o)
  change cmulR N k (latQ N ℓ) (orbCosetK N k o) = c at hℓ
  rw [hℓ, hptc] at hpt
  have h1 : r0 = (orbPtK N k o).1 - N * ℓ 1 := by
    have := congrArg Prod.fst hpt
    simpa [orbPtK] using this
  have h2 : r1 = (orbPtK N k o).2 - N * ℓ 0 := by
    have := congrArg Prod.snd hpt
    simpa [orbPtK] using this
  refine ⟨(mem_latCoset N).2 ?_, (mem_latCoset N).2 ?_⟩
  · have := latSet_add N hr0 (algebraMap_Nint_mem_lat N (-(ℓ 1)))
    convert this using 1
    rw [h1]
    push_cast
    ring
  · have := latSet_add N hr1 (algebraMap_Nint_mem_lat N (-(ℓ 0)))
    convert this using 1
    rw [h2]
    push_cast
    ring

/-- The integrand at the cusp `k`: the face-coordinate pullback of `φ(w₀⁻¹ u(σ, w) · (1, ι(k⁻¹)))`. -/
def FzK (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (x : Face) (p q : Fin 4) (m : Fin 3 →₀ ℕ)
    (z : (FiniteAdeles × FiniteAdeles) × (Fin 2 → ℝ)) : ℂ :=
  (fPull jFace (fun y a b => adelicSection N n (hfun f) (gReal z.2) (gFin z.1 * kInvFin k) y a b) x p q).coeff m

theorem FzK_eq_zero_of_not (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (x : Face) (p q : Fin 4)
    (m : Fin 3 →₀ ℕ) (σ : FiniteAdeles × FiniteAdeles) (w : Fin 2 → ℝ) (hd : ¬∃ π κ, IsDecomp N (gFin σ * kInvFin k) π κ) :
    FzK N k n f x p q m (σ, w) = 0 := by
  unfold FzK fPull
  simp [adelicSection_of_not N n _ (gReal w) hd]

/-- **On the cell of the free orbit `o` the integrand is the summand `PhiQ0` of `lineA1K N k`.** -/
theorem FzK_on_piece (hN : 3 ≤ N) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) {x : Face} (hx : x ∈ faceSet)
    (p q : Fin 4) (m : Fin 3 →₀ ℕ) (o : FreeOrbK N k) {σ : FiniteAdeles × FiniteAdeles} (hσ : σ ∈ pieceFinK N k o)
    (w : Fin 2 → ℝ) :
    FzK N k n f x p q m (σ, w) = PhiQ0 N k n f x p q m (orbCosetK N k o) (shiftV (orbPtK N k o) w) := by
  set c := orbCosetK N k o with hc
  set A : SL(3, ℤ) := k * (Quotient.out c).1 with hA
  have hr : orbPtK N k o = slRowPt A := ptCk_out N k c
  have hAN : A * k⁻¹ ∈ gammaN N := by
    have := conj_mem_gammaN N k _ (Quotient.out c).2
    simpa [hA] using this
  have hA0 : (A : Matrix (Fin 3) (Fin 3) ℤ) 2 0 ≠ 0 := (cuspRow_ne_zero_iffK N k c).1 (orbCosetK_r0 N k o)
  set a : FiniteAdeles × FiniteAdeles :=
    (algebraMap ℚ FiniteAdeles (slRowPt A).1, algebraMap ℚ FiniteAdeles (slRowPt A).2) with ha
  have h1 : σ.1 - a.1 ∈ latSet N := by
    have := (mem_latCoset N).1 hσ.1
    rwa [hr] at this
  have h2 : σ.2 - a.2 ∈ latSet N := by
    have := (mem_latCoset N).1 hσ.2
    rwa [hr] at this
  have hy : jFace x ∈ Omega := jPlane_mem (ptOf_mem hx)
  have hσe : σ = a + (σ - a) := by abel
  unfold FzK PhiQ0
  refine congrArg (fun F => F.coeff m) (fPull_congr_at jFace _ _ x (fun a' b' => ?_) p q)
  have e1 := adelicSection_gFin_add_latK N hN n f k w a (σ - a) h1 h2 hy a' b'
  rw [← hσe] at e1
  simp only
  rw [e1, adelicSection_gFin_rational_K N hN n f k A hAN hA0 w hy a' b', hr, hA, realMat_mul]

end TernaryPeriodPolynomials.Argument.FormClassK
