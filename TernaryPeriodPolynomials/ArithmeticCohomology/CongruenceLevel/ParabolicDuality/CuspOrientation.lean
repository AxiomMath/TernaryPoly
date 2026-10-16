module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.GammaN
public import TernaryPeriodPolynomials.PeriodPolynomial.FareyDuality.Hecke.FareyNeighbours
public import TernaryPeriodPolynomials.PeriodPolynomial.FareyDuality.Hecke.StDelta

@[expose] public section


/-!
# Orientation of the dual Farey tree and the cusps at the ends of its edges

Formalized by Claude Sonnet 5.5.  Context: `ar:eq:facepair`.

Every oriented dual edge `q = h • p0` with `h ∈ SL₂(ℤ)` crosses the Farey edge `{h cusp₁, h cusp₂}` of the two adjacent triangles; this
orients the Farey edge (`tail q = h cusp₁`, `head q = h cusp₂`).  This is well defined because the stabilizer of `p0` in `SL₂(ℤ)` is `{±1}`
(`stab_sl_fix`), `SL₂(ℤ)` is transitive on oriented edges (`ote_transitive_sl`), reversal of the dual edge reverses the Farey edge
(`tail_swap`, `head_swap`), `SL₂(ℤ)` acts compatibly (`head_smul`, `tail_smul`), and the three edges leaving a triangle are oriented cyclically
(`sum_head_nbF`, `sum_tail_nbF`: the heads, and the tails, of the three edges leaving `t` are the three cusps of `t`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNParabolicPD

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open scoped Classical

section SL

/-- Determinant one. -/
def IsSL (g : IntegralGL) : Prop := g.val.det = 1

theorem det_cases (g : IntegralGL) : g.val.det = 1 ∨ g.val.det = -1 := by
  have h : IsUnit g.val.det := Matrix.isUnits_det_units g
  exact Int.isUnit_iff.mp h

theorem isSL_one : IsSL 1 := by simp [IsSL]

theorem IsSL.mul {g h : IntegralGL} (hg : IsSL g) (hh : IsSL h) : IsSL (g * h) := by
  unfold IsSL at *
  rw [Units.val_mul, Matrix.det_mul, hg, hh, mul_one]

theorem IsSL.inv {g : IntegralGL} (hg : IsSL g) : IsSL g⁻¹ := by
  unfold IsSL at *
  have e : g⁻¹.val * g.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have := congrArg Matrix.det e
  rw [Matrix.det_mul, hg, mul_one, Matrix.det_one] at this
  exact this

/-- The swap of the two coordinate axes, a determinant `-1` element fixing the standard oriented edge. -/
def s0 : IntegralGL := colGL e2 e1 (Or.inr (by simp [det2, e1, e2]))

theorem s0_det : s0.val.det = -1 := by
  simp [Matrix.det_fin_two, s0, colGL_val_zero, colGL_val_one, e1, e2]

theorem s0_mem : s0 ∈ MulAction.stabilizer IntegralGL p0 := by
  apply stab_p0_of_entries
  right; right; left
  simp [s0, colGL_val_zero, colGL_val_one, e1, e2]

theorem s0_cusp1 : s0 • cusp1 = cusp2 :=
  smul_cusp1_eq isGen_cusp2 (Or.inl (by funext i; fin_cases i <;> simp [s0, colGL_val_zero, e2]))

theorem s0_cusp2 : s0 • cusp2 = cusp1 :=
  smul_cusp2_eq isGen_cusp1 (Or.inl (by funext i; fin_cases i <;> simp [s0, colGL_val_one, e1]))

theorem sOne_det : sOne.val.det = -1 := by
  simp [Matrix.det_fin_two, sOne, colGL_val_zero, colGL_val_one, e1, e2]

theorem sOne_cusp1 : sOne • cusp1 = cusp1 :=
  smul_cusp1_eq isGen_cusp1 (Or.inl (by funext i; fin_cases i <;> simp [sOne, colGL_val_zero, e1]))

theorem sOne_cusp2 : sOne • cusp2 = cusp2 :=
  smul_cusp2_eq isGen_cusp2 (Or.inr (by funext i; fin_cases i <;> simp [sOne, colGL_val_one, e2]))

theorem rho_det : IsSL rho := by
  simp [IsSL, Matrix.det_fin_two, rho, colGL_val_zero, colGL_val_one, e2, e12]

theorem rho2_det : IsSL rho2 := by
  simp [IsSL, Matrix.det_fin_two, rho2, colGL_val_zero, colGL_val_one, e12, e1]

/-- `SL₂(ℤ)` is transitive on the oriented dual edges. -/
theorem ote_transitive_sl (q : OTE) : ∃ h : IntegralGL, IsSL h ∧ h • p0 = q := by
  obtain ⟨g, hg⟩ := ote_transitive q
  rcases det_cases g with h | h
  · exact ⟨g, h, hg⟩
  · refine ⟨g * s0, ?_, ?_⟩
    · unfold IsSL
      rw [Units.val_mul, Matrix.det_mul, h, s0_det]; norm_num
    · rw [mul_smul, MulAction.mem_stabilizer_iff.mp s0_mem, hg]

/-- `SL₂(ℤ)` is transitive on the triangles. -/
theorem tri_transitive_sl (t : Tri) : ∃ g : IntegralGL, IsSL g ∧ g • triPlus = t := by
  obtain ⟨g, hg⟩ := tri_transitive t
  have hs0 : s0 • triPlus = triPlus := congrArg (fun q : OTE => q.1.1) (MulAction.mem_stabilizer_iff.mp s0_mem)
  rcases det_cases g with h | h
  · exact ⟨g, h, hg⟩
  · refine ⟨g * s0, ?_, ?_⟩
    · unfold IsSL
      rw [Units.val_mul, Matrix.det_mul, h, s0_det]; norm_num
    · rw [mul_smul, hs0, hg]

/-- An element of `SL₂(ℤ)` fixing the standard oriented edge fixes both of its cusps. -/
theorem stab_sl_fix {s : IntegralGL} (hs : IsSL s) (h : s • p0 = p0) : s • cusp1 = cusp1 ∧ s • cusp2 = cusp2 := by
  have hmem : s ∈ MulAction.stabilizer IntegralGL p0 := h
  rcases stab_p0_entries s hmem with ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩
  · exact ⟨smul_cusp1_eq isGen_cusp1 (Or.inl (by funext i; fin_cases i <;> simp [a, c, e1])),
      smul_cusp2_eq isGen_cusp2 (Or.inl (by funext i; fin_cases i <;> simp [b, d, e2]))⟩
  · exact ⟨smul_cusp1_eq isGen_cusp1 (Or.inr (by funext i; fin_cases i <;> simp [a, c, e1])),
      smul_cusp2_eq isGen_cusp2 (Or.inr (by funext i; fin_cases i <;> simp [b, d, e2]))⟩
  · exfalso
    unfold IsSL at hs
    rw [Matrix.det_fin_two, a, b, c, d] at hs
    norm_num at hs
  · exfalso
    unfold IsSL at hs
    rw [Matrix.det_fin_two, a, b, c, d] at hs
    norm_num at hs

end SL

section HeadTail

/-- The tail cusp of an oriented dual edge `q = h • p0` (`h ∈ SL₂(ℤ)`): `h cusp₁`. -/
def tail (q : OTE) : RationalLine2 := (Classical.choose (ote_transitive_sl q)) • cusp1

/-- The head cusp of an oriented dual edge `q = h • p0` (`h ∈ SL₂(ℤ)`): `h cusp₂`. -/
def head (q : OTE) : RationalLine2 := (Classical.choose (ote_transitive_sl q)) • cusp2

theorem choose_rep_aux {h : IntegralGL} (hh : IsSL h) {q : OTE} (hq : h • p0 = q) :
    (Classical.choose (ote_transitive_sl q)) • cusp1 = h • cusp1 ∧
      (Classical.choose (ote_transitive_sl q)) • cusp2 = h • cusp2 := by
  obtain ⟨h0sl, h0⟩ := Classical.choose_spec (ote_transitive_sl q)
  set h₀ := Classical.choose (ote_transitive_sl q)
  have hs : IsSL (h⁻¹ * h₀) := hh.inv.mul h0sl
  have hsp : (h⁻¹ * h₀) • p0 = p0 := by
    rw [mul_smul, h0, ← hq, inv_smul_smul]
  obtain ⟨c1, c2⟩ := stab_sl_fix hs hsp
  have e : h₀ = h * (h⁻¹ * h₀) := by group
  constructor
  · rw [e, mul_smul, c1]
  · rw [e, mul_smul, c2]

theorem tail_eq {h : IntegralGL} (hh : IsSL h) {q : OTE} (hq : h • p0 = q) : tail q = h • cusp1 :=
  (choose_rep_aux hh hq).1

theorem head_eq {h : IntegralGL} (hh : IsSL h) {q : OTE} (hq : h • p0 = q) : head q = h • cusp2 :=
  (choose_rep_aux hh hq).2

theorem tail_smul {g : IntegralGL} (hg : IsSL g) (q : OTE) : tail (g • q) = g • tail q := by
  obtain ⟨h, hh, hq⟩ := ote_transitive_sl q
  rw [tail_eq hh hq, tail_eq (hg.mul hh) (show (g * h) • p0 = g • q by rw [mul_smul, hq]), mul_smul]

theorem head_smul {g : IntegralGL} (hg : IsSL g) (q : OTE) : head (g • q) = g • head q := by
  obtain ⟨h, hh, hq⟩ := ote_transitive_sl q
  rw [head_eq hh hq, head_eq (hg.mul hh) (show (g * h) • p0 = g • q by rw [mul_smul, hq]), mul_smul]

/-- The `SL₂(ℤ)` element exchanging the two triangles over the standard edge and the two cusps of the edge. -/
def wSwap : IntegralGL := sOne * s0

theorem wSwap_det : IsSL wSwap := by
  unfold IsSL wSwap
  rw [Units.val_mul, Matrix.det_mul, sOne_det, s0_det]; norm_num

theorem wSwap_p0 : wSwap • p0 = p0.swap := by
  unfold wSwap
  rw [mul_smul, MulAction.mem_stabilizer_iff.mp s0_mem, sOne_smul_p0]

theorem wSwap_cusp1 : wSwap • cusp1 = cusp2 := by
  unfold wSwap; rw [mul_smul, s0_cusp1, sOne_cusp2]

theorem wSwap_cusp2 : wSwap • cusp2 = cusp1 := by
  unfold wSwap; rw [mul_smul, s0_cusp2, sOne_cusp1]

theorem swap_eq (h : IntegralGL) (q : OTE) (hq : h • p0 = q) : (h * wSwap) • p0 = q.swap := by
  rw [mul_smul, wSwap_p0, ← hq, OTE.swap_smul]

theorem tail_swap (q : OTE) : tail q.swap = head q := by
  obtain ⟨h, hh, hq⟩ := ote_transitive_sl q
  rw [tail_eq (hh.mul wSwap_det) (swap_eq h q hq), head_eq hh hq, mul_smul, wSwap_cusp1]

theorem head_swap (q : OTE) : head q.swap = tail q := by
  obtain ⟨h, hh, hq⟩ := ote_transitive_sl q
  rw [head_eq (hh.mul wSwap_det) (swap_eq h q hq), tail_eq hh hq, mul_smul, wSwap_cusp2]

theorem tail_p0 : tail p0 = cusp1 := by
  rw [tail_eq isSL_one (one_smul _ _), one_smul]

theorem head_p0 : head p0 = cusp2 := by
  rw [head_eq isSL_one (one_smul _ _), one_smul]

/-- The Farey edge (as a function on oriented dual edges) of a function on cusps. -/
def dfun {E : Type} [AddCommGroup E] (Φ : RationalLine2 → E) (q : OTE) : E := Φ (head q) - Φ (tail q)

theorem dfun_swap {E : Type} [AddCommGroup E] (Φ : RationalLine2 → E) (q : OTE) : dfun Φ q.swap = -dfun Φ q := by
  unfold dfun
  rw [head_swap, tail_swap]
  abel

end HeadTail

section Triangle

/-- The heads of the three edges leaving the standard triangle. -/
theorem sum_head_triPlus {M : Type*} [AddCommMonoid M] (Φ : RationalLine2 → M) :
    ∑ q ∈ nbF triPlus, Φ (head q) = Φ cusp1 + Φ cusp2 + Φ cusp3 := by
  rw [sum_nbF_triPlus, head_eq isSL_one (q := p0) (one_smul _ _),
    head_eq rho_det (q := rho • p0) rfl, head_eq rho2_det (q := rho2 • p0) rfl, one_smul, rho_c2, rho2_c2]
  abel

theorem sum_tail_triPlus {M : Type*} [AddCommMonoid M] (Φ : RationalLine2 → M) :
    ∑ q ∈ nbF triPlus, Φ (tail q) = Φ cusp1 + Φ cusp2 + Φ cusp3 := by
  rw [sum_nbF_triPlus, tail_eq isSL_one (q := p0) (one_smul _ _),
    tail_eq rho_det (q := rho • p0) rfl, tail_eq rho2_det (q := rho2 • p0) rfl, one_smul, rho_c1, rho2_c1]

theorem sum_triPlus_cusps {M : Type*} [AddCommMonoid M] (Φ : RationalLine2 → M) :
    ∑ x ∈ triPlus.1, Φ x = Φ cusp1 + Φ cusp2 + Φ cusp3 := by
  have h12 : cusp1 ≠ cusp2 := cusp1_ne_cusp2
  have h13 : cusp1 ≠ cusp3 := cusp3_ne_cusp1.symm
  have h23 : cusp2 ≠ cusp3 := cusp3_ne_cusp2.symm
  show ∑ x ∈ ({cusp1, cusp2, cusp3} : Finset RationalLine2), Φ x = _
  rw [Finset.sum_insert (by simp [h12, h13]), Finset.sum_insert (by simp [h23]), Finset.sum_singleton, add_assoc]

/-- **The heads of the three oriented dual edges leaving a triangle are its three cusps.** -/
theorem sum_head_nbF {M : Type*} [AddCommMonoid M] (Φ : RationalLine2 → M) (t : Tri) :
    ∑ q ∈ nbF t, Φ (head q) = ∑ x ∈ t.1, Φ x := by
  obtain ⟨g, hg, rfl⟩ := tri_transitive_sl t
  rw [nbF_smul, Finset.sum_image (fun a _ b _ h => MulAction.injective g h), tri_smul_val,
    Finset.sum_image (fun a _ b _ h => MulAction.injective g h), sum_triPlus_cusps]
  have : ∀ q : OTE, Φ (head (g • q)) = (fun x => Φ (g • x)) (head q) := fun q => by rw [head_smul hg]
  simp only [this]
  rw [sum_head_triPlus (fun x => Φ (g • x))]

/-- **The tails of the three oriented dual edges leaving a triangle are its three cusps.** -/
theorem sum_tail_nbF {M : Type*} [AddCommMonoid M] (Φ : RationalLine2 → M) (t : Tri) :
    ∑ q ∈ nbF t, Φ (tail q) = ∑ x ∈ t.1, Φ x := by
  obtain ⟨g, hg, rfl⟩ := tri_transitive_sl t
  rw [nbF_smul, Finset.sum_image (fun a _ b _ h => MulAction.injective g h), tri_smul_val,
    Finset.sum_image (fun a _ b _ h => MulAction.injective g h), sum_triPlus_cusps]
  have : ∀ q : OTE, Φ (tail (g • q)) = (fun x => Φ (g • x)) (tail q) := fun q => by rw [tail_smul hg]
  simp only [this]
  rw [sum_tail_triPlus (fun x => Φ (g • x))]

/-- The Farey differential of a function on cusps sums to zero around every triangle. -/
theorem sum_dfun_nbF {E : Type} [AddCommGroup E] (Φ : RationalLine2 → E) (t : Tri) :
    ∑ q ∈ nbF t, dfun Φ q = 0 := by
  unfold dfun
  rw [Finset.sum_sub_distrib, sum_head_nbF, sum_tail_nbF, sub_self]

end Triangle

end TernaryPeriodPolynomials.Argument.GammaNParabolicPD
