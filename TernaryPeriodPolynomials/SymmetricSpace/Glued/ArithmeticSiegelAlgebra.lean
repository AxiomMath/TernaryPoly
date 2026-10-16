module

public import TernaryPeriodPolynomials.SymmetricSpace.Glued.ArithmeticBorelBounds
public import TernaryPeriodPolynomials.SymmetricSpace.Corner.Separation

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceGluedArithmetic
open Matrix SymmetricSpacePositive SymmetricSpaceFlagCoordinates SymmetricSpaceBorelCorner
open SymmetricSpaceRationalGluing SymmetricSpaceRationalAction SymmetricSpaceCornerDegeneration
open SymmetricSpaceCornerSeparation

/-- The actual polynomial corner form has determinant t1^4 t2^2. -/
theorem rawA_det (p : Corner) : (rawA p).det=p.2.1.val^4*p.2.2.val^2 := by
  unfold rawA weightedFlag
  rw [det_mul,det_mul,det_transpose,det_diagonal]
  simp [upper,det_fin_three,Fin.prod_univ_succ]
  ring

@[simp] theorem rawA_two_two (p : Corner) : rawA p 2 2=p.2.1.val^2*p.2.2.val^2 := by
  rw [rawA,weightedFlag_explicit]
  rfl

/-- The bottom row is an explicit sum of three nonnegative weighted squares. -/
theorem conjugate_rawA_two_two (r : RealGL) (p : Corner) :
    conjugate r (rawA p) 2 2=r.val 2 0^2+
      p.2.1.val^2*(r.val 2 0*p.1 0+r.val 2 1)^2+
      p.2.1.val^2*p.2.2.val^2*(r.val 2 0*p.1 2+r.val 2 1*p.1 1+r.val 2 2)^2 := by
  simp [conjugate,rawA,weightedFlag_explicit,Matrix.mul_apply,Fin.sum_univ_succ]
  ring

/-- Equality of actual primary detectors gives a positive scalar relating the unnormalized forms. -/
theorem rawA_congruence_scale (r : RealGL) (p q : Corner)
    (h : A q=normalize (conjugate r (A p))) :
    ∃ c : ℝ,0<c ∧ conjugate r (rawA p)=c • rawA q := by
  let C := conjugate r (rawA p)
  let T := rawA q
  have hc : 0<C.trace := conjugate_trace_pos r (rawA_psd p) (rawA_ne_zero p)
  have ht : 0<T.trace := rawA_trace_pos q
  have hn : normalize C=normalize T := by
    change normalize T=normalize (conjugate r ((rawA p).trace⁻¹ • rawA p)) at h
    rw [conjugate_smul,normalize_smul _ (inv_ne_zero (ne_of_gt (rawA_trace_pos p)))] at h
    exact h.symm
  refine ⟨C.trace/T.trace,div_pos hc ht,?_⟩
  have he := congrArg (fun M : Mat => C.trace • M) hn
  simpa only [SymmetricSpacePositive.normalize,smul_smul,mul_inv_cancel₀ (ne_of_gt hc),one_smul,div_eq_mul_inv] using he

/-- The exact rank-three bottom-left Siegel inequality holds even at zero roots. -/
theorem lowerLeft_sixth_bound (r : RealGL) (p q : Corner)
    (h : A q=normalize (conjugate r (A p))) :
    r.val 2 0^6≤r.val.det^2*p.2.1.val^4*p.2.2.val^2*q.2.1.val^2*q.2.2.val^4 := by
  obtain ⟨c,hc,he⟩ := rawA_congruence_scale r p q h
  have hdet := congrArg Matrix.det he
  simp only [conjugate,det_mul,Matrix.star_eq_conjTranspose,det_conjTranspose,star_trivial,det_smul,Fintype.card_fin,rawA_det] at hdet
  have hd : c^3*q.2.1.val^4*q.2.2.val^2=r.val.det^2*p.2.1.val^4*p.2.2.val^2 := by
    nlinarith only [hdet]
  have hb := congrArg (fun M : Mat => M 2 2) he
  change conjugate r (rawA p) 2 2=c*rawA q 2 2 at hb
  rw [conjugate_rawA_two_two,rawA_two_two] at hb
  have hrow : r.val 2 0^2≤c*q.2.1.val^2*q.2.2.val^2 := by
    have h1 := mul_nonneg (sq_nonneg p.2.1.val) (sq_nonneg (r.val 2 0*p.1 0+r.val 2 1))
    have h2 := mul_nonneg (mul_nonneg (sq_nonneg p.2.1.val) (sq_nonneg p.2.2.val))
      (sq_nonneg (r.val 2 0*p.1 2+r.val 2 1*p.1 1+r.val 2 2))
    nlinarith only [hb,h1,h2]
  calc
    r.val 2 0^6=(r.val 2 0^2)^3 := by ring
    _ ≤ (c*q.2.1.val^2*q.2.2.val^2)^3 := pow_le_pow_left₀ (sq_nonneg _) hrow 3
    _ = (c^3*q.2.1.val^4*q.2.2.val^2)*(q.2.1.val^2*q.2.2.val^4) := by ring
    _ = _ := by rw [hd]; ring

/-- Every actual full transition satisfies the primary detector equation. -/
theorem transition_primary (r : RealGL) (p : domain r) :
    A (transition r p).val=normalize (conjugate r (A p.val)) := by
  have hg : (p.val,(transition r p).val)∈fullGraph r := ⟨p.property,rfl⟩
  rw [fullGraph_eq_closure_interior] at hg
  exact (closure_transition_subset_equations r hg).1

theorem transition_lowerLeft_bound (r : RealGL) (p : domain r) :
    r.val 2 0^6≤r.val.det^2*p.val.2.1.val^4*p.val.2.2.val^2*
      (transition r p).val.2.1.val^2*(transition r p).val.2.2.val^4 :=
  lowerLeft_sixth_bound r p.val (transition r p).val (transition_primary r p)

/-- Two zero bottom-left entries of mutually inverse rank-three matrices force a parabolic. -/
theorem two_lowerLeft_zero_parabolic (r : RealGL) (hr : r.val 2 0=0) (hi : r⁻¹.val 2 0=0) :
    r∈planeStabilizer ∨ r∈SymmetricSpaceLineBordification.lineStabilizer := by
  have h := hi
  rw [Matrix.coe_units_inv,Matrix.inv_def] at h
  simp [Matrix.adjugate_fin_three,hr,Matrix.smul_apply,smul_eq_mul,Ring.inverse_eq_inv] at h
  rcases h.resolve_left r.det_ne_zero with h10|h21
  · exact Or.inr ((SymmetricSpaceLineBordification.mem_lineStabilizer_iff r).mpr ⟨h10,hr⟩)
  · exact Or.inl ((mem_planeStabilizer_iff r).mpr ⟨hr,h21⟩)

end TernaryPoly.SymmetricSpaceGluedArithmetic
