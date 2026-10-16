module

public import TernaryPeriodPolynomials.SymmetricSpace.Glued.ArithmeticBorelBounds

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceGluedArithmetic
open Matrix SymmetricSpacePositive SymmetricSpaceFlagCoordinates SymmetricSpaceBorelCorner
open SymmetricSpaceRationalGluing SymmetricSpaceRationalAction

/-- Actual Borel shear formulas bound all entries from diagonal and coordinate bounds. -/
theorem borel_entries_bound (A M : ℝ) (hA : 0<A) (hM : 1≤M) :
    ∃ R : ℝ,∀ (r : BorelGroup) (p q : Corner),
      (∀ i,|r.val.val i i|≤A) → (∀ i,|p.1 i|≤M) → (∀ i,|q.1 i|≤M) →
      extend r p=q → ∀ i j,|r.val.val i j|≤R := by
  let B := 2*A*M
  let C := 2*A*M+B*M
  let R := A+B+C
  have hM0 : 0≤M := le_trans zero_le_one hM
  have hB : 0≤B := by dsimp [B]; positivity
  have hC : 0≤C := by dsimp [C]; positivity
  have hAR : A≤R := by dsimp [R]; linarith
  have hBR : B≤R := by dsimp [R]; linarith
  have hCR : C≤R := by dsimp [R]; linarith
  refine ⟨R,?_⟩
  intro r p q hd hp hq he
  have hdn := diagonal_nonzero r
  have hx : r.val.val 0 1=q.1 0*r.val.val 1 1-r.val.val 0 0*p.1 0 := by
    have e := congrArg (fun v : Corner => v.1 0) he
    change (r.val.val 0 0*p.1 0+r.val.val 0 1)/r.val.val 1 1=q.1 0 at e
    have := (div_eq_iff hdn.2.1).mp e
    linarith
  have hy : r.val.val 1 2=q.1 1*r.val.val 2 2-r.val.val 1 1*p.1 1 := by
    have e := congrArg (fun v : Corner => v.1 1) he
    change (r.val.val 1 1*p.1 1+r.val.val 1 2)/r.val.val 2 2=q.1 1 at e
    have := (div_eq_iff hdn.2.2).mp e
    linarith
  have hz : r.val.val 0 2=q.1 2*r.val.val 2 2-r.val.val 0 0*p.1 2-r.val.val 0 1*p.1 1 := by
    have e := congrArg (fun v : Corner => v.1 2) he
    change (r.val.val 0 0*p.1 2+r.val.val 0 1*p.1 1+r.val.val 0 2)/r.val.val 2 2=q.1 2 at e
    have := (div_eq_iff hdn.2.2).mp e
    linarith
  have h01 : |r.val.val 0 1|≤B := calc
    _ = |q.1 0*r.val.val 1 1-r.val.val 0 0*p.1 0| := congrArg abs hx
    _ ≤ |q.1 0*r.val.val 1 1|+|r.val.val 0 0*p.1 0| := abs_sub _ _
    _ ≤ M*A+A*M := by
      simp only [abs_mul]
      exact add_le_add (mul_le_mul (hq 0) (hd 1) (abs_nonneg _) hM0)
        (mul_le_mul (hd 0) (hp 0) (abs_nonneg _) hA.le)
    _ = B := by dsimp [B]; ring
  have h12 : |r.val.val 1 2|≤B := calc
    _ = |q.1 1*r.val.val 2 2-r.val.val 1 1*p.1 1| := congrArg abs hy
    _ ≤ |q.1 1*r.val.val 2 2|+|r.val.val 1 1*p.1 1| := abs_sub _ _
    _ ≤ M*A+A*M := by
      simp only [abs_mul]
      exact add_le_add (mul_le_mul (hq 1) (hd 2) (abs_nonneg _) hM0)
        (mul_le_mul (hd 1) (hp 1) (abs_nonneg _) hA.le)
    _ = B := by dsimp [B]; ring
  have h02 : |r.val.val 0 2|≤C := calc
    _ = |q.1 2*r.val.val 2 2-r.val.val 0 0*p.1 2-r.val.val 0 1*p.1 1| := congrArg abs hz
    _ ≤ |q.1 2*r.val.val 2 2-r.val.val 0 0*p.1 2|+|r.val.val 0 1*p.1 1| := abs_sub _ _
    _ ≤ (|q.1 2*r.val.val 2 2|+|r.val.val 0 0*p.1 2|)+|r.val.val 0 1*p.1 1| :=
      add_le_add (abs_sub _ _) le_rfl
    _ ≤ (M*A+A*M)+B*M := by
      simp only [abs_mul]
      exact add_le_add (add_le_add (mul_le_mul (hq 2) (hd 2) (abs_nonneg _) hM0)
        (mul_le_mul (hd 0) (hp 2) (abs_nonneg _) hA.le))
        (mul_le_mul h01 (hp 1) (abs_nonneg _) hB)
    _ = C := by dsimp [C]; ring
  obtain ⟨h10,h20,h21⟩ := (mem_borelStabilizer_iff r.val).mp r.property
  have h0R : (0 : ℝ)≤R := hA.le.trans hAR
  intro i j
  fin_cases i <;> fin_cases j
  · exact (hd 0).trans hAR
  · exact h01.trans hBR
  · exact h02.trans hCR
  · change |r.val.val 1 0|≤R
    simpa only [h10,abs_zero] using h0R
  · exact (hd 1).trans hAR
  · exact h12.trans hBR
  · change |r.val.val 2 0|≤R
    simpa only [h20,abs_zero] using h0R
  · change |r.val.val 2 1|≤R
    simpa only [h21,abs_zero] using h0R
  · exact (hd 2).trans hAR

/-- The four-case gluing transition is the literal existing Borel action whenever applicable. -/
theorem transition_borel (r : BorelGroup) (p : domain r.val) :
    (transition r.val p).val=extend r p.val := by
  have h : (fun q : domain r.val => (transition r.val q).val)=
      (fun q : domain r.val => extend r q.val) :=
    (denseRange_liftInterior (domain r.val) (interior_subset_domain r.val)).equalizer
      (continuous_subtype_val.comp (transition r.val).continuous)
      ((continuous_extend r).comp continuous_subtype_val) (by
        funext S
        change (transition r.val (interiorPoint r.val S)).val=extend r (cornerEmbedding S)
        rw [transition_interiorPoint,extend_embedding])
  exact congrFun h p

/-- An arithmetic equality in actual glued charts yields the literal Borel coordinate equality. -/
theorem borel_extend_of_chart_eq (a b : RationalGL) (g : IntegralGL) (p q : Corner)
    (hB : realRational (relative a b g)∈borelStabilizer)
    (he : integralAction g (chart a p)=chart b q) :
    extend ⟨realRational (relative a b g),hB⟩ p=q := by
  rw [integralAction_chart] at he
  obtain ⟨hp,ht⟩ := (chart_eq_iff _ b p q).mp he
  have hr : changeMatrix (integralRational g*a) b=realRational (relative a b g) := by
    simp only [changeMatrix,relative,mul_assoc]
  have hp' : p∈domain (realRational (relative a b g)) := hr ▸ hp
  have hc := transition_congr hr ⟨p,hp⟩ ⟨p,hp'⟩ rfl
  rw [transition_borel ⟨_,hB⟩] at hc
  exact hc.symm.trans ht

/-- Compact-chart arithmetic transporters with actual Borel relative matrix are finite. -/
theorem compact_borel_chart_transporters (a b : RationalGL) (K L : Set Corner)
    (hK : IsCompact K) (hL : IsCompact L) :
    {g : IntegralGL | realRational (relative a b g)∈borelStabilizer ∧
      ∃ p∈K,∃ q∈L,integralAction g (chart a p)=chart b q}.Finite := by
  obtain ⟨A,hA,hdiag⟩ := borel_diagonal_bound a b
  obtain ⟨M,hM,hcoord⟩ := compact_unipotent_bound K L hK hL
  obtain ⟨R,hR⟩ := borel_entries_bound A M hA hM
  refine (finite_relative_entry_bound a b R).subset ?_
  rintro g ⟨hB,p,hp,q,hq,he⟩
  exact hR ⟨realRational (relative a b g),hB⟩ p q (hdiag g hB)
    (hcoord p (Or.inl hp)) (hcoord q (Or.inr hq)) (borel_extend_of_chart_eq a b g p q hB he)

end TernaryPoly.SymmetricSpaceGluedArithmetic
