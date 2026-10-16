module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.CoordinateInputs

@[expose] public section


/-!
# Parity of the degree and the vacuous cases of local nondegeneracy

Local nondegeneracy at a line cusp (`LocalNondegenerate`) only concerns line summand classes whose
Shapiro coordinate at the representative line is nonzero. The coordinate of a summand class at the
reference flag of its cusp is a local joint generalized eigenclass of the pair character
(`cuspRes_mem_localJoint_of_mem`), and the coordinate at any other flag of the same cusp orbit is
its transport along the level. Hence if the local joint generalized eigenspace at the cusp is zero,
every summand class has zero coordinate at the representative line and local nondegeneracy holds
vacuously (`localNondegenerate_of_localJoint_eq_bot`).

The parity of the degree `n` decides which cusps carry local cohomology:

* **Good line `L₁`.** The local cohomology embeds into `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det^τ)` for a
  twist `τ` depending on the character. The central element `-1 ∈ GL₂(ℤ)` acts there by
  `(-1)^{n+1}` for every `τ`, so the group cohomology vanishes for even `n`: the local joint
  generalized eigenspace is zero for the trivial character and for the odd character of conductor
  three (`localJoint_goodLine_eq_bot_of_even`), and local nondegeneracy at `L₁` is vacuous
  (`localNondegenerate_goodLine_of_even`). For odd `n` the cohomology is nonzero and the
  nondegeneracy is the content of the Kostant bridge.
* **Bad line `L₀`.** For an odd character the local cohomology is zero for every `n`
  (`localNondegenerate_badLine_of_odd`). For the trivial character `-1 ∉ Γ₁'(3)`, so no parity
  forces vanishing: both parities of `n` carry classes (level one oldforms and level three newforms),
  and the nondegeneracy is a genuine input for both.

The nonvacuous inputs are named (`GoodLineOddInput`, `BadLineEvenInput`,
`BadLineOddInput`), and the headline duality theorem is assembled from them by parity
(`associatePairDuality_of_parityInputs`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.BoundaryDuality.ParityCases

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace
open TernaryPeriodPolynomials.BoundaryDuality.ChainLocal
open TernaryPeriodPolynomials.BoundaryDuality.CuspSeparation
open TernaryPeriodPolynomials.BoundaryDuality.CuspFullness
open TernaryPeriodPolynomials.BoundaryDuality.CuspDualL2
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits
  (cuspFlag cuspFlag_transporter)
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Separation

variable {ι L P : Type} [Fintype ι] [Fintype L] [Fintype P] [DecidableEq L] [DecidableEq P]
  {n : ℕ}

/-! ### Vanishing coordinates from a vanishing local joint eigenspace -/

/-- A class with vanishing Shapiro coordinate at the reference flag of a cusp has vanishing
Shapiro coordinate at every flag of the same cusp orbit. -/
theorem fixedPointH2_eq_zero_of_cuspRes_side {χ : RankOneCharacter} {side : Side} {c : Bool}
    {F : Flags side} (hF : ∃ γ : rationalLevel, γ.val • cuspFlag side c = F)
    {a : StratumH2 n χ side} (ha : cuspRes n χ side c a = 0) :
    fixedPointH2 rationalLevel (rationalCoefficientComponent n χ) F a = 0 := by
  obtain ⟨γ, hγ⟩ := hF
  rw [← stabilizerTransportH2_fixedPointH2 rationalLevel (rationalCoefficientComponent n χ) γ
    (cuspFlag side c) F hγ a]
  change stabilizerTransportH2 rationalLevel (rationalCoefficientComponent n χ) γ
    (cuspFlag side c) F hγ (cuspRes n χ side c a) = 0
  rw [ha, map_zero]

/-- If the local joint generalized eigenspace of the pair character at a cusp is zero, every
summand class has zero Shapiro coordinate at every flag of the cusp orbit. -/
theorem fixedPointH2_eq_zero_of_localJoint_eq_bot (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke) {side : Side}
    {c : Bool} (hbot : localJoint n D.chi (pairCharacter D hecke hhecke) side c = ⊥)
    {F : Flags side} (hF : ∃ γ : rationalLevel, γ.val • cuspFlag side c = F)
    {a : StratumH2 n D.chi side} (ha : a ∈ boundarySummand D side) :
    fixedPointH2 rationalLevel (rationalCoefficientComponent n D.chi) F a = 0 := by
  have hmem := Separation.cuspRes_mem_localJoint_of_mem D hecke hhecke side c ha
  rw [hbot, Submodule.mem_bot] at hmem
  exact fixedPointH2_eq_zero_of_cuspRes_side hF hmem

/-- **Local nondegeneracy is vacuous when every line summand class has zero coordinate at the
representative line.** -/
theorem localNondegenerate_of_coordinates_eq_zero (Θ : TraceData ι L P) {D : InducingData n}
    (T : DualityData n D.chi) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (v : L) (g : Bool)
    (hzero : ∀ b ∈ boundarySummand D .line,
      fixedPointH2 rationalLevel (rationalCoefficientComponent n D.chi) (Θ.lineRep v) b = 0) :
    LocalNondegenerate Θ D T hecke hhecke v g :=
  fun b hb hne => absurd (hzero b hb) hne

/-- **Local nondegeneracy is vacuous when the local joint generalized eigenspace at the line cusp
of the representative line is zero.** -/
theorem localNondegenerate_of_localJoint_eq_bot (Θ : TraceData ι L P) {D : InducingData n}
    (T : DualityData n D.chi) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (v : L) (g c : Bool)
    (hbot : localJoint n D.chi (pairCharacter D hecke hhecke) .line c = ⊥)
    (hF : ∃ γ : rationalLevel, γ.val • cuspFlag .line c = Θ.lineRep v) :
    LocalNondegenerate Θ D T hecke hhecke v g :=
  localNondegenerate_of_coordinates_eq_zero Θ T hecke hhecke v g fun _ hb =>
    fixedPointH2_eq_zero_of_localJoint_eq_bot D hecke hhecke hbot hF hb

/-! ### The orbits of the two representative lines -/

/-- The representative line `L₁` of the boundary trace is a translate of the reference good line. -/
theorem goodLine_orbit :
    ∃ γ : rationalLevel, γ.val • cuspFlag .line true = traceDataL2.lineRep 1 :=
  cuspFlag_transporter .line true (traceDataL2.lineRep 1)
    (iff_of_true (by rw [lineRep_one]; exact goodFlag_L₁) rfl)

/-- The representative line `L₀` of the boundary trace is the reference bad line. -/
theorem badLine_orbit :
    ∃ γ : rationalLevel, γ.val • cuspFlag .line false = traceDataL2.lineRep 0 := by
  refine ⟨1, ?_⟩
  rw [lineRep_zero]
  exact one_smul RationalGL3 _

/-! ### The good line in even degree -/

/-- **The local joint generalized eigenspace at the good line vanishes in even degree for the odd
character**: the composite of the transport to the standard good line and the full good-line edge is
injective into `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)`, which is zero because `-1` acts by `-1`. -/
theorem localJoint_goodLine_twisted_eq_bot_of_even (hn : 0 < n) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (heven : Even n)
    (c : HeckeCorrespondence → ℂ) : localJoint n χ c .line true = ⊥ := by
  have hf : Function.Injective
      ((Twisted.edgeH2LT n χ hχ hn).comp (Twisted.psiLT n χ)) :=
    (Twisted.edgeH2LT_injective n χ hχ hn).comp (Twisted.psiLT_injective n χ)
  rw [eq_bot_iff]
  intro y _
  have h0 : ((Twisted.edgeH2LT n χ hχ hn).comp (Twisted.psiLT n χ)) y =
      ((Twisted.edgeH2LT n χ hχ hn).comp (Twisted.psiLT n χ)) 0 := by
    rw [map_zero]
    exact Spectral.IdentityPlaneEven.arithmeticH1_eq_zero_of_odd (n + 1)
      (Even.add_one heven) (-1) _
  exact (Submodule.mem_bot ℂ).mpr (hf h0)

/-- **The local joint generalized eigenspace at the good line vanishes in even degree** for a
nonzero associate pair, for the trivial character and for the odd character of conductor three (the
only nontrivial character with a nonzero pair). -/
theorem localJoint_goodLine_eq_bot_of_even (hn : 3 ≤ n) (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (heven : Even n) (hne : associatePair D ≠ ⊥) :
    localJoint n D.chi (pairCharacter D hecke hhecke) .line true = ⊥ := by
  by_cases hχ : D.chi = trivialCharacter
  · exact Separation.localJoint_line_true_eq_bot_of_even D hχ hecke hhecke hn heven hne
  · have h3 := LevelOneNontrivial.conductorThree_of_associatePair_ne_bot D hne
    have hodd := LevelOneNontrivial.chi_realNegOne_eq_neg_one hχ h3
    exact localJoint_goodLine_twisted_eq_bot_of_even (by omega) D.chi hodd heven _

/-- **Local nondegeneracy at the good line is vacuous in even degree.** -/
theorem localNondegenerate_goodLine_of_even (hn : 3 ≤ n) (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (heven : Even n) (hne : associatePair D ≠ ⊥) :
    LocalNondegenerate traceDataL2 D (dualityData n D.chi) hecke hhecke 1 (good 1) :=
  localNondegenerate_of_localJoint_eq_bot traceDataL2 (dualityData n D.chi) hecke hhecke 1
    (good 1) true (localJoint_goodLine_eq_bot_of_even hn D hecke hhecke heven hne) goodLine_orbit

/-! ### The bad line for an odd character -/

/-- **Local nondegeneracy at the bad line is vacuous for an odd character**, in every degree. -/
theorem localNondegenerate_badLine_of_odd (D : InducingData n)
    (hodd : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) :
    LocalNondegenerate traceDataL2 D (dualityData n D.chi) hecke hhecke 0 (good 0) :=
  localNondegenerate_of_localJoint_eq_bot traceDataL2 (dualityData n D.chi) hecke hhecke 0
    (good 0) false
    (SourceConstruction.localJoint_line_false_eq_bot n D.chi hodd _) badLine_orbit

/-! ### The nonvacuous inputs, by parity -/

/-- **Good line, odd degree** (all characters with a nonzero pair): local nondegeneracy at `L₁`.
This is the case of the level-one Kostant bridge `levelOneBridgeTrivial` / `levelOneBridgeOdd`,
where the degree must be odd. -/
def GoodLineOddInput (n : ℕ) : Prop :=
  ∀ (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke), Odd n → associatePair D ≠ ⊥ →
    LocalNondegenerate traceDataL2 D (dualityData n D.chi) hecke hhecke 1 (good 1)

/-- **Bad line, even degree** (trivial character): local nondegeneracy at `L₀`. This is the case
of the level-three Kostant bridge `levelThreeBridgeBad`, where the degree must be even. -/
def BadLineEvenInput (n : ℕ) : Prop :=
  ∀ (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke), D.chi = trivialCharacter → Even n →
    associatePair D ≠ ⊥ →
    LocalNondegenerate traceDataL2 D (dualityData n D.chi) hecke hhecke 0 (good 0)

/-- **Bad line, odd degree** (trivial character): local nondegeneracy at `L₀`. The local
cohomology at the bad line is not forced to vanish by parity here (`-1 ∉ Γ₁'(3)`), and the
level-three Kostant bridge of the dual coordinate is only available for even degree. -/
def BadLineOddInput (n : ℕ) : Prop :=
  ∀ (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke), D.chi = trivialCharacter → Odd n →
    associatePair D ≠ ⊥ →
    LocalNondegenerate traceDataL2 D (dualityData n D.chi) hecke hhecke 0 (good 0)

/-- **The local nondegeneracy hypothesis of `associatePairDuality_of_localNondegenerate` from the
three nonvacuous parity inputs**; the good line in even degree is vacuous. -/
theorem nondeg_of_parityInputs (hn : 3 ≤ n) (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (h₁ : GoodLineOddInput n) (h₂ : BadLineEvenInput n) (h₃ : BadLineOddInput n) :
    associatePair D ≠ ⊥ → ∀ v : Fin 2, (D.chi = trivialCharacter ∨ v = 1) →
      LocalNondegenerate traceDataL2 D (dualityData n D.chi) hecke hhecke v (good v) := by
  intro hne
  refine Fin.forall_fin_two.mpr ⟨fun hv => ?_, fun _ => ?_⟩
  · have hχ : D.chi = trivialCharacter := hv.resolve_right (by decide)
    rcases Nat.even_or_odd n with he | ho
    · exact h₂ D hecke hhecke hχ he hne
    · exact h₃ D hecke hhecke hχ ho hne
  · rcases Nat.even_or_odd n with he | ho
    · exact localNondegenerate_goodLine_of_even hn D hecke hhecke he hne
    · exact h₁ D hecke hhecke ho hne

/-- **Boundary duality on the associate pair from the three nonvacuous parity inputs**: local
nondegeneracy at the good line in odd degree, and at the bad line in even and odd degree. -/
theorem associatePairDuality_of_parityInputs (hn : 3 ≤ n) (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (h₁ : GoodLineOddInput n) (h₂ : BadLineEvenInput n) (h₃ : BadLineOddInput n) :
    AssociatePairDuality D :=
  CoordinateInputs.associatePairDuality_of_localNondegenerate hn D hecke hhecke
    (nondeg_of_parityInputs hn D hecke hhecke h₁ h₂ h₃)

end TernaryPeriodPolynomials.BoundaryDuality.ParityCases

end
