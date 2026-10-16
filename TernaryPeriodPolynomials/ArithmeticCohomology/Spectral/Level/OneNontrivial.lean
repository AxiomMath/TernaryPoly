module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.Assembly
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Obstructions
public import TernaryPeriodPolynomials.EisensteinSeries.CuspIntegral.CentralIdele

@[expose] public section


/-!
# Eigencharacter separation for a nontrivial character

`eigenSeparated_of_openInputs` asks for the level-one inputs (`hloc1`, `hS1`, `hS1L`, `hS2`, `hS2L`)
for every character `χ ≠ trivialCharacter`.  This file shows that these inputs are only needed for
one very special family of characters, and that for the same family the level-three inputs collapse
to a vanishing statement.

* **Route (a), proved.**  If `χ` is nontrivial on a finite integral unit `u ≡ 1 (mod 3)` then
  `associatePair D = ⊥` (`associatePair_eq_bot_of_not_conductorThree`, from the character
  obstructions of `SourceConstruction.Obstructions`: a section induced from `σ ⊗ χ` and
  right invariant under the finite level vanishes at the cusp frame, because the Levi unit `u` is
  moved into the level and acts there by `χ(u)`).  Hence a nonzero pair forces `ConductorThree χ`:
  `χ` is trivial on `{u ∈ Ẑˣ : u ≡ 1 (3)}`.  Since every idele is `q · t · w` with `q ∈ ℚˣ`,
  `t ∈ ℝˣ` and `w ≡ 1 (3)` (`CuspIntegral.ideleDecomp_exists`), such a `χ` is determined by
  `χ(-1_∞)`, and a nontrivial one is the odd quadratic character of conductor three
  (`chi_realNegOne_eq_neg_one`).
* **Level three, proved.**  For *every* nontrivial `χ` the Shapiro coordinate image at the good
  plane and at the bad line is zero (`coordinateImage_levelThree_eq_bot_of_nontrivial`, the
  obstructions O1 and O3).  So the coordinate statement there is *equivalent* to the vanishing of
  the local joint generalized eigenspace (`coordinateStatement_plane_true_iff_of_nontrivial`), and
  the four inputs `hfin3p`, `hfin3l`, `hrank3p`, `hrank3l` are equivalent to the single vanishing
  statement `LevelThreeVanishing` (`levelThreeVanishing_iff_finite_rank`).  No source construction
  is needed at the level-three cusps for a nontrivial character.
* **Route (b), not available.**  No central-character or parity obstruction removes the level-one
  cusps for `ConductorThree χ`, `χ ≠ 1`: the central element `-I₃` acts on the coefficients by
  `χ_∞(-1) (-1)^{n+1}` and on the induced representation by `χ_f(-1) = χ_∞(-1)` times the central
  character of `σ`, which for a spherical `σ` is `1` on `-1_f`; this only forces `n` odd for a
  spherical `D.cusp`, independently of `χ`, and it does not make the level-one local joint
  eigenspaces vanish.
* **Route (c), not done: where `χ = 1` is used.**  The level-one results (`LocalLevelOne`,
  `LevelOneEisenstein.LocalMultiplicity`, `IdentityPlaneEven`, the edge maps
  `IdentityPlaneEdge`, `IdentityPlaneCoordinate`, `IdentityPlaneLocalOp`, `GoodLineLocalOp`) are all
  stated for `rationalCoefficientComponent n trivialCharacter`.  For `ConductorThree χ` with
  `χ(-1_∞) = -1`, the representation on the level group `Γ ⊆ GL₃(ℤ)` is the trivial one twisted by
  `sgn ∘ det = det`, i.e. `Sym^n ⊗ det⁰` instead of `Sym^n ⊗ det⁻¹` on `GL₃(ℤ)`; the edge maps to
  `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det^σ)` exist for the twisted coefficients but the explicit coset
  formulas, and the comparison `c(T_p) = χ(p) + (p² + p) p^{-(n+3)/2} ω`, change by the sign
  `χ(sAd p) = (p/3)`, so that `‖c(T₂) - 1‖ ≤ 3/4` becomes `‖c(T₂) + 1‖ ≤ 3/4`.  None of these
  have been transported to the twisted representation, so the level-one local multiplicity one
  (`LevelOneLocalMultiplicityOne`) stays an input, as do the bridge inputs `hS1`, `hS1L`
  (construction of a summand class with nonzero coordinate at the level-one cusp) and `hS2`,
  `hS2L` (strong multiplicity one at the prime three).

The residual inputs for `χ ≠ trivialCharacter` are therefore exactly those of
`eigenSeparated_of_openInputs`, but only for characters with `ConductorThree χ`, and with the two
level-three inputs replaced by `LevelThreeVanishing`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SpectralSeparation
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Separation

namespace TernaryPeriodPolynomials.Spectral.LevelOneNontrivial

variable {n : ℕ}

/-! ## Characters of conductor dividing three -/

/-- The character is trivial on every finite integral unit congruent to `1` modulo three: its
conductor divides three. -/
def ConductorThree (χ : RankOneCharacter) : Prop :=
  ∀ u : IntegralAdelesˣ, integralReduction u.val = 1 → χ.toMonoidHom (integralAdeleUnit u) = 1

/-- A rank-one character with trivial underlying homomorphism is the trivial character. -/
theorem rankOneCharacter_eq_trivial {χ : RankOneCharacter} (h : χ.toMonoidHom = 1) :
    χ = trivialCharacter := by
  cases χ with
  | mk f c u r p =>
    have hf : f = 1 := h
    subst hf
    rfl

theorem ideleOf_eq (q : ℚˣ) (t : ℝˣ) (w : IntegralAdelesˣ) :
    TernaryPeriodPolynomials.CuspIntegral.ideleOf q t w =
      Units.map rationalAdele q * (realAdeleUnit t * integralAdeleUnit w) :=
  Units.ext rfl

/-- On a character of conductor dividing three every value is a value at a real unit. -/
theorem character_eq_real {χ : RankOneCharacter} (hcond : ConductorThree χ) (z : Adelesˣ) :
    ∃ t : ℝˣ, χ.toMonoidHom z = χ.toMonoidHom (realAdeleUnit t) := by
  obtain ⟨q, t, w, hw, hz⟩ :=
    TernaryPeriodPolynomials.CuspIntegral.ideleDecomp_exists z
  refine ⟨t, ?_⟩
  rw [hz, ideleOf_eq, map_mul, map_mul, χ.rational q, hcond w hw, mul_one, one_mul]

/-- Triviality at `-1_∞` gives triviality at every real unit. -/
theorem real_eq_one_of_neg_one (χ : RankOneCharacter)
    (h : χ.toMonoidHom (realAdeleUnit (-1)) = 1) (t : ℝˣ) :
    χ.toMonoidHom (realAdeleUnit t) = 1 := by
  rcases lt_or_gt_of_ne t.ne_zero with hneg | hpos
  · have hdec : t = (-1) * (-t) := by rw [neg_mul, one_mul, neg_neg]
    have hpos' : 0 < (-t).val := by
      rw [Units.val_neg]
      exact neg_pos.mpr hneg
    have hmul := map_mul realUnitHom (-1 : ℝˣ) (-t)
    rw [← hdec] at hmul
    have hmul' : realAdeleUnit t = realAdeleUnit (-1) * realAdeleUnit (-t) := hmul
    rw [hmul', map_mul, h, χ.positiveReal _ hpos', one_mul]
  · exact χ.positiveReal t hpos

/-- If `χ` is trivial on the finite integral units it is trivial at `-1_∞`: the rational unit `-1`
is `(-1)_∞ · (-1)_f`. -/
theorem real_neg_one_of_units (χ : RankOneCharacter)
    (hall : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1) :
    χ.toMonoidHom (realAdeleUnit (-1)) = 1 := by
  have hsplit : Units.map rationalAdele (-1 : ℚˣ) =
      realAdeleUnit (-1) * integralAdeleUnit (-1) := by
    apply Units.ext
    refine Prod.ext ?_ ?_
    · simp [realAdeleUnit, integralAdeleUnit]
    · simp [realAdeleUnit, integralAdeleUnit]
  have hrat := χ.rational (-1)
  rw [hsplit, map_mul, hall, mul_one] at hrat
  exact hrat

/-- A nontrivial character is nontrivial on some finite integral unit (every idele is a rational
times a real unit times an integral unit). -/
theorem exists_unit_character_ne_one {χ : RankOneCharacter} (hχ : χ ≠ trivialCharacter) :
    ∃ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) ≠ 1 := by
  by_contra hall
  push Not at hall
  apply hχ
  apply rankOneCharacter_eq_trivial
  refine MonoidHom.ext fun z => ?_
  rw [MonoidHom.one_apply]
  have hcond : ConductorThree χ := fun u _ => hall u
  obtain ⟨t, ht⟩ := character_eq_real hcond z
  rw [ht]
  exact real_eq_one_of_neg_one χ (real_neg_one_of_units χ hall) t

/-- A character of conductor dividing three with trivial value at `-1_∞` is trivial. -/
theorem eq_trivial_of_real_neg_one {χ : RankOneCharacter} (hcond : ConductorThree χ)
    (h : χ.toMonoidHom (realAdeleUnit (-1)) = 1) : χ = trivialCharacter := by
  apply rankOneCharacter_eq_trivial
  refine MonoidHom.ext fun z => ?_
  rw [MonoidHom.one_apply]
  obtain ⟨t, ht⟩ := character_eq_real hcond z
  rw [ht]
  exact real_eq_one_of_neg_one χ h t

/-- A nontrivial character of conductor dividing three is odd: `χ(-1_∞) = -1`. -/
theorem chi_realNegOne_eq_neg_one {χ : RankOneCharacter} (hχ : χ ≠ trivialCharacter)
    (hcond : ConductorThree χ) : χ.toMonoidHom (realAdeleUnit (-1)) = -1 := by
  have hmm : ((-1 : ℝˣ) * (-1)) = 1 := by simp
  have hsq' := map_mul realUnitHom (-1 : ℝˣ) (-1)
  rw [hmm, map_one] at hsq'
  have hsq'' : realAdeleUnit (-1) * realAdeleUnit (-1) = 1 := hsq'.symm
  have hsq : χ.toMonoidHom (realAdeleUnit (-1)) * χ.toMonoidHom (realAdeleUnit (-1)) = 1 := by
    rw [← map_mul, hsq'', map_one]
  have hne1 : χ.toMonoidHom (realAdeleUnit (-1)) ≠ 1 := fun h1 =>
    hχ (eq_trivial_of_real_neg_one hcond h1)
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · exact absurd h hne1
  · exact h

/-! ## Route (a): the pair vanishes unless the conductor divides three -/

/-- **Route (a).**  If `χ` is nontrivial on a finite integral unit congruent to `1` modulo three,
the associate pair is zero. -/
theorem associatePair_eq_bot_of_not_conductorThree (D : InducingData n)
    (h : ¬ ConductorThree D.chi) : associatePair D = ⊥ := by
  unfold ConductorThree at h
  push Not at h
  obtain ⟨u, hu1, hu⟩ := h
  exact TernaryPeriodPolynomials.SourceConstruction.associatePair_eq_bot_of_character
    D u hu1 hu

/-- A nonzero associate pair forces the conductor of `χ` to divide three. -/
theorem conductorThree_of_associatePair_ne_bot (D : InducingData n)
    (hne : associatePair D ≠ ⊥) : ConductorThree D.chi := by
  by_contra h
  exact hne (associatePair_eq_bot_of_not_conductorThree D h)

/-! ## The level-three cusps for a nontrivial character -/

/-- For a nontrivial character the Shapiro coordinate images at the good plane and the bad line
are zero. -/
theorem coordinateImage_levelThree_eq_bot_of_nontrivial (D : InducingData n)
    (hχ : D.chi ≠ trivialCharacter) :
    coordinateImage D .plane true = ⊥ ∧ coordinateImage D .line false = ⊥ := by
  obtain ⟨u, hu⟩ := exists_unit_character_ne_one hχ
  exact ⟨TernaryPeriodPolynomials.SourceConstruction.coordinateImage_plane_true_eq_bot
      D u hu,
    TernaryPeriodPolynomials.SourceConstruction.coordinateImage_line_false_eq_bot
      D u hu⟩

/-- For a nontrivial character the coordinate statement at the good plane is the vanishing of the
local joint eigenspace. -/
theorem coordinateStatement_plane_true_iff_of_nontrivial (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hχ : D.chi ≠ trivialCharacter) :
    CoordinateStatement D hecke hhecke .plane true ↔
      localJoint n D.chi (pairCharacter D hecke hhecke) .plane true = ⊥ := by
  unfold CoordinateStatement
  rw [(coordinateImage_levelThree_eq_bot_of_nontrivial D hχ).1]
  exact le_bot_iff

/-- For a nontrivial character the coordinate statement at the bad line is the vanishing of the
local joint eigenspace. -/
theorem coordinateStatement_line_false_iff_of_nontrivial (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hχ : D.chi ≠ trivialCharacter) :
    CoordinateStatement D hecke hhecke .line false ↔
      localJoint n D.chi (pairCharacter D hecke hhecke) .line false = ⊥ := by
  unfold CoordinateStatement
  rw [(coordinateImage_levelThree_eq_bot_of_nontrivial D hχ).2]
  exact le_bot_iff

/-- **Vanishing of the local joint generalized eigenspaces at the two level-three cusps**, for a
nonzero pair. -/
def LevelThreeVanishing (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) : Prop :=
  associatePair D ≠ ⊥ →
    localJoint n D.chi (pairCharacter D hecke hhecke) .plane true = ⊥ ∧
      localJoint n D.chi (pairCharacter D hecke hhecke) .line false = ⊥

/-- Finiteness and the global lower bound at a cusp with zero coordinate image force the local joint
eigenspace to vanish. -/
theorem localJoint_eq_bot_of_coordinateImage_eq_bot (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side)
    (good : Bool) (hne : associatePair D ≠ ⊥) (hfin : LocalJointFinite D hecke hhecke side good)
    (hrank : CoordinateRankLowerBound D hecke hhecke side good)
    (hbot : coordinateImage D side good = ⊥) :
    localJoint n D.chi (pairCharacter D hecke hhecke) side good = ⊥ := by
  obtain ⟨_, hfd, -⟩ := hfin hne
  obtain ⟨s, hs, hind⟩ := hrank hne hfd
  have hzero : Module.finrank ℂ
      (localJoint n D.chi (pairCharacter D hecke hhecke) side good) = 0 := by
    by_contra hpos
    have hpos' : 0 < Module.finrank ℂ
        (localJoint n D.chi (pairCharacter D hecke hhecke) side good) := Nat.pos_of_ne_zero hpos
    have h0 : s ⟨0, hpos'⟩ = 0 := by
      have hmem := hs ⟨0, hpos'⟩
      rw [hbot, Submodule.mem_bot] at hmem
      exact hmem
    exact hind.ne_zero ⟨0, hpos'⟩ h0
  exact Submodule.finrank_eq_zero.mp hzero

/-- Vanishing of the local joint eigenspace gives the finiteness input. -/
theorem localJointFinite_of_eq_bot (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool)
    (hbot : localJoint n D.chi (pairCharacter D hecke hhecke) side good = ⊥) :
    LocalJointFinite D hecke hhecke side good := by
  intro _
  refine ⟨0, ?_⟩
  unfold LocalUpperBound
  rw [hbot]
  exact ⟨inferInstance, by simp⟩

/-- Vanishing of the local joint eigenspace gives the global lower bound input. -/
theorem coordinateRankLowerBound_of_eq_bot (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (side : Side) (good : Bool)
    (hbot : localJoint n D.chi (pairCharacter D hecke hhecke) side good = ⊥) :
    CoordinateRankLowerBound D hecke hhecke side good := by
  intro _ _
  rw [hbot, finrank_bot]
  exact ⟨fun i => i.elim0, fun i => i.elim0, linearIndependent_empty_type⟩

/-- **For a nontrivial character the four level-three inputs of `eigenSeparated_of_openInputs`
amount to one vanishing statement.** -/
theorem levelThreeVanishing_of_finite_rank (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hχ : D.chi ≠ trivialCharacter)
    (hfin3p : LocalJointFinite D hecke hhecke .plane true)
    (hfin3l : LocalJointFinite D hecke hhecke .line false)
    (hrank3p : CoordinateRankLowerBound D hecke hhecke .plane true)
    (hrank3l : CoordinateRankLowerBound D hecke hhecke .line false) :
    LevelThreeVanishing D hecke hhecke := by
  intro hne
  have hbot := coordinateImage_levelThree_eq_bot_of_nontrivial D hχ
  exact ⟨localJoint_eq_bot_of_coordinateImage_eq_bot D hecke hhecke .plane true hne hfin3p hrank3p
      hbot.1,
    localJoint_eq_bot_of_coordinateImage_eq_bot D hecke hhecke .line false hne hfin3l hrank3l
      hbot.2⟩

/-- The converse: vanishing gives the four level-three inputs. -/
theorem finite_rank_of_levelThreeVanishing (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hvan : LevelThreeVanishing D hecke hhecke) :
    (LocalJointFinite D hecke hhecke .plane true ∧ LocalJointFinite D hecke hhecke .line false) ∧
      (CoordinateRankLowerBound D hecke hhecke .plane true ∧
        CoordinateRankLowerBound D hecke hhecke .line false) := by
  refine ⟨⟨fun hne => localJointFinite_of_eq_bot D hecke hhecke .plane true (hvan hne).1 hne,
    fun hne => localJointFinite_of_eq_bot D hecke hhecke .line false (hvan hne).2 hne⟩,
    ⟨fun hne => coordinateRankLowerBound_of_eq_bot D hecke hhecke .plane true (hvan hne).1 hne,
    fun hne => coordinateRankLowerBound_of_eq_bot D hecke hhecke .line false (hvan hne).2 hne⟩⟩

/-- For a nontrivial character, `hfin3p`, `hfin3l`, `hrank3p`, `hrank3l` hold together exactly when
the level-three local joint eigenspaces vanish. -/
theorem levelThreeVanishing_iff_finite_rank (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hχ : D.chi ≠ trivialCharacter) :
    LevelThreeVanishing D hecke hhecke ↔
      ((LocalJointFinite D hecke hhecke .plane true ∧ LocalJointFinite D hecke hhecke .line false) ∧
        (CoordinateRankLowerBound D hecke hhecke .plane true ∧
          CoordinateRankLowerBound D hecke hhecke .line false)) :=
  ⟨finite_rank_of_levelThreeVanishing D hecke hhecke, fun h =>
    levelThreeVanishing_of_finite_rank D hecke hhecke hχ h.1.1 h.1.2 h.2.1 h.2.2⟩

/-! ## The assembly -/

/-- **Separation from the level-one inputs for `ConductorThree` characters and the level-three
vanishing.**  Every input is only asked for a nonzero pair, which forces `ConductorThree D.chi`. -/
theorem eigenSeparated_of_levelThreeVanishing (hn : 3 ≤ n) (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hloc1 : ConductorThree D.chi → LevelOneLocalMultiplicityOne D hecke hhecke)
    (hS1 : ConductorThree D.chi → associatePair D ≠ ⊥ → SphericalSourceConstruction D)
    (hS1L : ConductorThree D.chi → associatePair D ≠ ⊥ → SphericalSourceConstructionLine D)
    (hS2 : ConductorThree D.chi → associatePair D ≠ ⊥ → SphericalForcedByLocal D hecke hhecke)
    (hS2L : ConductorThree D.chi → associatePair D ≠ ⊥ →
      SphericalForcedByLocalLine D hecke hhecke)
    (hvan3 : LevelThreeVanishing D hecke hhecke) :
    EigenSeparated (awayThreeHeckeAlgebra D hecke) (associatePair D) := by
  by_cases hbot : associatePair D = ⊥
  · exact eigenSeparated_of_eq_bot D hecke hbot
  have hcond : ConductorThree D.chi := conductorThree_of_associatePair_ne_bot D hbot
  refine eigenSeparated_of_levelThreeCoordinate hn D hecke hhecke (fun _ => hloc1 hcond)
    (fun _ hne => hS1 hcond hne) (fun _ hne => hS1L hcond hne) (fun _ hne => hS2 hcond hne)
    (fun _ hne => hS2L hcond hne) ?_ ?_
  · intro hne
    unfold CoordinateStatement
    rw [(hvan3 hne).1]
    exact bot_le
  · intro hne
    unfold CoordinateStatement
    rw [(hvan3 hne).2]
    exact bot_le

/-- **Eigencharacter separation of the associate pair for `3 ≤ n` and `χ ≠ trivialCharacter`.**

The level-one inputs `hloc1`, `hS1`, `hS1L`, `hS2`, `hS2L` of `eigenSeparated_of_openInputs` are
only needed when the conductor of `χ` divides three (otherwise the associate pair is zero), i.e.
for the odd quadratic character of conductor three twisted by cusp forms; the inputs `hfin3p`,
`hfin3l`, `hrank3p`, `hrank3l` are used only through `levelThreeVanishing_of_finite_rank`. -/
theorem eigenSeparated_of_openInputs_nontrivial (hn : 3 ≤ n) (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hχ : D.chi ≠ trivialCharacter)
    (hloc1 : ConductorThree D.chi → LevelOneLocalMultiplicityOne D hecke hhecke)
    (hS1 : ConductorThree D.chi → associatePair D ≠ ⊥ → SphericalSourceConstruction D)
    (hS1L : ConductorThree D.chi → associatePair D ≠ ⊥ → SphericalSourceConstructionLine D)
    (hS2 : ConductorThree D.chi → associatePair D ≠ ⊥ → SphericalForcedByLocal D hecke hhecke)
    (hS2L : ConductorThree D.chi → associatePair D ≠ ⊥ →
      SphericalForcedByLocalLine D hecke hhecke)
    (hfin3p : LocalJointFinite D hecke hhecke .plane true)
    (hfin3l : LocalJointFinite D hecke hhecke .line false)
    (hrank3p : CoordinateRankLowerBound D hecke hhecke .plane true)
    (hrank3l : CoordinateRankLowerBound D hecke hhecke .line false) :
    EigenSeparated (awayThreeHeckeAlgebra D hecke) (associatePair D) :=
  eigenSeparated_of_levelThreeVanishing hn D hecke hhecke hloc1 hS1 hS1L hS2 hS2L
    (levelThreeVanishing_of_finite_rank D hecke hhecke hχ hfin3p hfin3l hrank3p hrank3l)

end TernaryPeriodPolynomials.Spectral.LevelOneNontrivial
