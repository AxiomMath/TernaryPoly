module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.BadLinePotential
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.SphericalLineSource
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.RestrictLevelThree
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.Global

@[expose] public section


/-!
# The bad-line coordinate of the line source is nonzero (spherical, trivial character)

The line source `lineSource D E` at the identity adele and rational vertices is the cup product of
the potentials `bdA E` and `bdL` (`bd_lineSource`).  Hence, for a cocycle `z` evaluating the source,
the Shapiro coordinate at the bad line `cuspFlag .line false = mk 1` is the class of a cocycle of
`ΛB` representing that cup product (`bd_represents`), which is nonzero by the edge computation
`bd_classOf_ne_zero_of_cup` as soon as the Levi cocycle `A ↦ α(A) 1` has nonzero class on the
finite-index subgroup `Γ₁'(3)` of `GL₂(ℤ)`; that follows from the nonvanishing of the period class on
`GL₂(ℤ)` by the injectivity of restriction to a finite-index subgroup in characteristic zero
(`arithmeticBinaryRep_H1π_eq_zero_of_secondRow`).  The headline statements are
`lineSource_cuspRes_badLine_ne_zero`, `lineSource_exists_cuspRes_badLine_ne_zero` and
`lineSourceConstruction_false_of_spherical`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix MvPolynomial GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.SphericalDetection.Helpers (arithmeticBinaryRep)
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCoordinate (ρn)
open TernaryPeriodPolynomials.Spectral.CuspOrbits (cuspFlag)
open TernaryPeriodPolynomials.Spectral.CuspReduction (cuspRes)
open TernaryPeriodPolynomials.LevelThree.BadLineCoordinates (ΛB)
open TernaryPeriodPolynomials.LevelThree.BadLineTransitions (Lm)
open TernaryPeriodPolynomials.Separation (sourceCoordinate sourceCoordinate_apply)
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SourceSpace
  (sourceCocycles evaluatedSource_realizes)

namespace TernaryPeriodPolynomials.SourceConstruction

/-- The real image of a rational matrix. -/
local notation "ratReal" => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)

variable {n : ℕ}

/-! ## The line source at the identity -/

theorem bd_realGroup : realGroup (rationalGroup ((1 : RationalGL3)⁻¹)) = 1 := by
  simp

theorem bd_finiteGroup :
    finiteGroup (rationalGroup ((1 : RationalGL3)⁻¹)) =
      Matrix.GeneralLinearGroup.map integralEmbedding
        (1 : Matrix.GeneralLinearGroup (Fin 3) IntegralAdeles) := by
  simp

/-- **The line source at the identity adele and rational vertices is the cup product of the
potentials of the bad line.** -/
theorem bd_lineSource (D : InducingData n) (E : LineLeviCocycleData D.cusp n)
    (hchi : D.chi = trivialCharacter) (x : Fin 3 → RationalGL3) :
    lineSource D E (fun i => ratReal (x i)) (rationalGroup ((1 : RationalGL3)⁻¹)) =
      (bdL n (x 2) - bdL n (x 1)) (bdA E (x 1) - bdA E (x 0)) := by
  have hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1 := by
    intro u
    rw [hchi]
    rfl
  unfold lineSource
  rw [lineSourceAt_integral D E hχ _ 1 bd_finiteGroup, bd_realGroup, hchi]
  simp only [inv_one, map_one, Module.End.one_apply, one_mul]
  rfl

/-- **An evaluated line source represents the cup product of the potentials on `ΛB`.** -/
theorem bd_represents (D : InducingData n) (E : LineLeviCocycleData D.cusp n)
    (hchi : D.chi = trivialCharacter)
    {z : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .line)}
    (hz : Evaluates D .line (lineSource D E) z) (g h : ΛB) :
    z.val.val ![1, g.val, g.val * h.val] (QuotientGroup.mk 1) =
      (bdL n (g.val * h.val) - bdL n g.val) (bdA E g.val - bdA E 1) :=
  (hz ![1, g.val, g.val * h.val] 1).trans
    (bd_lineSource D E hchi ![1, g.val, g.val * h.val])

/-! ## From the period class to the bad-line Levi coordinate -/

theorem bd_mem_level {m : Matrix.GeneralLinearGroup (Fin 2) ℤ}
    (h10 : ((m.val 1 0 : ℤ) : ZMod 3) = 0) (h11 : ((m.val 1 1 : ℤ) : ZMod 3) = 1) :
    m ∈ binaryArithmeticLevel := by
  rw [mem_binaryArithmeticLevel_iff]
  intro column
  fin_cases column
  · simpa using h10
  · simpa using h11

/-- **The Levi coordinates `(n + 1) α(A) 1` on `Γ₁'(3)` are not a coboundary** if the period
cocycle `φ(m) = α(m) 1` of `GL₂(ℤ)` has nonzero class. -/
theorem bd_levi_not_coboundary {σ : CuspidalRepresentation} (E : LineLeviCocycleData σ n)
    (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) 0))
    (hφ : ∀ m : Matrix.GeneralLinearGroup (Fin 2) ℤ,
      lineCocyclePhi n φ m = E.α (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) m) 1)
    (hφ0 : groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0) φ ≠ 0) :
    ¬ ∃ w : Binary.HomogeneousPoly (n + 1), ∀ A : binaryArithmeticLevel,
      ((n + 1 : ℕ) : ℂ) • (bdA E ((Lm A : ΛB) : RationalGL3) - bdA E 1) =
        binaryArithmeticRepresentation n A w - w := by
  rintro ⟨w, hw⟩
  apply hφ0
  have hc : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  refine arithmeticBinaryRep_H1π_eq_zero_of_secondRow n 0 φ
    ((((n + 1 : ℕ) : ℂ)⁻¹) • w : Binary.HomogeneousPoly (n + 1)) ?_
  intro m h10 h11
  have hm : m ∈ binaryArithmeticLevel := bd_mem_level h10 h11
  have e : bdA E ((Lm (⟨m, hm⟩ : binaryArithmeticLevel) : ΛB) : RationalGL3) =
      lineCocyclePhi n φ m := by
    rw [bdA_Lm]
    exact (hφ m).symm
  have hh : ((n + 1 : ℕ) : ℂ) • lineCocyclePhi n φ m = dlAct n m w - w := by
    have h := hw ⟨m, hm⟩
    rw [e, bdA_one, sub_zero] at h
    exact h
  have hmul : dlAct n m (((n + 1 : ℕ) : ℂ)⁻¹ • w) = ((n + 1 : ℕ) : ℂ)⁻¹ • dlAct n m w :=
    map_smul ((arithmeticBinaryRep (n + 1) 0).ρ m) ((n + 1 : ℕ) : ℂ)⁻¹ w
  have e1 : lineCocyclePhi n φ m =
      ((n + 1 : ℕ) : ℂ)⁻¹ • (((n + 1 : ℕ) : ℂ) • lineCocyclePhi n φ m) := by
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
  have key : lineCocyclePhi n φ m =
      dlAct n m (((n + 1 : ℕ) : ℂ)⁻¹ • w) - ((n + 1 : ℕ) : ℂ)⁻¹ • w := by
    exact e1.trans ((congrArg (fun x : Binary.HomogeneousPoly (n + 1) =>
      ((n + 1 : ℕ) : ℂ)⁻¹ • x) hh).trans ((smul_sub _ _ _).trans
        (congrArg (fun x : Binary.HomogeneousPoly (n + 1) =>
          x - ((n + 1 : ℕ) : ℂ)⁻¹ • w) hmul.symm)))
  exact key

/-! ## The headline: the bad-line Shapiro coordinate -/

/-- **The bad-line Shapiro coordinate of a stratum class whose values at the flag `mk 1` represent
the cup product of the potentials of the bad line is nonzero**, for the trivial character, when the
period cocycle `m ↦ α(m) 1` of `GL₂(ℤ)` in `arithmeticBinaryRep (n + 1) 0` has nonzero class. -/
theorem bd_cuspRes_ne_zero (χ : RankOneCharacter) (hχ : χ = trivialCharacter) (pos : 0 < n)
    {σ : CuspidalRepresentation} (E : LineLeviCocycleData σ n)
    (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) 0))
    (hφ : ∀ m : Matrix.GeneralLinearGroup (Fin 2) ℤ,
      lineCocyclePhi n φ m = E.α (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) m) 1)
    (hφ0 : groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0) φ ≠ 0)
    (z : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line))
    (hrep : ∀ g h : ΛB, z.val.val ![1, g.val, g.val * h.val] (QuotientGroup.mk 1) =
      (bdL n (g.val * h.val) - bdL n g.val) (bdA E g.val - bdA E 1)) :
    cuspRes n χ .line false
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line) z) ≠
        0 := by
  subst hχ
  let C : cocycles ΛB (ρn n) :=
    fixedPointCycle rationalLevel (rationalCoefficientComponent n trivialCharacter)
      (cuspFlag .line false) z
  have hne : classOf ΛB (ρn n) C ≠ 0 :=
    bd_classOf_ne_zero_of_cup pos C (bdA E) (bdL n) (fun g h => hrep g h) (bdA_radical E)
      (bdL_radical n) (bd_levi_not_coboundary E φ hφ hφ0)
  intro h0
  apply hne
  exact (TernaryPeriodPolynomials.Separation.cuspRes_classOf trivialCharacter .line
    false z).symm.trans h0

/-- **The bad-line Shapiro coordinate of the line source is nonzero**, provided the period cocycle
`m ↦ α(m) 1` of `GL₂(ℤ)` in `arithmeticBinaryRep (n + 1) 0` has nonzero class. -/
theorem lineSource_cuspRes_badLine_ne_zero (D : InducingData n)
    (E : LineLeviCocycleData D.cusp n) (hchi : D.chi = trivialCharacter) (pos : 0 < n)
    (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) 0))
    (hφ : ∀ m : Matrix.GeneralLinearGroup (Fin 2) ℤ,
      lineCocyclePhi n φ m = E.α (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) m) 1)
    (hφ0 : groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0) φ ≠ 0)
    {z : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .line)}
    (hz : Evaluates D .line (lineSource D E) z) :
    cuspRes n D.chi .line false
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n D.chi) .line) z) ≠ 0 :=
  bd_cuspRes_ne_zero D.chi hchi pos E φ hφ hφ0 z (bd_represents D E hchi hz)

/-- **Unconditional existence of the Levi cocycle data with nonzero bad-line coordinate**
(spherical cuspidal part, trivial character, odd degree). -/
theorem lineSource_exists_cuspRes_badLine_ne_zero (D : InducingData n)
    (spherical : SphericalCusp D.cusp) (hchi : D.chi = trivialCharacter) (odd : Odd n) :
    ∃ E : LineLeviCocycleData D.cusp n,
      ∀ {z : cocycles rationalLevel
          (flagRepresentation (rationalCoefficientComponent n D.chi) .line)},
        Evaluates D .line (lineSource D E) z →
          cuspRes n D.chi .line false (classOf rationalLevel
            (flagRepresentation (rationalCoefficientComponent n D.chi) .line) z) ≠ 0 := by
  obtain ⟨E, φ, hφ, hφ0⟩ := exists_lineLeviCocycleData_period_ne_zero D spherical odd
  refine ⟨E, fun {z} hz => ?_⟩
  exact lineSource_cuspRes_badLine_ne_zero D E hchi odd.pos φ (fun m => hφ m) hφ0 hz

/-- **The bad-line line source construction for the trivial character**: a spherical `D` with
trivial character has a source cocycle with nonzero Shapiro coordinate at the bad line. -/
theorem lineSourceConstruction_false_of_spherical (D : InducingData n)
    (hchi : D.chi = trivialCharacter) (hsph : SphericalCusp D.cusp) :
    ∃ c : sourceCocycles D .line, sourceCoordinate D .line false c ≠ 0 := by
  have odd : Odd n :=
    TernaryPeriodPolynomials.LevelOneCohomologicalParity.Helpers.cohomological_spherical_odd
      n D.cusp D.cohomological hsph
  obtain ⟨E, hE⟩ := lineSource_exists_cuspRes_badLine_ne_zero D hsph hchi odd
  let c : sourceCocycles D .line :=
    ⟨lineSource D E, lineSource_isSourceCocycle D E (integral_character_trivial_of_eq D hchi)⟩
  refine ⟨c, ?_⟩
  rw [sourceCoordinate_apply]
  exact hE (evaluatedSource_realizes D .line c)

end TernaryPeriodPolynomials.SourceConstruction
