module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.ClassIdentity
public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.BadPlaneSupply
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.PerDatumMS
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.CuspResProj
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.ModelComparisonNeg

@[expose] public section


/-!
# CMP-8 (entry, plane half): the model's bad-plane section of an Eichler datum is the classical seed class

Comparison obligation CMP-8, plane half at the bad reference plane (level one).

For a level-one cohomological datum `M`, an Eichler input `I` of `M` and the finite spherical datum `S` of the same weight (the data of
the entry computation of Appendix C.6), the bad-plane section of the entry is
`a_pl = SphericalEntryData.badPlaneClass S I`, the class of `badPlaneWeight · planeSource`.  Proved here, with standard axioms:

* `cuspRes_plane_false_badPlane`: the weight `badPlaneWeight` does not change the coordinate at the bad plane;
  `cuspRes_plane_true_badPlane` (`Entry/CuspResProj`) says it kills the good-plane coordinate.
* `badPlane_edge`: the bad-plane binary edge of `a_pl` is `-[φ_I]`, with `φ_I` the arithmetic period cocycle of `I`.
* `badPlaneClass_seed_class`: with `f` the classical level-one cusp form of `I` (`f = cuspScalarWeightedLinear`, the scalar function of
  the Eichler vector), the restriction of the bad-plane coordinate of `a_pl` to `Λ₀⁺ = ℤ² ⋊ SL₂(ℤ)` is
  `-((n+1)/2)` times the complexified de Rham class of the reflection-invariant classical seed `ω_f + \overline{ω_{f^*}}`.

So the model's bad-plane section IS the paper's classical seed class of the form of the Eichler input, up to the uniform nonzero
scalar `-(n+1)/2` (Kostant constant `-1` of `BadPlaneEdgeExact` and the factor `(n+1)/2` of `SeedC3S4c.ClassIdentity`).  Not covered: the
line half (the good-line section against the classical line seed), the identification of `f` with the normalized eigenform
`S.form` (equal Hecke eigenvalues; multiplicity one is not formalized), and the passage from `Λ₀⁺` to the principal congruence
group `Γ(N)` of `seedBoundary`.

Formalized by Claude Sonnet 5.5.
-/


open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.IdentityPlaneHecke
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SourceSpace
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.CuspidalSpan
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

noncomputable section

namespace TernaryPeriodPolynomials.Argument.KDaggerComparison

theorem goodWeight_cuspFlag_false (s : Side) : goodWeight s (cuspFlag s false) = 0 := by
  unfold goodWeight
  rw [ite_eq_right (by rw [cuspFlag_good_iff]; simp)]

/-- **The bad-plane weight does not change the coordinate at the bad plane** (it kills the good-plane coordinate,
`Entry.cuspRes_plane_true_badPlane`). -/
theorem cuspRes_plane_false_badPlane {n : ℕ} (D : InducingData n)
    (c : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly n) (hc : IsSourceCocycle D .plane c)
    (hc' : IsSourceCocycle D .plane (fun y g => badPlaneWeight g • c y g)) :
    cuspRes n D.chi .plane false (sourceClass D .plane ⟨fun y g => badPlaneWeight g • c y g, hc'⟩) =
      cuspRes n D.chi .plane false (sourceClass D .plane ⟨c, hc⟩) := by
  have hw : ∀ (γ : rationalLevel) (x : Flags .plane),
      (fun x => 1 - goodWeight .plane x) (γ.val • x) = (fun x => 1 - goodWeight .plane x) x := by
    intro γ x
    simp only [goodWeight_invariant]
  rw [← flagProj_sourceClass D .plane (fun x => 1 - goodWeight .plane x) hw badPlaneWeight
    (fun q => badPlaneWeight_rational q) c hc hc', cuspRes_flagProj, goodWeight_cuspFlag_false]
  simp

/-- **The bad-plane edge of the plane source of an Eichler input is minus its arithmetic period class** (Kostant constant `-1`);
this is `CuspidalSpan.eichlerInput_realized` without the cutoff. -/
theorem planeSource_edge {n : ℕ} (hn : 0 < n) (hodd : Odd n) (M : CohomologicalCuspData n) (I : EichlerInput M.cusp n)
    (hs : IsSourceCocycle M.inducingData .plane
      (planeSource M.inducingData (SphericalEntryData.planeLevi (D := M.inducingData) I))) :
    edgeH2 n hn hodd (cuspRes n trivialCharacter .plane false
        (sourceClass M.inducingData .plane
          ⟨planeSource M.inducingData (SphericalEntryData.planeLevi (D := M.inducingData) I), hs⟩)) =
      -groupCohomology.H1π (arithmeticBinaryRep (n + 1) (-1))
        (I.arithmeticPeriodCocycle
          (TernaryPeriodPolynomials.AnalyticClasses.continuousStages M.inducingData)) := by
  let stages := TernaryPeriodPolynomials.AnalyticClasses.continuousStages M.inducingData
  let E : LeviCocycleData M.cusp n := LeviCocycleData.ofEichler (I.eichlerCocycle_spec stages)
  let s : sourceCocycles M.inducingData .plane :=
    ⟨planeSource M.inducingData E, hs⟩
  have hz : ∀ g h : PlaneStab,
      (evaluatedSource M.inducingData .plane s).val.val ![1, g.val, g.val * h.val]
          (QuotientGroup.mk 1) =
        ((sourceCupData E).l (g.val * h.val) - (sourceCupData E).l g.val)
          ((sourceCupData E).a g.val - (sourceCupData E).a 1) := fun g h =>
    (evaluatedSource_realizes M.inducingData .plane s ![1, g.val, g.val * h.val] 1).trans
      (sourceCupData_identity M.inducingData E rfl ![1, g.val, g.val * h.val])
  have hedge := edgeH2_cuspRes_plane_false_eq (sourceCupData E)
    (kostantLaw_of_planeRadical (lam := (sourceCupData E).lam) (fun _ _ => rfl))
    (I.arithmeticPeriodCocycle stages) (fun m => (sourceA_levi E m).symm) hn hodd
    (evaluatedSource M.inducingData .plane s) hz
  exact hedge.trans (neg_one_smul ℂ _)

/-- **The bad-plane edge of the entry section `a_pl`.** -/
theorem badPlane_edge {n : ℕ} (hn : 0 < n) (hodd : Odd n) (M : CohomologicalCuspData n)
    (S : SphericalEntryData M.inducingData) (I : EichlerInput M.cusp n) :
    edgeH2 n hn hodd (cuspRes n trivialCharacter .plane false (SphericalEntryData.badPlaneClass S I).val) =
      -groupCohomology.H1π (arithmeticBinaryRep (n + 1) (-1))
        (I.arithmeticPeriodCocycle
          (TernaryPeriodPolynomials.AnalyticClasses.continuousStages M.inducingData)) := by
  rw [SphericalEntryData.badPlaneClass_val]
  rw [cuspRes_plane_false_badPlane M.inducingData _ (planeSource_isSourceCocycle M.inducingData _ S.hχ)
    (SphericalEntryData.badPlane_isSourceCocycle S I)]
  exact planeSource_edge hn hodd M I _

open TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Spectral.ModularH2
open TernaryPeriodPolynomials.Spectral.LevelOneESDimension
open TernaryPeriodPolynomials.Spectral.LevelOneHeckeH1
open TernaryPeriodPolynomials.Spectral.LevelOneEichlerShimura
open TernaryPeriodPolynomials.Spectral.ParabolicES
open TernaryPeriodPolynomials.Spectral.PlaneCoordinates
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCoordinate
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)
open CategoryTheory

private theorem parityOf_neg_one' : (parityOf (-1)).val = 1 := by
  simp [parityOf]

/-- **A bad-plane class whose binary edge is the period class of `f` has the restriction `(n+1)/2 · [ω_f + \overline{ω_{f^*}}]`**
(the tail of `SeedC3S4c.seed_class_identity`, for an arbitrary class `b`). -/
theorem seed_class_of_edge_eq_per (k : ℕ) (f : CuspForm Lvl1 (((2 * k + 1) + 3 : ℕ) : ℤ))
    (fL : CuspForm levelOne (-2 * hw (k + 1))) (hfun : (fL : UpperHalfPlane → ℂ) = f)
    (hn : 0 < 2 * k + 1) (hodd : Odd (2 * k + 1)) (b : StratumH2 (2 * k + 1) trivialCharacter .plane)
    (hedge : edgeH2 (2 * k + 1) hn hodd (cuspRes (2 * k + 1) trivialCharacter .plane false b) =
      per (k + 1) (-1) fL) :
    plusResH2 (2 * k + 1) (ambientToGroupH2 (2 * k + 1) (cuspRes (2 * k + 1) trivialCharacter .plane false b)) =
      ((((2 * k + 1 : ℕ) : ℂ) + 1) / 2) • complexify (2 * k + 1)
        (ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty plusPlaneData.action
          (plusPlaneData.rhoR (2 * k + 1)) (reflSeedInv plusPlaneData plus_hΛ f 1)) := by
  have hw' : (((2 * k + 1) + 3 : ℕ) : ℤ) = (((2 * k + 1) + 1 : ℕ) : ℤ) + 2 := by push_cast; ring
  have hW : (((2 * k + 1) + 3 : ℕ) : ℤ) = -2 * hw (k + 1) := by simp only [hw]; push_cast; ring
  obtain ⟨y, hy, hyedge⟩ := plusEdge_resH2 (2 * k + 1) hn hodd
    (ambientToGroupH2 (2 * k + 1) (cuspRes (2 * k + 1) trivialCharacter .plane false b))
  rw [← hy]
  have he := (edgeH2_eq_full (2 * k + 1) hn hodd
    (cuspRes (2 * k + 1) trivialCharacter .plane false b)).symm
  rw [he, hedge] at hyedge
  have hpow : ((-1 : ℂ)) ^ (2 * k + 1 + 1) = 1 := by
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul]; norm_num
  refine eq_seed_of_edge f hw' hpow y (hyedge.trans ?_)
  change restriction (2 * (k + 1)) (-1) (-1) (per (k + 1) (-1) fL) = _
  rw [restriction_levelOnePeriodMap (2 * (k + 1)) (-1) (hw (k + 1)) (weight_eq_r (k + 1))
    (even_two_mul (k + 1)) (parityOf (-1)) (parityOf_sign (-1)) fL]
  rw [modularPeriod_eq, parityOf_neg_one']
  have hc : classicalBinaryCocycle fL (2 * (k + 1)) (weight_eq_r (k + 1)) (-1) =
      classicalBinaryCocycle f (2 * k + 1 + 1) hw' (-1) :=
    classicalBinaryCocycle_congr hW.symm fL f hfun _ _ _ _
  rw [hc]
  unfold periodClass periodClassRefl
  simp only [modularCocycleParity, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply,
    map_smul, map_add, pow_one]
  module

/-- **CMP-8, plane half (level one, bad reference plane).**  Let `M` be a level-one cohomological datum of odd degree `n = 2k+1`,
`S` the finite spherical datum of the entry and `I` an Eichler input.  If `f` is the classical level-one cusp form of weight `n + 3`
whose function is the scalar function of the Eichler vector (`cuspScalarWeightedLinear`), the restriction to `Λ₀⁺ = ℤ² ⋊ SL₂(ℤ)` of
the bad-plane coordinate of the entry section `a_pl = badPlaneClass S I` is `-((n+1)/2)` times the complexified de Rham class of the
classical reflection-invariant seed `ω_f + \overline{ω_{f^*}}`. -/
theorem badPlaneClass_seed_class (k : ℕ) (M : CohomologicalCuspData (2 * k + 1)) (S : SphericalEntryData M.inducingData)
    (I : EichlerInput M.cusp (2 * k + 1)) (f : CuspForm Lvl1 (((2 * k + 1) + 3 : ℕ) : ℤ))
    (fL : CuspForm levelOne (-2 * hw (k + 1)))
    (hfL : (fL : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear M.cusp I.halfWeight 1 I.vector)
    (hfun : (fL : UpperHalfPlane → ℂ) = f) :
    plusResH2 (2 * k + 1) (ambientToGroupH2 (2 * k + 1)
        (cuspRes (2 * k + 1) trivialCharacter .plane false (SphericalEntryData.badPlaneClass S I).val)) =
      -((((2 * k + 1 : ℕ) : ℂ) + 1) / 2) • complexify (2 * k + 1)
        (ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty plusPlaneData.action
          (plusPlaneData.rhoR (2 * k + 1)) (reflSeedInv plusPlaneData plus_hΛ f 1)) := by
  have hn : 0 < 2 * k + 1 := by omega
  have hodd : Odd (2 * k + 1) := ⟨k, rfl⟩
  have h1 := badPlane_edge hn hodd M S I
  rw [arithmeticPeriodCocycle_class_eq_per I _ fL hfL] at h1
  set a := (SphericalEntryData.badPlaneClass S I).val with ha
  have e1 : cuspRes (2 * k + 1) trivialCharacter .plane false (-a) =
      -(cuspRes (2 * k + 1) trivialCharacter .plane false a) := map_neg _ _
  have e2 : edgeH2 (2 * k + 1) hn hodd (-(cuspRes (2 * k + 1) trivialCharacter .plane false a)) =
      -(edgeH2 (2 * k + 1) hn hodd (cuspRes (2 * k + 1) trivialCharacter .plane false a)) := map_neg _ _
  have key : edgeH2 (2 * k + 1) hn hodd (cuspRes (2 * k + 1) trivialCharacter .plane false (-a)) =
      per (k + 1) (-1) fL := by
    rw [e1, e2, h1, neg_neg]
  have h2 := seed_class_of_edge_eq_per k f fL hfun hn hodd (-a) key
  have e3 : plusResH2 (2 * k + 1) (ambientToGroupH2 (2 * k + 1)
        (cuspRes (2 * k + 1) trivialCharacter .plane false (-a))) =
      -(plusResH2 (2 * k + 1) (ambientToGroupH2 (2 * k + 1)
        (cuspRes (2 * k + 1) trivialCharacter .plane false a))) :=
    map_neg ((plusResH2 (2 * k + 1)).comp ((ambientToGroupH2 (2 * k + 1)).comp
      (cuspRes (2 * k + 1) trivialCharacter .plane false))) a
  rw [e3] at h2
  rw [neg_smul]
  exact neg_eq_iff_eq_neg.mp h2

/-- **The classical form of the Eichler input exists** and the class identity holds for it. -/
theorem badPlaneClass_seed_class_exists (k : ℕ) (M : CohomologicalCuspData (2 * k + 1))
    (S : SphericalEntryData M.inducingData) (I : EichlerInput M.cusp (2 * k + 1)) :
    ∃ f : CuspForm Lvl1 (((2 * k + 1) + 3 : ℕ) : ℤ),
      (f : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear M.cusp I.halfWeight 1 I.vector ∧
      plusResH2 (2 * k + 1) (ambientToGroupH2 (2 * k + 1)
          (cuspRes (2 * k + 1) trivialCharacter .plane false (SphericalEntryData.badPlaneClass S I).val)) =
        -((((2 * k + 1 : ℕ) : ℂ) + 1) / 2) • complexify (2 * k + 1)
          (ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty plusPlaneData.action
            (plusPlaneData.rhoR (2 * k + 1)) (reflSeedInv plusPlaneData plus_hΛ f 1)) := by
  obtain ⟨form, hform⟩ := CuspidalSpan.EichlerInput.exists_classicalForm I M.cohomological
  have hI := I.weight
  have hhw : -2 * I.halfWeight = -2 * hw (k + 1) := by
    unfold hw
    push_cast at hI ⊢
    omega
  have hW : (((2 * k + 1) + 3 : ℕ) : ℤ) = -2 * hw (k + 1) := by simp only [hw]; push_cast; ring
  obtain ⟨fL, hfL⟩ := TernaryPeriodPolynomials.Oldform.exists_cuspForm_cast hhw form
  obtain ⟨f, hf⟩ := TernaryPeriodPolynomials.Oldform.exists_cuspForm_cast hW.symm fL
  exact ⟨f, hf.trans (hfL.trans hform), badPlaneClass_seed_class k M S I f fL (hfL.trans hform) hf.symm⟩

open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparison
open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparisonNeg
open TernaryPeriodPolynomials.Argument.LatticeCounts.AdelicValue
open TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation Matrix in
/-- **The binary section of the entry is the classical section `v_h`.**  The Eichler vector of `I` has a classical
level-one cusp form `form` (its scalar function), and the adelic section of the vector (its realization at every local element
`ι_p A` and every real element) is the classical section `v_h` built from `form` by a rational lattice reduction
(`H4`, `ModelComparisonNeg.vhModel_eq_full`).  The plane datum `f` of `badPlaneClass_seed_class` is this form. -/
theorem eichler_classical_section {n : ℕ} (M : CohomologicalCuspData n) (I : EichlerInput M.cusp n) :
    ∃ form : CuspForm levelOne (-2 * I.halfWeight),
      (form : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear M.cusp I.halfWeight 1 I.vector ∧
      ∀ (p : FinitePlace) (A : GeneralLinearGroup (Fin 2) (p.adicCompletion ℚ)) (gInf : BinaryRealGL),
        smoothReal M.cusp (M.cusp.π (atFinite (ιGL p A)) I.vector.val) (atInfinity gInf) =
          vhValueFull (-2 * I.halfWeight) form gInf (ιGL p A) := by
  obtain ⟨form, hform⟩ := CuspidalSpan.EichlerInput.exists_classicalForm I M.cohomological
  exact ⟨form, hform, fun p A gInf => vhModel_eq_full I form hform p A gInf⟩

end TernaryPeriodPolynomials.Argument.KDaggerComparison
