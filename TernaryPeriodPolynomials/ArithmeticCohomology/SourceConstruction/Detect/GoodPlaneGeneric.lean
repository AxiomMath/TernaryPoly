module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.GoodPlaneSource
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.SourceRealizationPlaneLevel

@[expose] public section


/-!
# The good-plane detection for an arbitrary Levi cocycle

Everything about the Levi cocycle that the good-plane detection uses is the cocycle law and the
vanishing on the orthogonal group.  `PlaneLeviCocycle n` packages exactly these two properties of a
map `α : GL₂(ℝ) → (GL₂(𝔸) → Sym^{n+1})`; every `LeviCocycleData` (spherical, `GL₂(ẑ)`-fixed
vectors) gives one (`LeviCocycleData.toPlaneLeviCocycle`), and so does any other Levi cocycle with
the same two laws (for instance the level-three Levi cocycle).

* `gpCupOf A : GoodPlaneCupData n` has the potentials `a y = N • α (iwA y) (atInfinity δ)`,
  `l y = planeRadical (iwP y)` and the Kostant law with the constant `-1` (`gpCupOf_kostant`); its
  Levi potential is `Φ (a (Pg 0 m 1) - a 1) = α (m δ) 1 - α δ 1` (`gpCupOf_leviDelta`), the cocycle
  law for `δ κ(m) = m δ`.  `gpCup E = gpCupOf E.toPlaneLeviCocycle` (`gpCup_eq_gpCupOf`).
* `identityCupOf χ A z` is the identity-plane value of the plane source at the vertices `z`.  At the
  good-plane cusp point `rationalGroup (planeFrameQ true)⁻¹` a plane source whose values are
  `ρ(W)` of `identityCupOf` at the vertices `W⁻¹ x` has the cup form `identityCupOf_goodPlane`
  (the Levi `W⁻¹ gF = diag(1, 3, 1) = planeLevi δ 1` moves into the argument of `α`), hence nonzero
  good-plane coordinate (`cuspRes_plane_true_ne_zero_of_identityCup`) as soon as the Levi potential
  `m ↦ α (m δ) 1 - α δ 1` is not a crossed coboundary.
* `notCoboundary_of_period`: if `α δ` does not see the real integral translate `atInfinity m`, this
  is the nonvanishing of the period class of `m ↦ α m 1` restricted to `Γ₁'(3)`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.LevelThree.GoodPlaneFrame
open TernaryPeriodPolynomials.LevelThree.GoodPlaneModel (goodPlaneExtension)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge2 (Phi)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.Spectral.CuspReduction (cuspRes)
open TernaryPeriodPolynomials.Separation (planeFrameQ)
open TernaryPeriodPolynomials.Spectral.CuspOrbits (goodPlaneFrame)
open TernaryPeriodPolynomials.BoundaryFiniteness.IntegralFlags (rational)

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

/-- The real image of a rational matrix. -/
local notation "ratReal" => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)

/-- **A Levi cocycle**: the cocycle law of the cohomological action and the vanishing on the
orthogonal group are all that the good-plane detection uses. -/
structure PlaneLeviCocycle (n : ℕ) where
  /-- The cocycle. -/
  α : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)
  /-- The cocycle law. -/
  cocycle : ∀ g h x, α (g * h) x = α g x + binaryCohomologicalAction n g (α h) x
  /-- The cocycle vanishes on the orthogonal group. -/
  orth : ∀ k : BinaryRealGL, k.val.transpose * k.val = 1 → ∀ x, α k x = 0

/-- Every `LeviCocycleData` is a Levi cocycle. -/
def LeviCocycleData.toPlaneLeviCocycle {σ : CuspidalRepresentation} {n : ℕ}
    (E : LeviCocycleData σ n) : PlaneLeviCocycle n :=
  ⟨E.α, E.cocycle, E.orth⟩

section Generic

variable {n : ℕ}

/-! ## Generic copies of the algebra of the Levi cocycle -/

theorem plc_alpha_one (A : PlaneLeviCocycle n) (x : BinaryAdelicGL) : A.α 1 x = 0 :=
  A.orth 1 (by simp) x

theorem plc_alpha_iwA_one (A : PlaneLeviCocycle n) : A.α (iwA (1 : RealGL3)) = fun _ => 0 :=
  funext fun x => by
    rw [iwA_one]
    exact plc_alpha_one A x

/-- **The Levi cocycle along the Iwasawa factor.** -/
theorem plc_alpha_iwA_mul (A : PlaneLeviCocycle n) (p : planeParabolic ℝ) (y : RealGL3)
    (x : BinaryAdelicGL) :
    A.α (iwA (p.1 * y)) x =
      A.α (leviBlock p) x + binaryCohomologicalAction n (leviBlock p) (A.α (iwA y)) x := by
  obtain ⟨k, hk, he⟩ := leviBlock_iwP_mul p y
  have h1 : A.α (iwA (p.1 * y) * k) x = A.α (iwA (p.1 * y)) x := by
    rw [A.cocycle]
    have h0 : A.α k = fun _ => 0 := funext (A.orth k hk)
    rw [h0]
    simp [binaryCohomologicalAction]
  rw [← h1, he, A.cocycle]

theorem plc_alpha_radical (A : PlaneLeviCocycle n) (r : RadicalLattice) (x : BinaryAdelicGL) :
    A.α (iwA (radicalUnipotent r).1) x = 0 := by
  have h := plc_alpha_iwA_mul A (radicalUnipotent r) 1 x
  rw [mul_one] at h
  have hl : leviBlock (radicalUnipotent r) = 1 := leviBlock_planeUnipotent _ _
  rw [h, hl, plc_alpha_iwA_one A, plc_alpha_one A]
  simp [binaryCohomologicalAction]

theorem plc_alpha_levi (A : PlaneLeviCocycle n) (B : BinaryRealGL) (x : BinaryAdelicGL) :
    A.α (iwA (gpLevi B).1) x = A.α B x := by
  have h := plc_alpha_iwA_mul A (gpLevi B) 1 x
  rw [mul_one] at h
  have hl : leviBlock (gpLevi B) = B := leviBlock_planeLevi B 1
  rw [h, hl, plc_alpha_iwA_one A]
  simp [binaryCohomologicalAction]

/-- **The transformation law of the differenced potentials** under the plane parabolic. -/
theorem plc_planeCore (χ : RankOneCharacter) (hc : ∀ g : RealGL3, componentCharacter χ g = 1)
    (A : PlaneLeviCocycle n) (p : planeParabolic ℝ) (u : Fin 3 → RealGL3) (t : BinaryAdelicGL)
    (c : ℂ) :
    (planeRadical n χ (iwP (p.1 * u 2)) - planeRadical n χ (iwP (p.1 * u 1)))
        (c • (A.α (iwA (p.1 * u 1)) t - A.α (iwA (p.1 * u 0)) t)) =
      realCoefficientComponent n χ p.1
        ((c * normPower (GeneralLinearGroup.det (atInfinity (leviBlock p))) (((n : ℂ) + 3) / 2)) •
          (planeRadical n χ (iwP (u 2)) - planeRadical n χ (iwP (u 1)))
            (A.α (iwA (u 1)) (t * atInfinity (leviBlock p)) -
              A.α (iwA (u 0)) (t * atInfinity (leviBlock p)))) := by
  have hdiff : A.α (iwA (p.1 * u 1)) t - A.α (iwA (p.1 * u 0)) t =
      normPower (GeneralLinearGroup.det (atInfinity (leviBlock p))) (((n : ℂ) + 3) / 2) •
        binaryCoefficient n (leviBlock p)
          (A.α (iwA (u 1)) (t * atInfinity (leviBlock p)) -
            A.α (iwA (u 0)) (t * atInfinity (leviBlock p))) := by
    rw [plc_alpha_iwA_mul A p (u 1) t, plc_alpha_iwA_mul A p (u 0) t]
    simp only [binaryCohomologicalAction, map_sub, smul_sub]
    abel
  have hstar : leviStar χ (n + 1) p⁻¹
      (c • normPower (GeneralLinearGroup.det (atInfinity (leviBlock p))) (((n : ℂ) + 3) / 2) •
        binaryCoefficient n (leviBlock p)
          (A.α (iwA (u 1)) (t * atInfinity (leviBlock p)) -
            A.α (iwA (u 0)) (t * atInfinity (leviBlock p)))) =
      (c * normPower (GeneralLinearGroup.det (atInfinity (leviBlock p))) (((n : ℂ) + 3) / 2)) •
        (A.α (iwA (u 1)) (t * atInfinity (leviBlock p)) -
          A.α (iwA (u 0)) (t * atInfinity (leviBlock p))) := by
    rw [map_smul, map_smul, leviStar_binaryCoefficient χ hc, smul_smul]
  rw [hdiff, LinearMap.sub_apply, planeRadical_iwP_mul χ p (u 2),
    planeRadical_iwP_mul χ p (u 1), hstar]
  simp only [map_smul, map_sub, LinearMap.sub_apply, smul_sub]
  abel

/-! ## The generic potentials -/

/-- **The potentials of the good plane for an arbitrary Levi cocycle.** -/
def gpCupOf (A : PlaneLeviCocycle n) : GoodPlaneCupData n where
  a y := gpN n • A.α (iwA (ratReal y)) (atInfinity gpDelta)
  l y := planeRadical n trivialCharacter (iwP (ratReal y))
  lam r := planeRadical n trivialCharacter (radicalUnipotent r)
  a_radical r := by
    show gpN n • A.α (iwA (ratReal (goodPlaneExtension.inl r).val)) (atInfinity gpDelta) =
      gpN n • A.α (iwA (ratReal (1 : RationalGL3))) (atInfinity gpDelta)
    rw [gp_ratReal_radInc r, plc_alpha_radical A r, ratReal_one, iwA_one, plc_alpha_one A]
  l_radical r g Q := by
    have hp : ratReal ((goodPlaneExtension.inl r).val * g) =
        (radicalUnipotent r).1 * ratReal g := by
      rw [map_mul, gp_ratReal_radInc r]
    show planeRadical n trivialCharacter (iwP (ratReal ((goodPlaneExtension.inl r).val * g))) Q =
      planeRadical n trivialCharacter (radicalUnipotent r) Q +
        realCoefficientComponent n trivialCharacter (ratReal (goodPlaneExtension.inl r).val)
          (planeRadical n trivialCharacter (iwP (ratReal g)) Q)
    rw [hp, gp_ratReal_radInc r,
      planeRadical_iwP_mul trivialCharacter (radicalUnipotent r) (ratReal g) Q,
      leviStar_radical_inv]

/-- The spherical potentials are the generic potentials of the underlying Levi cocycle. -/
theorem gpCup_eq_gpCupOf {σ : CuspidalRepresentation} (E : LeviCocycleData σ n) :
    gpCup E = gpCupOf E.toPlaneLeviCocycle :=
  rfl

/-- **The Kostant law of the generic potentials**, with the constant `-1`. -/
theorem gpCupOf_kostant (A : PlaneLeviCocycle n) : KostantLaw n (gpCupOf A).lam (-1) :=
  kostantLaw_of_planeRadical (fun _ _ => rfl)

/-- **The Levi potential of the generic potentials**: the cocycle law for `δ κ(m) = m δ`,
`Φ (a (Pg 0 m 1) - a 1) = α (m δ) 1 - α δ 1`. -/
theorem gpCupOf_leviDelta (A : PlaneLeviCocycle n) (m : binaryArithmeticLevel) :
    (gpCupOf A).leviDelta m = A.α (gpMu m * gpDelta) 1 - A.α gpDelta 1 := by
  have h1 : ratReal (Pg 0 m 1) = (gpLevi (gpKappa m)).1 := gp_ratReal_Pg m
  have e : (gpCupOf A).leviDelta m = Phi n (gpN n • A.α (gpKappa m) (atInfinity gpDelta)) := by
    show Phi n (gpN n • A.α (iwA (ratReal (Pg 0 m 1))) (atInfinity gpDelta) -
      gpN n • A.α (iwA (ratReal (1 : RationalGL3))) (atInfinity gpDelta)) = _
    rw [h1, plc_alpha_levi A, ratReal_one, iwA_one, plc_alpha_one A, smul_zero, sub_zero]
  rw [e]
  have c1 := A.cocycle gpDelta (gpKappa m) 1
  rw [gp_delta_comm m] at c1
  have e1 : binaryCohomologicalAction n gpDelta (A.α (gpKappa m)) 1 =
      Phi n (gpN n • A.α (gpKappa m) (atInfinity gpDelta)) := by
    unfold binaryCohomologicalAction
    rw [one_mul, binaryCoefficient_gpDelta, map_smul]
  rw [e1] at c1
  exact eq_sub_of_add_eq' c1.symm

/-- **Not a crossed coboundary**, from the period class: if `α δ` does not see the real integral
translates `atInfinity m` (automorphy and `GL₂(ẑ)`-invariance), the Levi potential
`m ↦ α (m δ) 1 - α δ 1` is a coboundary only if the period cocycle `m ↦ α m 1` is one on
`Γ₁'(3)`. -/
theorem notCoboundary_of_period (A : PlaneLeviCocycle n)
    (hlev : ∀ m : binaryArithmeticLevel, A.α gpDelta (atInfinity (gpMu m)) = A.α gpDelta 1)
    (hP : ¬ ∃ w : Binary.HomogeneousPoly (n + 1), ∀ m : binaryArithmeticLevel,
      A.α (gpMu m) 1 = levelRep (n + 1) (-1) m w - w) :
    ¬ ∃ w : Binary.HomogeneousPoly (n + 1), ∀ m : binaryArithmeticLevel,
      A.α (gpMu m * gpDelta) 1 - A.α gpDelta 1 = levelRep (n + 1) (-1) m w - w := by
  rintro ⟨w, hw⟩
  refine hP ⟨w - A.α gpDelta 1, fun m => ?_⟩
  have c2 := A.cocycle (gpMu m) gpDelta 1
  have e2 : binaryCohomologicalAction n (gpMu m) (A.α gpDelta) 1 =
      levelRep (n + 1) (-1) m (A.α gpDelta 1) := by
    unfold binaryCohomologicalAction
    rw [gp_normPower_int m.val, one_smul, one_mul, hlev m, binaryCoefficient_gpMu]
  rw [e2] at c2
  have h := hw m
  rw [c2] at h
  rw [map_sub]
  refine (eq_sub_of_add_eq (sub_eq_iff_eq_add.mp h)).trans ?_
  abel

/-! ## The identity-plane value at the good-plane cusp point -/

/-- **The identity-plane value of the plane source at the vertices `z`**: the difference of the
radicals of the Iwasawa factors of the vertices applied to the difference of the Levi cocycles of
their `GL₂` blocks at the trivial `GL₂` adele. -/
def identityCupOf (χ : RankOneCharacter) (A : PlaneLeviCocycle n) (z : Fin 3 → RealGL3) :
    HomogeneousPoly n :=
  (planeRadical n χ (iwP (z 2)) - planeRadical n χ (iwP (z 1)))
    (A.α (iwA (z 1)) 1 - A.α (iwA (z 0)) 1)

/-- `W · diag(1, 3, 1) = gF` for the real image `W` of the good-plane frame. -/
theorem gp_frame_real :
    ratReal (rational goodPlaneFrame) * (gpLevi gpDelta).1 = ratReal gF := by
  have h : (gpLevi gpDelta).1 = ratReal ((rational goodPlaneFrame)⁻¹ * gF) := gp_frame_mul.symm
  rw [h, ← map_mul, mul_inv_cancel_left]

/-- **The identity-plane value at the good-plane cusp point is the cup chain of the generic
potentials**: for rational `y`, the `ρ(W)`-translate of `identityCupOf` at the vertices
`W⁻¹ (gF y_i)`, `W⁻¹ gF = diag(1, 3, 1)`, is the `ρ(gF)`-translate of the cup chain of `gpCupOf A`. -/
theorem identityCupOf_goodPlane (χ : RankOneCharacter) (hχ : χ = trivialCharacter)
    (A : PlaneLeviCocycle n) (y : Fin 3 → RationalGL3) :
    realCoefficientComponent n χ (ratReal (planeFrameQ true))
        (identityCupOf χ A (fun i => ratReal ((planeFrameQ true)⁻¹ * (gF * y i)))) =
      rationalCoefficientComponent n χ gF
        (((gpCupOf A).l (y 2) - (gpCupOf A).l (y 1))
          ((gpCupOf A).a (y 1) - (gpCupOf A).a (y 0))) := by
  subst hχ
  have hc : ∀ g : RealGL3, componentCharacter trivialCharacter g = 1 :=
    componentCharacter_eq_one_of_integral trivialCharacter (fun u => rfl)
  have hy : (fun i => ratReal ((planeFrameQ true)⁻¹ * (gF * y i))) =
      fun i => (gpLevi gpDelta).1 * ratReal (y i) := by
    funext i
    have e : ratReal ((rational goodPlaneFrame)⁻¹ * (gF * y i)) =
        ratReal ((rational goodPlaneFrame)⁻¹ * gF) * ratReal (y i) := by
      rw [← mul_assoc]
      exact map_mul (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)) _ _
    exact e.trans (congrArg (fun q => q * ratReal (y i)) gp_frame_mul)
  have hl : leviBlock (gpLevi gpDelta) = gpDelta := leviBlock_planeLevi gpDelta 1
  have h2 := plc_planeCore trivialCharacter hc A (gpLevi gpDelta) (fun i => ratReal (y i)) 1 1
  simp only [hl, one_smul, one_mul] at h2
  have hR : (planeRadical n trivialCharacter (iwP (ratReal (y 2))) -
        planeRadical n trivialCharacter (iwP (ratReal (y 1))))
      (gpN n • A.α (iwA (ratReal (y 1))) (atInfinity gpDelta) -
        gpN n • A.α (iwA (ratReal (y 0))) (atInfinity gpDelta)) =
      gpN n • ((planeRadical n trivialCharacter (iwP (ratReal (y 2))) -
          planeRadical n trivialCharacter (iwP (ratReal (y 1))))
        (A.α (iwA (ratReal (y 1))) (atInfinity gpDelta) -
          A.α (iwA (ratReal (y 0))) (atInfinity gpDelta))) := by
    exact (((map_smul (planeRadical n trivialCharacter (iwP (ratReal (y 2))) -
        planeRadical n trivialCharacter (iwP (ratReal (y 1)))) (gpN n)
        (A.α (iwA (ratReal (y 1))) (atInfinity gpDelta) -
          A.α (iwA (ratReal (y 0))) (atInfinity gpDelta))).symm).trans
      (congrArg (planeRadical n trivialCharacter (iwP (ratReal (y 2))) -
        planeRadical n trivialCharacter (iwP (ratReal (y 1))))
        (smul_sub (gpN n) (A.α (iwA (ratReal (y 1))) (atInfinity gpDelta))
          (A.α (iwA (ratReal (y 0))) (atInfinity gpDelta))))).symm
  have e0 : identityCupOf trivialCharacter A (fun i => (gpLevi gpDelta).1 * ratReal (y i)) =
      (planeRadical n trivialCharacter (iwP ((gpLevi gpDelta).1 * ratReal (y 2))) -
          planeRadical n trivialCharacter (iwP ((gpLevi gpDelta).1 * ratReal (y 1))))
        (A.α (iwA ((gpLevi gpDelta).1 * ratReal (y 1))) 1 -
          A.α (iwA ((gpLevi gpDelta).1 * ratReal (y 0))) 1) := rfl
  have e3 : rationalCoefficientComponent n trivialCharacter gF
      (((gpCupOf A).l (y 2) - (gpCupOf A).l (y 1))
        ((gpCupOf A).a (y 1) - (gpCupOf A).a (y 0))) =
      realCoefficientComponent n trivialCharacter (ratReal gF)
        ((planeRadical n trivialCharacter (iwP (ratReal (y 2))) -
            planeRadical n trivialCharacter (iwP (ratReal (y 1))))
          (gpN n • A.α (iwA (ratReal (y 1))) (atInfinity gpDelta) -
            gpN n • A.α (iwA (ratReal (y 0))) (atInfinity gpDelta))) := rfl
  have hf : ratReal (planeFrameQ true) * (gpLevi gpDelta).1 = ratReal gF := gp_frame_real
  rw [hy, e0, e3, h2, hR, ← Module.End.mul_apply, ← map_mul, hf]

end Generic

/-! ## The export -/

/-- **The good-plane coordinate of a source of identity-cup shape is nonzero.**  The source has, at
the good-plane cusp point and on rational vertices `x`, the value `ρ(W)` of the identity-plane value
of a Levi cocycle `A` at the vertices `W⁻¹ x`; the Levi potential `m ↦ α (m δ) 1 - α δ 1` is not a
crossed coboundary of `levelRep (n + 1) (-1)`. -/
theorem cuspRes_plane_true_ne_zero_of_identityCup {n : ℕ} (E : InducingData n)
    (hχ : E.chi = trivialCharacter) (hn : 0 < n) (A : PlaneLeviCocycle n)
    (hN : ¬ ∃ w : Binary.HomogeneousPoly (n + 1), ∀ m : binaryArithmeticLevel,
      A.α (gpMu m * gpDelta) 1 - A.α gpDelta 1 = levelRep (n + 1) (-1) m w - w)
    {source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly n}
    {z : cocycles rationalLevel
      (flagRepresentation (rationalCoefficientComponent n E.chi) .plane)}
    (hz : Evaluates E .plane source z)
    (hsource : ∀ x : Fin 3 → RationalGL3,
      source (fun i => ratReal (x i)) (rationalGroup (planeFrameQ true)⁻¹) =
        realCoefficientComponent n E.chi (ratReal (planeFrameQ true))
          (identityCupOf E.chi A (fun i => ratReal ((planeFrameQ true)⁻¹ * x i)))) :
    cuspRes n E.chi .plane true
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n E.chi) .plane)
        z) ≠ 0 := by
  have hN' : (gpCupOf A).NotCoboundary := by
    intro hex
    obtain ⟨w, hw⟩ := hex
    exact hN ⟨w, fun m => (gpCupOf_leviDelta A m).symm.trans (hw m)⟩
  exact cuspRes_plane_true_ne_zero_of_evaluates E hχ hn (gpCupOf A) (gpCupOf_kostant A)
    (neg_ne_zero.mpr one_ne_zero) hN' hz
    (fun y => (hsource (fun i => gF * y i)).trans (identityCupOf_goodPlane E.chi hχ A y))

end TernaryPeriodPolynomials.SourceConstruction
