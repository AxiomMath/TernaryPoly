module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.GoodPlaneCell
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Plane.SourceFinal

@[expose] public section


/-!
# The source cocycle at the good plane: definitions, finite laws and real laws

This is the good-plane analogue of the identity-plane source `planeSource`
(`SourceConstruction.PlaneSource*`).  The plan, by SC file:

* `PlaneSourceData`: the datum `LeviCocycleData` has a field `spherical`; here
  `LevelLeviCocycleData` has the same fields with `spherical` replaced by `level` (the Levi
  cocycle's smooth lifts lie in `levelThreeValues`).  The finite part `cFin`, `bFin`
  (from `finitePlaneVector`) is replaced by `gpsF`, `gpsB` (from `goodPlaneScalar`, `goodPlaneBlock`
  of the good-plane cell, with the same exponents `a = 0`, `b = (n + 3) / 2`).
  `goodPlaneSourceAt`, `goodPlaneSource` are SC's formula with these.
* `PlaneSourceFinite`: the finite transformation laws `gp_twist_left` (left `P_plane(𝔸_f)`),
  `gp_twist_level` (right finite level) are proved from `goodPlaneVector_mul`,
  `goodPlaneVector_mul_level`; new: `gp_twist_frame`, at an adele whose finite part is the good
  plane frame the finite twist disappears (`goodPlaneVector_frame`).
* `PlaneSourceReal`: the real law (`alpha_iwA_mul`, `planeCore`) mentions the datum, so
  it is restated here for `LevelLeviCocycleData` (`gp_alpha_iwA_mul`, `gpCore`, `gpCore_w`).
* `GoodPlaneSourceAlgebra` / `GoodPlaneSourceInduced` / `GoodPlaneSourceCusp` (other files) port
  `PlaneSourceAlgebra`, `PlaneSourceLaws`, `PlaneSourceVector`, `PlaneSourceInduced`,
  `PlaneSourceIdentity`.  Everything independent of the datum (radical, Iwasawa, analyticity
  `radicalAnalytic`, `coefficientAnalytic`, `radKernel`, cup algebra) is imported from SC.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.MultiplicityOne (levelThreeValues)

namespace TernaryPeriodPolynomials.LevelThreeSource

/-- The `O(2)`-normalized analytic Levi cocycle of a cuspidal representation whose smooth lifts
have values in the level-three vectors (the level-three counterpart of SC's `LeviCocycleData`). -/
structure LevelLeviCocycleData (σ : CuspidalRepresentation) (n : ℕ) where
  α : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)
  cocycle : ∀ g h x, α (g * h) x = α g x + binaryCohomologicalAction n g (α h) x
  orth : ∀ k : BinaryRealGL, k.val.transpose * k.val = 1 → ∀ x, α k x = 0
  lift : (Fin 2 →₀ ℕ) → BinaryRealGL → σ.smooth
  lift_realize : ∀ μ g A, σ.realize (lift μ g) A = (α g A).val.coeff μ
  lift_smooth : ∀ μ, Smooth (fun x : Fin 1 → BinaryRealGL => (lift μ (x 0)).val)
  scalar_smooth : ∀ μ A, Smooth (fun x : Fin 1 → BinaryRealGL => (α (x 0) A).val.coeff μ)
  level : ∀ μ g, (lift μ g).val ∈ levelThreeValues σ

section Defs

variable {n : ℕ}

/-- The finite scalar factor of the good-plane cell at an adelic matrix. -/
def gpsF (D : InducingData n) (g : AdelicGL) : ℂ :=
  goodPlaneScalar D.chi 0 (((n : ℂ) + 3) / 2) (finiteGroup g)

/-- The finite `GL₂` translation of the good-plane cell at an adelic matrix. -/
def gpsB (g : AdelicGL) : BinaryAdelicGL := atFinite (goodPlaneBlock (finiteGroup g))

/-- **The good-plane source cochain**, at the `GL₂` adele `x`. -/
def goodPlaneSourceAt (D : InducingData n) (E : LevelLeviCocycleData D.cusp n)
    (y : Fin 3 → RealGL3) (g : AdelicGL) (x : BinaryAdelicGL) : HomogeneousPoly n :=
  realCoefficientComponent n D.chi (realGroup g)⁻¹
    ((planeRadical n D.chi (iwP (realGroup g * y 2)) -
        planeRadical n D.chi (iwP (realGroup g * y 1)))
      (gpsF D g • (E.α (iwA (realGroup g * y 1)) (x * gpsB g) -
        E.α (iwA (realGroup g * y 0)) (x * gpsB g))))

/-- **The good-plane source cocycle.** -/
def goodPlaneSource (D : InducingData n) (E : LevelLeviCocycleData D.cusp n)
    (y : Fin 3 → RealGL3) (g : AdelicGL) : HomogeneousPoly n :=
  goodPlaneSourceAt D E y g 1

end Defs

/-! ## The finite twist -/

section Twist

variable {n : ℕ}

theorem gp_rz_lift {σ : CuspidalRepresentation} (E : LevelLeviCocycleData σ n) (ν : Fin 2 →₀ ℕ)
    (h : BinaryRealGL) (x : BinaryAdelicGL) :
    rz σ (E.lift ν h).val x = (E.α h x).val.coeff ν := by
  rw [rz_of_mem (E.lift ν h).property]
  exact E.lift_realize ν h x

theorem rz_goodPlaneVector {σ : CuspidalRepresentation} (χ : RankOneCharacter) (a b : ℂ)
    (g : FiniteGL) {v : σ.H} (hv : v ∈ σ.smooth) (x : BinaryAdelicGL) :
    rz σ (goodPlaneVector σ χ a b g v) x =
      goodPlaneScalar χ a b g * rz σ v (x * atFinite (goodPlaneBlock g)) := by
  rw [goodPlaneVector_eq_smul, rz_smul (σ.smooth_stable _ _ hv), rz_pi hv]

theorem gp_twist_coeff (D : InducingData n) (E : LevelLeviCocycleData D.cusp n) (g : AdelicGL)
    (h : BinaryRealGL) (x : BinaryAdelicGL) (ν : Fin 2 →₀ ℕ) :
    gpsF D g * (E.α h (x * gpsB g)).val.coeff ν =
      rz D.cusp (goodPlaneVector D.cusp D.chi 0 (((n : ℂ) + 3) / 2) (finiteGroup g)
        (E.lift ν h).val) x := by
  unfold gpsF gpsB
  rw [rz_goodPlaneVector D.chi 0 (((n : ℂ) + 3) / 2) (finiteGroup g) (E.lift ν h).property x,
    gp_rz_lift]

/-- **Left equivariance of the finite twist** under the finite plane parabolic. -/
theorem gp_twist_left (D : InducingData n) (E : LevelLeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (g g' : AdelicGL) (f : FiniteGL) (hf : f ∈ planeParabolic FiniteAdeles)
    (hfin : finiteGroup g' = f * finiteGroup g) (h : BinaryRealGL) (x : BinaryAdelicGL) :
    gpsF D g' • E.α h (x * gpsB g') =
      finitePlaneFactor D.chi 0 (((n : ℂ) + 3) / 2) f hf •
        (gpsF D g • E.α h (x * atFinite (planeBlockGL f hf) * gpsB g)) := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro ν
  simp only [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul]
  have hv : (E.lift ν h).val ∈ D.cusp.smooth := (E.lift ν h).property
  have hvf := goodPlaneVector_smooth (σ := D.cusp) D.chi 0 (((n : ℂ) + 3) / 2) (finiteGroup g) hv
  have e1 := gp_twist_coeff D E g' h x ν
  have e2 := gp_twist_coeff D E g h (x * atFinite (planeBlockGL f hf)) ν
  have e3 : rz D.cusp (goodPlaneVector D.cusp D.chi 0 (((n : ℂ) + 3) / 2) (finiteGroup g')
        (E.lift ν h).val) x =
      finitePlaneFactor D.chi 0 (((n : ℂ) + 3) / 2) f hf *
        rz D.cusp (goodPlaneVector D.cusp D.chi 0 (((n : ℂ) + 3) / 2) (finiteGroup g)
          (E.lift ν h).val) (x * atFinite (planeBlockGL f hf)) := by
    rw [hfin, goodPlaneVector_mul D.chi 0 (((n : ℂ) + 3) / 2) hχ (E.level ν h) hf (finiteGroup g),
      rz_smul (D.cusp.smooth_stable _ _ hvf), rz_pi hvf]
  rw [e1, e2, e3]

/-- **Right invariance of the finite twist** under the finite level. -/
theorem gp_twist_level (D : InducingData n) (E : LevelLeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (g : AdelicGL) (k : finiteLevel) (h : BinaryRealGL) (x : BinaryAdelicGL) :
    gpsF D (g * atFinite k.val) • E.α h (x * gpsB (g * atFinite k.val)) =
      gpsF D g • E.α h (x * gpsB g) := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro ν
  simp only [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul]
  rw [gp_twist_coeff D E (g * atFinite k.val) h x ν, gp_twist_coeff D E g h x ν,
    finiteGroup_mul_atFinite,
    goodPlaneVector_mul_level D.chi 0 (((n : ℂ) + 3) / 2) hχ (E.level ν h) (finiteGroup g) k]

/-- **At the good-plane frame the finite twist disappears.** -/
theorem gp_twist_frame (D : InducingData n) (E : LevelLeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (g : AdelicGL) (hg : finiteGroup g = goodPlaneFrameF) (h : BinaryRealGL)
    (x : BinaryAdelicGL) :
    gpsF D g • E.α h (x * gpsB g) = E.α h x := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro ν
  simp only [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul]
  rw [gp_twist_coeff D E g h x ν, hg,
    goodPlaneVector_frame D.chi 0 (((n : ℂ) + 3) / 2) hχ (E.level ν h), gp_rz_lift]

end Twist

/-! ## The real law of the differenced potentials -/

section Real

variable {n : ℕ}

/-- **The Levi cocycle along the Iwasawa factor.** -/
theorem gp_alpha_iwA_mul {σ : CuspidalRepresentation} (E : LevelLeviCocycleData σ n)
    (p : planeParabolic ℝ) (y : RealGL3) (x : BinaryAdelicGL) :
    E.α (iwA (p.1 * y)) x =
      E.α (leviBlock p) x + binaryCohomologicalAction n (leviBlock p) (E.α (iwA y)) x := by
  obtain ⟨k, hk, he⟩ := leviBlock_iwP_mul p y
  have h1 : E.α (iwA (p.1 * y) * k) x = E.α (iwA (p.1 * y)) x := by
    rw [E.cocycle]
    have h0 : E.α k = fun _ => 0 := funext (E.orth k hk)
    rw [h0]
    simp [binaryCohomologicalAction]
  rw [← h1, he, E.cocycle]

/-- **The transformation law of the differenced potentials.** -/
theorem gpCore {σ : CuspidalRepresentation} (χ : RankOneCharacter)
    (hc : ∀ g : RealGL3, componentCharacter χ g = 1) (E : LevelLeviCocycleData σ n)
    (p : planeParabolic ℝ) (u : Fin 3 → RealGL3) (t : BinaryAdelicGL) (c : ℂ) :
    (planeRadical n χ (iwP (p.1 * u 2)) - planeRadical n χ (iwP (p.1 * u 1)))
        (c • (E.α (iwA (p.1 * u 1)) t - E.α (iwA (p.1 * u 0)) t)) =
      realCoefficientComponent n χ p.1
        ((c * normPower (GeneralLinearGroup.det (atInfinity (leviBlock p))) (((n : ℂ) + 3) / 2)) •
          (planeRadical n χ (iwP (u 2)) - planeRadical n χ (iwP (u 1)))
            (E.α (iwA (u 1)) (t * atInfinity (leviBlock p)) -
              E.α (iwA (u 0)) (t * atInfinity (leviBlock p)))) := by
  have hdiff : E.α (iwA (p.1 * u 1)) t - E.α (iwA (p.1 * u 0)) t =
      normPower (GeneralLinearGroup.det (atInfinity (leviBlock p))) (((n : ℂ) + 3) / 2) •
        binaryCoefficient n (leviBlock p)
          (E.α (iwA (u 1)) (t * atInfinity (leviBlock p)) -
            E.α (iwA (u 0)) (t * atInfinity (leviBlock p))) := by
    rw [gp_alpha_iwA_mul E p (u 1) t, gp_alpha_iwA_mul E p (u 0) t]
    simp only [binaryCohomologicalAction, map_sub, smul_sub]
    abel
  have hstar : leviStar χ (n + 1) p⁻¹
      (c • normPower (GeneralLinearGroup.det (atInfinity (leviBlock p))) (((n : ℂ) + 3) / 2) •
        binaryCoefficient n (leviBlock p)
          (E.α (iwA (u 1)) (t * atInfinity (leviBlock p)) -
            E.α (iwA (u 0)) (t * atInfinity (leviBlock p)))) =
      (c * normPower (GeneralLinearGroup.det (atInfinity (leviBlock p))) (((n : ℂ) + 3) / 2)) •
        (E.α (iwA (u 1)) (t * atInfinity (leviBlock p)) -
          E.α (iwA (u 0)) (t * atInfinity (leviBlock p))) := by
    rw [map_smul, map_smul, leviStar_binaryCoefficient χ hc, smul_smul]
  rw [hdiff, LinearMap.sub_apply, planeRadical_iwP_mul χ p (u 2),
    planeRadical_iwP_mul χ p (u 1), hstar]
  simp only [map_smul, map_sub, LinearMap.sub_apply, smul_sub]
  abel

/-- `gpCore` for the vertices `w * y i`. -/
theorem gpCore_w {σ : CuspidalRepresentation} (χ : RankOneCharacter)
    (hc : ∀ g : RealGL3, componentCharacter χ g = 1) (E : LevelLeviCocycleData σ n)
    (p : planeParabolic ℝ) (w : RealGL3) (y : Fin 3 → RealGL3) (t : BinaryAdelicGL) (c : ℂ) :
    (planeRadical n χ (iwP (p.1 * (w * y 2))) - planeRadical n χ (iwP (p.1 * (w * y 1))))
        (c • (E.α (iwA (p.1 * (w * y 1))) t - E.α (iwA (p.1 * (w * y 0))) t)) =
      realCoefficientComponent n χ p.1
        ((c * normPower (GeneralLinearGroup.det (atInfinity (leviBlock p))) (((n : ℂ) + 3) / 2)) •
          (planeRadical n χ (iwP (w * y 2)) - planeRadical n χ (iwP (w * y 1)))
            (E.α (iwA (w * y 1)) (t * atInfinity (leviBlock p)) -
              E.α (iwA (w * y 0)) (t * atInfinity (leviBlock p)))) :=
  gpCore χ hc E p (fun i => w * y i) t c

end Real

end TernaryPeriodPolynomials.LevelThreeSource
