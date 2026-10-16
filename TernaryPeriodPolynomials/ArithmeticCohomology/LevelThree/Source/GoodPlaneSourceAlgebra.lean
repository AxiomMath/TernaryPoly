module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.GoodPlaneSourceData

@[expose] public section


/-!
# The algebraic laws of the good-plane source cocycle

For a character `χ` trivial on the integral units the good-plane source `goodPlaneSourceAt` is
* a homogeneous two-cocycle (the cup product of the two potentials),
* equivariant for the real group,
* transforms under the adelic Levi, torus and unipotent generators of the plane parabolic exactly
  as a normalized plane-induced section, and is invariant under the finite level.

This ports SC's `PlaneSourceAlgebra` (cup, cocycle, equivariance, translation) and
`PlaneSourceLaws` (level, unipotent, torus, Levi) with the finite part `gpsF`, `gpsB`; the
algebra of
the cup product (`psCup`, `evalPair`, `psCup_cocycle`) and the small facts about the generators are
imported from SC.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm (finiteAdeleUnit)

namespace TernaryPeriodPolynomials.LevelThreeSource

section Cup

variable {n : ℕ}

theorem gpsF_mul_atInfinity (D : InducingData n) (g : AdelicGL) (z : RealGL3) :
    gpsF D (g * atInfinity z) = gpsF D g := by
  unfold gpsF
  rw [finiteGroup_mul_atInfinity]

theorem gpsB_mul_atInfinity (g : AdelicGL) (z : RealGL3) : gpsB (g * atInfinity z) = gpsB g := by
  unfold gpsB
  rw [finiteGroup_mul_atInfinity]

theorem goodPlaneSourceAt_eq_cup (D : InducingData n) (E : LevelLeviCocycleData D.cusp n)
    (y : Fin 3 → RealGL3) (g : AdelicGL) (a : BinaryAdelicGL) :
    goodPlaneSourceAt D E y g a =
      realCoefficientComponent n D.chi (realGroup g)⁻¹
        (psCup (evalPair (Binary.HomogeneousPoly (n + 1)) (HomogeneousPoly n))
          (fun u : RealGL3 => gpsF D g • E.α (iwA (realGroup g * u)) (a * gpsB g))
          (fun u : RealGL3 => planeRadical n D.chi (iwP (realGroup g * u))) y) := by
  unfold goodPlaneSourceAt psCup
  rw [smul_sub]
  rfl

/-- **The cocycle condition of the good-plane source.** -/
theorem goodPlaneSourceAt_cocycle (D : InducingData n) (E : LevelLeviCocycleData D.cusp n)
    (x : Fin 4 → RealGL3) (g : AdelicGL) (a : BinaryAdelicGL) :
    goodPlaneSourceAt D E ![x 1, x 2, x 3] g a - goodPlaneSourceAt D E ![x 0, x 2, x 3] g a +
      goodPlaneSourceAt D E ![x 0, x 1, x 3] g a - goodPlaneSourceAt D E ![x 0, x 1, x 2] g a =
        0 := by
  have h := psCup_cocycle
    (evalPair (Binary.HomogeneousPoly (n + 1)) (HomogeneousPoly n))
    (fun u : RealGL3 => gpsF D g • E.α (iwA (realGroup g * u)) (a * gpsB g))
    (fun u : RealGL3 => planeRadical n D.chi (iwP (realGroup g * u))) x
  have h2 := congrArg (realCoefficientComponent n D.chi (realGroup g)⁻¹) h
  simp only [map_sub, map_add, _root_.map_zero] at h2
  simp only [goodPlaneSourceAt_eq_cup]
  exact h2

/-- **Equivariance of the good-plane source** for the real group. -/
theorem goodPlaneSourceAt_equivariant (D : InducingData n) (E : LevelLeviCocycleData D.cusp n)
    (h : RealGL3) (y : Fin 3 → RealGL3) (g : AdelicGL) (a : BinaryAdelicGL) :
    goodPlaneSourceAt D E (fun i => h * y i) g a =
      realCoefficientComponent n D.chi h (goodPlaneSourceAt D E y (g * atInfinity h) a) := by
  unfold goodPlaneSourceAt
  rw [realGroup_mul_atInfinity, gpsF_mul_atInfinity, gpsB_mul_atInfinity]
  simp only [mul_assoc]
  rw [rho_mul_inv_mul]

end Cup

/-! ## The translation law -/

section Translate

variable {n : ℕ}

theorem gp_sub_twist (D : InducingData n) (E : LevelLeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (g g' : AdelicGL) (f : FiniteGL) (hf : f ∈ planeParabolic FiniteAdeles)
    (hfin : finiteGroup g' = f * finiteGroup g) (h1 h0 : BinaryRealGL) (x : BinaryAdelicGL) :
    gpsF D g' • (E.α h1 (x * gpsB g') - E.α h0 (x * gpsB g')) =
      (finitePlaneFactor D.chi 0 (((n : ℂ) + 3) / 2) f hf * gpsF D g) •
        (E.α h1 (x * atFinite (planeBlockGL f hf) * gpsB g) -
          E.α h0 (x * atFinite (planeBlockGL f hf) * gpsB g)) := by
  rw [smul_sub, gp_twist_left D E hχ g g' f hf hfin h1 x, gp_twist_left D E hχ g g' f hf hfin h0 x]
  simp only [smul_sub, smul_smul]

/-- **The general translation law of the good-plane source.** -/
theorem goodPlaneSourceAt_translate (D : InducingData n) (E : LevelLeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (g g' : AdelicGL) (p : planeParabolic ℝ) (f : FiniteGL)
    (hf : f ∈ planeParabolic FiniteAdeles) (hr : realGroup g' = p.1 * realGroup g)
    (hfin : finiteGroup g' = f * finiteGroup g) (y : Fin 3 → RealGL3) (x : BinaryAdelicGL) :
    goodPlaneSourceAt D E y g' x =
      (normPower (GeneralLinearGroup.det (atInfinity (leviBlock p))) (((n : ℂ) + 3) / 2) *
          finitePlaneFactor D.chi 0 (((n : ℂ) + 3) / 2) f hf) •
        goodPlaneSourceAt D E y g
          (x * (atFinite (planeBlockGL f hf) * atInfinity (leviBlock p))) := by
  have hc := componentCharacter_eq_one_of_integral D.chi hχ
  have hcomm : gpsB g * atInfinity (leviBlock p) = atInfinity (leviBlock p) * gpsB g :=
    atFinite_mul_atInfinity_comm _ _
  have ht : x * atFinite (planeBlockGL f hf) * gpsB g * atInfinity (leviBlock p) =
      x * (atFinite (planeBlockGL f hf) * atInfinity (leviBlock p)) * gpsB g := by
    simp only [mul_assoc, hcomm]
  have hu : ∀ i, p.1 * realGroup g * y i = p.1 * (realGroup g * y i) :=
    fun i => mul_assoc _ _ _
  unfold goodPlaneSourceAt
  rw [hr, hu 2, hu 1, hu 0, gp_sub_twist D E hχ g g' f hf hfin,
    gpCore_w D.chi hc E p (realGroup g) y (x * atFinite (planeBlockGL f hf) * gpsB g)
      (finitePlaneFactor D.chi 0 (((n : ℂ) + 3) / 2) f hf * gpsF D g), ht]
  simp only [map_smul, rho_inv_mul_rho, smul_smul]
  congr 1
  ring

end Translate

/-! ## The induced-section laws -/

section Laws

variable {n : ℕ} (D : InducingData n) (E : LevelLeviCocycleData D.cusp n)
  (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)

include hχ

/-- **Right invariance under the finite level.** -/
theorem goodPlaneSourceAt_level (g : AdelicGL) (k : finiteLevel) (y : Fin 3 → RealGL3)
    (x : BinaryAdelicGL) :
    goodPlaneSourceAt D E y (g * atFinite k.val) x = goodPlaneSourceAt D E y g x := by
  unfold goodPlaneSourceAt
  rw [realGroup_mul_atFinite]
  simp only [smul_sub]
  rw [gp_twist_level D E hχ g k _ x, gp_twist_level D E hχ g k _ x]

/-- **Unipotent invariance.** -/
theorem goodPlaneSourceAt_unipotent (a b : Adeles) (g : AdelicGL) (y : Fin 3 → RealGL3)
    (x : BinaryAdelicGL) :
    goodPlaneSourceAt D E y (planeUnipotent a b * g) x = goodPlaneSourceAt D E y g x := by
  have hr : realGroup (planeUnipotent a b * g) =
      planeUnipotent ((RingHom.fst ℝ FiniteAdeles) a) ((RingHom.fst ℝ FiniteAdeles) b) *
        realGroup g := by
    rw [map_mul, realGroup_planeUnipotent]
  have hfin : finiteGroup (planeUnipotent a b * g) =
      planeUnipotent ((RingHom.snd ℝ FiniteAdeles) a) ((RingHom.snd ℝ FiniteAdeles) b) *
        finiteGroup g := by
    rw [map_mul, finiteGroup_planeUnipotent]
  have h := goodPlaneSourceAt_translate D E hχ g (planeUnipotent a b * g)
    ⟨planeUnipotent ((RingHom.fst ℝ FiniteAdeles) a) ((RingHom.fst ℝ FiniteAdeles) b),
      planeUnipotent_mem' _ _⟩
    (planeUnipotent ((RingHom.snd ℝ FiniteAdeles) a) ((RingHom.snd ℝ FiniteAdeles) b))
    (planeUnipotent_mem' _ _) hr hfin y x
  rw [h, leviBlock_planeUnipotent, planeBlockGL_planeUnipotent, finitePlaneFactor_planeUnipotent]
  simp [ps_atFinite_one, ps_normPower_one]

/-- **The rank-one Levi character.** -/
theorem goodPlaneSourceAt_torus (t : Adelesˣ) (g : AdelicGL) (y : Fin 3 → RealGL3)
    (x : BinaryAdelicGL) :
    goodPlaneSourceAt D E y (planeLevi 1 t * g) x =
      D.chi.toMonoidHom t • goodPlaneSourceAt D E y g x := by
  have hr : realGroup (planeLevi 1 t * g) = planeLevi 1 (realUnitPart t) * realGroup g := by
    rw [map_mul, realGroup_planeLevi, realPart_one']
  have hfin : finiteGroup (planeLevi 1 t * g) = planeLevi 1 (finiteUnitPart t) * finiteGroup g := by
    rw [map_mul, finiteGroup_planeLevi, finitePart_one']
  have h := goodPlaneSourceAt_translate D E hχ g (planeLevi 1 t * g)
    ⟨planeLevi 1 (realUnitPart t), planeLevi_mem _ _⟩ (planeLevi 1 (finiteUnitPart t))
    (planeLevi_mem _ _) hr hfin y x
  rw [character_split D.chi t, character_real_eq_one D.chi hχ,
    one_mul (D.chi.toMonoidHom (finiteAdeleUnit (finiteUnitPart t)))]
  rw [h, leviBlock_planeLevi, planeBlockGL_planeLevi', finitePlaneFactor_planeLevi]
  simp [ps_atFinite_one, ps_normPower_one, ps_normPower_zero,
    ps_finiteAdeleUnit_one]

/-- **The `GL₂` Levi law.** -/
theorem goodPlaneSourceAt_levi (A : BinaryAdelicGL) (g : AdelicGL) (y : Fin 3 → RealGL3)
    (x : BinaryAdelicGL) :
    goodPlaneSourceAt D E y (planeLevi A 1 * g) x =
      normPower (GeneralLinearGroup.det A) (((n : ℂ) + 3) / 2) •
        goodPlaneSourceAt D E y g (x * A) := by
  have hr : realGroup (planeLevi A 1 * g) = planeLevi (realPart A) 1 * realGroup g := by
    rw [map_mul, realGroup_planeLevi, realUnitPart_one']
  have hfin : finiteGroup (planeLevi A 1 * g) = planeLevi (finitePart A) 1 * finiteGroup g := by
    rw [map_mul, finiteGroup_planeLevi, finiteUnitPart_one']
  have h := goodPlaneSourceAt_translate D E hχ g (planeLevi A 1 * g)
    ⟨planeLevi (realPart A) 1, planeLevi_mem _ _⟩ (planeLevi (finitePart A) 1)
    (planeLevi_mem _ _) hr hfin y x
  have hA : atFinite (finitePart A) * atInfinity (realPart A) = A := by
    rw [atFinite_mul_atInfinity_comm, ← adelic_split]
  rw [h, leviBlock_planeLevi, planeBlockGL_planeLevi', finitePlaneFactor_planeLevi,
    ps_finiteAdeleUnit_one, map_one D.chi.toMonoidHom, ps_normPower_zero, hA]
  simp only [one_mul, mul_one]
  rw [← normPower_det_split]

end Laws

end TernaryPeriodPolynomials.LevelThreeSource
