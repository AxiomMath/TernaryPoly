module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Plane.SourceReal
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Plane.SourceFinite
public import Mathlib.Tactic.Abel
public import Mathlib.Data.Fin.VecNotation

@[expose] public section


/-!
# The algebraic laws of the plane source cocycle

For a character `χ` trivial on the integral units the plane source `planeSourceAt` is
* a homogeneous two-cocycle (the cup product of the two potentials),
* equivariant for the real group, and
* transforms under the adelic Levi, torus and unipotent generators of the plane parabolic exactly as
  a normalized plane-induced section, and is invariant under the finite level.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm (finiteAdeleUnit)

namespace TernaryPeriodPolynomials.SourceConstruction

/-! ## Small facts -/

theorem ps_atInfinity_one {m : ℕ} : atInfinity (1 : GeneralLinearGroup (Fin m) ℝ) = 1 := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  by_cases equality : row = column <;>
    simp [atInfinity, combineGL, pairMatrix, equality]

theorem ps_atFinite_one {m : ℕ} : atFinite (1 : GeneralLinearGroup (Fin m) FiniteAdeles) = 1 := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  by_cases equality : row = column <;>
    simp [atFinite, combineGL, pairMatrix, equality]

theorem ps_normPower_one (z : ℂ) : normPower (1 : Adelesˣ) z = 1 := by
  simp [normPower]

theorem ps_normPower_zero (t : Adelesˣ) : normPower t 0 = 1 := by
  simp [normPower]

theorem ps_finiteAdeleUnit_one : finiteAdeleUnit (1 : FiniteAdelesˣ) = 1 := Units.ext rfl

theorem ps_realUnitPart_det {m : ℕ} (A : GeneralLinearGroup (Fin m) Adeles) :
    realUnitPart (GeneralLinearGroup.det A) = GeneralLinearGroup.det (realPart A) := by
  apply Units.ext
  change (RingHom.fst ℝ FiniteAdeles) A.val.det =
    ((RingHom.fst ℝ FiniteAdeles).mapMatrix A.val).det
  exact RingHom.map_det _ _

theorem ps_finiteUnitPart_det {m : ℕ} (A : GeneralLinearGroup (Fin m) Adeles) :
    finiteUnitPart (GeneralLinearGroup.det A) = GeneralLinearGroup.det (finitePart A) := by
  apply Units.ext
  change (RingHom.snd ℝ FiniteAdeles) A.val.det =
    ((RingHom.snd ℝ FiniteAdeles).mapMatrix A.val).det
  exact RingHom.map_det _ _

theorem normPower_det_atInfinity {m : ℕ} (r : GeneralLinearGroup (Fin m) ℝ) (z : ℂ) :
    normPower (GeneralLinearGroup.det (atInfinity r)) z =
      normPower (realAdeleUnit (GeneralLinearGroup.det r)) z := by
  rw [normPower_split (GeneralLinearGroup.det (atInfinity r)) z, ps_realUnitPart_det,
    ps_finiteUnitPart_det, realPart_atInfinity, finitePart_atInfinity]
  simp [ps_finiteAdeleUnit_one, ps_normPower_one]

theorem normPower_det_split {m : ℕ} (A : GeneralLinearGroup (Fin m) Adeles) (z : ℂ) :
    normPower (GeneralLinearGroup.det A) z =
      normPower (GeneralLinearGroup.det (atInfinity (realPart A))) z *
        normPower (finiteAdeleUnit (GeneralLinearGroup.det (finitePart A))) z := by
  rw [normPower_split (GeneralLinearGroup.det A) z, ps_realUnitPart_det, ps_finiteUnitPart_det,
    normPower_det_atInfinity]

theorem realUnitPart_one' : realUnitPart (1 : Adelesˣ) = 1 := map_one _

theorem finiteUnitPart_one' : finiteUnitPart (1 : Adelesˣ) = 1 := map_one _

theorem realPart_one' {k : ℕ} : realPart (1 : GeneralLinearGroup (Fin k) Adeles) = 1 := map_one _

theorem finitePart_one' {k : ℕ} : finitePart (1 : GeneralLinearGroup (Fin k) Adeles) = 1 :=
  map_one _

/-! ## Real and finite parts of the plane generators -/

theorem map_planeLevi' {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (A : GeneralLinearGroup (Fin 2) R) (d : Rˣ) :
    GeneralLinearGroup.map φ (planeLevi A d) =
      planeLevi (GeneralLinearGroup.map φ A) (Units.map φ.toMonoidHom d) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeLevi, planeBlock, GeneralLinearGroup.map_apply]

theorem map_planeUnipotent' {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (s t : R) :
    GeneralLinearGroup.map φ (planeUnipotent s t) = planeUnipotent (φ s) (φ t) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [planeUnipotent, GeneralLinearGroup.map_apply]

theorem realGroup_planeLevi (A : BinaryAdelicGL) (t : Adelesˣ) :
    realGroup (planeLevi A t) = planeLevi (realPart A) (realUnitPart t) :=
  map_planeLevi' _ A t

theorem finiteGroup_planeLevi (A : BinaryAdelicGL) (t : Adelesˣ) :
    finiteGroup (planeLevi A t) = planeLevi (finitePart A) (finiteUnitPart t) :=
  map_planeLevi' _ A t

theorem realGroup_planeUnipotent (a b : Adeles) :
    realGroup (planeUnipotent a b) =
      planeUnipotent ((RingHom.fst ℝ FiniteAdeles) a) ((RingHom.fst ℝ FiniteAdeles) b) :=
  map_planeUnipotent' _ a b

theorem finiteGroup_planeUnipotent (a b : Adeles) :
    finiteGroup (planeUnipotent a b) =
      planeUnipotent ((RingHom.snd ℝ FiniteAdeles) a) ((RingHom.snd ℝ FiniteAdeles) b) :=
  map_planeUnipotent' _ a b

theorem planeCornerUnit_planeLevi' {R : Type*} [CommRing R] (A : GeneralLinearGroup (Fin 2) R)
    (d : Rˣ) (h : planeLevi A d ∈ planeParabolic R) : planeCornerUnit (planeLevi A d) h = d :=
  Units.ext rfl

theorem planeBlockGL_planeLevi' {R : Type*} [CommRing R] (A : GeneralLinearGroup (Fin 2) R)
    (d : Rˣ) (h : planeLevi A d ∈ planeParabolic R) : planeBlockGL (planeLevi A d) h = A := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem planeCornerUnit_planeUnipotent {R : Type*} [CommRing R] (s t : R)
    (h : planeUnipotent s t ∈ planeParabolic R) : planeCornerUnit (planeUnipotent s t) h = 1 :=
  Units.ext rfl

theorem planeBlockGL_planeUnipotent {R : Type*} [CommRing R] (s t : R)
    (h : planeUnipotent s t ∈ planeParabolic R) : planeBlockGL (planeUnipotent s t) h = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem finitePlaneFactor_planeLevi (χ : RankOneCharacter) (a b : ℂ)
    (A : GeneralLinearGroup (Fin 2) FiniteAdeles) (d : FiniteAdelesˣ) :
    finitePlaneFactor χ a b (planeLevi A d) (planeLevi_mem A d) =
      χ.toMonoidHom (finiteAdeleUnit d) * normPower (finiteAdeleUnit d) a *
        normPower (finiteAdeleUnit (GeneralLinearGroup.det A)) b := by
  unfold finitePlaneFactor
  rw [planeCornerUnit_planeLevi', planeBlockGL_planeLevi']

theorem finitePlaneFactor_planeUnipotent (χ : RankOneCharacter) (a b : ℂ) (s t : FiniteAdeles)
    (h : planeUnipotent s t ∈ planeParabolic FiniteAdeles) :
    finitePlaneFactor χ a b (planeUnipotent s t) h = 1 := by
  unfold finitePlaneFactor
  rw [planeCornerUnit_planeUnipotent, planeBlockGL_planeUnipotent]
  simp [ps_finiteAdeleUnit_one, ps_normPower_one]

/-! ## The coefficient representation -/

section Rho

variable {n : ℕ}

theorem rho_mul_inv_cancel (χ : RankOneCharacter) (h : RealGL3) (u : HomogeneousPoly n) :
    realCoefficientComponent n χ h (realCoefficientComponent n χ h⁻¹ u) = u := by
  rw [← Module.End.mul_apply, ← map_mul, _root_.mul_inv_cancel, map_one, Module.End.one_apply]

theorem rho_inv_mul_cancel (χ : RankOneCharacter) (h : RealGL3) (u : HomogeneousPoly n) :
    realCoefficientComponent n χ h⁻¹ (realCoefficientComponent n χ h u) = u := by
  rw [← Module.End.mul_apply, ← map_mul, _root_.inv_mul_cancel, map_one, Module.End.one_apply]

theorem rho_inv_mul_rho (χ : RankOneCharacter) (p w : RealGL3) (v : HomogeneousPoly n) :
    realCoefficientComponent n χ (p * w)⁻¹ (realCoefficientComponent n χ p v) =
      realCoefficientComponent n χ w⁻¹ v := by
  rw [_root_.mul_inv_rev, map_mul, Module.End.mul_apply, rho_inv_mul_cancel]

theorem rho_mul_inv_mul (χ : RankOneCharacter) (h w : RealGL3) (v : HomogeneousPoly n) :
    realCoefficientComponent n χ h (realCoefficientComponent n χ (w * h)⁻¹ v) =
      realCoefficientComponent n χ w⁻¹ v := by
  rw [_root_.mul_inv_rev, map_mul, Module.End.mul_apply, rho_mul_inv_cancel]

end Rho

/-! ## The cup product form -/

section Cup

/-- The cup product of the coboundaries of two potentials (a copy of the generic construction). -/
def psCup {X M N W : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup W] [Module ℂ M]
    [Module ℂ N] [Module ℂ W] (pair : M →ₗ[ℂ] N →ₗ[ℂ] W) (a : X → M) (l : X → N)
    (y : Fin 3 → X) : W :=
  pair (a (y 1) - a (y 0)) (l (y 2) - l (y 1))

theorem ps_cup_alternating {M N W : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup W]
    [Module ℂ M] [Module ℂ N] [Module ℂ W] (pair : M →ₗ[ℂ] N →ₗ[ℂ] W) (a₀ a₁ a₂ : M)
    (l₁ l₂ l₃ : N) :
    pair (a₂ - a₁) (l₃ - l₂) - pair (a₂ - a₀) (l₃ - l₂) + pair (a₁ - a₀) (l₃ - l₁) -
      pair (a₁ - a₀) (l₂ - l₁) = 0 := by
  simp only [map_sub, LinearMap.sub_apply]
  abel

/-- **The cocycle condition**, in the exact alternating form of `IsSourceCocycle`. -/
theorem psCup_cocycle {X M N W : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup W]
    [Module ℂ M] [Module ℂ N] [Module ℂ W] (pair : M →ₗ[ℂ] N →ₗ[ℂ] W) (a : X → M) (l : X → N)
    (x : Fin 4 → X) :
    psCup pair a l ![x 1, x 2, x 3] - psCup pair a l ![x 0, x 2, x 3] +
      psCup pair a l ![x 0, x 1, x 3] - psCup pair a l ![x 0, x 1, x 2] = 0 := by
  exact ps_cup_alternating pair (a (x 0)) (a (x 1)) (a (x 2)) (l (x 1)) (l (x 2)) (l (x 3))


variable {n : ℕ}

/-- Evaluation of a linear map at a vector, as a pairing. -/
def evalPair (M W : Type*) [AddCommGroup M] [Module ℂ M] [AddCommGroup W] [Module ℂ W] :
    M →ₗ[ℂ] (M →ₗ[ℂ] W) →ₗ[ℂ] W where
  toFun v :=
    { toFun := fun f => f v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_add' v w := LinearMap.ext fun f => map_add f v w
  map_smul' c v := LinearMap.ext fun f => map_smul f c v

theorem planeSourceAt_eq_cup (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (y : Fin 3 → RealGL3) (g : AdelicGL) (a : BinaryAdelicGL) :
    planeSourceAt D E y g a =
      realCoefficientComponent n D.chi (realGroup g)⁻¹
        (psCup (evalPair (Binary.HomogeneousPoly (n + 1)) (HomogeneousPoly n))
          (fun u : RealGL3 => cF D g • E.α (iwA (realGroup g * u)) (a * bF g))
          (fun u : RealGL3 => planeRadical n D.chi (iwP (realGroup g * u))) y) := by
  unfold planeSourceAt psCup
  rw [smul_sub]
  rfl

/-- **The cocycle condition of the plane source.** -/
theorem planeSourceAt_cocycle (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (x : Fin 4 → RealGL3) (g : AdelicGL) (a : BinaryAdelicGL) :
    planeSourceAt D E ![x 1, x 2, x 3] g a - planeSourceAt D E ![x 0, x 2, x 3] g a +
      planeSourceAt D E ![x 0, x 1, x 3] g a - planeSourceAt D E ![x 0, x 1, x 2] g a = 0 := by
  have h := psCup_cocycle
    (evalPair (Binary.HomogeneousPoly (n + 1)) (HomogeneousPoly n))
    (fun u : RealGL3 => cF D g • E.α (iwA (realGroup g * u)) (a * bF g))
    (fun u : RealGL3 => planeRadical n D.chi (iwP (realGroup g * u))) x
  have h2 := congrArg (realCoefficientComponent n D.chi (realGroup g)⁻¹) h
  simp only [map_sub, map_add, _root_.map_zero] at h2
  simp only [planeSourceAt_eq_cup]
  exact h2

/-- **Equivariance of the plane source** for the real group. -/
theorem planeSourceAt_equivariant (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (h : RealGL3) (y : Fin 3 → RealGL3) (g : AdelicGL) (a : BinaryAdelicGL) :
    planeSourceAt D E (fun i => h * y i) g a =
      realCoefficientComponent n D.chi h (planeSourceAt D E y (g * atInfinity h) a) := by
  have hcF : cF D (g * atInfinity h) = cF D g := by
    unfold cF
    rw [finiteGroup_mul_atInfinity]
  have hbF : bF (g * atInfinity h) = bF g := by
    unfold bF
    rw [finiteGroup_mul_atInfinity]
  unfold planeSourceAt
  rw [realGroup_mul_atInfinity, hcF, hbF]
  simp only [mul_assoc]
  rw [rho_mul_inv_mul]

end Cup

/-! ## The finite twist in the adelic form -/

section Translate

variable {n : ℕ}

theorem twist_left_g (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (g g' : AdelicGL) (f : FiniteGL) (hf : f ∈ planeParabolic FiniteAdeles)
    (hfin : finiteGroup g' = f * finiteGroup g) (h : BinaryRealGL) (x : BinaryAdelicGL) :
    cF D g' • E.α h (x * bF g') =
      finitePlaneFactor D.chi 0 (((n : ℂ) + 3) / 2) f hf •
        (cF D g • E.α h (x * atFinite (planeBlockGL f hf) * bF g)) :=
  twist_left D E hχ (finiteGroup g) (finiteGroup g') f hf hfin h x

theorem sub_twist (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (g g' : AdelicGL) (f : FiniteGL) (hf : f ∈ planeParabolic FiniteAdeles)
    (hfin : finiteGroup g' = f * finiteGroup g) (h1 h0 : BinaryRealGL) (x : BinaryAdelicGL) :
    cF D g' • (E.α h1 (x * bF g') - E.α h0 (x * bF g')) =
      (finitePlaneFactor D.chi 0 (((n : ℂ) + 3) / 2) f hf * cF D g) •
        (E.α h1 (x * atFinite (planeBlockGL f hf) * bF g) -
          E.α h0 (x * atFinite (planeBlockGL f hf) * bF g)) := by
  rw [smul_sub, twist_left_g D E hχ g g' f hf hfin h1 x, twist_left_g D E hχ g g' f hf hfin h0 x]
  simp only [smul_sub, smul_smul]

/-- **The general translation law of the plane source.** -/
theorem planeSourceAt_translate (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (g g' : AdelicGL) (p : planeParabolic ℝ) (f : FiniteGL)
    (hf : f ∈ planeParabolic FiniteAdeles) (hr : realGroup g' = p.1 * realGroup g)
    (hfin : finiteGroup g' = f * finiteGroup g) (y : Fin 3 → RealGL3) (x : BinaryAdelicGL) :
    planeSourceAt D E y g' x =
      (normPower (GeneralLinearGroup.det (atInfinity (leviBlock p))) (((n : ℂ) + 3) / 2) *
          finitePlaneFactor D.chi 0 (((n : ℂ) + 3) / 2) f hf) •
        planeSourceAt D E y g
          (x * (atFinite (planeBlockGL f hf) * atInfinity (leviBlock p))) := by
  have hc := componentCharacter_eq_one_of_integral D.chi hχ
  have hcomm : bF g * atInfinity (leviBlock p) = atInfinity (leviBlock p) * bF g :=
    atFinite_mul_atInfinity_comm _ _
  have ht : x * atFinite (planeBlockGL f hf) * bF g * atInfinity (leviBlock p) =
      x * (atFinite (planeBlockGL f hf) * atInfinity (leviBlock p)) * bF g := by
    simp only [mul_assoc, hcomm]
  have hu : ∀ i, p.1 * realGroup g * y i = p.1 * (realGroup g * y i) :=
    fun i => mul_assoc _ _ _
  unfold planeSourceAt
  rw [hr, hu 2, hu 1, hu 0, sub_twist D E hχ g g' f hf hfin,
    planeCore_w D.chi hc E p (realGroup g) y (x * atFinite (planeBlockGL f hf) * bF g)
      (finitePlaneFactor D.chi 0 (((n : ℂ) + 3) / 2) f hf * cF D g), ht]
  simp only [map_smul, rho_inv_mul_rho, smul_smul]
  congr 1
  ring

end Translate

end TernaryPeriodPolynomials.SourceConstruction
