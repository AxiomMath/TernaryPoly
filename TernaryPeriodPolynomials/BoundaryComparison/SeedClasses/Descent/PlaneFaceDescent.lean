module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Level.DescentHom
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Face.FrameChange
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.BadPlaneLevelDescent
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Face.LocallyInner
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.PlaneParabolicBinaryProjection

@[expose] public section


/-!
# Level descent at every plane cusp: the locally inner classes versus `𝒞_{h⁻¹Ph}(E)` of `Γ(N)`

Paper: Lemma C.3 (`ar:lem:seed`),
 ("the finite reflection projection supplies the full-level statement") and.

For `N ≥ 3`, `3 ∣ N` and an integral change of basis `h ∈ SL₃(ℤ)`, let `F = h⁻¹⟨e₁,e₂⟩`
(`planeFlagAt h`) be the corresponding rational plane.

* `planeEmbed`: the plane group `Γ(N) ∩ h⁻¹Ph` (`gammaNPAt N h`) is isomorphic (`planeEmbed_injective`,
  `planeEmbed_surjective`) to the stabilizer of `F` in `Γ ∩ Γ(N)`, `Γ` the paper's level group.
* `planeH2Equiv`: Mathlib's `H²(Γ(N) ∩ h⁻¹Ph, E_n)` is the face library's homogeneous `H²` of that
  stabilizer (the bridge of `Statements.LevelTransfer` composed with `planeEmbed`; the character drops out
  because the group has determinant one, `coeff_mapGL`).
* `planeStabAt_iff`, `exists_frame_of_edge`, `exists_edge_of_frame`: the stabilizers in the plane group
  of the complete flags over `F` are exactly the flag stabilizers `faceFlagStab N h F'`, `F'` a frame of
  the binary Levi (`conj_mem_borel_iff` is the matrix computation).
* `mem_locallyInnerAt_iff_faceLocallyInner`: under `planeH2Equiv`, the locally inner classes for the level
  `Γ ∩ Γ(N)` are `faceLocallyInner N h n`.
* **`locallyInnerClasses_planeFlag_iff`**: a class of the face library's `H²(Γ_F, E)` is locally inner
  iff its restriction to `Γ_F ∩ Γ(N)`, read in Mathlib's `H²` of the plane group, lies in
  `faceCuspidalInH2 N h n`, the image of the literal mixed cuspidal group `𝒞_{h⁻¹Ph}(E)` (and hence, by
  the unconditional Eichler--Shimura spanning, in the span of the seeds).
* **`mem_map_locallyInnerClasses_planeFlag_iff`**: `𝒞(Γ) = 𝒞(Γ(N))^{invariants}`: the image of the
  locally inner classes of the level group in `H²(Γ(N) ∩ h⁻¹Ph, E_n)` is the mixed cuspidal group
  intersected with the classes invariant under the stabilizer `Γ_F`.

All of this is presentation free: no splitting of the level group's stabilizer, no semidirect product,
and the same statement holds for the good plane, the bad plane and every conjugate plane.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.LevelTransfer (invariantsH2)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

section PlaneFaceEmbedding

variable (N : ℕ)

/-- The plane `h⁻¹⟨e₁, e₂⟩` of the integral change of basis `h`, as a rational plane flag. -/
def planeFlagAt (h : SL(3, ℤ)) : Flags .plane :=
  QuotientGroup.mk (Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹)

theorem gammaN_toGL_mem_arithmeticLevel (h3 : 3 ∣ N) {p : SL(3, ℤ)} (hp : p ∈ gammaN N) :
    Matrix.SpecialLinearGroup.toGL p ∈ arithmeticLevel := by
  change lastRow ᵥ* (reductionThree (Matrix.SpecialLinearGroup.toGL p)).val = lastRow
  have hred : ∀ i j, ((reductionThree (Matrix.SpecialLinearGroup.toGL p)).val i j : ZMod 3) =
      (1 : Matrix (Fin 3) (Fin 3) (ZMod 3)) i j := by
    intro i j
    have h1 := mem_gammaN.mp hp i j
    have h2 : (3 : ℤ) ∣ (p : Matrix (Fin 3) (Fin 3) ℤ) i j - (1 : Matrix (Fin 3) (Fin 3) ℤ) i j :=
      (Int.natCast_dvd_natCast.mpr h3 : (3 : ℤ) ∣ (N : ℤ)).trans h1
    have h3' : (((p : Matrix (Fin 3) (Fin 3) ℤ) i j - (1 : Matrix (Fin 3) (Fin 3) ℤ) i j : ℤ) :
        ZMod 3) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr h2
    rw [Int.cast_sub, sub_eq_zero] at h3'
    change (((p : Matrix (Fin 3) (Fin 3) ℤ) i j : ℤ) : ZMod 3) = _
    rw [h3']
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  funext j
  simp only [vecMul, dotProduct, lastRow, Fin.sum_univ_three, Pi.single_apply]
  simp only [hred, Matrix.one_apply, mul_ite, mul_one, mul_zero]
  simp
  exact if_congr eq_comm rfl rfl

theorem reduce_toGL_eq_one {p : SL(3, ℤ)} (hp : p ∈ gammaN N) :
    GeneralLinearGroup.map (Int.castRingHom (ZMod N)) (Matrix.SpecialLinearGroup.toGL p) = 1 := by
  apply Units.ext
  ext i j
  have h := mem_gammaN.mp hp i j
  have h2 : (((p : Matrix (Fin 3) (Fin 3) ℤ) i j - (1 : Matrix (Fin 3) (Fin 3) ℤ) i j : ℤ) :
      ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mpr h
  rw [Int.cast_sub, sub_eq_zero] at h2
  change (((p : Matrix (Fin 3) (Fin 3) ℤ) i j : ℤ) : ZMod N) = (1 : Matrix (Fin 3) (Fin 3) (ZMod N)) i j
  rw [h2]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem mapGL_mem_levelPrincipal (h3 : 3 ∣ N) {p : SL(3, ℤ)} (hp : p ∈ gammaN N) :
    Matrix.SpecialLinearGroup.mapGL ℚ p ∈ levelPrincipal N :=
  ⟨⟨Matrix.SpecialLinearGroup.toGL p, gammaN_toGL_mem_arithmeticLevel N h3 hp⟩,
    reduce_toGL_eq_one N hp, by
      apply Units.ext
      ext i j
      rfl⟩

theorem gammaNPAt_le_gammaN (h : SL(3, ℤ)) {p : SL(3, ℤ)} (hp : p ∈ gammaNPAt N h) :
    p ∈ gammaN N := by
  have hq : h * p * h⁻¹ ∈ gammaN N := hp.1
  have := (gammaN_normal N).conj_mem _ hq h⁻¹
  simpa [mul_assoc] using this

theorem mapGL_mem_stab (h : SL(3, ℤ)) {p : SL(3, ℤ)} (hp : p ∈ gammaNPAt N h) :
    Matrix.SpecialLinearGroup.mapGL ℚ p ∈ MulAction.stabilizer RationalGL3 (planeFlagAt h) := by
  rw [MulAction.mem_stabilizer_iff]
  change (QuotientGroup.mk (Matrix.SpecialLinearGroup.mapGL ℚ p *
    Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹) : Flags .plane) = QuotientGroup.mk _
  apply QuotientGroup.eq.mpr
  have hq : (h * p * h⁻¹)⁻¹ ∈ gammaNP N := (gammaNP N).inv_mem hp
  have h20 : ((h * p * h⁻¹)⁻¹ : SL(3, ℤ)) 2 0 = 0 := hq.2.1
  have h21 : ((h * p * h⁻¹)⁻¹ : SL(3, ℤ)) 2 1 = 0 := hq.2.2.1
  have : (Matrix.SpecialLinearGroup.mapGL ℚ p * Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹)⁻¹ *
      Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹ = Matrix.SpecialLinearGroup.mapGL ℚ (h * p * h⁻¹)⁻¹ := by
    simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv, mul_assoc]
  rw [this]
  refine ⟨?_, ?_⟩
  · change (((h * p * h⁻¹)⁻¹ : SL(3, ℤ)) 2 0 : ℚ) = 0
    rw [h20]; simp
  · change (((h * p * h⁻¹)⁻¹ : SL(3, ℤ)) 2 1 : ℚ) = 0
    rw [h21]; simp

variable (h3 : 3 ∣ N) (h : SL(3, ℤ))

/-- **The plane group of `Γ(N)` at the cusp `h⁻¹Ph` inside the stabilizer of the plane `h⁻¹⟨e₁,e₂⟩` in
`Γ ∩ Γ(N)`.** -/
def planeEmbed : ↥(gammaNPAt N h) →*
    ↥(fixedPointLevel (levelPrincipal N) (planeFlagAt h)) where
  toFun p := ⟨Matrix.SpecialLinearGroup.mapGL ℚ p.1,
    mapGL_mem_levelPrincipal N h3 (gammaNPAt_le_gammaN N h p.2), mapGL_mem_stab N h p.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

theorem planeEmbed_val (p : ↥(gammaNPAt N h)) :
    ((planeEmbed N h3 h p).1 : RationalGL3) = Matrix.SpecialLinearGroup.mapGL ℚ p.1 := rfl

theorem planeEmbed_injective : Function.Injective (planeEmbed N h3 h) := by
  intro a b hab
  have h1 := congrArg (fun x : ↥(fixedPointLevel (levelPrincipal N) (planeFlagAt h)) =>
    ((x.1 : RationalGL3).val : Matrix (Fin 3) (Fin 3) ℚ)) hab
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  have := congrFun (congrFun h1 i) j
  change (((a.1 : SL(3, ℤ)) i j : ℤ) : ℚ) = (((b.1 : SL(3, ℤ)) i j : ℤ) : ℚ) at this
  exact_mod_cast this

theorem planeEmbed_surjective (hN : 3 ≤ N) : Function.Surjective (planeEmbed N h3 h) := by
  rintro ⟨x, hxM, hxS⟩
  obtain ⟨g, hg, hgx⟩ := hxM
  -- the integral matrix has determinant one
  have hred : ∀ i j, (((g.1.val i j : ℤ)) : ZMod N) = (1 : Matrix (Fin 3) (Fin 3) (ZMod N)) i j := by
    intro i j
    have := congrArg (fun y : GL (Fin 3) (ZMod N) => (y.val : Matrix (Fin 3) (Fin 3) (ZMod N)) i j)
      (MonoidHom.mem_ker.mp hg)
    exact this
  have hdet1 : g.1.val.det = 1 := by
    have hu : IsUnit g.1.val.det := (Matrix.isUnit_iff_isUnit_det _).mp g.1.isUnit
    have hmod : ((g.1.val.det : ℤ) : ZMod N) = 1 := by
      have : (g.1.val.map (Int.castRingHom (ZMod N))).det = ((g.1.val.det : ℤ) : ZMod N) :=
        (RingHom.map_det (Int.castRingHom (ZMod N)) g.1.val).symm
      rw [← this]
      have hm : g.1.val.map (Int.castRingHom (ZMod N)) = 1 := by
        ext i j; exact hred i j
      rw [hm, Matrix.det_one]
    rcases Int.isUnit_iff.mp hu with h1 | h1
    · exact h1
    · rw [h1] at hmod
      have h2 : ((-1 : ℤ) : ZMod N) = ((1 : ℤ) : ZMod N) := by simpa using hmod
      have h3' := (ZMod.intCast_eq_intCast_iff_dvd_sub (-1) 1 N).mp h2
      have h4 : (N : ℤ) ∣ 2 := by
        have : (1 : ℤ) - -1 = 2 := by norm_num
        rwa [this] at h3'
      have h5 := Int.le_of_dvd (by norm_num) h4
      omega
  let p : SL(3, ℤ) := ⟨g.1.val, hdet1⟩
  have hpN : p ∈ gammaN N := by
    rw [mem_gammaN]
    intro i j
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp
    rw [Int.cast_sub, sub_eq_zero]
    have h1 : (((1 : Matrix (Fin 3) (Fin 3) ℤ) i j : ℤ) : ZMod N) =
        (1 : Matrix (Fin 3) (Fin 3) (ZMod N)) i j := by
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    rw [h1]
    exact hred i j
  have hxp : x = Matrix.SpecialLinearGroup.mapGL ℚ p := by
    rw [← hgx]
    apply Units.ext
    ext i j
    rfl
  -- stabilizing the plane
  have hstab : Matrix.SpecialLinearGroup.mapGL ℚ p ∈ MulAction.stabilizer RationalGL3
      (planeFlagAt h) := hxp ▸ hxS
  have hinv : (h * p⁻¹ * h⁻¹ : SL(3, ℤ)) 2 0 = 0 ∧ (h * p⁻¹ * h⁻¹ : SL(3, ℤ)) 2 1 = 0 := by
    rw [MulAction.mem_stabilizer_iff] at hstab
    change (QuotientGroup.mk (Matrix.SpecialLinearGroup.mapGL ℚ p *
      Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹) : Flags .plane) = QuotientGroup.mk _ at hstab
    have h1 := QuotientGroup.eq.mp hstab
    have : (Matrix.SpecialLinearGroup.mapGL ℚ p * Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹)⁻¹ *
        Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹ = Matrix.SpecialLinearGroup.mapGL ℚ (h * p⁻¹ * h⁻¹) := by
      simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv, mul_assoc]
    rw [this] at h1
    have h2 : Matrix.SpecialLinearGroup.mapGL ℚ (h * p⁻¹ * h⁻¹) ∈ planeParabolic ℚ := h1
    obtain ⟨e0, e1⟩ := h2
    constructor
    · have : (((h * p⁻¹ * h⁻¹ : SL(3, ℤ)) 2 0 : ℤ) : ℚ) = 0 := e0
      exact_mod_cast this
    · have : (((h * p⁻¹ * h⁻¹ : SL(3, ℤ)) 2 1 : ℤ) : ℚ) = 0 := e1
      exact_mod_cast this
  have hpinvN : p⁻¹ ∈ gammaN N := (gammaN N).inv_mem hpN
  have hrow := (mem_stabRow_ofSL_iff_rational hN h hpinvN).mpr hinv
  have hq' : h * p⁻¹ * h⁻¹ ∈ planeStab := (mem_stabRow_ofSL h p⁻¹).mp hrow
  have hq : h * p * h⁻¹ ∈ planeStab := by
    have := planeStab.inv_mem hq'
    simpa [mul_assoc] using this
  have hqN : h * p * h⁻¹ ∈ gammaN N := by
    have := (gammaN_normal N).conj_mem p hpN h
    simpa [mul_assoc] using this
  exact ⟨⟨p, hqN, hq⟩, Subtype.ext hxp.symm⟩

omit h3 in
theorem coeff_mapGL (n : ℕ) (character : RankOneCharacter) (p : SL(3, ℤ)) :
    rationalCoefficientComponent n character (Matrix.SpecialLinearGroup.mapGL ℚ p) = ambRep n p := by
  have hmat : GeneralLinearGroup.map (algebraMap ℚ ℝ) (Matrix.SpecialLinearGroup.mapGL ℚ p) =
      Matrix.SpecialLinearGroup.mapGL ℝ p := by
    apply Units.ext
    ext i j
    simp [GeneralLinearGroup.map_apply, Matrix.SpecialLinearGroup.mapGL]
  have hdet : GeneralLinearGroup.det (Matrix.SpecialLinearGroup.mapGL ℝ p) = 1 := by
    apply Units.ext
    simp [Matrix.SpecialLinearGroup.mapGL]
  apply LinearMap.ext
  intro v
  unfold rationalCoefficientComponent
  rw [MonoidHom.comp_apply, hmat]
  change (componentCharacter character (Matrix.SpecialLinearGroup.mapGL ℝ p)) •
    (realCoefficient n) (Matrix.SpecialLinearGroup.mapGL ℝ p) v = _
  have hc : componentCharacter character (Matrix.SpecialLinearGroup.mapGL ℝ p) = 1 := by
    unfold componentCharacter
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hdet, map_one, map_one]
  rw [hc, one_smul]
  rfl

omit h3 in
/-- Conjugation of a plane-parabolic element by a plane-parabolic element lies in the Borel group iff
the lower left entry of the conjugated binary block vanishes. -/
theorem conj_mem_borel_iff (g q : RationalGL3) (hg : g ∈ planeParabolic ℚ)
    (hq : q ∈ planeParabolic ℚ) :
    g⁻¹ * q * g ∈ parabolic .plane ⊓ parabolic .line ↔
      ((planeParabolicBinary (⟨g, hg⟩ : planeParabolic ℚ))⁻¹ *
        planeParabolicBinary (⟨q, hq⟩ : planeParabolic ℚ) *
        planeParabolicBinary (⟨g, hg⟩ : planeParabolic ℚ)).val 1 0 = 0 := by
  let pg : planeParabolic ℚ := ⟨g, hg⟩
  let pq : planeParabolic ℚ := ⟨q, hq⟩
  let P : planeParabolic ℚ := pg⁻¹ * pq * pg
  have hP : P.val = g⁻¹ * q * g := rfl
  have hbin : planeParabolicBinary P =
      (planeParabolicBinary pg)⁻¹ * planeParabolicBinary pq * planeParabolicBinary pg := by
    rw [show P = pg⁻¹ * pq * pg from rfl, map_mul, map_mul, map_inv]
  have h10 : (planeParabolicBinary P).val 1 0 = P.val.val 1 0 := rfl
  rw [← hP, ← hbin, h10]
  constructor
  · intro h
    exact h.2.1
  · intro h
    exact ⟨P.property, h, P.property.1⟩

/-- The subgroup of the plane group `Γ(N) ∩ h⁻¹Ph` stabilizing the complete flag `e`. -/
def planeStabAt (e : Edges) : Subgroup ↥(gammaNPAt N h) :=
  (MulAction.stabilizer RationalGL3 e).comap
    ((Matrix.SpecialLinearGroup.mapGL ℚ).comp (gammaNPAt N h).subtype)

theorem mapGL_mem_planeParabolic {q : SL(3, ℤ)} (hq : q ∈ planeStab) :
    Matrix.SpecialLinearGroup.mapGL ℚ q ∈ planeParabolic ℚ := by
  refine ⟨?_, ?_⟩
  · change (((q : Matrix (Fin 3) (Fin 3) ℤ) 2 0 : ℤ) : ℚ) = 0
    rw [hq.1]; simp
  · change (((q : Matrix (Fin 3) (Fin 3) ℤ) 2 1 : ℤ) : ℚ) = 0
    rw [hq.2.1]; simp

theorem binary_mapGL {q : SL(3, ℤ)} (hq : q ∈ planeStab) :
    ((planeParabolicBinary (⟨Matrix.SpecialLinearGroup.mapGL ℚ q, mapGL_mem_planeParabolic hq⟩ :
      planeParabolic ℚ)).val : Matrix (Fin 2) (Fin 2) ℚ) =
      (Int.castRingHom ℚ).mapMatrix (topLeft q) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem planeStabAt_iff [NeZero N] (g : RationalGL3) (hg : g ∈ planeParabolic ℚ)
    (p : ↥(gammaNPAt N h)) :
    p ∈ planeStabAt N h (QuotientGroup.mk (Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹ * g)) ↔
      p ∈ faceFlagStab N h (planeParabolicBinary (⟨g, hg⟩ : planeParabolic ℚ)) := by
  have hq : h * p.1 * h⁻¹ ∈ planeStab := p.2.2
  rw [mem_faceFlagStab_iff N h p.1 p.2]
  have hbin := binary_mapGL hq
  have key := conj_mem_borel_iff g (Matrix.SpecialLinearGroup.mapGL ℚ (h * p.1 * h⁻¹)) hg
    (mapGL_mem_planeParabolic hq)
  have hstep : p ∈ planeStabAt N h
      (QuotientGroup.mk (Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹ * g)) ↔
      g⁻¹ * Matrix.SpecialLinearGroup.mapGL ℚ (h * p.1 * h⁻¹) * g ∈
        parabolic .plane ⊓ parabolic .line := by
    change (Matrix.SpecialLinearGroup.mapGL ℚ p.1) • (QuotientGroup.mk
      (Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹ * g) : Edges) = QuotientGroup.mk _ ↔ _
    change (QuotientGroup.mk (Matrix.SpecialLinearGroup.mapGL ℚ p.1 *
      (Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹ * g)) : Edges) = QuotientGroup.mk _ ↔ _
    rw [QuotientGroup.eq, ← inv_mem_iff]
    have : ((Matrix.SpecialLinearGroup.mapGL ℚ p.1 *
        (Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹ * g))⁻¹ *
        (Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹ * g))⁻¹ =
        g⁻¹ * Matrix.SpecialLinearGroup.mapGL ℚ (h * p.1 * h⁻¹) * g := by
      simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv, mul_assoc]
    rw [this]
  rw [hstep, key, Units.val_mul, Units.val_mul]
  have hB : (planeParabolicBinary (⟨Matrix.SpecialLinearGroup.mapGL ℚ (h * p.1 * h⁻¹),
      mapGL_mem_planeParabolic hq⟩ : planeParabolic ℚ)).val =
      (Int.castRingHom ℚ).mapMatrix (topLeft (h * p.1 * h⁻¹)) := hbin
  rw [hB]

theorem exists_frame_of_edge [NeZero N] (e : Edges) (he : endpoint .plane e = planeFlagAt h) :
    ∃ F : GL (Fin 2) ℚ, planeStabAt N h e = faceFlagStab N h F := by
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective e
  have h1 : (QuotientGroup.mk c : Flags .plane) =
      QuotientGroup.mk (Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹) := he
  have h2 : c⁻¹ * Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹ ∈ parabolic .plane :=
    QuotientGroup.eq.mp h1
  have h3 : (c⁻¹ * Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹)⁻¹ ∈ parabolic .plane :=
    (parabolic .plane).inv_mem h2
  have hg : (Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹)⁻¹ * c ∈ planeParabolic ℚ := by
    have : (c⁻¹ * Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹)⁻¹ =
        (Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹)⁻¹ * c := by group
    rw [this] at h3
    exact h3
  obtain ⟨g, hgmem, hc⟩ : ∃ g, g ∈ planeParabolic ℚ ∧
      c = Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹ * g :=
    ⟨_, hg, by group⟩
  subst hc
  refine ⟨planeParabolicBinary (⟨g, hgmem⟩ : planeParabolic ℚ), ?_⟩
  ext p
  exact planeStabAt_iff N h g hgmem p

theorem exists_edge_of_frame [NeZero N] (F : GL (Fin 2) ℚ) :
    ∃ e : Edges, endpoint .plane e = planeFlagAt h ∧ planeStabAt N h e = faceFlagStab N h F := by
  have hg : planeLevi F 1 ∈ planeParabolic ℚ := planeLevi_mem F 1
  refine ⟨QuotientGroup.mk (Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹ * planeLevi F 1), ?_, ?_⟩
  · change (QuotientGroup.mk _ : Flags .plane) = QuotientGroup.mk _
    apply QuotientGroup.eq.mpr
    simpa using (parabolic .plane).inv_mem hg
  · ext p
    rw [planeStabAt_iff N h _ hg p, planeParabolicBinary_planeLevi]

variable (n : ℕ) (character : RankOneCharacter)

/-- The coefficient representation of the level group restricted to `Γ_F ∩ Γ(N)`, in Mathlib's
language. -/
abbrev planeRep : Rep ℂ ↥(fixedPointLevel (levelPrincipal N) (planeFlagAt h)) :=
  Rep.of ((rationalCoefficientComponent n character).comp
    (fixedPointLevel (levelPrincipal N) (planeFlagAt h)).subtype)

omit h3 in
theorem planeEmbed_hT (h3 : 3 ∣ N) (g : ↥(gammaNPAt N h)) (v : planeRep N h n character) :
    (LinearMap.id : planeRep N h n character →ₗ[ℂ] faceRep N h n)
      ((planeRep N h n character).ρ (planeEmbed N h3 h g) v) =
    (faceRep N h n).ρ g ((LinearMap.id : planeRep N h n character →ₗ[ℂ] faceRep N h n) v) := by
  change rationalCoefficientComponent n character (Matrix.SpecialLinearGroup.mapGL ℚ g.1) v =
    ambRep n g.1 v
  rw [coeff_mapGL]

/-- **Mathlib's `H²` of the plane group `Γ(N) ∩ h⁻¹Ph` is the homogeneous `H²` of the stabilizer of the
plane `h⁻¹⟨e₁,e₂⟩` in `Γ ∩ Γ(N)`** (`N ≥ 3`, `3 ∣ N`). -/
def planeH2Equiv (hN : 3 ≤ N) :
    GeneralEisenstein.Homogeneous.H2 (fixedPointLevel (levelPrincipal N) (planeFlagAt h))
        (rationalCoefficientComponent n character) ≃ₗ[ℂ]
      groupCohomology.H2 (faceRep N h n) :=
  (LevelTransfer.bridge (rationalCoefficientComponent n character)
    (fixedPointLevel (levelPrincipal N) (planeFlagAt h))).trans
    (LinearEquiv.ofBijective
      (EdgeNat.h2Map (planeEmbed N h3 h) (planeRep N h n character) (faceRep N h n)
        LinearMap.id (planeEmbed_hT N h n character h3))
      ⟨EdgeNat.h2Map_injective (planeEmbed N h3 h) (planeRep N h n character) (faceRep N h n)
          LinearMap.id (planeEmbed_hT N h n character h3)
          ⟨planeEmbed_injective N h3 h, planeEmbed_surjective N h3 h hN⟩ Function.bijective_id,
        EdgeNat.h2Map_surjective (planeEmbed N h3 h) (planeRep N h n character) (faceRep N h n)
          LinearMap.id (planeEmbed_hT N h n character h3)
          ⟨planeEmbed_injective N h3 h, planeEmbed_surjective N h3 h hN⟩ Function.bijective_id⟩)

theorem res_zero_iff_planeStab [NeZero N] (hN : 3 ≤ N) (e : Edges)
    (he : endpoint .plane e = planeFlagAt h)
    (x : GeneralEisenstein.Homogeneous.H2 (fixedPointLevel (levelPrincipal N) (planeFlagAt h))
      (rationalCoefficientComponent n character)) :
    LevelTransfer.resH2 (rationalCoefficientComponent n character)
        (fixedPointLevel_edge_le_flag' (levelPrincipal N) .plane e (planeFlagAt h) he) x = 0 ↔
      twoCohomologyRestriction (planeStabAt N h e).subtype (faceRep N h n)
        (planeH2Equiv N h3 h n character hN x) = 0 := by
  let le := fixedPointLevel_edge_le_flag' (levelPrincipal N) .plane e (planeFlagAt h) he
  let κ : ↥(planeStabAt N h e) →* ↥(fixedPointLevel (levelPrincipal N) e) :=
    { toFun := fun p => ⟨(planeEmbed N h3 h p.1).1, (planeEmbed N h3 h p.1).2.1, p.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  have hκ : ∀ k : ↥(planeStabAt N h e),
      planeEmbed N h3 h ((planeStabAt N h e).subtype k) =
        (Subgroup.inclusion le) (κ k) := fun k => rfl
  have hκb : Function.Bijective κ := by
    constructor
    · intro a b hab
      apply Subtype.ext
      apply planeEmbed_injective N h3 h
      exact Subtype.ext (congrArg (fun y : ↥(fixedPointLevel (levelPrincipal N) e) =>
        (y.1 : RationalGL3)) hab)
    · intro y
      obtain ⟨p, hp⟩ := planeEmbed_surjective N h3 h hN ⟨y.1, le y.2⟩
      refine ⟨⟨p, ?_⟩, ?_⟩
      · have := y.2.2
        have h1 : (planeEmbed N h3 h p).1 = y.1 := congrArg Subtype.val hp
        change Matrix.SpecialLinearGroup.mapGL ℚ p.1 ∈ MulAction.stabilizer RationalGL3 e
        rw [← planeEmbed_val N h3 h, h1]
        exact this
      · apply Subtype.ext
        exact congrArg (fun z : ↥(fixedPointLevel (levelPrincipal N) (planeFlagAt h)) =>
          (z.1 : RationalGL3)) hp
  have key := EdgeNat.restriction_h2Map_eq_zero_iff (planeEmbed N h3 h)
    (planeRep N h n character) (faceRep N h n) LinearMap.id (planeEmbed_hT N h n character h3)
    (Subgroup.inclusion le) (planeStabAt N h e).subtype κ hκ hκb Function.bijective_id
    (LevelTransfer.bridge (rationalCoefficientComponent n character)
      (fixedPointLevel (levelPrincipal N) (planeFlagAt h)) x)
  refine Iff.trans ?_ key.symm
  have hbr := LevelTransfer.bridge_res (rationalCoefficientComponent n character) le x
  constructor
  · intro h0
    have : twoCohomologyRestriction (Subgroup.inclusion le) (planeRep N h n character)
        (LevelTransfer.bridge (rationalCoefficientComponent n character)
          (fixedPointLevel (levelPrincipal N) (planeFlagAt h)) x) = 0 := by
      refine hbr.trans ?_
      rw [h0, LinearEquiv.map_zero]
      rfl
    exact this
  · intro h0
    have h1 : LevelTransfer.bridge (rationalCoefficientComponent n character)
        (fixedPointLevel (levelPrincipal N) e)
        (LevelTransfer.resH2 (rationalCoefficientComponent n character) le x) = 0 := by
      refine hbr.symm.trans ?_
      exact h0
    exact (LevelTransfer.bridge (rationalCoefficientComponent n character)
      (fixedPointLevel (levelPrincipal N) e)).map_eq_zero_iff.mp h1

theorem res_congr {G : Type} [Group G] (ρ : Rep ℂ G) {K K' : Subgroup G} (hK : K = K')
    (y : groupCohomology.H2 ρ) :
    twoCohomologyRestriction K.subtype ρ y = 0 ↔ twoCohomologyRestriction K'.subtype ρ y = 0 := by
  subst hK; exact Iff.rfl

/-- **The face library's locally inner classes at the plane `h⁻¹⟨e₁, e₂⟩`, for the level
`Γ ∩ Γ(N)`, are the classes of `𝒞_{h⁻¹Ph}(E)`** (`N ≥ 3`, `3 ∣ N`): under the identification
`planeH2Equiv` of the homogeneous `H²` of `Γ_F ∩ Γ(N)` with Mathlib's `H²` of the plane group
`gammaNPAt N h`, `locallyInnerAt` is `faceLocallyInner N h n`. -/
theorem mem_locallyInnerAt_iff_faceLocallyInner [NeZero N] (hN : 3 ≤ N)
    (x : GeneralEisenstein.Homogeneous.H2 (fixedPointLevel (levelPrincipal N) (planeFlagAt h))
      (rationalCoefficientComponent n character)) :
    x ∈ locallyInnerAt (rationalCoefficientComponent n character) (levelPrincipal N)
        (planeFlagAt h) ↔
      planeH2Equiv N h3 h n character hN x ∈ faceLocallyInner N h n := by
  rw [faceLocallyInner_eq_iInf]
  simp only [locallyInnerAt, Submodule.mem_iInf, LinearMap.mem_ker, Subtype.forall]
  constructor
  · intro H F
    obtain ⟨e, he, hK⟩ := exists_edge_of_frame N h F
    have h1 := (res_zero_iff_planeStab N h3 h n character hN e he x).mp (H e he)
    exact (res_congr _ hK _).mp h1
  · intro H e he
    obtain ⟨F, hF⟩ := exists_frame_of_edge N h e he
    exact (res_zero_iff_planeStab N h3 h n character hN e he x).mpr
      ((res_congr _ hF _).mpr (H F))

/-- **Level descent at every plane cusp.**  For `N ≥ 3` with `3 ∣ N`, an integral change of basis `h` and
a class `x` of the homogeneous `H²` of the stabilizer `Γ_F` of the plane `F = h⁻¹⟨e₁,e₂⟩` in the level
group: `x` is locally inner (vanishes on the stabilizer of every complete flag over `F`) iff its
restriction to `Γ_F ∩ Γ(N)`, read in Mathlib's `H²` of the plane group `Γ(N) ∩ h⁻¹Ph`, lies in the image
`faceCuspidalInH2 N h n` of the mixed cuspidal group `𝒞_{h⁻¹Ph}(E)`. -/
theorem locallyInnerClasses_planeFlag_iff [NeZero N] (hN : 3 ≤ N)
    (x : GeneralEisenstein.Homogeneous.H2 (fixedPointLevel rationalLevel (planeFlagAt h))
      (rationalCoefficientComponent n character)) :
    x ∈ locallyInnerClasses n character .plane (planeFlagAt h) ↔
      planeH2Equiv N h3 h n character hN
        (resPrincipal N (planeFlagAt h) (rationalCoefficientComponent n character) x) ∈
        faceCuspidalInH2 N h n := by
  rw [locallyInnerClasses_level_descent N n character (planeFlagAt h) x,
    mem_locallyInnerAt_iff_faceLocallyInner N h3 h n character hN,
    faceCuspidalInH2_eq_locallyInner]

/-- **`𝒞(Γ) = 𝒞(Γ(N))^{invariants}` at every plane cusp.**  A class `y` of Mathlib's `H²(Γ(N) ∩ h⁻¹Ph,
E_n)` is the restriction of a locally inner class of the level group iff it lies in the mixed cuspidal
group `faceCuspidalInH2 N h n` and is invariant under conjugation by the stabilizer `Γ_F` of the plane
in the level group (read on the homogeneous side through `planeH2Equiv`). -/
theorem mem_map_locallyInnerClasses_planeFlag_iff [NeZero N] (hN : 3 ≤ N)
    (y : groupCohomology.H2 (faceRep N h n)) :
    y ∈ Submodule.map
        ((planeH2Equiv N h3 h n character hN).toLinearMap ∘ₗ
          resPrincipal N (planeFlagAt h) (rationalCoefficientComponent n character))
        (locallyInnerClasses n character .plane (planeFlagAt h)) ↔
      y ∈ faceCuspidalInH2 N h n ∧
        (planeH2Equiv N h3 h n character hN).symm y ∈
          invariantsH2 (rationalCoefficientComponent n character)
            (fixedPointLevel_hnorm (levelPrincipal N) (levelPrincipal_norm N) (planeFlagAt h)) := by
  have hmap := map_locallyInnerClasses_eq N n character (planeFlagAt h)
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · exact (locallyInnerClasses_planeFlag_iff N h3 h n character hN x).mp hx
    · have : resPrincipal N (planeFlagAt h) (rationalCoefficientComponent n character) x ∈
          Submodule.map (resPrincipal N (planeFlagAt h) (rationalCoefficientComponent n character))
            (locallyInnerClasses n character .plane (planeFlagAt h)) := ⟨x, hx, rfl⟩
      rw [hmap] at this
      simpa using this.2
  · rintro ⟨hy, hinv⟩
    set z := (planeH2Equiv N h3 h n character hN).symm y with hz
    have hzLI : z ∈ locallyInnerAt (rationalCoefficientComponent n character) (levelPrincipal N)
        (planeFlagAt h) := by
      rw [mem_locallyInnerAt_iff_faceLocallyInner N h3 h n character hN, hz,
        LinearEquiv.apply_symm_apply, ← faceCuspidalInH2_eq_locallyInner]
      exact hy
    have hmem : z ∈ Submodule.map (resPrincipal N (planeFlagAt h)
        (rationalCoefficientComponent n character))
        (locallyInnerClasses n character .plane (planeFlagAt h)) := by
      rw [hmap]; exact ⟨hzLI, hinv⟩
    obtain ⟨x, hx, hxz⟩ := hmem
    refine ⟨x, hx, ?_⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hxz, hz, LinearEquiv.apply_symm_apply]

end PlaneFaceEmbedding

end TernaryPeriodPolynomials.Argument.SeedC3S4c
