module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.PlaneCusps
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.FlagStabilizers

@[expose] public section


/-!
# The mixed cuspidal group of a plane cusp is the group of locally inner classes; change of frame

Paper: Lemma C.3 (`ar:lem:seed`).

* `faceFlagStab N h F`: the stabilizer, in the plane group `Γ_{h⁻¹Ph}` of the cusp `h⁻¹Ph`, of the
  complete flag attached to the rational cusp of the frame `F ∈ GL₂(ℚ)` (the elements whose Levi block
  fixes the cusp `F · ∞`; `mem_faceFlagStab_iff`).
* `faceLocallyInner N h n`: the classes of `H²(Γ_{h⁻¹Ph}, E_n)` vanishing on the radical and on every
  flag stabilizer.
* `faceCuspidalInH2_eq_locallyInner`: the image of the (frame dependent) group `𝒞_{P'}(E)` of
  `H¹(Γ₂(N), H¹(N_{P'}, E))` in `H²` is the group of locally inner classes. This characterization
  involves only the plane group and its flag stabilizers.
* `faceFlagStab_mul_left`: for `q ∈ P(ℚ) ∩ SL₃(ℤ)` (`planeBorel`), the cusps `h⁻¹Ph` and `(qh)⁻¹P(qh)`
  have the same plane group (`gammaNPAt_mul_left`) and the same family of flag stabilizers: the frame
  `h` only parametrizes the cusps of the binary Levi, so `𝒞_{P'}(E) ⊂ H²(Γ_{P'}, E)` does not depend
  on the choice of the integral conjugator within the plane.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3 TernaryPeriodPolynomials.Argument.ConvergenceC4

section Face

variable (N : ℕ) [NeZero N] (h : SL(3, ℤ))

/-- **The stabilizer, in the plane group of the cusp `h⁻¹Ph`, of the complete flag attached to the
rational cusp of a frame `F ∈ GL₂(ℚ)`**: the elements whose Levi block fixes the cusp `F · ∞`. -/
def faceFlagStab (F : GL (Fin 2) ℚ) : Subgroup (gammaNPAt N h) :=
  (leviCuspStab (CongruenceSubgroup.Gamma N) F).comap (faceExt N h).rightHom

/-- **The locally inner classes of the cusp `h⁻¹Ph`**: the classes of `H²(Γ_{h⁻¹Ph}, E_n)` vanishing on
the radical and on the stabilizer of every complete flag over the plane. -/
def faceLocallyInner (n : ℕ) : Submodule ℂ (groupCohomology.H2 (faceRep N h n)) :=
  LinearMap.ker (twoCohomologyRestriction (faceExt N h).inl (faceRep N h n)) ⊓
    ⨅ F : GL (Fin 2) ℚ, LinearMap.ker
      (twoCohomologyRestriction (faceFlagStab N h F).subtype (faceRep N h n))

theorem faceFlagStab_eq (F : GL (Fin 2) ℚ) :
    faceFlagStab N h F =
      ((leviCuspStab (CongruenceSubgroup.Gamma N) F).comap (faceExt N h).rightHom) := rfl


/-- **The mixed cuspidal group of the cusp `h⁻¹Ph` is the group of locally inner classes.** The image
in `H²(Γ_{h⁻¹Ph}, E_n)` of the group `𝒞_{P'}(E) ⊂ H¹(Γ₂(N), H¹(N_{P'}, E))` of classes vanishing at
every rational cusp of the binary Levi is exactly the group of classes vanishing on the stabilizer of
every complete flag over the plane (Hochschild--Serre, `FlagStabilizers.edge_mem_cuspidalFamily_iff`). -/
theorem faceCuspidalInH2_eq_locallyInner (n : ℕ) :
    faceCuspidalInH2 N h n = faceLocallyInner N h n := by
  have hB : ∀ (F : GL (Fin 2) ℚ) (V : Rep ℂ ↥(leviCuspStab (CongruenceSubgroup.Gamma N) F))
      (x : groupCohomology.H2 V), x = 0 := fun F V x =>
    LocallyInner.h2_zero_subgroup
      (fun A x => H2_vanish_level (CongruenceSubgroup.Gamma N) A x) _ V x
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    have := (LocallyInner.edge_mem_cuspidalFamily_iff (faceSplitting N h) (faceRep N h n)
      (leviCuspStab (CongruenceSubgroup.Gamma N)) hB x.1 x.2).mp hx
    exact Submodule.mem_iInf _ |>.mpr fun F => this F
  · rintro ⟨hy0, hF⟩
    refine ⟨⟨y, hy0⟩, ?_, rfl⟩
    exact (LocallyInner.edge_mem_cuspidalFamily_iff (faceSplitting N h) (faceRep N h n)
      (leviCuspStab (CongruenceSubgroup.Gamma N)) hB y hy0).mpr
      (fun F => LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hF F))

end Face



open TernaryPeriodPolynomials.Argument.SeedC3 TernaryPeriodPolynomials.Argument.ConvergenceC4

/-- The elements of `SL₃(ℤ)` with bottom row `(0, 0, ±1)`: the rational stabilizer of the standard
plane, `P(ℚ) ∩ SL₃(ℤ)`. -/
def planeBorel : Subgroup SL(3, ℤ) where
  carrier := {q | (q : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0 ∧ (q : Matrix (Fin 3) (Fin 3) ℤ) 2 1 = 0}
  one_mem' := by simp
  mul_mem' := by
    rintro q q' ⟨h0, h1⟩ ⟨k0, k1⟩
    refine ⟨?_, ?_⟩ <;> simp [Matrix.mul_apply, Fin.sum_univ_three, h0, h1, k0, k1]
  inv_mem' := by
    rintro q ⟨h0, h1⟩
    have hq : (q : Matrix (Fin 3) (Fin 3) ℤ) * ((q⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]; rfl
    show ((q⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0 ∧
      ((q⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 1 = 0
    generalize ((q⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) = Y at hq ⊢
    have e0 := congrFun (congrFun hq 2) 0
    have e1 := congrFun (congrFun hq 2) 1
    have e2 := congrFun (congrFun hq 2) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, h0, h1] at e0 e1 e2
    have u : IsUnit ((q : Matrix (Fin 3) (Fin 3) ℤ) 2 2) :=
      ⟨⟨_, Y 2 2, e2, by rw [mul_comm]; exact e2⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rcases e0 with h | h
      · exact absurd h u.ne_zero
      · exact h
    · rcases e1 with h | h
      · exact absurd h u.ne_zero
      · exact h


theorem mul_inv_mem_planeStab {q X : SL(3, ℤ)} (hq : q ∈ planeBorel) (hX : X ∈ planeStab) :
    q * X * q⁻¹ ∈ planeStab := by
  obtain ⟨h0, h1⟩ := hq
  obtain ⟨x0, x1, x2⟩ := hX
  have hY : q⁻¹ ∈ planeBorel := planeBorel.inv_mem ⟨h0, h1⟩
  obtain ⟨y0, y1⟩ := hY
  have hqY : (q : Matrix (Fin 3) (Fin 3) ℤ) * ((q⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]; rfl
  show ((q * X * q⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0 ∧
    ((q * X * q⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 1 = 0 ∧
    ((q * X * q⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 2 = 1
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  generalize ((q⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) = Y at hqY y0 y1 ⊢
  have e2 := congrFun (congrFun hqY 2) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, h0, h1] at e2
  refine ⟨?_, ?_, ?_⟩
  · simp [Matrix.mul_apply, Fin.sum_univ_three, h0, h1, x0, x1, x2, y0]
  · simp [Matrix.mul_apply, Fin.sum_univ_three, h0, h1, x0, x1, x2, y1]
  · simp [Matrix.mul_apply, Fin.sum_univ_three, h0, h1, x0, x1, x2]
    linear_combination e2

theorem conj_mem_gammaNP (N : ℕ) {q X : SL(3, ℤ)} (hq : q ∈ planeBorel) (hX : X ∈ gammaNP N) :
    q * X * q⁻¹ ∈ gammaNP N :=
  ⟨(gammaN_normal N).conj_mem X hX.1 q |> fun h => by simpa using h,
    mul_inv_mem_planeStab hq hX.2⟩

/-- The upper-left `2 × 2` block of an element of `SL₃(ℤ)`. -/
def topLeft (X : SL(3, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(X : Matrix (Fin 3) (Fin 3) ℤ) 0 0, (X : Matrix (Fin 3) (Fin 3) ℤ) 0 1;
    (X : Matrix (Fin 3) (Fin 3) ℤ) 1 0, (X : Matrix (Fin 3) (Fin 3) ℤ) 1 1]

theorem topLeft_mul {A B : SL(3, ℤ)} (hB : B ∈ planeBorel) : topLeft (A * B) = topLeft A * topLeft B +
    Matrix.of (fun i j => (A : Matrix (Fin 3) (Fin 3) ℤ) i.castSucc 2 *
      (B : Matrix (Fin 3) (Fin 3) ℤ) 2 j.castSucc) := by
  obtain ⟨b0, b1⟩ := hB
  rw [topLeft, topLeft, topLeft, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, b0, b1]

theorem topLeft_mul_of_mem {A B : SL(3, ℤ)} (hB : B ∈ planeBorel) (hAB : ∀ j : Fin 2,
    (B : Matrix (Fin 3) (Fin 3) ℤ) 2 j.castSucc = 0) :
    topLeft (A * B) = topLeft A * topLeft B := by
  rw [topLeft_mul hB]
  have : (Matrix.of (fun (i j : Fin 2) => (A : Matrix (Fin 3) (Fin 3) ℤ) i.castSucc 2 *
      (B : Matrix (Fin 3) (Fin 3) ℤ) 2 j.castSucc) : Matrix (Fin 2) (Fin 2) ℤ) = 0 := by
    ext i j
    simp [hAB j]
  rw [this, add_zero]


/-- The cast to `ℚ` of an integral matrix with integral inverse, as an element of `GL₂(ℚ)`. -/
def castGL (A A' : Matrix (Fin 2) (Fin 2) ℤ) (h : A * A' = 1) (h' : A' * A = 1) :
    GL (Fin 2) ℚ :=
  ⟨(Int.castRingHom ℚ).mapMatrix A, (Int.castRingHom ℚ).mapMatrix A', by
    rw [← map_mul, h, map_one], by rw [← map_mul, h', map_one]⟩

theorem cond_conj (F : GL (Fin 2) ℚ) (A A' B : Matrix (Fin 2) (Fin 2) ℤ) (h : A * A' = 1)
    (h' : A' * A = 1) :
    ((F⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) *
        (Int.castRingHom ℚ).mapMatrix (A * B * A') * (F : Matrix (Fin 2) (Fin 2) ℚ) =
      (((castGL A' A h' h * F)⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) *
        (Int.castRingHom ℚ).mapMatrix B * ((castGL A' A h' h * F : GL (Fin 2) ℚ) :
          Matrix (Fin 2) (Fin 2) ℚ) := by
  have hinv : ((castGL A' A h' h)⁻¹ : GL (Fin 2) ℚ) = castGL A A' h h' := by
    apply inv_eq_of_mul_eq_one_right
    apply Units.ext
    change (Int.castRingHom ℚ).mapMatrix A' * (Int.castRingHom ℚ).mapMatrix A = 1
    rw [← map_mul, h', map_one]
  have e1 : (((castGL A' A h' h * F)⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      ((F⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) * (Int.castRingHom ℚ).mapMatrix A := by
    rw [mul_inv_rev, hinv]; rfl
  have e2 : ((castGL A' A h' h * F : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      (Int.castRingHom ℚ).mapMatrix A' * (F : Matrix (Fin 2) (Fin 2) ℚ) := rfl
  rw [e1, e2, map_mul, map_mul]
  simp only [mul_assoc]

section Frame

variable (N : ℕ) (h q : SL(3, ℤ))

theorem gammaNPAt_mul_left (hq : q ∈ planeBorel) :
    gammaNPAt N (q * h) = gammaNPAt N h := by
  ext p
  rw [mem_gammaNPAt, mem_gammaNPAt]
  have e : q * h * p * (q * h)⁻¹ = q * (h * p * h⁻¹) * q⁻¹ := by group
  rw [e]
  constructor
  · intro hp
    have := conj_mem_gammaNP N (planeBorel.inv_mem hq) hp
    simpa [mul_assoc] using this
  · intro hp
    exact conj_mem_gammaNP N hq hp


theorem topLeft_one : topLeft (1 : SL(3, ℤ)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [topLeft]

theorem mem_planeBorel_of_mem_planeStab {X : SL(3, ℤ)} (hX : X ∈ planeStab) : X ∈ planeBorel :=
  ⟨hX.1, hX.2.1⟩

theorem planeBorel_row (q : SL(3, ℤ)) (hq : q ∈ planeBorel) (j : Fin 2) :
    (q : Matrix (Fin 3) (Fin 3) ℤ) 2 j.castSucc = 0 := by
  fin_cases j
  · exact hq.1
  · exact hq.2

theorem topLeft_inv_mul (q : SL(3, ℤ)) (hq : q ∈ planeBorel) :
    topLeft q * topLeft q⁻¹ = 1 ∧ topLeft q⁻¹ * topLeft q = 1 := by
  have hq' : q⁻¹ ∈ planeBorel := planeBorel.inv_mem hq
  constructor
  · rw [← topLeft_mul_of_mem hq' (planeBorel_row _ hq'), mul_inv_cancel, topLeft_one]
  · rw [← topLeft_mul_of_mem hq (planeBorel_row _ hq), inv_mul_cancel, topLeft_one]

theorem topLeft_conj (q X : SL(3, ℤ)) (hq : q ∈ planeBorel) (hX : X ∈ planeBorel) :
    topLeft (q * X * q⁻¹) = topLeft q * topLeft X * topLeft q⁻¹ := by
  have hq' : q⁻¹ ∈ planeBorel := planeBorel.inv_mem hq
  rw [topLeft_mul_of_mem hq' (planeBorel_row _ hq'), topLeft_mul_of_mem hX (planeBorel_row _ hX)]

theorem mem_faceFlagStab_iff (N : ℕ) [NeZero N] (h p : SL(3, ℤ)) (hp : p ∈ gammaNPAt N h)
    (F : GL (Fin 2) ℚ) :
    (⟨p, hp⟩ : gammaNPAt N h) ∈ faceFlagStab N h F ↔
      (((F⁻¹ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) *
        (Int.castRingHom ℚ).mapMatrix (topLeft (h * p * h⁻¹)) * (F : Matrix (Fin 2) (Fin 2) ℚ))
          1 0 = 0 := by
  change ((F⁻¹ * Matrix.SpecialLinearGroup.mapGL ℚ (leviBlock (h * p * h⁻¹) hp.2) * F :
    GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0 ↔ _
  have : ((Matrix.SpecialLinearGroup.mapGL ℚ (leviBlock (h * p * h⁻¹) hp.2) : GL (Fin 2) ℚ) :
      Matrix (Fin 2) (Fin 2) ℚ) = (Int.castRingHom ℚ).mapMatrix (topLeft (h * p * h⁻¹)) := by
    rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Units.val_mul, Units.val_mul, this]

/-- **Change of frame within a plane.** For `q ∈ P(ℚ) ∩ SL₃(ℤ)` the cusps `h⁻¹Ph` and `(qh)⁻¹P(qh)`
are the same plane, with the same plane group, and the families of stabilizers of complete flags (one
for each frame `F ∈ GL₂(ℚ)`) coincide: the frame is only a parametrization of the cusps of the binary
Levi. -/
theorem faceFlagStab_mul_left (N : ℕ) [NeZero N] (h q : SL(3, ℤ)) (hq : q ∈ planeBorel)
    (F : GL (Fin 2) ℚ) :
    ∃ F' : GL (Fin 2) ℚ,
      (faceFlagStab N (q * h) F).map (gammaNPAt N (q * h)).subtype =
        (faceFlagStab N h F').map (gammaNPAt N h).subtype := by
  obtain ⟨h1, h2⟩ := topLeft_inv_mul q hq
  refine ⟨castGL (topLeft q⁻¹) (topLeft q) h2 h1 * F, ?_⟩
  ext p
  constructor
  · rintro ⟨⟨p, hp⟩, hmem, rfl⟩
    have hp' : p ∈ gammaNPAt N h := by rwa [← gammaNPAt_mul_left N h q hq]
    have hmem2 := (mem_faceFlagStab_iff N (q * h) p hp F).mp hmem
    refine ⟨⟨p, hp'⟩, (mem_faceFlagStab_iff N h p hp' _).mpr ?_, rfl⟩
    have hX : h * p * h⁻¹ ∈ planeStab := hp'.2
    have e : q * h * p * (q * h)⁻¹ = q * (h * p * h⁻¹) * q⁻¹ := by group
    rw [e, topLeft_conj q _ hq (mem_planeBorel_of_mem_planeStab hX)] at hmem2
    rw [← cond_conj F (topLeft q) (topLeft q⁻¹) _ h1 h2]
    exact hmem2
  · rintro ⟨⟨p, hp⟩, hmem, rfl⟩
    have hp' : p ∈ gammaNPAt N (q * h) := by rwa [gammaNPAt_mul_left N h q hq]
    have hmem2 := (mem_faceFlagStab_iff N h p hp _).mp hmem
    refine ⟨⟨p, hp'⟩, (mem_faceFlagStab_iff N (q * h) p hp' F).mpr ?_, rfl⟩
    have hX : h * p * h⁻¹ ∈ planeStab := hp.2
    have e : q * h * p * (q * h)⁻¹ = q * (h * p * h⁻¹) * q⁻¹ := by group
    rw [e, topLeft_conj q _ hq (mem_planeBorel_of_mem_planeStab hX)]
    rw [cond_conj F (topLeft q) (topLeft q⁻¹) _ h1 h2]
    exact hmem2

end Frame

end TernaryPeriodPolynomials.Argument.SeedC3S4c
