module

public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.LevelVector

@[expose] public section


/-!
# Level-three weight vectors

Both level-three cusps (the good plane and the bad line) have the same Levi level
`{k ∈ GL₂(ℤ̂) : k₁₀ ≡ 0, k₁₁ ≡ 1 (mod 3)}` (`PlaneLeviLevel`): at the good plane by
`goodPlane_shift`, at the bad line because `diag(1, k)` lies in the finite level exactly for these
`k` (`planeLeviLevel_iff_lineLevi_mem`).  The source construction at these cusps starts from a
vector of `σ` fixed by this level and of a fixed rotation weight at infinity
(`levelThreeWeightVectors σ weight`, the weight being `-(n + 3)` for the cohomological degree `n`).
These are the abstract counterparts of the classical cusp forms of weight `n + 3` on `Γ₁(3)`.

* `levelThreeWeightVectors σ weight` — smooth vectors in `levelThreeValues σ` with
  `π(r_θ) v = e^{i weight θ} v`;
* `levelThreeClassicalVectors_le_levelThreeWeightVectors` — the holomorphic level-three vectors
 are among them;
* `levelThreeWeightVectors_mem_of_spherical` — a spherical vector of the right weight is one.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Separation
open TernaryPeriodPolynomials.MultiplicityOne

namespace TernaryPeriodPolynomials.LevelThreeSource

/-- Smooth level-three vectors of rotation weight `weight`. -/
def levelThreeWeightVectors (σ : CuspidalRepresentation) (weight : ℤ) :
    Submodule ℂ σ.smooth where
  carrier := {v | v.val ∈ levelThreeValues σ ∧
    ∀ angle : Circle, σ.π (atInfinity (binaryRotations angle)) v.val =
      (angle : ℂ) ^ weight • v.val}
  zero_mem' := by
    refine ⟨(levelThreeValues σ).zero_mem, ?_⟩
    intro angle
    simp
  add_mem' first second := by
    refine ⟨(levelThreeValues σ).add_mem first.1 second.1, ?_⟩
    intro angle
    simp only [Submodule.coe_add, map_add, first.2 angle, second.2 angle, smul_add]
  smul_mem' scalar v member := by
    refine ⟨(levelThreeValues σ).smul_mem scalar member.1, ?_⟩
    intro angle
    simp only [Submodule.coe_smul, map_smul, member.2 angle]
    exact smul_comm _ _ _

theorem mem_levelThreeWeightVectors {σ : CuspidalRepresentation} {weight : ℤ} {v : σ.smooth} :
    v ∈ levelThreeWeightVectors σ weight ↔ v.val ∈ levelThreeValues σ ∧
      ∀ angle : Circle, σ.π (atInfinity (binaryRotations angle)) v.val =
        (angle : ℂ) ^ weight • v.val :=
  Iff.rfl

/-- The holomorphic level-three vectors of rotation weight `2 * halfWeight` are level-three weight
vectors. -/
theorem levelThreeClassicalVectors_le_levelThreeWeightVectors (σ : CuspidalRepresentation)
    (halfWeight weight : ℤ) (h : 2 * halfWeight = weight) :
    levelThreeClassicalVectors σ halfWeight ≤ levelThreeWeightVectors σ weight := by
  intro v hv
  refine ⟨hv.1, fun angle => ?_⟩
  rw [← h]
  exact hv.2.1 angle

/-- A spherical vector of rotation weight `weight` is a level-three weight vector. -/
theorem levelThreeWeightVectors_mem_of_spherical {σ : CuspidalRepresentation} {weight : ℤ}
    {v : σ.smooth}
    (hsph : ∀ k : GeneralLinearGroup (Fin 2) IntegralAdeles,
      σ.π (atFinite (GeneralLinearGroup.map integralEmbedding k)) v.val = v.val)
    (hrot : ∀ angle : Circle, σ.π (atInfinity (binaryRotations angle)) v.val =
      (angle : ℂ) ^ weight • v.val) :
    v ∈ levelThreeWeightVectors σ weight :=
  ⟨fun k _ => hsph k, hrot⟩

/-! ## The bad-line Levi level is the plane Levi level -/

/-- `diag(1, k)` lies in the finite level iff `k` lies in the level-three Levi level. -/
theorem planeLeviLevel_iff_lineLevi_mem (k : GeneralLinearGroup (Fin 2) IntegralAdeles) :
    PlaneLeviLevel k ↔
      GeneralLinearGroup.map integralEmbedding (lineLevi 1 k) ∈ finiteLevel := by
  refine ⟨lineLevi_mem_finiteLevel_of_planeLeviLevel k, fun hk => ?_⟩
  obtain ⟨k', hk', hkk⟩ := Subgroup.mem_map.mp hk
  have hentry : ∀ i j, k'.val i j = (lineLevi 1 k).val i j := by
    intro i j
    apply integralEmbedding_injective
    have h := congrArg (fun g : GeneralLinearGroup (Fin 3) FiniteAdeles => g.val i j) hkk
    simpa only [GeneralLinearGroup.map_apply] using h
  have hrow : lastRow ᵥ* (GeneralLinearGroup.map integralReduction k').val = lastRow := hk'
  rw [CuspOrbits.lastRow_vecMul] at hrow
  have h1 := congrFun hrow 1
  have h2 := congrFun hrow 2
  simp only [GeneralLinearGroup.map_apply, hentry, lineLevi_val] at h1 h2
  refine ⟨?_, ?_⟩
  · rw [GeneralLinearGroup.map_apply]
    simpa [lastRow] using h1
  · rw [GeneralLinearGroup.map_apply]
    simpa [lastRow] using h2

end TernaryPeriodPolynomials.LevelThreeSource
