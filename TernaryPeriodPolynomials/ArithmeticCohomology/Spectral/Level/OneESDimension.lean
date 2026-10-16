module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Level.OneEichlerShimura
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.ModularSymDimension
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.OneCocyclePullback
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Modular.CocycleReflection
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.BinaryPeriodBoundary

@[expose] public section


/-!
# Eichler–Shimura at level one: the dimension count for `GL₂(ℤ)`

Restriction from `GL₂(ℤ)` to `SL₂(ℤ)` is injective on `H¹` (index two, characteristic zero), and
the restrictions of the two twists `det^τ`, `det^{τ+1}` land in opposite eigenspaces of the reflection
involution of `H¹(SL₂(ℤ), Sym^d)`. Hence
`dim H¹(GL₂ℤ, Sym^d ⊗ det^τ) + dim H¹(GL₂ℤ, Sym^d ⊗ det^{τ+1}) ≤ dim H¹(SL₂ℤ, Sym^d)`.
With the level-one dimension identity (`finrank_H1_sym_eq_cuspForms`) and injectivity of the period
map on all cusp forms (`levelOnePeriodMap_injective`), for `d = 2r ≥ 2`:
`dim S_{d+2} ≤ dim H¹(GL₂ℤ, Sym^d ⊗ det^τ) ≤ dim S_{d+2} + 1`
(`finrank_cuspForm_le_H1`, `finrank_H1_le_cuspForm_add_one`): the period image has codimension at
most one (the Eisenstein line).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open scoped ModularForm MatrixGroups
open Matrix GeneralEisenstein CategoryTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.Spectral.LevelOneESDimension

/-- The reflection `diag(1,-1)` in `GL₂(ℤ)`. -/
def reflectionGL : GL (Fin 2) ℤ :=
  ⟨!![1, 0; 0, -1], !![1, 0; 0, -1], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem reflectionGL_mul_self : reflectionGL * reflectionGL = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [reflectionGL, Matrix.mul_apply, Fin.sum_univ_two]

theorem reflectionGL_inv : reflectionGL⁻¹ = reflectionGL :=
  inv_eq_of_mul_eq_one_right reflectionGL_mul_self

theorem toGL_modularReflection (n : SL(2, ℤ)) :
    SpecialLinearGroup.toGL (modularReflection n) =
      reflectionGL * SpecialLinearGroup.toGL n * reflectionGL := by
  ext i j
  change (modularReflection n).val i j = _
  rw [modularReflection_apply]
  fin_cases i <;> fin_cases j <;>
    simp [reflectionGL, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

variable (d : ℕ)

theorem rho_reflection (σ : ℤ) (P : Binary.HomogeneousPoly d) :
    (arithmeticBinaryRep d σ).ρ reflectionGL P = (-1 : ℂ) ^ σ • binaryParityReflection d P := by
  apply Subtype.ext
  change (Binary.homogeneousAction d σ (GeneralLinearGroup.map (Int.castRingHom ℂ) reflectionGL) P).val =
    (-1 : ℂ) ^ σ • Binary.substitute !![1, 0; 0, -1] P.val
  rw [Binary.homogeneousAction_coe, Binary.action_apply]
  have hdet : Binary.determinantCharacter σ
      (GeneralLinearGroup.map (Int.castRingHom ℂ) reflectionGL) = (-1 : ℂ) ^ σ := by
    unfold Binary.determinantCharacter
    simp only [MonoidHom.coe_mk, OneHom.coe_mk]
    congr 1
    change ((reflectionGL.val).map (Int.castRingHom ℂ)).det = -1
    simp [reflectionGL, Matrix.det_fin_two]
  have hmat : (((GeneralLinearGroup.map (Int.castRingHom ℂ) reflectionGL)⁻¹ : Binary.GL2) :
      Matrix (Fin 2) (Fin 2) ℂ) = !![1, 0; 0, -1] := by
    rw [← map_inv, reflectionGL_inv]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [reflectionGL, GeneralLinearGroup.map_apply]
  rw [hdet, hmat]

theorem rho_reflection_sq (σ : ℤ) (P : arithmeticBinaryRep d σ) :
    (arithmeticBinaryRep d σ).ρ reflectionGL ((arithmeticBinaryRep d σ).ρ reflectionGL P) = P := by
  have h : (arithmeticBinaryRep d σ).ρ (reflectionGL * reflectionGL) = 1 := by
    rw [reflectionGL_mul_self, map_one]
  rw [map_mul] at h
  exact LinearMap.congr_fun h P

/-- `SL₂`-elements act by the same operator in every twist. -/
theorem rho_specialLinear_twist (σ τ : ℤ) (n : SL(2, ℤ)) :
    (arithmeticBinaryRep d σ).ρ (SpecialLinearGroup.toGL n) =
      (arithmeticBinaryRep d τ).ρ (SpecialLinearGroup.toGL n) := by
  apply LinearMap.ext
  intro P
  exact Subtype.ext ((arithmeticBinaryRep_specialLinear_coe d σ n P).trans
    (arithmeticBinaryRep_specialLinear_coe d τ n P).symm)

theorem restriction_intertwines (σ τ : ℤ) (n : SL(2, ℤ)) :
    ((modularBinaryRep d τ).ρ n).comp LinearMap.id =
      LinearMap.id.comp ((arithmeticBinaryRep d σ).ρ (SpecialLinearGroup.toGL n)) := by
  rw [LinearMap.comp_id, LinearMap.id_comp]
  exact (rho_specialLinear_twist d σ τ n).symm

/-- Restriction `H¹(GL₂ℤ, Sym^d ⊗ det^σ) → H¹(SL₂ℤ, Sym^d)` (target written with twist `τ`). -/
def restriction (σ τ : ℤ) :
    groupCohomology.H1 (arithmeticBinaryRep d σ) →ₗ[ℂ] groupCohomology.H1 (modularBinaryRep d τ) :=
  oneCocyclePullbackH1 (arithmeticBinaryRep d σ) (modularBinaryRep d τ) SpecialLinearGroup.toGL
    LinearMap.id (restriction_intertwines d σ τ)

theorem reflection_intertwines (τ : ℤ) (n : SL(2, ℤ)) :
    ((modularBinaryRep d τ).ρ n).comp (binaryParityReflection d) =
      (binaryParityReflection d).comp ((modularBinaryRep d τ).ρ (modularReflection n)) := by
  apply LinearMap.ext
  intro P
  exact (binaryParityReflection_modular_intertwines d τ n P).symm

/-- The reflection involution on `H¹(SL₂ℤ, Sym^d)`. -/
def reflectionH1 (τ : ℤ) :
    groupCohomology.H1 (modularBinaryRep d τ) →ₗ[ℂ] groupCohomology.H1 (modularBinaryRep d τ) :=
  oneCocyclePullbackH1 (modularBinaryRep d τ) (modularBinaryRep d τ) modularReflection
    (binaryParityReflection d) (reflection_intertwines d τ)

theorem restriction_apply (σ τ : ℤ) (z : groupCohomology.cocycles₁ (arithmeticBinaryRep d σ)) :
    restriction d σ τ (groupCohomology.H1π (arithmeticBinaryRep d σ) z) =
      groupCohomology.H1π (modularBinaryRep d τ)
        (oneCocyclePullback (arithmeticBinaryRep d σ) (modularBinaryRep d τ) SpecialLinearGroup.toGL
          LinearMap.id (restriction_intertwines d σ τ) z) :=
  oneCocyclePullbackH1_apply _ _ _ _ _ z

/-- The twist-`σ` action as an endomorphism of the polynomial space. -/
def rhoE (σ : ℤ) (g : GL (Fin 2) ℤ) : Module.End ℂ (Binary.HomogeneousPoly d) :=
  (arithmeticBinaryRep d σ).ρ g

/-- Values of a cocycle as polynomials. -/
def val {σ : ℤ} (z : groupCohomology.cocycles₁ (arithmeticBinaryRep d σ)) (g : GL (Fin 2) ℤ) :
    Binary.HomogeneousPoly d := z g

theorem val_mul {σ : ℤ} (z : groupCohomology.cocycles₁ (arithmeticBinaryRep d σ))
    (g h : GL (Fin 2) ℤ) : val d z (g * h) = rhoE d σ g (val d z h) + val d z g :=
  oneCocycle_mul _ z g h

theorem rhoE_mul (σ : ℤ) (g h : GL (Fin 2) ℤ) : rhoE d σ (g * h) = rhoE d σ g * rhoE d σ h :=
  map_mul _ g h

theorem rhoE_reflection (σ : ℤ) (P : Binary.HomogeneousPoly d) :
    rhoE d σ reflectionGL P = (-1 : ℂ) ^ σ • binaryParityReflection d P :=
  rho_reflection d σ P

theorem rhoE_sq (σ : ℤ) (P : Binary.HomogeneousPoly d) :
    rhoE d σ reflectionGL (rhoE d σ reflectionGL P) = P :=
  rho_reflection_sq d σ P

theorem rhoE_twist (σ τ : ℤ) (n : SL(2, ℤ)) :
    rhoE d σ (SpecialLinearGroup.toGL n) = rhoE d τ (SpecialLinearGroup.toGL n) :=
  rho_specialLinear_twist d σ τ n

theorem refl_eq_rho (σ : ℤ) (P : Binary.HomogeneousPoly d) :
    binaryParityReflection d P = (-1 : ℂ) ^ σ • rhoE d σ reflectionGL P := by
  rw [rhoE_reflection, smul_smul, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
    (show Even (σ + σ) from ⟨σ, rfl⟩).neg_one_zpow, one_smul]

/-- A function on `GL₂(ℤ)` satisfying the cocycle identity and vanishing on `SL₂(ℤ)` is a
coboundary (index two, characteristic zero). -/
theorem coboundary_of_vanishing (σ : ℤ) (c : GL (Fin 2) ℤ → Binary.HomogeneousPoly d)
    (hc : ∀ g h, c (g * h) = rhoE d σ g (c h) + c g)
    (hz : ∀ g : GL (Fin 2) ℤ, (g.val).det = 1 → c g = 0) :
    ∀ g, c g = rhoE d σ g (-(1 / 2 : ℂ) • c reflectionGL) - (-(1 / 2 : ℂ) • c reflectionGL) := by
  set w := c reflectionGL
  have hc1 : c 1 = 0 := hz 1 (by simp)
  have hεε : rhoE d σ reflectionGL w = -w := by
    have h1 := hc reflectionGL reflectionGL
    rw [reflectionGL_mul_self, hc1] at h1
    exact eq_neg_of_add_eq_zero_left h1.symm
  have hdetε : (reflectionGL.val).det = -1 := by simp [reflectionGL, Matrix.det_fin_two]
  have hfix : ∀ h : GL (Fin 2) ℤ, (h.val).det = 1 → rhoE d σ h w = w := by
    intro h hh
    have hconj : ((reflectionGL * h * reflectionGL).val).det = 1 := by
      simp [Matrix.det_mul, hh, hdetε]
    have h1 := hc reflectionGL (reflectionGL * h * reflectionGL)
    have h3 := hc h reflectionGL
    rw [hz _ hconj, map_zero, zero_add] at h1
    rw [hz h hh, add_zero] at h3
    have heq : reflectionGL * (reflectionGL * h * reflectionGL) = h * reflectionGL := by
      rw [← mul_assoc, ← mul_assoc, reflectionGL_mul_self, one_mul]
    rw [heq] at h1
    exact h3.symm.trans h1
  intro g
  have hunit : (g.val).det = 1 ∨ (g.val).det = -1 := Int.isUnit_iff.mp
    ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit)
  rcases hunit with hg | hg
  · rw [hz g hg, map_smul, hfix g hg, sub_self]
  · have hgε : ((g * reflectionGL).val).det = 1 := by
      simp [Matrix.det_mul, hg, hdetε]
    have h1 := hc (g * reflectionGL) reflectionGL
    rw [mul_assoc, reflectionGL_mul_self, mul_one, hz _ hgε, add_zero, hfix _ hgε] at h1
    have hρg : rhoE d σ g w = -w := by
      have : rhoE d σ g w = rhoE d σ (g * reflectionGL) (rhoE d σ reflectionGL w) := by
        rw [← Module.End.mul_apply, ← rhoE_mul, mul_assoc, reflectionGL_mul_self, mul_one]
      rw [this, hεε, map_neg, hfix _ hgε]
    rw [h1, map_smul, hρg]
    module

/-- **Restriction is injective** (index two, characteristic zero). -/
theorem restriction_injective (σ τ : ℤ) : Function.Injective (restriction d σ τ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨z, rfl⟩ := oneCocycle_H1_surjective (arithmeticBinaryRep d σ) x
  rw [restriction_apply, groupCohomology.H1π_eq_zero_iff] at hx
  obtain ⟨v₀, hv⟩ := hx
  let v : Binary.HomogeneousPoly d := v₀
  have hvn : ∀ n : SL(2, ℤ), val d z (SpecialLinearGroup.toGL n) =
      rhoE d σ (SpecialLinearGroup.toGL n) v - v := by
    intro n
    have h := congrFun hv n
    change rhoE d τ (SpecialLinearGroup.toGL n) v - v = val d z (SpecialLinearGroup.toGL n) at h
    rw [← h, rhoE_twist d τ σ n]
  let c : GL (Fin 2) ℤ → Binary.HomogeneousPoly d := fun g => val d z g - (rhoE d σ g v - v)
  have hc : ∀ g h, c (g * h) = rhoE d σ g (c h) + c g := by
    intro g h
    simp only [c, val_mul, rhoE_mul, Module.End.mul_apply, map_sub]
    abel
  have hz : ∀ g : GL (Fin 2) ℤ, (g.val).det = 1 → c g = 0 := by
    intro g hg
    have hgl : SpecialLinearGroup.toGL (⟨g.val, hg⟩ : SL(2, ℤ)) = g := Units.ext rfl
    have h := hvn ⟨g.val, hg⟩
    rw [hgl] at h
    simp only [c]
    rw [h, sub_self]
  have hcob := coboundary_of_vanishing d σ c hc hz
  apply (groupCohomology.H1π_eq_zero_iff z).mpr
  refine ⟨v + (-(1 / 2 : ℂ) • c reflectionGL), ?_⟩
  funext g
  change rhoE d σ g (v + (-(1 / 2 : ℂ) • c reflectionGL)) - (v + (-(1 / 2 : ℂ) • c reflectionGL)) =
    val d z g
  have hzg : val d z g = c g + (rhoE d σ g v - v) := by
    simp only [c]
    abel
  rw [hzg, hcob g, map_add]
  abel

/-- The restriction of a twist-`σ` class is a `(-1)^σ`-eigenvector of the reflection. -/
theorem reflectionH1_restriction (σ τ : ℤ) (x : groupCohomology.H1 (arithmeticBinaryRep d σ)) :
    reflectionH1 d τ (restriction d σ τ x) = (-1 : ℂ) ^ σ • restriction d σ τ x := by
  obtain ⟨z, rfl⟩ := oneCocycle_H1_surjective (arithmeticBinaryRep d σ) x
  rw [restriction_apply]
  set c := oneCocyclePullback (arithmeticBinaryRep d σ) (modularBinaryRep d τ)
    SpecialLinearGroup.toGL LinearMap.id (restriction_intertwines d σ τ) z
  let w : modularBinaryRep d τ := z reflectionGL
  have hcocycle : oneCocyclePullback (modularBinaryRep d τ) (modularBinaryRep d τ) modularReflection
      (binaryParityReflection d) (reflection_intertwines d τ) c =
      (-1 : ℂ) ^ σ • (c + oneBoundaryCycle (modularBinaryRep d τ) w) := by
    apply groupCohomology.cocycles₁_ext
    intro n
    have hεε : rhoE d σ reflectionGL (val d z reflectionGL) = -val d z reflectionGL := by
      have h1 := val_mul d z reflectionGL reflectionGL
      rw [reflectionGL_mul_self] at h1
      have h0 : val d z 1 = 0 := groupCohomology.cocycles₁_map_one z
      rw [h0] at h1
      exact eq_neg_of_add_eq_zero_left h1.symm
    have hval : val d z (SpecialLinearGroup.toGL (modularReflection n)) =
        rhoE d σ reflectionGL
          (rhoE d σ (SpecialLinearGroup.toGL n) (val d z reflectionGL) +
            val d z (SpecialLinearGroup.toGL n)) + val d z reflectionGL := by
      rw [toGL_modularReflection, mul_assoc, val_mul, val_mul]
    have key : rhoE d σ reflectionGL (val d z (SpecialLinearGroup.toGL (modularReflection n))) =
        val d z (SpecialLinearGroup.toGL n) +
          (rhoE d σ (SpecialLinearGroup.toGL n) (val d z reflectionGL) - val d z reflectionGL) := by
      rw [hval, map_add, rhoE_sq, hεε]
      abel
    change binaryParityReflection d (val d z (SpecialLinearGroup.toGL (modularReflection n))) =
      (-1 : ℂ) ^ σ • (val d z (SpecialLinearGroup.toGL n) +
        (rhoE d τ (SpecialLinearGroup.toGL n) (val d z reflectionGL) - val d z reflectionGL))
    rw [refl_eq_rho d σ, key, rhoE_twist d τ σ n]
  rw [show reflectionH1 d τ (groupCohomology.H1π (modularBinaryRep d τ) c) =
      groupCohomology.H1π (modularBinaryRep d τ)
        (oneCocyclePullback (modularBinaryRep d τ) (modularBinaryRep d τ) modularReflection
          (binaryParityReflection d) (reflection_intertwines d τ) c) from
      oneCocyclePullbackH1_apply _ _ _ _ _ c, hcocycle, map_smul, map_add,
    oneBoundaryCycle_H1_zero, add_zero]

/-- The two twists restrict to independent subspaces of `H¹(SL₂ℤ, Sym^d)`. -/
theorem restriction_pair_injective (τ : ℤ) :
    Function.Injective ((restriction d τ τ).coprod (restriction d (τ + 1) τ)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨x, y⟩ hxy
  simp only [LinearMap.coprod_apply] at hxy
  have href := congrArg (reflectionH1 d τ) hxy
  rw [map_add, reflectionH1_restriction, reflectionH1_restriction, map_zero,
    zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_one, mul_neg_one, neg_smul, ← sub_eq_add_neg,
    ← smul_sub] at href
  have hsub : restriction d τ τ x - restriction d (τ + 1) τ y = 0 :=
    (smul_eq_zero.mp href).resolve_left (zpow_ne_zero _ (by norm_num))
  have hx : restriction d τ τ x = 0 := by
    have h2 : (2 : ℂ) • restriction d τ τ x = 0 := by
      rw [two_smul]
      calc restriction d τ τ x + restriction d τ τ x =
          (restriction d τ τ x + restriction d (τ + 1) τ y) +
            (restriction d τ τ x - restriction d (τ + 1) τ y) := by abel
        _ = 0 := by rw [hxy, hsub, add_zero]
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
  have hy : restriction d (τ + 1) τ y = 0 := by
    rw [hx, zero_add] at hxy
    exact hxy
  have hx0 : x = 0 := restriction_injective d τ τ (by rw [hx, map_zero])
  have hy0 : y = 0 := restriction_injective d (τ + 1) τ (by rw [hy, map_zero])
  rw [hx0, hy0]
  rfl

theorem modularH1_finiteDimensional (τ : ℤ) :
    FiniteDimensional ℂ (groupCohomology.H1 (modularBinaryRep d τ)) := by
  have : FiniteDimensional ℂ (modularBinaryRep d τ) :=
    Module.Finite.of_basis (ModularSymDimension.monomialBasis d)
  exact Module.Finite.of_surjective (ModularH1.connecting (modularBinaryRep d τ))
    (ModularH1.connecting_surjective (modularBinaryRep d τ))

theorem arithmeticH1_finiteDimensional (σ : ℤ) :
    FiniteDimensional ℂ (groupCohomology.H1 (arithmeticBinaryRep d σ)) := by
  have := modularH1_finiteDimensional d σ
  exact Module.Finite.of_injective (restriction d σ σ) (restriction_injective d σ σ)

/-- **Dimension count**: the two twists together fit into `H¹(SL₂ℤ)`. -/
theorem finrank_H1_twists_le (τ : ℤ) :
    Module.finrank ℂ (groupCohomology.H1 (arithmeticBinaryRep d τ)) +
        Module.finrank ℂ (groupCohomology.H1 (arithmeticBinaryRep d (τ + 1))) ≤
      Module.finrank ℂ (groupCohomology.H1 (modularBinaryRep d τ)) := by
  have := modularH1_finiteDimensional d τ
  have := arithmeticH1_finiteDimensional d τ
  have := arithmeticH1_finiteDimensional d (τ + 1)
  rw [← Module.finrank_prod]
  exact LinearMap.finrank_le_finrank_of_injective (restriction_pair_injective d τ)

theorem exists_parity (σ : ℤ) : ∃ parity : Fin 2, (-1 : ℂ) ^ σ = (-1 : ℂ) ^ parity.val := by
  rcases Int.even_or_odd σ with h | h
  · exact ⟨0, by rw [h.neg_one_zpow]; simp⟩
  · exact ⟨1, by rw [h.neg_one_zpow]; simp⟩

/-- **Lower bound**: every level-one cusp form contributes, for every twist. -/
theorem finrank_cuspForm_le_H1 (r : ℕ) (σ : ℤ) :
    Module.finrank ℂ (CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range
        ((2 * r + 2 : ℕ) : ℤ)) ≤
      Module.finrank ℂ (groupCohomology.H1 (arithmeticBinaryRep (2 * r) σ)) := by
  have := arithmeticH1_finiteDimensional (2 * r) σ
  obtain ⟨parity, sign⟩ := exists_parity σ
  have weight_eq : -2 * (-((r : ℤ) + 1)) = ((2 * r : ℕ) : ℤ) + 2 := by push_cast; ring
  have hk : ((2 * r + 2 : ℕ) : ℤ) = -2 * (-((r : ℤ) + 1)) := by push_cast; ring
  rw [hk]
  exact LinearMap.finrank_le_finrank_of_injective
    (LevelOneEichlerShimura.levelOnePeriodMap_injective (-((r : ℤ) + 1)) (2 * r) weight_eq
      (even_two_mul r) σ parity sign)

/-- **Eichler–Shimura at level one (dimension form)**: for `r ≥ 1` and every twist,
`dim H¹(GL₂ℤ, Sym^{2r} ⊗ det^σ) ≤ dim S_{2r+2}(SL₂ℤ) + 1`; together with the injective period map
(`finrank_cuspForm_le_H1`) the period image has codimension at most one. -/
theorem finrank_H1_le_cuspForm_add_one (r : ℕ) (positive : 0 < r) (σ : ℤ) :
    Module.finrank ℂ (groupCohomology.H1 (arithmeticBinaryRep (2 * r) σ)) ≤
      Module.finrank ℂ (CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range
        ((2 * r + 2 : ℕ) : ℤ)) + 1 := by
  have hsum := finrank_H1_twists_le (2 * r) σ
  have hmod := ModularSymDimension.finrank_H1_sym_eq_cuspForms r positive σ
  have hlow := finrank_cuspForm_le_H1 r (σ + 1)
  change Module.finrank ℂ (groupCohomology.H1 (modularBinaryRep (2 * r) σ)) = _ at hmod
  omega

end TernaryPeriodPolynomials.Spectral.LevelOneESDimension
