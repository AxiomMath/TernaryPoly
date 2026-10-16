module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.PrimeHecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.ResolutionModelFarey
public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.Inflation

@[expose] public section


/-!
# The binary Hecke datum of `diag(1/p, 1)` on `GL₂(ℤ)` and its operator in the dual Farey tree

Formalized by Claude Sonnet 5.5.

* `binDatum p : HeckeDatum binIota (C1 p)`: `Γ = GL₂(ℤ) ⊂ GL₂(ℚ)`, `g = diag(1/p, 1)`, `S = {k | p ∣ k₀₁}`
  (`mem_commSubgroup_C1`; of finite index since it contains the kernel of reduction mod `p`),
  `f k = g k g⁻¹ = (k₀₀, k₀₁/p; p k₁₀, k₁₁)` (`binDatum_f_val`).  Its homology operator `heckeOp (binDatum p) M 1` on
  `H₁(GL₂(ℤ), Res M)` is the binary `T₂(p)` that `T₃(p,1)` decomposes into (the `P_H`-level correspondence of `ξ₁` has
  Levi image this datum).
* `binDatum_hproj`, `binDatum_hprojS`: the terms of the dual Farey tree are projective over `S`, also after restriction
  along `f` (inflation from the finite-kernel lemma `projective_res_P0/P1`).
* `binLift p`: an abstract lift of the correspondence to the dual Farey tree (by projectivity), over the identity of the
  trivial module (`binLift_overId`).
* `binary_hecke_H1Iso`: under `H1Iso`, `heckeOp (binDatum p) M 1` is the restriction to `ker dC` of the degree-one component
  of the ambient operator of `binLift p`; `binary_resHecke_mk` gives it on generators.
-/

open CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeHomology

open TernaryPoly.RankTwoAugmentedFrames TernaryPoly.OrdinaryResidueParabolic
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.BinaryDuality
open CategoryTheory.Limits ZeroObject

/-- The integral points in the rational binary group. -/
abbrev binIota : IntegralGL →* GL2 := TernaryPoly.BinaryModularSymbol.integral

theorem binIota_injective : Function.Injective binIota := by
  intro g h he
  apply Units.ext
  ext i j
  have e := congrArg (fun r : GL2 => r.val i j) he
  change ((g.val i j : ℤ) : ℚ) = ((h.val i j : ℤ) : ℚ) at e
  exact_mod_cast e

variable (p : ℕ) [Fact p.Prime]

/-- Conjugation by `diag(1/p, 1)` on integer matrices whose `(0,1)` entry is divisible by `p`:
`(a b; c d) ↦ (a b/p; p c d)`. -/
def cjMat (M : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![M 0 0, M 0 1 / p; p * M 1 0, M 1 1]

theorem cjMat_mul {M N : Matrix (Fin 2) (Fin 2) ℤ} (hM : (p : ℤ) ∣ M 0 1) (hN : (p : ℤ) ∣ N 0 1) :
    cjMat p (M * N) = cjMat p M * cjMat p N := by
  obtain ⟨b, hb⟩ := hM
  obtain ⟨b', hb'⟩ := hN
  have hp := p_ne_zero_int (p := p)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cjMat, Matrix.mul_apply, Fin.sum_univ_two, hb, hb', Int.mul_ediv_cancel_left _ hp]
  all_goals try ring1
  all_goals
    rw [show M 0 0 * ((p : ℤ) * b') + (p : ℤ) * b * N 1 1 = p * (M 0 0 * b' + b * N 1 1) by ring,
      Int.mul_ediv_cancel_left _ hp]

theorem cjMat_one : cjMat p 1 = 1 := by
  have hp := p_ne_zero_int (p := p)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cjMat]

theorem dvd_inv_zero_one {K L : Matrix (Fin 2) (Fin 2) ℤ} (hKL : K * L = 1) (h : (p : ℤ) ∣ K 0 1) :
    (p : ℤ) ∣ L 0 1 := by
  have e00 := congrArg (fun m : Matrix (Fin 2) (Fin 2) ℤ => m 0 0) hKL
  have e01 := congrArg (fun m : Matrix (Fin 2) (Fin 2) ℤ => m 0 1) hKL
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01
  have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
  have h1 : (p : ℤ) ∣ K 0 0 * L 0 1 := by
    have : K 0 0 * L 0 1 = -(K 0 1 * L 1 1) := by linarith
    rw [this]
    exact (h.mul_right _).neg_right
  rcases hpr.dvd_or_dvd h1 with h2 | h2
  · exfalso
    have : (p : ℤ) ∣ 1 := by
      have : (1 : ℤ) = K 0 0 * L 0 0 + K 0 1 * L 1 0 := e00.symm
      rw [this]
      exact (h2.mul_right _).add (h.mul_right _)
    exact hpr.not_dvd_one this
  · exact h2

/-- Conjugation by `diag(1/p, 1)` as a map on `GL₂(ℤ)`, defined on the elements with `p ∣ k₀₁`. -/
def cjUnit (k : IntegralGL) (hk : (p : ℤ) ∣ k.val 0 1) : IntegralGL where
  val := cjMat p k.val
  inv := cjMat p k.inv
  val_inv := by
    rw [← cjMat_mul p hk (dvd_inv_zero_one p k.val_inv hk), k.val_inv, cjMat_one]
  inv_val := by
    rw [← cjMat_mul p (dvd_inv_zero_one p k.val_inv hk) hk, k.inv_val, cjMat_one]

theorem C1_conj_val (k : IntegralGL) :
    ((C1 p * binIota k * (C1 p)⁻¹ : GL2) : Matrix (Fin 2) (Fin 2) ℚ) =
      !![((k.val 0 0 : ℤ) : ℚ), ((k.val 0 1 : ℤ) : ℚ) / p; (p : ℚ) * ((k.val 1 0 : ℤ) : ℚ),
        ((k.val 1 1 : ℤ) : ℚ)] := by
  have hp := p_ne_zero_rat p
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [binIota, TernaryPoly.BinaryModularSymbol.integral, C1, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.GeneralLinearGroup.map, Matrix.vecMul, dotProduct, Matrix.map_apply]
  all_goals field_simp

theorem mem_commSubgroup_C1 (k : IntegralGL) :
    k ∈ commSubgroup binIota (C1 p) ↔ (p : ℤ) ∣ k.val 0 1 := by
  have hp := p_ne_zero_rat p
  constructor
  · rintro ⟨δ, hδ⟩
    have e := congrArg (fun r : GL2 => r.val 0 1) hδ
    have e2 := congrArg (fun m : Matrix (Fin 2) (Fin 2) ℚ => m 0 1) (C1_conj_val p k)
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] at e2
    have e3 : ((δ.val 0 1 : ℤ) : ℚ) = ((k.val 0 1 : ℤ) : ℚ) / p := by
      rw [← e2]
      exact e
    refine ⟨δ.val 0 1, ?_⟩
    have : ((k.val 0 1 : ℤ) : ℚ) = (p : ℚ) * ((δ.val 0 1 : ℤ) : ℚ) := by
      rw [e3]; field_simp
    exact_mod_cast this
  · intro hk
    refine ⟨cjUnit p k hk, ?_⟩
    apply Units.ext
    rw [C1_conj_val]
    obtain ⟨b, hb⟩ := hk
    have hp' := p_ne_zero_int (p := p)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [binIota, TernaryPoly.BinaryModularSymbol.integral, cjUnit, cjMat, Matrix.GeneralLinearGroup.map, hb,
        Int.mul_ediv_cancel_left _ hp', hp]

theorem binIota_cjUnit (k : IntegralGL) (hk : (p : ℤ) ∣ k.val 0 1) :
    binIota (cjUnit p k hk) = C1 p * binIota k * (C1 p)⁻¹ := by
  apply Units.ext
  rw [C1_conj_val]
  obtain ⟨b, hb⟩ := hk
  have hp := p_ne_zero_rat p
  have hp' := p_ne_zero_int (p := p)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [binIota, TernaryPoly.BinaryModularSymbol.integral, cjUnit, cjMat, Matrix.GeneralLinearGroup.map, hb,
      Int.mul_ediv_cancel_left _ hp', hp]

/-- The commensurated subgroup `{k | p ∣ k₀₁}` has finite index: it contains the kernel of reduction mod `p`. -/
theorem finiteIndex_commSubgroup_C1 : (commSubgroup binIota (C1 p)).FiniteIndex := by
  let red : IntegralGL →* GL (Fin 2) (ZMod p) :=
    Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod p))
  have : Finite (GL (Fin 2) (ZMod p)) := inferInstance
  have : red.ker.FiniteIndex := Subgroup.finiteIndex_ker red
  refine Subgroup.finiteIndex_of_le (H := red.ker) ?_
  intro k hk
  rw [mem_commSubgroup_C1]
  have h01 := congrArg (fun m : GL (Fin 2) (ZMod p) => (m : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1)
    (MonoidHom.mem_ker.mp hk)
  simp [red, Matrix.GeneralLinearGroup.map] at h01
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h01

/-- **The binary Hecke datum** of `g = diag(1/p, 1)` on `Γ = GL₂(ℤ) ⊂ GL₂(ℚ)`: `S = {k | p ∣ k₀₁}`,
`f k = g k g⁻¹ = (k₀₀, k₀₁/p; p k₁₀, k₁₁)`. -/
def binDatum : HeckeDatum binIota (C1 p) :=
  HeckeDatum.ofInjective binIota_injective (C1 p) (finiteIndex_commSubgroup_C1 p)

theorem binDatum_S : (binDatum p).S = commSubgroup binIota (C1 p) := rfl

theorem binDatum_f (s : (binDatum p).S) :
    (binDatum p).f s = cjUnit p s.1 ((mem_commSubgroup_C1 p s.1).mp s.2) := by
  apply binIota_injective
  rw [(binDatum p).hf s, binIota_cjUnit]

theorem binDatum_f_val (s : (binDatum p).S) :
    (((binDatum p).f s : IntegralGL).val : Matrix (Fin 2) (Fin 2) ℤ) = cjMat p s.1.val := by
  rw [binDatum_f]
  rfl

theorem binDatum_f_injective : Function.Injective (binDatum p).f := by
  intro s t h
  have h1 := (binDatum p).hf s
  have h2 := (binDatum p).hf t
  rw [h] at h1
  have h3 : binIota s.1 = binIota t.1 := by
    have : C1 p * binIota s.1 * (C1 p)⁻¹ = C1 p * binIota t.1 * (C1 p)⁻¹ := h1.symm.trans h2
    simpa using this
  exact Subtype.ext (binIota_injective h3)

theorem binDatum_ker_finite : (((binDatum p).f.ker : Subgroup (binDatum p).S) : Set (binDatum p).S).Finite := by
  have : (binDatum p).f.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr (binDatum_f_injective p)
  rw [this, Subgroup.coe_bot]
  exact Set.finite_singleton _

/-- The terms of the Farey resolution restricted along the correspondence map are projective. -/
theorem binDatum_hproj (q : ℕ) :
    Projective ((Rep.resFunctor (binDatum p).f).obj (farResolution.complex.X q)) := by
  change Projective (Rep.res (binDatum p).f (farX q))
  match q with
  | 0 => exact HochschildSerre.projective_res_P0 (binDatum p).f (binDatum_ker_finite p)
  | 1 => exact HochschildSerre.projective_res_P1 (binDatum p).f (binDatum_ker_finite p)
  | q + 2 =>
    exact ((Rep.resFunctor (binDatum p).f).map_isZero (isZero_zero (Rep ℚ IntegralGL))).projective

theorem binDatum_hprojS (q : ℕ) :
    Projective ((Rep.resFunctor (binDatum p).S.subtype).obj (farResolution.complex.X q)) := by
  change Projective (Rep.res (binDatum p).S.subtype (farX q))
  have hker : (((binDatum p).S.subtype.ker : Subgroup (binDatum p).S) : Set (binDatum p).S).Finite := by
    have : (binDatum p).S.subtype.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr (Subtype.val_injective)
    rw [this, Subgroup.coe_bot]
    exact Set.finite_singleton _
  match q with
  | 0 => exact HochschildSerre.projective_res_P0 (binDatum p).S.subtype hker
  | 1 => exact HochschildSerre.projective_res_P1 (binDatum p).S.subtype hker
  | q + 2 =>
    exact ((Rep.resFunctor (binDatum p).S.subtype).map_isZero (isZero_zero (Rep ℚ IntegralGL))).projective

/-- **An abstract lift of the binary correspondence to the dual Farey tree**, by projectivity. -/
def binLift : LiftRes (binDatum p) farResolution :=
  ProjectiveResolution.lift (𝟙 (Rep.trivial ℚ (binDatum p).S ℚ))
    (resfResolution (binDatum p).S.subtype farResolution (binDatum_hprojS p))
    (resfResolution (binDatum p).f farResolution (binDatum_hproj p))

theorem binLift_overId : LiftOverId (binDatum p) farResolution (binLift p) := by
  have h := ProjectiveResolution.lift_commutes_zero (𝟙 (Rep.trivial ℚ (binDatum p).S ℚ))
    (resfResolution (binDatum p).S.subtype farResolution (binDatum_hprojS p))
    (resfResolution (binDatum p).f farResolution (binDatum_hproj p))
  exact h.trans (Category.comp_id _)

/-- **The binary Hecke operator in the Farey model.**  Under `H1Iso`, the homology Hecke operator of the binary
datum on `H₁(GL₂(ℤ), Res_ι M)` is the restriction to `ker dC` of the degree-one component of the ambient
operator computed with the lift `binLift`. -/
theorem binary_hecke_H1Iso (M : Rep.{0} ℚ GL2) :
    heckeOp (binDatum p) M 1 ≫ (H1Iso (Rep.res binIota M)).hom =
      (H1Iso (Rep.res binIota M)).hom ≫ ResHeckeKer (binDatum p) M (binLift p) :=
  heckeOp_H1Iso (binDatum p) M (binLift p) (binLift_overId p) (binDatum_hproj p)

/-- The ambient operator on generators: `[m ⊗ r] ↦ ∑_{S x ∈ S\Γ} [C₁ (x m) ⊗ lam (x r)]`. -/
theorem binary_resHecke_mk (M : Rep.{0} ℚ GL2) (q : ℕ) (m : Rep.res binIota M)
    (r : farResolution.complex.X q) :
    ((ResHecke (binDatum p) M farResolution (binLift p)).f q).hom
        (Representation.Coinvariants.mk _ (m ⊗ₜ[ℚ] r)) =
      ∑ x : RC (binDatum p).S, Representation.Coinvariants.mk
        ((Rep.res binIota M).ρ.tprod (farResolution.complex.X q).ρ)
        (M.ρ (C1 p) ((Rep.res binIota M).ρ x.out m) ⊗ₜ[ℚ]
          ((binLift p).f q).hom ((farResolution.complex.X q).ρ x.out r)) :=
  ResHecke_f_mk (binDatum p) M farResolution (binLift p) q m r

end TernaryPeriodPolynomials.Argument.HeckeHomology
