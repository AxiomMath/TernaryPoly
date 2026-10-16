module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.LocalInterface
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.ParabolicES
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.PairCharacterBound
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Good.LineRestriction
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Identity.PlaneEven

@[expose] public section


/-!
# Local uniqueness at the two level-one cusps

At the identity-plane cusp and at the good-line cusp the Levi quotient of the stabilizer is
`GL₂(ℤ)`, and the binary Hochschild–Serre edges are injective:
* identity plane: `E : H²(Γ_F, V) ↪ H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)` with
  `E(T_p x) = E x + p^{-(n+2)} T_p^{GL₂} E x`;
* good line: `T_p` acts by `λ_p = p + 1 + ε_p^{-(n+1)}` modulo the subspace `KL` of classes with
  vanishing radical restriction, and `E : KL ↪ H¹(GL₂(ℤ), Sym^{n+1})` with
  `E(T_p y) = E y + p^{-(n+1)} T_p^{GL₂} E y`.
The pair character satisfies `|c(T_p) - 1| ≤ (p² + p) p^{-(n+3)/2}`, which at `p = 2` and `n ≥ 3` is at
most `3/4`. This separates it from `λ_2` (so local generalized eigenclasses lie in `KL`) and from the
Eisenstein eigenvalue of the boundary functional of `H¹(GL₂(ℤ))`. The local joint generalized
eigenspace therefore embeds into a joint generalized eigenspace of level-one `H¹` which consists of
period classes, hence has dimension at most one by generalized multiplicity one.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.Spectral.LocalUniqueness

open CuspOrbits CuspReduction LocalInterface ParabolicES

section Generic

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- A map with `f (A v) = f v + s • B (f v)` (`s ≠ 0`) sends generalized eigenvectors of `A` of
eigenvalue `μ` to generalized eigenvectors of `B` of eigenvalue `(μ - 1) / s`. -/
theorem map_mem_maxGenEigenspace_of_affine (f : V →ₗ[ℂ] W) (A : Module.End ℂ V)
    (B : Module.End ℂ W) (s μ : ℂ) (hs : s ≠ 0) (hrel : ∀ v, f (A v) = f v + s • B (f v))
    {v : V} (hv : v ∈ A.maxGenEigenspace μ) : f v ∈ B.maxGenEigenspace ((μ - 1) / s) := by
  rw [Module.End.mem_maxGenEigenspace] at hv ⊢
  obtain ⟨k, hk⟩ := hv
  refine ⟨k, ?_⟩
  have hone : ∀ w : V, f ((A - μ • 1) w) = s • (B - ((μ - 1) / s) • 1) (f w) := by
    intro w
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub,
      map_smul, hrel, smul_sub, smul_smul]
    rw [mul_div_cancel₀ _ hs, sub_smul, one_smul]
    abel
  have hpow : ∀ (m : ℕ) (w : V),
      f (((A - μ • 1) ^ m) w) = s ^ m • ((B - ((μ - 1) / s) • 1) ^ m) (f w) := by
    intro m
    induction m with
    | zero => intro w; simp
    | succ m ih =>
      intro w
      rw [pow_succ, Module.End.mul_apply, ih, hone, map_smul, smul_smul, pow_succ, pow_succ,
        Module.End.mul_apply]
  have h := hpow k v
  rw [hk, map_zero] at h
  exact (smul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ hs)

/-- A map with `L (A v) = q • L v` kills generalized eigenvectors of `A` of eigenvalue `μ ≠ q`. -/
theorem map_eq_zero_of_mem_maxGenEigenspace (L : V →ₗ[ℂ] W) (A : Module.End ℂ V) (q μ : ℂ)
    (hL : ∀ v, L (A v) = q • L v) (hμ : μ ≠ q) {v : V} (hv : v ∈ A.maxGenEigenspace μ) :
    L v = 0 := by
  rw [Module.End.mem_maxGenEigenspace] at hv
  obtain ⟨k, hk⟩ := hv
  have hpow : ∀ (m : ℕ) (w : V), L (((A - μ • 1) ^ m) w) = (q - μ) ^ m • L w := by
    intro m
    induction m with
    | zero => intro w; simp
    | succ m ih =>
      intro w
      rw [pow_succ, Module.End.mul_apply, ih]
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub,
        map_smul, hL, smul_sub, smul_smul, pow_succ]
      rw [← sub_smul, ← mul_sub]
  have h := hpow k v
  rw [hk, map_zero] at h
  exact (smul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hμ)))

end Generic

/-- The prime `2`. -/
def two : Nat.Primes := ⟨2, Nat.prime_two⟩

theorem two_ne_three : two.val ≠ 3 := by decide

variable {n : ℕ}

/-- For `n ≥ 3` the pair character at `T_2` is within `3/4` of `1`. -/
theorem pairCharacter_two_sub_one_norm_le (D : CohomologicalCuspData n)
    (hecke : BoundaryHecke n D.inducingData.chi)
    (hhecke : ActualBoundaryHecke n D.inducingData.chi hecke) (hn : 3 ≤ n)
    (hne : associatePair D.inducingData ≠ ⊥) :
    ‖pairCharacter D.inducingData hecke hhecke (TpExistence.tp two) - 1‖ ≤ 3 / 4 := by
  have h := PairCharacterBound.pairCharacter_tp_sub_one_norm_le D.inducingData rfl hecke hhecke
    hne two two_ne_three
  refine h.trans ?_
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hexp : Real.exp (-(((n : ℝ) + 3) / 2 * Real.log ((two.val : ℕ) : ℝ))) ≤ 1 / 8 := by
    have h8 : Real.exp (-(3 * Real.log 2)) = 1 / 8 := by
      rw [Real.exp_neg, ← Real.log_rpow (by norm_num), Real.exp_log (by positivity)]
      norm_num
    rw [← h8]
    apply Real.exp_le_exp.mpr
    have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
    change -(((n : ℝ) + 3) / 2 * Real.log ((2 : ℕ) : ℝ)) ≤ -(3 * Real.log 2)
    push_cast
    nlinarith
  change ((((2 : ℕ) : ℝ)) ^ 2 + ((2 : ℕ) : ℝ)) *
      Real.exp (-(((n : ℝ) + 3) / 2 * Real.log ((2 : ℕ) : ℝ))) ≤ 3 / 4
  have : (((2 : ℕ) : ℝ)) ^ 2 + ((2 : ℕ) : ℝ) = 6 := by norm_num
  rw [this]
  change (6 : ℝ) * Real.exp (-(((n : ℝ) + 3) / 2 * Real.log ((two.val : ℕ) : ℝ))) ≤ 3 / 4
  linarith

/-- Transport of finrank of the joint generalized eigenspace along an equality of degrees. -/
theorem finrank_jointH1_congr {d d' : ℕ} (h : d = d') (σ : ℤ) (e : Nat.Primes → ℂ) :
    Module.finrank ℂ (jointH1 d σ e) = Module.finrank ℂ (jointH1 d' σ e) := by
  subst h
  rfl

/-- A submodule mapped injectively into a submodule has smaller dimension. -/
theorem finrank_le_of_injective_map {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (f : V →ₗ[ℂ] W) (hf : Function.Injective f) (K : Submodule ℂ V)
    (L : Submodule ℂ W) [FiniteDimensional ℂ L] (hKL : ∀ x ∈ K, f x ∈ L) :
    Module.finrank ℂ K ≤ Module.finrank ℂ L := by
  rw [LinearEquiv.finrank_eq (Submodule.equivMapOfInjective f hf K)]
  apply Submodule.finrank_mono
  rintro _ ⟨x, hx, rfl⟩
  exact hKL x hx

/-! ### The identity-plane cusp -/

section IdentityPlane

open IdentityPlaneHecke IdentityPlaneLocalOp

/-- The `H¹` eigenvalues seen by the identity-plane edge: `p^{n+2} (c(T_p) - 1)`. -/
def eIdentity (n : ℕ) (c : HeckeCorrespondence → ℂ) (p : Nat.Primes) : ℂ :=
  (c (TpExistence.tp p) - 1) / ((p.val : ℂ) ^ (n + 2))⁻¹

/-- **The identity-plane edge maps the local joint generalized eigenspace into the joint
generalized eigenspace of level-one `H¹`.** -/
theorem edgeH2_mem_jointH1 (c : HeckeCorrespondence → ℂ) (hn : 0 < n) (hodd : Odd n)
    {x : CuspH2 n trivialCharacter .plane false}
    (hx : x ∈ localJoint n trivialCharacter c .plane false) :
    edgeH2 n hn hodd x ∈ jointH1 (n + 1) (-1) (eIdentity n c) := by
  rw [jointH1, Submodule.mem_iInf]
  rintro ⟨p, hp3⟩
  have hxp := (Submodule.mem_iInf _).mp hx ⟨TpExistence.tp p, TpExistence.tp_awayThree p hp3⟩
  have hs : ((p.val : ℂ) ^ (n + 2))⁻¹ ≠ 0 :=
    inv_ne_zero (pow_ne_zero _ (by exact_mod_cast p.property.ne_zero))
  exact map_mem_maxGenEigenspace_of_affine (edgeH2 n hn hodd)
    (localOp n trivialCharacter (TpExistence.tp p) (TpExistence.tp_awayThree p hp3) .plane false)
    (LevelOneHeckeH1.arithmeticHecke (n + 1) (-1) p) _ _ hs
    (edgeH2_localOp_tp p n hn hodd hp3) hxp

/-- The local joint generalized eigenspace at the identity plane has dimension at most that of the
joint generalized eigenspace of level-one `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)`. -/
theorem finrank_localJoint_identityPlane_le (c : HeckeCorrespondence → ℂ) (hn : 0 < n)
    (hodd : Odd n)
    [FiniteDimensional ℂ (jointH1 (n + 1) (-1) (eIdentity n c))] :
    Module.finrank ℂ
        (localJoint n trivialCharacter c .plane false) ≤
      Module.finrank ℂ (jointH1 (n + 1) (-1) (eIdentity n c)) :=
  finrank_le_of_injective_map (edgeH2 n hn hodd) (edgeH2_injective n hn hodd) _ _
    (fun _ hx => edgeH2_mem_jointH1 c hn hodd hx)

end IdentityPlane

/-! ### The good-line cusp -/

section GoodLine

open GoodLineHecke GoodLineLocalOp GoodLineRestriction IdentityPlaneCosets

/-- The `H¹` eigenvalues seen by the good-line edge: `p^{n+1} (c(T_p) - 1)`. -/
def eGoodLine (n : ℕ) (c : HeckeCorrespondence → ℂ) (p : Nat.Primes) : ℂ :=
  (c (TpExistence.tp p) - 1) / ((p.val : ℂ) ^ (n + 1))⁻¹

/-- The good-line classes whose transport has vanishing radical restriction. -/
abbrev ML (n : ℕ) : Submodule ℂ (CuspH2 n trivialCharacter .line true) := (KL n).comap (psiL n)

/-- The good-line edge on `ML`. -/
def phiL (n : ℕ) (hn : 0 < n) : ML n →ₗ[ℂ] groupCohomology.H1 (arithmeticBinaryRep (n + 1) 0) :=
  edgeK n hn ∘ₗ (psiL n).restrict (fun _ hy => Submodule.mem_comap.mp hy)

theorem phiL_injective (hn : 0 < n) : Function.Injective (phiL n hn) := by
  intro y y' h
  have h1 := edgeK_injective n hn h
  apply Subtype.ext
  exact psiL_injective n (congrArg Subtype.val h1)

/-- `λ_2 = 3 + ε_2^{-(n+1)}` is at distance more than `3/4` from `1 + ...`: `|λ_2 - 1| > 3/4`. -/
theorem lamL_two_sub_one_norm (n : ℕ) : 3 / 4 < ‖lamL n two - 1‖ := by
  have heps : epsP two = -2 := by decide
  have hval : lamL n two - 1 = 2 + ((-1 / 2 : ℂ)) ^ (n + 1) := by
    rw [lamL, heps]
    change ((2 : ℕ) : ℂ) + 1 + (((-2 : ℤ) : ℂ)⁻¹) ^ (n + 1) - 1 = _
    push_cast
    ring_nf
  rw [hval]
  have hsmall : ‖((-1 / 2 : ℂ)) ^ (n + 1)‖ ≤ 1 / 2 := by
    rw [norm_pow]
    have h2 : ‖(-1 / 2 : ℂ)‖ = 1 / 2 := by
      rw [norm_div, norm_neg, norm_one]
      simp
    rw [h2]
    calc (1 / 2 : ℝ) ^ (n + 1) ≤ (1 / 2) ^ 1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 2 := by norm_num
  have htri := norm_sub_norm_le (2 : ℂ) (-(((-1 / 2 : ℂ)) ^ (n + 1)))
  rw [sub_neg_eq_add, norm_neg] at htri
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  linarith

/-- **Local generalized eigenclasses at the good line lie in `ML`**: the pair character at `T_2`
differs from the eigenvalue `λ_2` of `T_2` on the quotient by `KL`. -/
theorem localJoint_le_ML (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp two) - 1‖ ≤ 3 / 4) :
    localJoint n trivialCharacter c .line true ≤ ML n := by
  intro y hy
  have hy2 := (Submodule.mem_iInf _).mp hy ⟨TpExistence.tp two, TpExistence.tp_awayThree two two_ne_three⟩
  have hne2 : c (TpExistence.tp two) ≠ lamL n two := by
    intro h
    have h2 := lamL_two_sub_one_norm n
    rw [h] at hc
    linarith
  have hzero := map_eq_zero_of_mem_maxGenEigenspace ((KL n).mkQ ∘ₗ psiL n)
    (localOp n trivialCharacter (TpExistence.tp two) (TpExistence.tp_awayThree two two_ne_three)
      .line true) (lamL n two) _ (fun v => by
        have hmem := localOp_sub_mem_KL n two (TpExistence.tp two)
          (TpExistence.tp_awayThree two two_ne_three) (TpExistence.tp_g two) two_ne_three v
        simp only [LinearMap.comp_apply]
        rw [← sub_eq_zero, ← map_smul, ← map_sub, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero]
        exact hmem) hne2 hy2
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hzero
  exact Submodule.mem_comap.mpr hzero

theorem localOp_mem_ML (n : ℕ) (hn : 0 < n) (p : Nat.Primes) (hp3 : p.val ≠ 3)
    (y : CuspH2 n trivialCharacter .line true) (hy : y ∈ ML n) :
    localOp n trivialCharacter (TpExistence.tp p) (TpExistence.tp_awayThree p hp3) .line true y ∈
      ML n := by
  obtain ⟨hmem, -⟩ := edgeK_localOp_tp n p hn hp3 y (Submodule.mem_comap.mp hy)
  exact Submodule.mem_comap.mpr hmem

/-- The local `T_p` at the good line, restricted to `ML`. -/
def localOpML (n : ℕ) (hn : 0 < n) (p : Nat.Primes) (hp3 : p.val ≠ 3) : Module.End ℂ (ML n) :=
  (localOp n trivialCharacter (TpExistence.tp p) (TpExistence.tp_awayThree p hp3) .line true).restrict
    (localOp_mem_ML n hn p hp3)

theorem phiL_localOpML (hn : 0 < n) (p : Nat.Primes) (hp3 : p.val ≠ 3) (y : ML n) :
    phiL n hn (localOpML n hn p hp3 y) =
      phiL n hn y + ((p.val : ℂ) ^ (n + 1))⁻¹ •
        LevelOneHeckeH1.arithmeticHecke (n + 1) 0 p (phiL n hn y) := by
  obtain ⟨hmem, h⟩ := edgeK_localOp_tp n p hn hp3 y.1 (Submodule.mem_comap.mp y.2)
  exact h

/-- **The good-line edge maps the local joint generalized eigenspace (inside `ML`) into the joint
generalized eigenspace of level-one `H¹`.** -/
theorem phiL_mem_jointH1 (c : HeckeCorrespondence → ℂ) (hn : 0 < n) (y : ML n)
    (hy : (y : CuspH2 n trivialCharacter .line true) ∈
      localJoint n trivialCharacter c .line true) :
    phiL n hn y ∈ jointH1 (n + 1) 0 (eGoodLine n c) := by
  rw [jointH1, Submodule.mem_iInf]
  rintro ⟨p, hp3⟩
  have hyp := (Submodule.mem_iInf _).mp hy ⟨TpExistence.tp p, TpExistence.tp_awayThree p hp3⟩
  have hs : ((p.val : ℂ) ^ (n + 1))⁻¹ ≠ 0 :=
    inv_ne_zero (pow_ne_zero _ (by exact_mod_cast p.property.ne_zero))
  apply map_mem_maxGenEigenspace_of_affine (phiL n hn) (localOpML n hn p hp3)
    (LevelOneHeckeH1.arithmeticHecke (n + 1) 0 p) _ _ hs (phiL_localOpML hn p hp3)
  -- membership of `y` in the generalized eigenspace of the restricted operator
  rw [Module.End.mem_maxGenEigenspace] at hyp ⊢
  obtain ⟨k, hk⟩ := hyp
  refine ⟨k, Subtype.ext ?_⟩
  rw [← (ML n).subtype_apply, intertwine_sub_pow (ML n).subtype (localOpML n hn p hp3)
    (localOp n trivialCharacter (TpExistence.tp p) (TpExistence.tp_awayThree p hp3) .line true)
    (fun _ => rfl)]
  exact hk

/-- The local joint generalized eigenspace at the good line has dimension at most that of the joint
generalized eigenspace of level-one `H¹(GL₂(ℤ), Sym^{n+1})`. -/
theorem finrank_localJoint_goodLine_le (c : HeckeCorrespondence → ℂ) (hn : 0 < n)
    (hc : ‖c (TpExistence.tp two) - 1‖ ≤ 3 / 4)
    [FiniteDimensional ℂ (jointH1 (n + 1) 0 (eGoodLine n c))] :
    Module.finrank ℂ
        (localJoint n trivialCharacter c .line true) ≤
      Module.finrank ℂ (jointH1 (n + 1) 0 (eGoodLine n c)) := by
  have hle := localJoint_le_ML (n := n) c hc
  set K := localJoint n trivialCharacter c .line true
  have hK : Module.finrank ℂ K = Module.finrank ℂ (K.comap (ML n).subtype) :=
    (LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hle)).symm
  rw [hK]
  exact finrank_le_of_injective_map (phiL n hn) (phiL_injective hn) _ _
    (fun y hy => phiL_mem_jointH1 c hn y hy)

end GoodLine

/-! ### Even degree: the local joint eigenspaces vanish -/

/-- For even `n` the identity-plane local statement holds: the local cohomology vanishes. -/
theorem identityPlane_localStatement_of_even (D : CohomologicalCuspData n)
    (hecke : BoundaryHecke n D.inducingData.chi)
    (hhecke : ActualBoundaryHecke n D.inducingData.chi hecke) (hn : 0 < n) (heven : Even n) :
    LocalStatement D.inducingData hecke hhecke .plane false :=
  localStatement_of_eq_bot _ _ _ _ _
    (IdentityPlaneEven.localJoint_identityPlane_eq_bot n hn heven _)

/-- For even `n ≥ 3` and a nonzero pair, the local joint generalized eigenspace at the good line
vanishes: it lies in `ML`, which embeds into `H¹(GL₂(ℤ), Sym^{n+1}) = 0`. -/
theorem localJoint_goodLine_eq_bot_of_even (c : HeckeCorrespondence → ℂ) (hn0 : 0 < n)
    (heven : Even n) (hc : ‖c (TpExistence.tp two) - 1‖ ≤ 3 / 4) :
    localJoint n trivialCharacter c .line true = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  have hyM := localJoint_le_ML c hc hy
  have h0 : phiL n hn0 ⟨y, hyM⟩ = phiL n hn0 0 := by
    rw [map_zero]
    exact IdentityPlaneEven.arithmeticH1_eq_zero_of_odd (n + 1) (Even.add_one heven) 0 _
  have := congrArg Subtype.val (phiL_injective hn0 h0)
  exact (Submodule.mem_bot ℂ).mpr this

theorem goodLine_localStatement_of_even (D : CohomologicalCuspData n)
    (hecke : BoundaryHecke n D.inducingData.chi)
    (hhecke : ActualBoundaryHecke n D.inducingData.chi hecke) (hn : 3 ≤ n) (heven : Even n)
    (hne : associatePair D.inducingData ≠ ⊥) :
    LocalStatement D.inducingData hecke hhecke .line true :=
  localStatement_of_eq_bot _ _ _ _ _ (localJoint_goodLine_eq_bot_of_even _ (by omega) heven
    (pairCharacter_two_sub_one_norm_le D hecke hhecke hn hne))

end TernaryPeriodPolynomials.Spectral.LocalUniqueness
