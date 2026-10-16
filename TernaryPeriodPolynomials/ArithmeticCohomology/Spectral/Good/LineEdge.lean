module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Good.LineCosets
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.LowerRadicalEdgeFormula

@[expose] public section


/-!
# The local `T_p` operator in edge coordinates at the good line

For a relative two-cocycle `c` of the good-line stabilizer `Λ₁ = {Q(3b, m, 1)}`, the Hecke image
`T c` for the explicit cosets of `GoodLineCosets` is again relative, and its edge cocycle at
`m ∈ GL₂(ℤ)` is
`ζ^{Tc}_m(u) = ∑_j ρ(ℓ_j) ζ_{μ_j}(u B_j) + ρ(diag(m,1)) Cor(m⁻¹ · ζ_m)(u m) + (ρ(u(u)) - 1) Φ`
(`edgeL_heckeTwoL`), where `B_j μ_j = m B_{k_j}` are the `GL₂` Hecke transitions and `Cor` is the
corestriction-type sum over the radical representatives `τ_c`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.Spectral.GoodLineEdge

open PlaneCoordinates LevelOneCosets IdentityPlaneCosets LineCoordinates GoodLineCosets AmbientHecke

/-! ### Group relations in `Λ₁` -/

theorem Qint_mul (b b' : ℤ × ℤ) (m m' : GL (Fin 2) ℤ) :
    Qint b m * Qint b' m' = Qint (b + ivmul b' (m⁻¹ : GL (Fin 2) ℤ).val) (m * m') := by
  simp only [Qint]
  rw [Q_mul, map_mul, Units.val_one, mul_one, one_smul, vmul_smul, ← map_inv, vmul_integralEmbed,
    icast_add, smul_add]

theorem M1_eq (b : ℤ × ℤ) (m : GL (Fin 2) ℤ) : M1 b m = U1 b * L1 m := by
  apply Subtype.ext
  change Qint b m = Qint b 1 * Qint 0 m
  rw [Qint_mul, inv_one, Units.val_one, ivmul_one, add_zero, one_mul]

theorem U1_mul (a b : ℤ × ℤ) : U1 a * U1 b = U1 (a + b) := by
  apply Subtype.ext
  change Qint a 1 * Qint b 1 = Qint (a + b) 1
  rw [Qint_mul, inv_one, Units.val_one, ivmul_one, mul_one]

theorem U1_zero : U1 0 = 1 := by
  apply Subtype.ext
  change Q ((3 : ℚ) • icast 0) (integralEmbed 1) 1 = 1
  rw [icast_zero, smul_zero, map_one, Q_one]

theorem L1_mul (m m' : GL (Fin 2) ℤ) : L1 m * L1 m' = L1 (m * m') := by
  apply Subtype.ext
  change Qint 0 m * Qint 0 m' = Qint 0 (m * m')
  rw [Qint_mul, zero_add]
  simp [ivmul]
  rfl

theorem L1_U1 (m : GL (Fin 2) ℤ) (b : ℤ × ℤ) :
    L1 m * U1 b = U1 (ivmul b (m⁻¹ : GL (Fin 2) ℤ).val) * L1 m := by
  apply Subtype.ext
  change Qint 0 m * Qint b 1 = Qint (ivmul b (m⁻¹ : GL (Fin 2) ℤ).val) 1 * Qint 0 m
  rw [Qint_mul, Qint_mul, zero_add, mul_one, one_mul, inv_one, Units.val_one]
  simp [ivmul]

theorem inl1_eq (u : RadicalLattice) : goodLineRadicalInclusion u = U1 (Multiplicative.toAdd u) := by
  apply Subtype.ext
  change lowerRadicalLattice u = Qint (Multiplicative.toAdd u) 1
  apply Units.ext
  rw [Qint, Q_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerRadicalLattice, lowerPlaneUnipotent, icast, vmul]

theorem splitting1_eq (m : GL (Fin 2) ℤ) : goodLineLeviSection m = L1 m := by
  apply Subtype.ext
  change arithmeticLevi m = Qint 0 m
  apply Units.ext
  rw [Qint, Q_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [arithmeticLevi, planeLevi, planeBlock, icast, vmul, GeneralLinearGroup.map_apply,
      integralEmbed]

/-! ### Relative two-cocycles on `Λ₁` -/

section Relative

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ RationalGL3 V)

/-- The coefficient representation of `Λ₁`. -/
abbrev Aρ1 : Rep ℂ Λ₁ := subgroupCoefficientRep Λ₁ ρ

/-- `ρ(g)` on the coefficients of `Λ₁`. -/
abbrev R1 (g : RationalGL3) : Module.End ℂ (Aρ1 ρ) := ρ g

theorem R1_mul (g h : RationalGL3) (v : Aρ1 ρ) : R1 ρ g (R1 ρ h v) = R1 ρ (g * h) v := by
  change ρ g (ρ h v) = ρ (g * h) v
  rw [map_mul]
  rfl

variable (c : groupCohomology.cocycles₂ (Aρ1 ρ)) (hrel : ∀ a b, c (U1 a, U1 b) = 0)

/-- `F(μ, x) = c(u(x), diag(μ, 1))`. -/
def F1 (μ : GL (Fin 2) ℤ) (x : ℤ × ℤ) : Aρ1 ρ := c (U1 x, L1 μ)

/-- The edge cocycle `ζ_μ(v) = c(diag(μ,1), u(v μ)) - c(u(v), diag(μ,1))`. -/
def edgeL (μ : GL (Fin 2) ℤ) (v : ℤ × ℤ) : Aρ1 ρ :=
  c (L1 μ, U1 (ivmul v μ.val)) - c (U1 v, L1 μ)

include hrel in
theorem relative1_right (x z : ℤ × ℤ) (μ : GL (Fin 2) ℤ) :
    c (U1 x, M1 z μ) = F1 ρ c μ (x + z) - (Aρ1 ρ).ρ (U1 x) (F1 ρ c μ z) := by
  have key := twoCocycle_relation (Aρ1 ρ) c (U1 x) (U1 z) (L1 μ)
  rw [U1_mul, hrel, add_zero, ← M1_eq] at key
  unfold F1
  rw [key]
  abel

include hrel in
theorem relative1_left (x y : ℤ × ℤ) (μ : GL (Fin 2) ℤ) :
    c (M1 x μ, U1 y) = (Aρ1 ρ).ρ (U1 x) (edgeL ρ c μ (ivmul y (μ⁻¹ : GL (Fin 2) ℤ).val)) +
      F1 ρ c μ (x + ivmul y (μ⁻¹ : GL (Fin 2) ℤ).val) - F1 ρ c μ x := by
  have key := twoCocycle_relation (Aρ1 ρ) c (U1 x) (L1 μ) (U1 y)
  rw [L1_U1, ← M1_eq, ← M1_eq, relative1_right ρ c hrel] at key
  unfold edgeL
  rw [ivmul_cancel_inv, map_sub]
  unfold F1 at key ⊢
  have : c (M1 x μ, U1 y) = (Aρ1 ρ).ρ (U1 x) (c (L1 μ, U1 y)) +
      (c (U1 (x + ivmul y (μ⁻¹ : GL (Fin 2) ℤ).val), L1 μ) -
        (Aρ1 ρ).ρ (U1 x) (c (U1 (ivmul y (μ⁻¹ : GL (Fin 2) ℤ).val), L1 μ))) - c (U1 x, L1 μ) := by
    rw [← key]
    abel
  rw [this]
  abel

end Relative


/-! ### Identities for the radical representatives -/

section Radical

variable (p : Nat.Primes)

theorem icast_cvec_crep (x : ℤ × ℤ) :
    icast (cvec p (crep p x)) = icast x - (epsP p : ℚ) • icast (cq p x) := by
  rw [cvec_crep, icast_sub, icast_smul_int]

/-- `τ_c u(β) = diag(m,1) τ_{c'} diag(m,1)⁻¹`. -/
theorem tau_levi (m : GL (Fin 2) ℤ) (c : Fin p.val × Fin p.val) :
    rExpl p (.inr c) * Qint (-ivmul (cq p (ivmul (cvec p c) m.val)) (m⁻¹ : GL (Fin 2) ℤ).val) 1 =
      Qint 0 m * rExpl p (.inr (crep p (ivmul (cvec p c) m.val))) * Qint 0 m⁻¹ := by
  simp only [rExpl, Qint]
  rw [Q_mul, Q_mul, Q_mul]
  congr 1
  · simp only [icast_cvec_crep, inv_one, Units.val_one, vmul_one, icast_zero, smul_zero, vmul_zero,
      add_zero, zero_add, one_smul, one_mul, mul_one, ← integralEmbed_inv, vmul_smul, vmul_sub,
      vmul_integralEmbed, ivmul_inv_cancel, icast_neg, epsU_val]
    module
  · simp
  · simp

/-- `τ_c u(γ) = u(u) τ_{d'}`. -/
theorem tau_shift (u : ℤ × ℤ) (c : Fin p.val × Fin p.val) :
    rExpl p (.inr c) * Qint (-cq p (cvec p c - u)) 1 = Qint u 1 * rExpl p (.inr (crep p (cvec p c - u))) := by
  simp only [rExpl, Qint]
  rw [Q_mul, Q_mul]
  congr 1
  · simp only [icast_cvec_crep, inv_one, Units.val_one, vmul_one, one_smul, map_one, icast_neg,
      icast_sub, epsU_val]
    module
  · simp
  · simp

/-- **Cancellation of the mixed terms.** -/
theorem mixed1 (u : ℤ × ℤ) (m : GL (Fin 2) ℤ) (c : Fin p.val × Fin p.val) :
    -ivmul (cq p (ivmul (cvec p c) m.val)) (m⁻¹ : GL (Fin 2) ℤ).val +
        ivmul (-cq p (cvec p (crep p (ivmul (cvec p c) m.val)) - ivmul u m.val)) (m⁻¹ : GL (Fin 2) ℤ).val =
      -cq p (cvec p c - u) +
        -ivmul (cq p (ivmul (cvec p (crep p (cvec p c - u))) m.val)) (m⁻¹ : GL (Fin 2) ℤ).val := by
  set X := ivmul (cvec p c) m.val
  set d' := crep p (cvec p c - u)
  have hcr : crep p (cvec p (crep p X) - ivmul u m.val) = crep p (ivmul (cvec p d') m.val) := by
    have e : ivmul (cvec p d') m.val = (cvec p (crep p X) - ivmul u m.val) +
        epsP p • (cq p X - ivmul (cq p (cvec p c - u)) m.val) := by
      rw [show cvec p d' = cvec p c - u - epsP p • cq p (cvec p c - u) from cvec_crep p _, cvec_crep,
        ivmul_sub, ivmul_sub, ivmul_smul, smul_sub]
      abel
    rw [e, crep_add_eps]
  apply ivmul_injective m
  apply eps_smul_injective p
  simp only [ivmul_add, ivmul_neg, ivmul_cancel_inv, smul_add, smul_neg, ← ivmul_smul, eps_smul_cq]
  rw [hcr, show cvec p d' = cvec p c - u - epsP p • cq p (cvec p c - u) from cvec_crep p _]
  simp only [ivmul_sub, ivmul_smul]
  abel

end Radical

/-! ### The Hecke image in inhomogeneous coordinates -/

section Hecke

variable (p : Nat.Primes) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ RationalGL3 V)

theorem toRepL_bijective : Function.Bijective (toRepL p) := by
  constructor
  · intro i i' h
    exact rExpl_injective p (congrArg Subtype.val h)
  · rintro ⟨s, hs⟩
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
    exact ⟨i, rfl⟩

theorem repsL_not_mem : ∀ s ∈ (goodLineCosets p).representatives, s ∉ Λ₁ := by
  intro s hs
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
  exact rExpl_not_mem p i

/-- The local Hecke image of an inhomogeneous cocycle at the good line. -/
def heckeTwoL (c : groupCohomology.cocycles₂ (Aρ1 ρ)) : groupCohomology.cocycles₂ (Aρ1 ρ) :=
  ambientCocycleToGroup Λ₁ ρ (LocalHecke.cocycleAction ρ (goodLineCosets p)
    (liftCocycle (goodLineCosets p) ρ c))

theorem heckeTwoL_apply (c : groupCohomology.cocycles₂ (Aρ1 ρ)) (g h : Λ₁) :
    heckeTwoL p ρ c (g, h) = ∑ i : LIdx p, R1 ρ (rExpl p i)
      (c (deltaRep (goodLineCosets p) g (toRepL p i),
        deltaRep (goodLineCosets p) h (nextRep (goodLineCosets p) g (toRepL p i)))) := by
  rw [heckeTwoL, ambientHecke_lift (goodLineCosets p) (repsL_not_mem p) ρ c g h]
  exact (Fintype.sum_bijective (toRepL p) (toRepL_bijective p) _ _ (fun i => rfl)).symm

theorem M1_one (x : ℤ × ℤ) : M1 x 1 = U1 x := rfl

theorem M1_zero (m : GL (Fin 2) ℤ) : M1 0 m = L1 m := rfl

theorem delta_U_inl (u : ℤ × ℤ) (j : Option (Fin p.val)) :
    deltaRep (goodLineCosets p) (U1 u) (toRepL p (.inl j)) = U1 (ivmul u (Bint p j)) := by
  rw [← M1_one, delta_inl, arithmeticDelta_one, M1_one]

theorem next_U_inl (u : ℤ × ℤ) (j : Option (Fin p.val)) :
    nextRep (goodLineCosets p) (U1 u) (toRepL p (.inl j)) = toRepL p (.inl j) := by
  rw [← M1_one, next_inl, arithmeticNext_one]

theorem delta_L_inl (m : GL (Fin 2) ℤ) (j : Option (Fin p.val)) :
    deltaRep (goodLineCosets p) (L1 m) (toRepL p (.inl j)) = L1 (arithmeticDelta p m j) := by
  rw [← M1_zero, delta_inl]
  congr 1
  simp [ivmul]

theorem next_L_inl (m : GL (Fin 2) ℤ) (j : Option (Fin p.val)) :
    nextRep (goodLineCosets p) (L1 m) (toRepL p (.inl j)) = toRepL p (.inl (arithmeticNext p m j)) := by
  rw [← M1_zero, next_inl]

theorem delta_U_inr (u : ℤ × ℤ) (c : Fin p.val × Fin p.val) :
    deltaRep (goodLineCosets p) (U1 u) (toRepL p (.inr c)) = U1 (-cq p (cvec p c - u)) := by
  rw [← M1_one, delta_inr, Units.val_one, ivmul_one, inv_one, Units.val_one, ivmul_one, M1_one]

theorem next_U_inr (u : ℤ × ℤ) (c : Fin p.val × Fin p.val) :
    nextRep (goodLineCosets p) (U1 u) (toRepL p (.inr c)) = toRepL p (.inr (crep p (cvec p c - u))) := by
  rw [← M1_one, next_inr, Units.val_one, ivmul_one]

theorem delta_L_inr (m : GL (Fin 2) ℤ) (c : Fin p.val × Fin p.val) :
    deltaRep (goodLineCosets p) (L1 m) (toRepL p (.inr c)) =
      M1 (-ivmul (cq p (ivmul (cvec p c) m.val)) (m⁻¹ : GL (Fin 2) ℤ).val) m := by
  rw [← M1_zero, delta_inr, sub_zero]

theorem next_L_inr (m : GL (Fin 2) ℤ) (c : Fin p.val × Fin p.val) :
    nextRep (goodLineCosets p) (L1 m) (toRepL p (.inr c)) =
      toRepL p (.inr (crep p (ivmul (cvec p c) m.val))) := by
  rw [← M1_zero, next_inr, sub_zero]

variable (c : groupCohomology.cocycles₂ (Aρ1 ρ)) (hrel : ∀ a b, c (U1 a, U1 b) = 0)

include hrel in
/-- **The Hecke image of a relative cocycle is relative.** -/
theorem heckeTwoL_relative (a b : ℤ × ℤ) : heckeTwoL p ρ c (U1 a, U1 b) = 0 := by
  rw [heckeTwoL_apply]
  apply Finset.sum_eq_zero
  intro i _
  rcases i with j | d
  · rw [delta_U_inl, next_U_inl, delta_U_inl, hrel, map_zero]
  · rw [delta_U_inr, next_U_inr, delta_U_inr, hrel, map_zero]

end Hecke

/-! ### The edge of the Hecke image -/

section Edge

variable (p : Nat.Primes) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ RationalGL3 V)

theorem Bint_mul_delta (m : GL (Fin 2) ℤ) (j : Option (Fin p.val)) :
    Bint p j * (arithmeticDelta p m j).val = m.val * Bint p (arithmeticNext p m j) := by
  have h := congrArg Units.val (BGL_mul_delta p m j)
  rw [Units.val_mul, Units.val_mul, BGL_val, BGL_val, Bmat_eq, Bmat_eq, integralEmbed_val,
    integralEmbed_val, ← Matrix.map_mul, ← Matrix.map_mul] at h
  ext a b
  have := congrFun (congrFun h a) b
  simpa using this

/-- The Levi translate `(ν · ξ)(y) = ρ(diag(ν,1)) ξ(y ν)`. -/
def conjL (ν : GL (Fin 2) ℤ) (ξ : ℤ × ℤ → Aρ1 ρ) (y : ℤ × ℤ) : Aρ1 ρ :=
  R1 ρ (Qint 0 ν) (ξ (ivmul y ν.val))

/-- The corestriction-type sum `Cor ξ (x) = ∑_c ρ(τ_c) ξ(-q_c(x))`. -/
def CorL (ξ : ℤ × ℤ → Aρ1 ρ) (x : ℤ × ℤ) : Aρ1 ρ :=
  ∑ c : Fin p.val × Fin p.val, R1 ρ (rExpl p (.inr c)) (ξ (-cq p (cvec p c - x)))

variable (c : groupCohomology.cocycles₂ (Aρ1 ρ)) (hrel : ∀ a b, c (U1 a, U1 b) = 0)

/-- The terms `Φ_c = ρ(τ_c) F(m, β_c)` of the radical coboundary. -/
def phiL (m : GL (Fin 2) ℤ) (d : Fin p.val × Fin p.val) : Aρ1 ρ :=
  R1 ρ (rExpl p (.inr d)) (F1 ρ c m (-ivmul (cq p (ivmul (cvec p d) m.val)) (m⁻¹ : GL (Fin 2) ℤ).val))

include hrel in
/-- **One radical term of the edge of the Hecke image.** -/
theorem edgeL_term (m : GL (Fin 2) ℤ) (u : ℤ × ℤ) (d : Fin p.val × Fin p.val) :
    R1 ρ (rExpl p (.inr d))
        (c (M1 (-ivmul (cq p (ivmul (cvec p d) m.val)) (m⁻¹ : GL (Fin 2) ℤ).val) m,
          U1 (-cq p (cvec p (crep p (ivmul (cvec p d) m.val)) - ivmul u m.val)))) -
      R1 ρ (rExpl p (.inr d))
        (c (U1 (-cq p (cvec p d - u)),
          M1 (-ivmul (cq p (ivmul (cvec p (crep p (cvec p d - u))) m.val)) (m⁻¹ : GL (Fin 2) ℤ).val) m)) =
      R1 ρ (Qint 0 m) (R1 ρ (rExpl p (.inr (crep p (ivmul (cvec p d) m.val))))
        (conjL ρ m⁻¹ (edgeL ρ c m)
          (-cq p (cvec p (crep p (ivmul (cvec p d) m.val)) - ivmul u m.val)))) -
        phiL p ρ c m d + R1 ρ (Qint u 1) (phiL p ρ c m (crep p (cvec p d - u))) := by
  rw [relative1_left ρ c hrel, relative1_right ρ c hrel, mixed1]
  simp only [map_add, map_sub]
  have e1 : R1 ρ (rExpl p (.inr d)) ((Aρ1 ρ).ρ (U1 (-ivmul (cq p (ivmul (cvec p d) m.val))
        (m⁻¹ : GL (Fin 2) ℤ).val))
      (edgeL ρ c m (ivmul (-cq p (cvec p (crep p (ivmul (cvec p d) m.val)) - ivmul u m.val))
        (m⁻¹ : GL (Fin 2) ℤ).val))) =
      R1 ρ (Qint 0 m) (R1 ρ (rExpl p (.inr (crep p (ivmul (cvec p d) m.val))))
        (conjL ρ m⁻¹ (edgeL ρ c m)
          (-cq p (cvec p (crep p (ivmul (cvec p d) m.val)) - ivmul u m.val)))) := by
    change R1 ρ (rExpl p (.inr d)) (R1 ρ (Qint _ 1) _) = _
    rw [R1_mul, tau_levi, conjL, R1_mul, R1_mul]
  have e2 : R1 ρ (rExpl p (.inr d)) ((Aρ1 ρ).ρ (U1 (-cq p (cvec p d - u)))
      (F1 ρ c m (-ivmul (cq p (ivmul (cvec p (crep p (cvec p d - u))) m.val))
        (m⁻¹ : GL (Fin 2) ℤ).val))) =
      R1 ρ (Qint u 1) (phiL p ρ c m (crep p (cvec p d - u))) := by
    change R1 ρ (rExpl p (.inr d)) (R1 ρ (Qint _ 1) _) = _
    rw [R1_mul, tau_shift, ← R1_mul]
    rfl
  rw [e1, e2]
  unfold phiL
  abel

include hrel in
/-- **The edge cocycle of the local Hecke image at the good line.** -/
theorem edgeL_heckeTwoL (m : GL (Fin 2) ℤ) (u : ℤ × ℤ) :
    edgeL ρ (heckeTwoL p ρ c) m u =
      ∑ j : Option (Fin p.val), R1 ρ (rExpl p (.inl j))
          (edgeL ρ c (arithmeticDelta p m j) (ivmul u (Bint p j))) +
        R1 ρ (Qint 0 m) (CorL p ρ (conjL ρ m⁻¹ (edgeL ρ c m)) (ivmul u m.val)) +
        (R1 ρ (Qint u 1) (∑ d : Fin p.val × Fin p.val, phiL p ρ c m d) -
          ∑ d : Fin p.val × Fin p.val, phiL p ρ c m d) := by
  change heckeTwoL p ρ c (L1 m, U1 (ivmul u m.val)) - heckeTwoL p ρ c (U1 u, L1 m) = _
  rw [heckeTwoL_apply, heckeTwoL_apply, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [delta_L_inl, next_L_inl, delta_U_inl, next_U_inl, delta_L_inr, next_L_inr, delta_U_inr,
    next_U_inr]
  have hlevi : ∀ j : Option (Fin p.val),
      R1 ρ (rExpl p (.inl j)) (c (L1 (arithmeticDelta p m j),
          U1 (ivmul (ivmul u m.val) (Bint p (arithmeticNext p m j))))) -
        R1 ρ (rExpl p (.inl j)) (c (U1 (ivmul u (Bint p j)), L1 (arithmeticDelta p m j))) =
      R1 ρ (rExpl p (.inl j)) (edgeL ρ c (arithmeticDelta p m j) (ivmul u (Bint p j))) := by
    intro j
    rw [← map_sub, edgeL, ← ivmul_mul, ← ivmul_mul, Bint_mul_delta]
  have hrad : (∑ d : Fin p.val × Fin p.val, R1 ρ (rExpl p (.inr d))
        (c (M1 (-ivmul (cq p (ivmul (cvec p d) m.val)) (m⁻¹ : GL (Fin 2) ℤ).val) m,
          U1 (-cq p (cvec p (crep p (ivmul (cvec p d) m.val)) - ivmul u m.val))))) -
      (∑ d : Fin p.val × Fin p.val, R1 ρ (rExpl p (.inr d))
        (c (U1 (-cq p (cvec p d - u)),
          M1 (-ivmul (cq p (ivmul (cvec p (crep p (cvec p d - u))) m.val)) (m⁻¹ : GL (Fin 2) ℤ).val) m))) =
      R1 ρ (Qint 0 m) (CorL p ρ (conjL ρ m⁻¹ (edgeL ρ c m)) (ivmul u m.val)) +
        (R1 ρ (Qint u 1) (∑ d : Fin p.val × Fin p.val, phiL p ρ c m d) -
          ∑ d : Fin p.val × Fin p.val, phiL p ρ c m d) := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.sum_congr rfl (fun d _ => edgeL_term p ρ c hrel m u d)).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← map_sum, ← map_sum]
    have h1 := (crep_levi_bijective p m).sum_comp (fun c' => R1 ρ (rExpl p (.inr c'))
      (conjL ρ m⁻¹ (edgeL ρ c m) (-cq p (cvec p c' - ivmul u m.val))))
    have h2 := (crep_shift_bijective p u).sum_comp (phiL p ρ c m)
    rw [h1, h2, CorL]
    abel
  rw [show ∀ (A B C D : Aρ1 ρ), A + C - (B + D) = (A - B) + (C - D) by intro A B C D; abel]
  rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun j _ => hlevi j), hrad, add_assoc]

end Edge

end TernaryPeriodPolynomials.Spectral.GoodLineEdge
