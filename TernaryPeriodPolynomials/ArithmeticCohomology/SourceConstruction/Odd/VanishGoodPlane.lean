module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Odd.VanishCore
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Odd.VanishPoly
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneEdge
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.SymFixed
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.ArithmeticGenerators

@[expose] public section


/-!
# `H²(Γ_F, V_χ) = 0` at the good plane for an odd character

In the block coordinates of `GoodPlaneModel` the stabilizer of the good plane is the split extension
`Λ = ℤ² ⋊ (Γ₁'(3) × ℤˣ)`. For a character `χ` with `χ(-1_∞) = -1` the coefficient representation is
the trivial-character one twisted by the sign of the determinant. Then

* the central element `DK = diag(1, 1, -1)` of the Levi group inverts the radical and acts by `-1`
  on `H¹(ℤ², V)` (`gp_hneg`), by the Levi equivariance of the binary coordinate (`coord_levi`);
* the restriction `H²(Λ, V) → H²(ℤ², V)` vanishes: for `n > 0` the class in the coinvariants
  `Sym^n` is fixed by the two shears `Pg 0 (upper 1) 1`, `Pg 0 (lower 1) 1`, hence zero by
  `SymFixed.fixed_upper_inf_fixed_lower`; for `n = 0` the representation is trivial and the Levi
  reflection kills the alternation (`gp_restriction_zero_pos`, `gp_restriction_zero_zero`);
* `H²` of the Levi group vanishes (`ModularH2`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix MvPolynomial GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.ArithmeticGenerators
  (upper lower reflection)
open TernaryPeriodPolynomials.Spectral

namespace TernaryPeriodPolynomials.SourceConstruction

namespace GoodPlaneVanish

open TernaryPeriodPolynomials.LevelThree.GoodPlaneFrame
open TernaryPeriodPolynomials.LevelThree.GoodPlaneModel
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge
open TernaryPeriodPolynomials.LevelThree.SymFixed (upperC lowerC)
open TernaryPeriodPolynomials.Spectral.LevelOneCosets (integralEmbed)
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCosets (imul icast)
open TernaryPeriodPolynomials.Spectral.PlaneCoordinates (P)

variable (n : ℕ) (χ : RankOneCharacter)

/-! ### The twisted coefficient representation of `Λ` -/

/-- The coefficient representation of the good-plane stabilizer in block coordinates, for the
character `χ`. -/
abbrev gpRep : Rep ℂ ΛG :=
  subgroupCoefficientRep ΛG (rationalCoefficientComponent n χ)

/-- On the radical lattice the twisted and the trivial-character systems agree. -/
theorem gpRep_radical (r : RadicalLattice) (v : HomogeneousPoly n) :
    (gpRep n χ).ρ (goodPlaneExtension.inl r) v = (upperRadicalLatticeRep n).ρ r v := by
  change rationalCoefficientComponent n χ (upperRadicalLattice r) v =
    rationalCoefficientComponent n trivialCharacter (upperRadicalLattice r) v
  rw [Twisted.rho_upperRadicalLattice]

theorem gpRep_apply (g : ΛG) (v : HomogeneousPoly n) :
    (gpRep n χ).ρ g v = rationalCoefficientComponent n χ g.val v := rfl

theorem gpCoef_apply (g : ΛG) (v : HomogeneousPoly n) :
    (coefRep n).ρ g v = rationalCoefficientComponent n trivialCharacter g.val v := rfl

/-- On elements of positive determinant the twisted and the trivial-character systems agree. -/
theorem gpRep_eq_of_pos (g : ΛG) (hg : 0 < g.val.val.det) (v : HomogeneousPoly n) :
    (gpRep n χ).ρ g v = (coefRep n).ρ g v :=
  (gpRep_apply n χ g v).trans
    ((congrArg (fun f => f v) (Twisted.rho_eq_of_pos n χ hg)).trans
      (gpCoef_apply n g v).symm)

/-! ### Determinants of block elements -/

theorem kapMat_det (m : binaryArithmeticLevel) : (kapMat m.val.val).det = m.val.val.det := by
  obtain ⟨c, hc⟩ := level_dvd m
  have h3 : m.val.val 1 0 / 3 = c := by omega
  have e : kapMat m.val.val = !![m.val.val 0 0, 3 * m.val.val 0 1; c, m.val.val 1 1] := by
    rw [kapMat, h3]
  rw [e, Matrix.det_fin_two_of, Matrix.det_fin_two, hc]
  ring

theorem det_Pg (b : ℤ × ℤ) (m : binaryArithmeticLevel) (d : ℤˣ) :
    (Pg b m d).val.det = ((m.val.val.det : ℤ) : ℚ) * ((d : ℤ) : ℚ) := by
  have h : ((integralEmbed (kap m) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det =
      ((m.val.val.det : ℤ) : ℚ) := by
    rw [integralEmbed_kap_val, ← kapMat_det]
    exact (RingHom.map_det (Int.castRingHom ℚ) (kapMat m.val.val)).symm
  unfold Pg
  rw [IdentityPlaneCoordinate.det_P, h, uq_val]

theorem det_Pg_pos (m : binaryArithmeticLevel) (hm : m.val.val.det = 1) :
    0 < (Pg 0 m 1).val.det := by
  rw [det_Pg, hm]
  norm_num

theorem det_Pg_neg (m : binaryArithmeticLevel) (hm : m.val.val.det = -1) :
    (Pg 0 m 1).val.det = -1 := by
  rw [det_Pg, hm]
  norm_num

/-! ### The restricted action of a block element -/

theorem gp_res_rho (m : binaryArithmeticLevel) (hm : m.val.val.det = 1) (v : HomogeneousPoly n) :
    IdentityPlaneCoordinate.res n ((gpRep n χ).ρ (Gel 0 m 1) v) =
      IdentityPlaneCoordinate.Abin n (integralEmbed (kap m)) (IdentityPlaneCoordinate.res n v) := by
  have hpos : 0 < (Gel 0 m 1).val.val.det := by
    change 0 < (Pg 0 m 1).val.det
    exact det_Pg_pos m hm
  rw [gpRep_eq_of_pos n χ _ hpos v]
  change IdentityPlaneCoordinate.res n (IdentityPlaneCoordinate.ρn n (Pg 0 m 1) v) = _
  have e : Pg 0 m 1 = P (icast 0) (Em m) 1 := (PK_eq_Pg 0 m).symm
  rw [e, IdentityPlaneCoordinate.restrict_P, Units.val_one, Rat.cast_one, inv_one, one_smul,
    Em_apply]

/-- Conjugation of the radical by a Levi block element. -/
theorem gp_conj (ℓ : Levi) (r : RadicalLattice) :
    (goodPlaneSplitting ℓ)⁻¹ * goodPlaneExtension.inl r * goodPlaneSplitting ℓ =
      goodPlaneExtension.inl (splitRadicalInput goodPlaneSplitting ℓ r) := by
  have h := splitRadicalInput_commute goodPlaneSplitting ℓ r
  rw [mul_assoc, h, inv_mul_cancel_left]

theorem gp_radical_trivial (r : RadicalLattice) (v : HomogeneousPoly n) :
    IdentityPlaneCoordinate.res n ((gpRep n χ).ρ (goodPlaneExtension.inl r) v) =
      IdentityPlaneCoordinate.res n v := by
  rw [gpRep_radical]
  exact binaryHomogeneousRestrict_upperLattice n r v

/-- The projected alternation `x ∈ Sym^n` of a two-cocycle on the radical. -/
abbrev gpAlt (cycle : groupCohomology.cocycles₂ (gpRep n χ)) : Binary.HomogeneousPoly n :=
  IdentityPlaneCoordinate.res n
    (cycle (goodPlaneExtension.inl radicalLatticeFirst, goodPlaneExtension.inl radicalLatticeSecond) -
      cycle (goodPlaneExtension.inl radicalLatticeSecond,
        goodPlaneExtension.inl radicalLatticeFirst))

/-- The determinant of the action of the Levi element `(m, 1)` on the radical lattice. -/
def gpDet (m : binaryArithmeticLevel) : ℤ :=
  (splitRadicalInput goodPlaneSplitting (m, 1) radicalLatticeFirst).toAdd.1 *
      (splitRadicalInput goodPlaneSplitting (m, 1) radicalLatticeSecond).toAdd.2 -
    (splitRadicalInput goodPlaneSplitting (m, 1) radicalLatticeFirst).toAdd.2 *
      (splitRadicalInput goodPlaneSplitting (m, 1) radicalLatticeSecond).toAdd.1

/-- **A shear of the Levi group fixes the projected alternation** (up to the determinant of its
action on the radical). -/
theorem gp_alt_fixed (m : binaryArithmeticLevel) (hm : m.val.val.det = 1)
    (cycle : groupCohomology.cocycles₂ (gpRep n χ)) :
    IdentityPlaneCoordinate.Abin n (integralEmbed (kap m)) (gpDet m • gpAlt n χ cycle) =
      gpAlt n χ cycle := by
  have reflect := projected_alternation_reflect goodPlaneExtension.inl (gpRep n χ)
    (IdentityPlaneCoordinate.res n) (gp_radical_trivial n χ) (goodPlaneSplitting (m, 1))
    radicalLatticeFirst radicalLatticeSecond
    (splitRadicalInput goodPlaneSplitting (m, 1) radicalLatticeFirst)
    (splitRadicalInput goodPlaneSplitting (m, 1) radicalLatticeSecond)
    (gp_conj (m, 1) radicalLatticeFirst) (gp_conj (m, 1) radicalLatticeSecond)
    (IdentityPlaneCoordinate.Abin n (integralEmbed (kap m)))
    (fun v => gp_res_rho n χ m hm v) cycle
  have det := projected_alternation_eq_det goodPlaneExtension.inl (gpRep n χ)
    (IdentityPlaneCoordinate.res n) (gp_radical_trivial n χ) cycle
    (splitRadicalInput goodPlaneSplitting (m, 1) radicalLatticeFirst)
    (splitRadicalInput goodPlaneSplitting (m, 1) radicalLatticeSecond)
  rw [det] at reflect
  exact reflect

/-! ### The two shears -/

theorem gp_upper_inv : (upper 1)⁻¹ = upper (-1) := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [upper, Matrix.mul_apply, Fin.sum_univ_two]

theorem gp_lower_inv : (lower 1)⁻¹ = lower (-1) := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [lower, Matrix.mul_apply, Fin.sum_univ_two]

theorem gp_reflection_inv : reflection⁻¹ = reflection := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [reflection, Matrix.mul_apply, Fin.sum_univ_two]

theorem gp_upper_det : (upper 1).val.val.det = 1 := by
  simp [upper, Matrix.det_fin_two]

theorem gp_lower_det : (lower 1).val.val.det = 1 := by
  simp [lower, Matrix.det_fin_two]

theorem gp_reflection_det : reflection.val.val.det = -1 := by
  simp [reflection, Matrix.det_fin_two]

theorem gp_phi_upper (b : RadicalLattice) :
    (splitRadicalInput goodPlaneSplitting (upper 1, 1) b).toAdd =
      (b.toAdd.1 - 3 * b.toAdd.2, b.toAdd.2) := by
  rw [splitRadicalInput_apply, toAdd_ofAdd, gp_upper_inv]
  apply Prod.ext
  · simp [act, imul, kap_val, kapMat, upper]; ring
  · simp [act, imul, kap_val, kapMat, upper]

theorem gp_phi_lower (b : RadicalLattice) :
    (splitRadicalInput goodPlaneSplitting (lower 1, 1) b).toAdd =
      (b.toAdd.1, b.toAdd.2 - b.toAdd.1) := by
  rw [splitRadicalInput_apply, toAdd_ofAdd, gp_lower_inv]
  apply Prod.ext
  · simp [act, imul, kap_val, kapMat, lower]
  · simp [act, imul, kap_val, kapMat, lower]; ring

theorem gp_phi_reflection (b : RadicalLattice) :
    (splitRadicalInput goodPlaneSplitting (reflection, 1) b).toAdd = (-b.toAdd.1, b.toAdd.2) := by
  rw [splitRadicalInput_apply, toAdd_ofAdd, gp_reflection_inv]
  apply Prod.ext
  · simp [act, imul, kap_val, kapMat, reflection]
  · simp [act, imul, kap_val, kapMat, reflection]

theorem gp_det_upper : gpDet (upper 1) = 1 := by
  unfold gpDet
  rw [gp_phi_upper, gp_phi_upper]
  simp [radicalLatticeFirst, radicalLatticeSecond]

theorem gp_det_lower : gpDet (lower 1) = 1 := by
  unfold gpDet
  rw [gp_phi_lower, gp_phi_lower]
  simp [radicalLatticeFirst, radicalLatticeSecond]

theorem binaryIntegralComplex_kap_upper :
    binaryIntegralComplex (kap (upper 1)) = upperC 3 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [binaryIntegralComplex, kap_val, kapMat, upper, upperC, GeneralLinearGroup.map_apply]

theorem binaryIntegralComplex_kap_lower :
    binaryIntegralComplex (kap (lower 1)) = lowerC 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [binaryIntegralComplex, kap_val, kapMat, lower, lowerC, GeneralLinearGroup.map_apply]

theorem gp_Abin_upper :
    IdentityPlaneCoordinate.Abin n (integralEmbed (kap (upper 1))) =
      Binary.homogeneousAction n (-1) (upperC 3) := by
  change Binary.homogeneousAction n (-1)
    (GeneralLinearGroup.map (algebraMap ℚ ℂ) (integralEmbed (kap (upper 1)))) = _
  rw [LevelThree.LevelThreeHeckeH1.map_integralEmbed, binaryIntegralComplex_kap_upper]

theorem gp_Abin_lower :
    IdentityPlaneCoordinate.Abin n (integralEmbed (kap (lower 1))) =
      Binary.homogeneousAction n (-1) (lowerC 1) := by
  change Binary.homogeneousAction n (-1)
    (GeneralLinearGroup.map (algebraMap ℚ ℂ) (integralEmbed (kap (lower 1)))) = _
  rw [LevelThree.LevelThreeHeckeH1.map_integralEmbed, binaryIntegralComplex_kap_lower]

theorem gp_fixed_upper (cycle : groupCohomology.cocycles₂ (gpRep n χ)) :
    Binary.homogeneousAction n (-1) (upperC 3) (gpAlt n χ cycle) = gpAlt n χ cycle := by
  have h := gp_alt_fixed n χ (upper 1) gp_upper_det cycle
  rw [gp_det_upper, one_smul, gp_Abin_upper] at h
  exact h

theorem gp_fixed_lower (cycle : groupCohomology.cocycles₂ (gpRep n χ)) :
    Binary.homogeneousAction n (-1) (lowerC 1) (gpAlt n χ cycle) = gpAlt n χ cycle := by
  have h := gp_alt_fixed n χ (lower 1) gp_lower_det cycle
  rw [gp_det_lower, one_smul, gp_Abin_lower] at h
  exact h

/-- **For `n > 0` the projected alternation vanishes**: it is fixed by two shears with no common
invariant. -/
theorem gp_alternation_zero (hn : 0 < n) (cycle : groupCohomology.cocycles₂ (gpRep n χ)) :
    gpAlt n χ cycle = 0 := by
  have hmem : gpAlt n χ cycle ∈
      LevelThree.SymFixed.fixedSpace (m := n) (-1) (upperC 3) ⊓
        LevelThree.SymFixed.fixedSpace (m := n) (-1) (lowerC 1) := by
    exact ⟨(LevelThree.SymFixed.mem_fixedSpace (m := n) (-1)).mpr (gp_fixed_upper n χ cycle),
      (LevelThree.SymFixed.mem_fixedSpace (m := n) (-1)).mpr (gp_fixed_lower n χ cycle)⟩
  rw [LevelThree.SymFixed.fixed_upper_inf_fixed_lower (m := n) (-1) hn
    (c := 3) (c' := 1) (by norm_num) (by norm_num)] at hmem
  exact (Submodule.mem_bot ℂ).mp hmem

/-! ### Vanishing of the restriction to the radical -/

/-- **Positive degree.** -/
theorem gp_restriction_zero_pos (hn : 0 < n) (cycle : groupCohomology.cocycles₂ (gpRep n χ)) :
    groupCohomology.H2π (Rep.res goodPlaneExtension.inl (gpRep n χ))
      (twoCocycleRestriction goodPlaneExtension.inl (gpRep n χ) cycle) = 0 := by
  refine latticeH2_eq_zero_of_projected (Rep.res goodPlaneExtension.inl (gpRep n χ))
    (binaryHomogeneousRestrict n) ?_ _ ?_
  · intro v hv
    obtain ⟨y, hy⟩ := (SetLike.ext_iff.mp (upperRadicalLattice_first_range n hn) v).mpr hv
    exact Submodule.mem_sup_left
      ⟨y, sub_apply_aux (gpRep_radical n χ radicalLatticeFirst y) (y := y) hy⟩
  · exact gp_alternation_zero n χ hn cycle

/-- **Degree zero.** The representation is trivial and the Levi reflection kills the alternation. -/
theorem gp_restriction_zero_zero (hodd : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (cycle : groupCohomology.cocycles₂ (gpRep 0 χ)) :
    groupCohomology.H2π (Rep.res goodPlaneExtension.inl (gpRep 0 χ))
      (twoCocycleRestriction goodPlaneExtension.inl (gpRep 0 χ) cycle) = 0 := by
  have hφ1 : splitRadicalInput goodPlaneSplitting (reflection, 1) radicalLatticeFirst =
      radicalLatticeFirst⁻¹ := by
    apply Multiplicative.toAdd.injective
    rw [gp_phi_reflection]
    simp [radicalLatticeFirst]
  have hφ2 : splitRadicalInput goodPlaneSplitting (reflection, 1) radicalLatticeSecond =
      radicalLatticeSecond := by
    apply Multiplicative.toAdd.injective
    rw [gp_phi_reflection]
    simp [radicalLatticeSecond]
  have htrivial : ∀ (r : RadicalLattice) (v : HomogeneousPoly 0),
      (gpRep 0 χ).ρ (goodPlaneExtension.inl r) v = v := by
    intro r v
    change rationalCoefficientComponent 0 χ (upperRadicalLattice r) v = v
    exact rho_chi_zero hodd _ (Or.inl (Twisted.det_planeUnipotent _ _)) v
  have hfixed : ∀ v : HomogeneousPoly 0,
      (gpRep 0 χ).ρ (goodPlaneSplitting (reflection, 1)) v = v := by
    intro v
    change rationalCoefficientComponent 0 χ (Pg 0 reflection 1) v = v
    exact rho_chi_zero hodd _ (Or.inr (det_Pg_neg reflection gp_reflection_det)) v
  refine latticeH2_eq_zero_of_projected (Rep.res goodPlaneExtension.inl (gpRep 0 χ))
    LinearMap.id ?_ _ ?_
  · rw [LinearMap.ker_id]
    exact bot_le
  · exact projected_alternation_zero_of_reflection goodPlaneExtension.inl (gpRep 0 χ)
      LinearMap.id (fun r v => by simp only [LinearMap.id_apply]; exact htrivial r v)
      (goodPlaneSplitting (reflection, 1))
      (by rw [gp_conj, hφ1]) (by rw [gp_conj, hφ2])
      (fun v => by simp only [LinearMap.id_apply]; exact hfixed v) cycle

/-- **The restriction of every class to the radical vanishes.** -/
theorem gp_hres (hodd : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (x : groupCohomology.H2 (gpRep n χ)) :
    twoCohomologyRestriction goodPlaneExtension.inl (gpRep n χ) x = 0 := by
  obtain ⟨cycle, rfl⟩ := twoCocycle_H2_surjective (gpRep n χ) x
  rw [twoCohomologyRestriction_apply]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact gp_restriction_zero_zero χ hodd cycle
  · exact gp_restriction_zero_pos n χ hn cycle

/-! ### The central element acts by `-1` on `H¹` of the radical -/

/-- The central Levi element `diag(1, 1, -1)`. -/
abbrev gpZ : Levi := (1, -1)

theorem gpZ_central (g : Levi) : gpZ * g = g * gpZ :=
  Prod.ext (by rw [Prod.fst_mul, Prod.fst_mul]; simp)
    (by rw [Prod.snd_mul, Prod.snd_mul]; exact mul_comm _ _)

theorem det_DK : DK.val.val.det = -1 := by
  change (Pg 0 1 (-1)).val.det = -1
  rw [det_Pg]
  simp

/-- The twisted action of the central element is minus the untwisted one. -/
theorem gpRep_DK (hodd : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (v : HomogeneousPoly n) :
    (gpRep n χ).ρ DK v = -((coefRep n).ρ DK v) := by
  refine (gpRep_apply n χ DK v).trans ?_
  refine Eq.trans ?_ (congrArg Neg.neg (gpCoef_apply n DK v)).symm
  have hneg : ¬ (0 : ℚ) < DK.val.val.det := by
    rw [det_DK]
    norm_num
  rw [Twisted.rho_apply_eq_detSign_smul n χ DK.val v, Twisted.detSign_odd hodd,
    ite_eq_right hneg]
  exact neg_one_smul ℂ _

/-- The transfer of a radical cocycle of the twisted system to the trivial-character system. -/
def gpToTriv (ξ : groupCohomology.cocycles₁ (Rep.res goodPlaneExtension.inl (gpRep n χ))) :
    groupCohomology.cocycles₁ (upperRadicalLatticeRep n) :=
  ⟨ξ.val, by
    apply (groupCohomology.mem_cocycles₁_iff _).mpr
    intro g h
    have key := (groupCohomology.mem_cocycles₁_iff _).mp ξ.property g h
    exact eq_add_aux key (gpRep_radical n χ g (ξ.val h))⟩

theorem gpToTriv_add (ξ ξ' : groupCohomology.cocycles₁ (Rep.res goodPlaneExtension.inl (gpRep n χ))) :
    gpToTriv n χ (ξ + ξ') = gpToTriv n χ ξ + gpToTriv n χ ξ' :=
  Subtype.ext rfl

theorem gp_H1π_eq_zero_of_triv
    (ξ : groupCohomology.cocycles₁ (Rep.res goodPlaneExtension.inl (gpRep n χ)))
    (h : groupCohomology.H1π (upperRadicalLatticeRep n) (gpToTriv n χ ξ) = 0) :
    groupCohomology.H1π (Rep.res goodPlaneExtension.inl (gpRep n χ)) ξ = 0 := by
  rw [groupCohomology.H1π_eq_zero_iff] at h ⊢
  obtain ⟨y, hy⟩ := h
  refine ⟨y, ?_⟩
  funext g
  exact (sub_congr_aux (gpRep_radical n χ g y) y).trans (congrFun hy g)

theorem gpToTriv_action (hodd : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (ξ : groupCohomology.cocycles₁ (Rep.res goodPlaneExtension.inl (gpRep n χ))) :
    gpToTriv n χ (splitRadicalCocycleAction goodPlaneSplitting (gpRep n χ) gpZ ξ) =
      -(splitRadicalCocycleAction goodPlaneSplitting (coefRep n) gpZ (gpToTriv n χ ξ)) := by
  apply Subtype.ext
  funext r
  change (gpRep n χ).ρ (goodPlaneSplitting gpZ) (ξ (splitRadicalInput goodPlaneSplitting gpZ r)) =
    -((coefRep n).ρ (goodPlaneSplitting gpZ) (ξ (splitRadicalInput goodPlaneSplitting gpZ r)))
  exact gpRep_DK n χ hodd _

theorem gp_coord_zero (hodd : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (ξ : groupCohomology.cocycles₁ (Rep.res goodPlaneExtension.inl (gpRep n χ))) :
    upperRadicalCocycleCoordinate n
      (gpToTriv n χ (splitRadicalCocycleAction goodPlaneSplitting (gpRep n χ) gpZ ξ + ξ)) = 0 := by
  have hc : upperRadicalCocycleCoordinate n
        (splitRadicalCocycleAction goodPlaneSplitting (coefRep n) gpZ (gpToTriv n χ ξ)) =
      upperRadicalCocycleCoordinate n (gpToTriv n χ ξ) := by
    have h := coord_levi n (gpToTriv n χ ξ) (1 : binaryArithmeticLevel) (-1 : ℤˣ)
    simp only [map_one, Module.End.one_apply] at h
    exact h
  have e1 := (congrArg (upperRadicalCocycleCoordinate n)
    (gpToTriv_add n χ (splitRadicalCocycleAction goodPlaneSplitting (gpRep n χ) gpZ ξ) ξ)).trans
    (map_add (upperRadicalCocycleCoordinate n) _ _)
  have e2 := (congrArg (upperRadicalCocycleCoordinate n) (gpToTriv_action n χ hodd ξ)).trans
    (map_neg (upperRadicalCocycleCoordinate n) _)
  exact e1.trans ((congrArg (· + upperRadicalCocycleCoordinate n (gpToTriv n χ ξ))
    (e2.trans (congrArg Neg.neg hc))).trans (neg_add_cancel _))

/-- **The central element acts by `-1` on `H¹(ℤ², V_χ)`.** -/
theorem gp_hneg (hodd : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (w : groupCohomology.H1 (Rep.res goodPlaneExtension.inl (gpRep n χ))) :
    splitRadicalH1Action goodPlaneSplitting (gpRep n χ) gpZ w = -w := by
  obtain ⟨ξ, rfl⟩ := oneCocycle_H1_surjective _ w
  rw [splitRadicalH1Action_apply]
  have key : groupCohomology.H1π (Rep.res goodPlaneExtension.inl (gpRep n χ))
      (splitRadicalCocycleAction goodPlaneSplitting (gpRep n χ) gpZ ξ + ξ) = 0 := by
    apply gp_H1π_eq_zero_of_triv
    exact (upperRadicalCocycleCoordinate_zero_iff _).mp (gp_coord_zero n χ hodd ξ)
  rw [map_add] at key
  exact eq_neg_of_add_eq_zero_left key

/-! ### Assembly -/

/-- The embedding of the Levi group in `GL₂(ℤ) × ℤˣ`. -/
def gpPsi : Levi →* GeneralLinearGroup (Fin 2) ℤ × ℤˣ :=
  (binaryArithmeticLevel.subtype.comp (MonoidHom.fst _ _)).prod (MonoidHom.snd _ _)

theorem gpPsi_injective : Function.Injective gpPsi := by
  intro x y h
  have h1 : (gpPsi x).1 = (gpPsi y).1 := congrArg Prod.fst h
  have h2 : (gpPsi x).2 = (gpPsi y).2 := congrArg Prod.snd h
  exact Prod.ext (Subtype.ext h1) h2

/-- **`H²(Λ, V_χ) = 0`** for `χ(-1_∞) = -1`. -/
theorem gp_groupH2_eq_zero (hodd : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (x : groupCohomology.H2 (gpRep n χ)) : x = 0 :=
  groupH2_eq_zero_of_split goodPlaneSplitting (gpRep n χ) gpPsi gpPsi_injective
    (gp_hres n χ hodd) gpZ gpZ_central (gp_hneg n χ hodd) x

theorem gp_hH : ∀ h ∈ ΛG, gF * h * gF⁻¹ ∈ CuspReduction.cuspLevel .plane true :=
  fun _ hh => (mem_ΛG _).mp hh

theorem gp_hH' : ∀ h ∈ CuspReduction.cuspLevel .plane true, gF⁻¹ * h * gF⁻¹⁻¹ ∈ ΛG := by
  intro h hh
  rw [mem_ΛG]
  have e : gF * (gF⁻¹ * h * gF⁻¹⁻¹) * gF⁻¹ = h := by group
  rw [e]
  exact hh

/-- **The local cohomology at the good-plane cusp vanishes for an odd character.** -/
theorem cuspH2_plane_true_eq_zero (hodd : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (x : CuspReduction.CuspH2 n χ .plane true) : x = 0 := by
  apply (LevelThree.GoodPlaneConj.conjH2Equiv (rationalCoefficientComponent n χ) gF
    (CuspReduction.cuspLevel .plane true) ΛG gp_hH gp_hH').injective
  rw [LinearEquiv.map_zero]
  exact homogeneousH2_eq_zero_of_group ΛG (rationalCoefficientComponent n χ)
    (gp_groupH2_eq_zero n χ hodd) _

end GoodPlaneVanish

end TernaryPeriodPolynomials.SourceConstruction
