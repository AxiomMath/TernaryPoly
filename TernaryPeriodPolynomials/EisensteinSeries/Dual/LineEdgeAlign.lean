module

public import TernaryPeriodPolynomials.EisensteinSeries.Dual.JFace
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.LeviTransport
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.EdgeSurjective

@[expose] public section


open CategoryTheory groupCohomology
open scoped MatrixGroups

/-!
# The canonical alignment of `𝒞_Q(E*)` with the `QDiLit`

Formalized by Claude Sonnet 5.5.

`dualCuspidalQLiteral N n h` is `𝒞_Q(E*) ⊂ H²(Γ_{h⁻¹Qh}, E*)`, defined by transport from the plane cusp `ȷ(h)`.  the `QDiLit` is the cuspidal subspace of
`H¹(Γ₂(N), H¹(N_{Q'}, E*))`.  They are related by the Hochschild-Serre edge of the line face for the literal dual, by the equivalence `dualCuspidalLiteralEquiv`:

* `ȷ` is a morphism of split extensions `(lineFaceExt N h, lineFaceSplitting N h) → (faceExt N ȷ(h), faceSplitting N ȷ(h))` over `(τ, σ)` (`JFace`), with coefficient comparison `dualIso`;
* `edgeLit_kerMap`: its edge is natural: `edge_{Q'}(ȷ^* x) = H¹(σ)(edge_{P''}(x))` (`EdgeNat.edge_kerMap`);
* `dualCuspidalLiteralEquiv`: `edge_{Q'} : 𝒞_Q(E*) ≃ QDiLit`, because both edges are bijective (`splitCohomologyEdge_surjective`, `…_injective_of_invariant_H2_zero`), `H¹(σ)` is a bijection
  (`LeviTransport.h1Map_bijective`) and carries the cuspidal subspace onto the cuspidal subspace (`σ` carries the cusp stabilizers `Γ₂(N) ∩ Stab(F ∞)` to those of `D F`, `D = diag(1,-1)`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinDual

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD TernaryPeriodPolynomials.Argument.EisensteinClass

/-- The matrix `D = diag(1, -1) ∈ GL₂(ℚ)`: `σ(γ) = D γ D`. -/
def DGL : GL (Fin 2) ℚ :=
  ⟨!![1, 0; 0, -1], !![1, 0; 0, -1], by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem DGL_mul_self : DGL * DGL = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [DGL, Matrix.mul_apply, Fin.sum_univ_two]

theorem mapGL_sigmaSL (γ : SL(2, ℤ)) :
    Matrix.SpecialLinearGroup.mapGL ℚ (sigmaSL γ) = DGL * Matrix.SpecialLinearGroup.mapGL ℚ γ * DGL := by
  apply Units.ext
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix, Units.val_mul, Units.val_mul, Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  have key : ∀ (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det = 1) (i j : Fin 2),
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℚ) ⟨M, hM⟩ : SL(2, ℚ)) : Matrix (Fin 2) (Fin 2) ℚ) i j = ((M i j : ℤ) : ℚ) :=
    fun _ _ _ _ => rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [key, DGL, sigmaSL, Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.map_apply_coe, Matrix.vecMul, dotProduct,
      RingHom.mapMatrix_apply, Matrix.map_apply]


/-- `σ` carries the cusp stabilizer of the frame `D F` onto that of `F`. -/
theorem sigma_leviCuspStab (N : ℕ) (F : GL (Fin 2) ℚ) (γ : ↥(CongruenceSubgroup.Gamma N)) :
    sigmaGamma N γ ∈ leviCuspStab (CongruenceSubgroup.Gamma N) F ↔ γ ∈ leviCuspStab (CongruenceSubgroup.Gamma N) (DGL * F) := by
  have hD : DGL⁻¹ = DGL := inv_eq_of_mul_eq_one_right DGL_mul_self
  have key : F⁻¹ * Matrix.SpecialLinearGroup.mapGL ℚ (sigmaSL γ.1) * F =
      (DGL * F)⁻¹ * Matrix.SpecialLinearGroup.mapGL ℚ γ.1 * (DGL * F) := by
    rw [mapGL_sigmaSL, mul_inv_rev, hD]
    group
  change ((F⁻¹ * Matrix.SpecialLinearGroup.mapGL ℚ (sigmaSL γ.1) * F : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0 ↔
    (((DGL * F)⁻¹ * Matrix.SpecialLinearGroup.mapGL ℚ γ.1 * (DGL * F) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0
  rw [key]

section Align

variable (N : ℕ) [NeZero N] (n : ℕ) (h : SL(3, ℤ))

/-- The radical-kernel classes of the plane face of `ȷ(h)` (coefficient `E`). -/
abbrev KerP := (twoCohomologyRestriction (faceExt N (jmath h)).inl (faceRep N (jmath h) n)).ker

/-- The radical-kernel classes of the line face of `h` for the literal dual. -/
abbrev KerL := (twoCohomologyRestriction (lineFaceExt N h).inl (lineFaceRepLit N n h)).ker

/-- The transport of the radical-kernel classes along `ȷ`. -/
abbrev kerJ : KerP N n h →ₗ[ℂ] KerL N n h :=
  EdgeNat.kerMap (faceJ N h) tauRad (faceJ_inl N h) (faceRep N (jmath h) n) (lineFaceRepLit N n h) (faceJT N n h) (faceJ_hT N n h)

/-- The Hochschild-Serre edge of the line face for the literal dual. -/
abbrev edgeL : KerL N n h →ₗ[ℂ] groupCohomology.H1 (lineFaceRadH1Lit N n h) :=
  splitCohomologyEdge (lineFaceSplitting N h) (lineFaceRepLit N n h)

theorem edgeL_injective : Function.Injective (edgeL N n h) :=
  splitCohomologyEdge_injective_of_invariant_H2_zero (lineFaceSplitting N h) (lineFaceRepLit N n h)
    (fun x => H2_vanish_level (CongruenceSubgroup.Gamma N) _ x)

theorem edgeL_surjective : Function.Surjective (edgeL N n h) :=
  splitCohomologyEdge_surjective (lineFaceSplitting N h) (lineFaceRepLit N n h) (leviH2Vanishes_subgroup _)

/-- The Levi comparison `H¹(N_{P''}, E) → H¹(N_{Q'}, E*)` over `σ`. -/
abbrev phiJ : Rep.res (sigmaGamma N) (faceRadH1 N (jmath h) n) ⟶ lineFaceRadH1Lit N n h :=
  EdgeNat.modMor (faceSplitting N (jmath h)) (lineFaceSplitting N h) (faceJ N h) (sigmaGamma N) tauRad (faceJ_inl N h) (faceJ_split N h)
    (faceRep N (jmath h) n) (lineFaceRepLit N n h) (faceJT N n h) (faceJ_hT N n h)

theorem phiJ_bijective : Function.Bijective (phiJ N n h).hom :=
  EdgeNat.radH1Map_bijective (faceJ N h) (faceRep N (jmath h) n) (lineFaceRepLit N n h) (faceJT N n h) (faceJ_hT N n h)
    tauRad (faceJ_inl N h) tauRad_bijective (dualIso n).bijective

/-- The induced map on `H¹(Γ₂(N), ·)`. -/
abbrev h1J : groupCohomology.H1 (faceRadH1 N (jmath h) n) →ₗ[ℂ] groupCohomology.H1 (lineFaceRadH1Lit N n h) :=
  (groupCohomology.map (sigmaGamma N) (phiJ N n h) 1).hom

theorem h1J_bijective : Function.Bijective (h1J N n h) :=
  h1Map_bijective (sigmaGamma N) (sigmaGamma_bijective N) (phiJ N n h) (phiJ_bijective N n h)

/-- **Naturality of the edge**: `edge_{Q'}(ȷ^* x) = H¹(σ)(edge_{P''}(x))`. -/
theorem edgeL_kerJ (x : KerP N n h) : edgeL N n h (kerJ N n h x) = h1J N n h (faceEdge N (jmath h) n x) :=
  EdgeNat.edge_kerMap (faceSplitting N (jmath h)) (lineFaceSplitting N h) (faceJ N h) (sigmaGamma N) tauRad (faceJ_inl N h)
    (faceJ_split N h) (faceRep N (jmath h) n) (lineFaceRepLit N n h) (faceJT N n h) (faceJ_hT N n h) x

/-- **`H¹(σ)` carries `𝒞_P(E)` onto S2's `QDiLit`** (the cusp stabilizers correspond under `F ↦ D F`). -/
theorem h1J_mem_cuspidal_iff (x : groupCohomology.H1 (faceRadH1 N (jmath h) n)) :
    x ∈ faceCuspidal N (jmath h) n ↔ h1J N n h x ∈ cuspidalSubspace (CongruenceSubgroup.Gamma N) (lineFaceRadH1Lit N n h) :=
  mem_cuspidalFamily_map_iff (sigmaGamma N) (sigmaGamma_bijective N) (phiJ N n h) (phiJ_bijective N n h)
    (leviCuspStab (CongruenceSubgroup.Gamma N)) (leviCuspStab (CongruenceSubgroup.Gamma N)) (fun F => DGL * F)
    (fun b => ⟨DGL * b, by show DGL * (DGL * b) = b; rw [← mul_assoc, DGL_mul_self, one_mul]⟩) (fun F γ => sigma_leviCuspStab N F γ) x

/-- **Characterisation of `𝒞_Q(E*)` through the plane edge**: its elements are exactly the `ȷ`-transports `h2Map x` of the radical-kernel classes `x` at the plane cusp `ȷ(h)` whose edge is in `𝒞_P(E)`. -/
theorem mem_dualCuspidalQLiteral_iff_edge
    (η : groupCohomology.H2 (Rep.of ((dualRepC (gammaN N) n).comp (Subgroup.inclusion (gammaNQAt_le_N N h))))) :
    η ∈ dualCuspidalQLiteral N n h ↔
      ∃ x : KerP N n h, faceEdge N (jmath h) n x ∈ faceCuspidal N (jmath h) n ∧
        EdgeNat.h2Map (faceJ N h) (faceRep N (jmath h) n) (lineFaceRepLit N n h) (faceJT N n h) (faceJ_hT N n h) x.1 = η := by
  constructor
  · intro hη
    obtain ⟨y1, hy1, rfl⟩ := hη
    obtain ⟨y2, hy2, rfl⟩ := hy1
    obtain ⟨y3, hy3, rfl⟩ := hy2
    exact ⟨y3, hy3, h2Map_faceJ N n h y3.1⟩
  · rintro ⟨x, hx, rfl⟩
    rw [h2Map_faceJ]
    have h1 : x.1 ∈ faceCuspidalInH2 N (jmath h) n := Submodule.mem_map_of_mem (Submodule.mem_comap.2 hx)
    have h2 : facePullC (gammaNQAt_le_N N h) (gammaNPAt_le N (jmath h)) (jmath_Q_to_P h) n x.1 ∈ dualCuspidalQ N n h :=
      Submodule.mem_map_of_mem h1
    exact Submodule.mem_map_of_mem h2

theorem dualCuspidalQLiteral_le_ker
    (η : groupCohomology.H2 (Rep.of ((dualRepC (gammaN N) n).comp (Subgroup.inclusion (gammaNQAt_le_N N h)))))
    (hη : η ∈ dualCuspidalQLiteral N n h) :
    twoCohomologyRestriction (lineFaceExt N h).inl (lineFaceRepLit N n h) η = 0 := by
  obtain ⟨x, -, rfl⟩ := (mem_dualCuspidalQLiteral_iff_edge N n h η).1 hη
  exact EdgeNat.h2Map_ker (faceJ N h) tauRad (faceJ_inl N h) (faceRep N (jmath h) n) (lineFaceRepLit N n h) (faceJT N n h)
    (faceJ_hT N n h) x.1 x.2

/-- The inclusion `𝒞_Q(E*) ⊂ ker(res_N)`. -/
def cuspToKer : dualCuspidalQLiteral N n h →ₗ[ℂ] KerL N n h :=
  LinearMap.codRestrict _ (Submodule.subtype _) (fun η => dualCuspidalQLiteral_le_ker N n h η.1 η.2)

theorem cuspToKer_injective : Function.Injective (cuspToKer N n h) := fun a b hab => by
  have h' := congrArg Subtype.val hab
  exact Subtype.ext h'

/-- **The canonical alignment**: the Hochschild-Serre edge of the line face for the literal dual maps `𝒞_Q(E*)` into S2's `QDiLit`. -/
def cuspEdge : dualCuspidalQLiteral N n h →ₗ[ℂ] cuspidalSubspace (CongruenceSubgroup.Gamma N) (lineFaceRadH1Lit N n h) :=
  LinearMap.codRestrict _ ((edgeL N n h).comp (cuspToKer N n h)) (fun η => by
    obtain ⟨x, hx, hxη⟩ := (mem_dualCuspidalQLiteral_iff_edge N n h η.1).1 η.2
    have e : cuspToKer N n h η = kerJ N n h x := Subtype.ext hxη.symm
    change edgeL N n h (cuspToKer N n h η) ∈ _
    rw [e, edgeL_kerJ]
    exact (h1J_mem_cuspidal_iff N n h _).1 hx)

theorem cuspEdge_bijective : Function.Bijective (cuspEdge N n h) := by
  constructor
  · intro a b hab
    apply cuspToKer_injective
    apply edgeL_injective
    exact congrArg Subtype.val hab
  · rintro ⟨w, hw⟩
    obtain ⟨w₁, rfl⟩ := (h1J_bijective N n h).2 w
    have hw₁ : w₁ ∈ faceCuspidal N (jmath h) n := (h1J_mem_cuspidal_iff N n h w₁).2 hw
    obtain ⟨x, rfl⟩ := faceEdge_surjective N (jmath h) n w₁
    refine ⟨⟨EdgeNat.h2Map (faceJ N h) (faceRep N (jmath h) n) (lineFaceRepLit N n h) (faceJT N n h) (faceJ_hT N n h) x.1,
      (mem_dualCuspidalQLiteral_iff_edge N n h _).2 ⟨x, hw₁, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change edgeL N n h (kerJ N n h x) = _
    exact edgeL_kerJ N n h x

/-- **`𝒞_Q(E*) ≃ QDiLit`, canonically** (through the Hochschild-Serre edge and `ȷ`). -/
def dualCuspidalLiteralEquiv :
    dualCuspidalQLiteral N n h ≃ₗ[ℂ] cuspidalSubspace (CongruenceSubgroup.Gamma N) (lineFaceRadH1Lit N n h) :=
  LinearEquiv.ofBijective (cuspEdge N n h) (cuspEdge_bijective N n h)

/-- It carries the `ȷ`-pullback of a plane class with cuspidal edge to `H¹(σ)` of its edge. -/
theorem dualCuspidalLiteralEquiv_apply (x : KerP N n h) (hx : faceEdge N (jmath h) n x ∈ faceCuspidal N (jmath h) n) :
    ((dualCuspidalLiteralEquiv N n h ⟨EdgeNat.h2Map (faceJ N h) (faceRep N (jmath h) n) (lineFaceRepLit N n h) (faceJT N n h)
        (faceJ_hT N n h) x.1, (mem_dualCuspidalQLiteral_iff_edge N n h _).2 ⟨x, hx, rfl⟩⟩ :
      cuspidalSubspace (CongruenceSubgroup.Gamma N) (lineFaceRadH1Lit N n h)) : groupCohomology.H1 (lineFaceRadH1Lit N n h)) =
      h1J N n h (faceEdge N (jmath h) n x) :=
  edgeL_kerJ N n h x

end Align

end TernaryPeriodPolynomials.Argument.EisensteinDual
