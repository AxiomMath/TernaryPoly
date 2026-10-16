module

public import TernaryPeriodPolynomials.BoundaryComparison.SeriesModel.TermwiseIntegration

@[expose] public section


/-!
# The term of a coset is the translated seed pulled back to the Gram cone

Formalized by Claude Sonnet 5.5.
-/

open scoped Matrix.Norms.Elementwise MatrixGroups ContDiff
open Matrix Set

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormSeriesModel

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.EisensteinClass
  TernaryPeriodPolynomials.Argument.FormCochainBridge TernaryPeriodPolynomials.Argument.SeedC3

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

theorem sum_swap4 {M : Type*} [AddCommMonoid M] (f : Fin 5 → Fin 5 → Fin 5 → Fin 5 → M) :
    ∑ a, ∑ b, ∑ k, ∑ l, f a b k l = ∑ k, ∑ l, ∑ a, ∑ b, f a b k l := by
  calc ∑ a, ∑ b, ∑ k, ∑ l, f a b k l = ∑ a, ∑ k, ∑ b, ∑ l, f a b k l :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ k, ∑ a, ∑ b, ∑ l, f a b k l := Finset.sum_comm
    _ = ∑ k, ∑ a, ∑ l, ∑ b, f a b k l :=
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ a, ∑ b, f a b k l := Finset.sum_congr rfl fun k _ => Finset.sum_comm

/-- **Chain rule for the translated seed.**  For `δ ∈ SL₃(ℤ)` (matrix `g = realMat δ`) and a point `x` of the Gram cone, the
tangent vectors `u, v` pulled back along the normalization `φ = conePoint` and paired with the summand `ρ(g)⁻¹ g^* ω_h` at `φ x`
give `ρ(g)⁻¹` of the seed pulled back to the cone at the translated point `g x gᵀ`, evaluated on the translated vectors
`g u gᵀ, g v gᵀ`. -/
theorem summand_cone_chain (n : ℕ) (h : ℂ → ℂ) (δ : Matrix.SpecialLinearGroup (Fin 3) ℤ) {x : Mat3}
    (hx : x ∈ gramCone) (u v : Mat3) :
    ∑ a : Fin 5, ∑ b : Fin 5, MvPolynomial.C (((fderiv ℝ conePoint x u a * fderiv ℝ conePoint x v b : ℝ)) : ℂ) *
        summandPoly n h (realMat δ) (conePoint x) a b =
      rho (realMat δ)⁻¹ (∑ k : Fin 5, ∑ l : Fin 5,
        MvPolynomial.C (((fderiv ℝ conePoint (realMat δ * x * (realMat δ).transpose)
          (realMat δ * u * (realMat δ).transpose) k *
          fderiv ℝ conePoint (realMat δ * x * (realMat δ).transpose)
            (realMat δ * v * (realMat δ).transpose) l : ℝ)) : ℂ) *
          seedForm n h (conePoint (realMat δ * x * (realMat δ).transpose)) k l) := by
  have hg : (realMat δ).det = 1 := det_realMat δ
  set g := realMat δ with hgdef
  have hconj : conePoint (g * x * g.transpose) = planeAct g (conePoint x) := conePoint_conj hg hx
  have hpΩ : conePoint x ∈ Omega := conePoint_mem hx
  have hxc : g * x * g.transpose ∈ gramCone := conj_mem_gramCone hg hx
  -- derivative chain
  have hΦd : DifferentiableAt ℝ (planeAct g) (conePoint x) :=
    ((contDiffOn_planeAct g hg) _ hpΩ).contDiffAt (isOpen_Omega.mem_nhds hpΩ) |>.differentiableAt (by simp)
  have hφd : ∀ {z : Mat3}, z ∈ gramCone → DifferentiableAt ℝ conePoint z := fun {z} hz =>
    (contDiffOn_conePoint z hz).contDiffAt (isOpen_gramCone.mem_nhds hz) |>.differentiableAt (by simp)
  have heq : (planeAct g ∘ conePoint) =ᶠ[nhds x] (conePoint ∘ conjCLM g) := by
    filter_upwards [isOpen_gramCone.mem_nhds hx] with y hy
    change planeAct g (conePoint y) = conePoint (conjCLM g y)
    rw [FormCochainBridge.conjCLM_apply]
    exact (conePoint_conj hg hy).symm
  have hchain : ∀ w : Mat3, fderiv ℝ (planeAct g) (conePoint x) (fderiv ℝ conePoint x w) =
      fderiv ℝ conePoint (g * x * g.transpose) (g * w * g.transpose) := by
    intro w
    have hA : HasFDerivAt (planeAct g ∘ conePoint)
        ((fderiv ℝ (planeAct g) (conePoint x)).comp (fderiv ℝ conePoint x)) x :=
      hΦd.hasFDerivAt.comp x (hφd hx).hasFDerivAt
    have hxc' : conjCLM g x ∈ gramCone := by rw [FormCochainBridge.conjCLM_apply]; exact hxc
    have hB : HasFDerivAt (conePoint ∘ conjCLM g)
        ((fderiv ℝ conePoint (conjCLM g x)).comp (conjCLM g)) x :=
      (hφd hxc').hasFDerivAt.comp x (conjCLM g).hasFDerivAt
    have hA' := (Filter.EventuallyEq.hasFDerivAt_iff heq).mp hA
    have := congrArg (fun L => L w) (hA'.unique hB)
    simpa [FormCochainBridge.conjCLM_apply] using this
  have hcomp : ∀ (w : Fin 5 → ℝ) (k : Fin 5), fderiv ℝ (planeAct g) (conePoint x) w k =
      ∑ a : Fin 5, w a * fderiv ℝ (planeAct g) (conePoint x) (Pi.single a 1) k := by
    intro w k
    have hw : w = ∑ a : Fin 5, w a • (Pi.single a (1 : ℝ) : Fin 5 → ℝ) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hw]
    simp [map_sum, Finset.sum_apply]
  rw [← hchain u, ← hchain v, hconj]
  simp only [summandPoly, formPullback, rho_sum, rho_C_mul]
  simp only [hcomp (fderiv ℝ conePoint x u), hcomp (fderiv ℝ conePoint x v)]
  have key : ∀ k l : Fin 5, (MvPolynomial.C (((∑ a, fderiv ℝ conePoint x u a *
        fderiv ℝ (planeAct g) (conePoint x) (Pi.single a 1) k) *
        ∑ a, fderiv ℝ conePoint x v a * fderiv ℝ (planeAct g) (conePoint x) (Pi.single a 1) l : ℝ) : ℂ) :
        MvPolynomial (Fin 3) ℂ) =
      ∑ a, ∑ b, MvPolynomial.C (((fderiv ℝ conePoint x u a * fderiv ℝ conePoint x v b : ℝ)) : ℂ) *
        MvPolynomial.C (((fderiv ℝ (planeAct g) (conePoint x) (Pi.single a 1) k *
          fderiv ℝ (planeAct g) (conePoint x) (Pi.single b 1) l : ℝ)) : ℂ) := by
    intro k l
    rw [Finset.sum_mul_sum]
    simp only [Complex.ofReal_sum, map_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← map_mul]
    congr 1
    push_cast
    ring
  simp only [key]
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact sum_swap4 _

open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4 in
/-- **The seed pulled back to the Gram cone, on the triangle of the Gram matrices of three vertices**: the polynomial-valued integrand of the
Gram-triangle cochain of the (non-equivariant) seed form `ω_h`. -/
def seedTri (n : ℕ) (h : ℂ → ℂ) (y : Fin 3 → GeneralEisenstein.RealGL3) (q : ℝ × ℝ) : MvPolynomial (Fin 3) ℂ :=
  ∑ k : Fin 5, ∑ l : Fin 5,
    MvPolynomial.C (((fderiv ℝ conePoint (affTri (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) q)
        (gramOf (y 1) - gramOf (y 0)) k *
      fderiv ℝ conePoint (affTri (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) q)
        (gramOf (y 2) - gramOf (y 0)) l : ℝ)) : ℂ) *
      seedForm n h (conePoint (affTri (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) q)) k l

open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4 in
/-- **Each term of the series is the translated seed cochain** (OB7 step (c), classical side): for the coset `c = Γ_P δ`, the integrand
of the `c`-th term at the triangle point `q` of the Gram matrices of `y` is `coeff_m ρ(δ)⁻¹` of the integrand of the seed
Gram-triangle cochain at the translated vertices `δ y`. -/
theorem gTerm_eq_translated (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) (n : ℕ) {Fm : Type*}
    [FunLike Fm UpperHalfPlane ℂ] (f : Fm) (c : PlaneCoset Γ) (m : Fin 3 →₀ ℕ)
    (y : Fin 3 → GeneralEisenstein.RealGL3) {q : ℝ × ℝ} (hq : q ∈ stdTriangle) :
    gTerm Γ n f c m y q =
      (rho (realMat (Quotient.out c).1)⁻¹
        (seedTri n (fun z => f (UpperHalfPlane.ofComplex z))
          (fun i => Matrix.SpecialLinearGroup.mapGL ℝ (Quotient.out c).1 * y i) q)).coeff m := by
  generalize hδ : (Quotient.out c).1 = δ
  have hp : ∀ i, gramOf (y i) ∈ gramCone := fun i => gramOf_mem_gramCone (y i)
  have hpt : affTri (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) q ∈ gramCone :=
    affTri_mem convex_gramCone (hp 0) (hp 1) (hp 2) hq
  have e1 : ∀ i, gramOf (Matrix.SpecialLinearGroup.mapGL ℝ δ * y i) =
      realMat δ * gramOf (y i) * (realMat δ).transpose := by
    intro i; rw [gramOf_mul, mapGL_val]
  have haff : affTri (realMat δ * gramOf (y 0) * (realMat δ).transpose)
      (realMat δ * gramOf (y 1) * (realMat δ).transpose) (realMat δ * gramOf (y 2) * (realMat δ).transpose) q =
      realMat δ * affTri (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) q * (realMat δ).transpose := by
    have := (FormCochainBridge.conjCLM (realMat δ)).map_add
    simp only [affTri]
    simp only [← FormCochainBridge.conjCLM_apply, map_add, map_smul, map_sub]
  have hdiff : ∀ i j, realMat δ * gramOf (y i) * (realMat δ).transpose -
      realMat δ * gramOf (y j) * (realMat δ).transpose =
      realMat δ * (gramOf (y i) - gramOf (y j)) * (realMat δ).transpose := by
    intro i j; simp [Matrix.mul_sub, Matrix.sub_mul]
  have hchain := summand_cone_chain n (fun z => f (UpperHalfPlane.ofComplex z)) δ hpt
    (gramOf (y 1) - gramOf (y 0)) (gramOf (y 2) - gramOf (y 0))
  have hL : gTerm Γ n f c m y q = (∑ a : Fin 5, ∑ b : Fin 5,
      MvPolynomial.C (((fderiv ℝ conePoint (affTri (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) q)
        (gramOf (y 1) - gramOf (y 0)) a *
      fderiv ℝ conePoint (affTri (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) q)
        (gramOf (y 2) - gramOf (y 0)) b : ℝ)) : ℂ) *
      summandPoly n (fun z => f (UpperHalfPlane.ofComplex z)) (realMat δ)
        (conePoint (affTri (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) q)) a b).coeff m := by
    subst hδ
    unfold gTerm
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, termFun_def, summandPoly]
  have hs : seedTri n (fun z => f (UpperHalfPlane.ofComplex z))
      (fun i => Matrix.SpecialLinearGroup.mapGL ℝ δ * y i) q =
      ∑ k : Fin 5, ∑ l : Fin 5, MvPolynomial.C (((fderiv ℝ conePoint
          (realMat δ * affTri (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) q * (realMat δ).transpose)
          (realMat δ * (gramOf (y 1) - gramOf (y 0)) * (realMat δ).transpose) k *
        fderiv ℝ conePoint (realMat δ * affTri (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) q * (realMat δ).transpose)
          (realMat δ * (gramOf (y 2) - gramOf (y 0)) * (realMat δ).transpose) l : ℝ)) : ℂ) *
        seedForm n (fun z => f (UpperHalfPlane.ofComplex z))
          (conePoint (realMat δ * affTri (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) q * (realMat δ).transpose)) k l := by
    unfold seedTri
    simp only [e1, haff, hdiff]
  rw [hL, hchain, hs]

open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4
  TernaryPeriodPolynomials.Argument.Statements.EisensteinClass in
/-- **The Gram-triangle cochain of the series is the sum over `Γ_P\Γ` of the translated seed cochains** (classical side of OB7 steps (b)
and (c)).  Coefficientwise: `coeff_m F(y) = ∑_{c = Γ_P δ} ∫_{Δ(y)} coeff_m ρ(δ)⁻¹ [ (φ^*ω_h) at the translated triangle Δ(δ y) ]`. -/
theorem coeff_gramCochain_translated (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) {Fm : Type*}
    [FunLike Fm UpperHalfPlane ℂ] (Λ : Subgroup (GL (Fin 2) ℝ)) [Λ.HasDetOne] [Λ.IsArithmetic] (n : ℕ)
    [CuspFormClass Fm Λ ((n + 3 : ℕ) : ℤ)] (f : Fm) (hn : 4 ≤ n) (hLevi : LeviIn Γ Λ)
    (y : Fin 3 → GeneralEisenstein.RealGL3) (m : Fin 3 →₀ ℕ) :
    (Coef.toPoly (gramCochain Γ n (planeEisensteinInv Γ Λ n f hn hLevi) y)).coeff m =
      ∑' c : PlaneCoset Γ, ∫ q in stdTriangle,
        (rho (realMat (Quotient.out c).1)⁻¹
          (seedTri n (fun z => f (UpperHalfPlane.ofComplex z))
            (fun i => Matrix.SpecialLinearGroup.mapGL ℝ (Quotient.out c).1 * y i) q)).coeff m := by
  rw [coeff_gramCochain_tsum Γ Λ n f hn hLevi y m]
  refine tsum_congr fun c => ?_
  exact MeasureTheory.setIntegral_congr_fun measurableSet_stdTriangle fun q hq =>
    gTerm_eq_translated Γ n f c m y hq

end TernaryPeriodPolynomials.Argument.FormSeriesModel
