module

public import ModularLambdaRatio
public import TauCeti.Analysis.Complex.Fuchsian.LevelOne.Sphere
import TauCeti.NumberTheory.ModularForms.SiegelFunction.GammaTwo
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Algebra.Group.DiscontinuousSubgroup
import TauCeti.Analysis.Complex.Fuchsian.ProperAction
import Mathlib.Tactic.Ring

public section

open Complex TauCeti.ModularForm UpperHalfPlane Filter Set Topology
open scoped MatrixGroups

namespace BelgianChocolate.ModularLambdaRatio

private noncomputable def g0 (τ : ℍ) : ℂ := siegelFunction ![0, 1 / 2] τ ^ 4
private noncomputable def g1 (τ : ℍ) : ℂ := siegelFunction ![1 / 2, 0] τ ^ 4
private noncomputable def g2 (τ : ℍ) : ℂ := siegelFunction ![1 / 2, 1 / 2] τ ^ 4

private theorem siegel_product (τ : ℍ) : g0 τ * g1 τ * g2 τ = -16 :=
  siegelFunction_pow_four_mul_mul τ

private theorem g2_ne_zero (τ : ℍ) : g2 τ ≠ 0 := by
  intro hz
  have h := siegel_product τ
  rw [hz, mul_zero] at h
  norm_num at h

private theorem g1_eq (τ : ℍ) : g1 τ = (lambdaRatio τ - 1) * g2 τ := by
  have hc := one_sub_lambdaRatio τ
  change 1 - lambdaRatio τ = -g1 τ / g2 τ at hc
  have h := (eq_div_iff (g2_ne_zero τ)).mp hc
  linear_combination h

private theorem g0_eq (τ : ℍ) : g0 τ = -lambdaRatio τ * g2 τ := by
  have hs : g0 τ + g1 τ + g2 τ = 0 := siegelFunction_pow_four_add_add τ
  rw [g1_eq] at hs
  linear_combination hs

/-- The rational function on the moduli coordinate which forgets the level-two marking. -/
noncomputable def anharmonicInvariant (x : ℂ) : ℂ :=
  256 * (x ^ 2 - x + 1) ^ 3 / (x ^ 2 * (x - 1) ^ 2)

/-- The normalized modular invariant factors through the Siegel lambda coordinate. -/
theorem j_eq_anharmonicInvariant (τ : ℍ) : j τ = anharmonicInvariant (lambdaRatio τ) := by
  set a := lambdaRatio τ
  set z := g2 τ
  have hz : z ≠ 0 := g2_ne_zero τ
  have hp := siegel_product τ
  rw [g0_eq, g1_eq] at hp
  change (-a * z) * ((a - 1) * z) * z = -16 at hp
  have hp' : a * (a - 1) * z ^ 3 = 16 := by linear_combination -hp
  have hγ := gammaTwo_eq_siegelFunction_half_half τ
  have hpow : siegelFunction ![1 / 2, 1 / 2] τ ^ 12 = z ^ 3 := by
    change _ = (siegelFunction ![1 / 2, 1 / 2] τ ^ 4) ^ 3
    rw [← pow_mul]
  change gammaTwo τ = (siegelFunction ![1 / 2, 1 / 2] τ ^ 12 + 16) / z at hγ
  rw [hpow, eq_div_iff hz] at hγ
  have hvalue : gammaTwo τ = (a ^ 2 - a + 1) * z ^ 2 := by
    apply mul_right_cancel₀ hz
    linear_combination hγ - hp'
  have hden : a ^ 2 * (a - 1) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (lambdaRatio_ne_zero τ))
      (pow_ne_zero _ (sub_ne_zero.mpr (lambdaRatio_ne_one τ)))
  rw [← gammaTwo_pow_three, hvalue, anharmonicInvariant]
  apply (eq_div_iff hden).2
  linear_combination (a ^ 2 - a + 1) ^ 3 * congrArg (fun t : ℂ => t ^ 2) hp'

#print axioms j_eq_anharmonicInvariant


/-- Inversion exchanges the lambda coordinate with its complement. -/
theorem lambdaRatio_S (τ : ℍ) : lambdaRatio (ModularGroup.S • τ) = 1 - lambdaRatio τ := by
  have h := g0_eq (ModularGroup.S • τ)
  change siegelFunction ![0, 1 / 2] (↑(ModularGroup.S • τ) : ℂ) ^ 4 =
    -lambdaRatio (ModularGroup.S • τ) *
      siegelFunction ![1 / 2, 1 / 2] (↑(ModularGroup.S • τ) : ℂ) ^ 4 at h
  rw [ModularGroup.coe_S_smul, siegelFunction_zero_half_apply_neg_one_div τ.im_pos,
    siegelFunction_half_half_apply_neg_one_div τ.im_pos, mul_pow, neg_pow, I_pow_four] at h
  norm_num at h
  change g1 τ = -(lambdaRatio (ModularGroup.S • τ) * g2 τ) at h
  rw [g1_eq] at h
  apply mul_right_cancel₀ (g2_ne_zero τ)
  linear_combination h

/-- Translation by one acts by the second anharmonic involution. -/
theorem lambdaRatio_T (τ : ℍ) :
    lambdaRatio (ModularGroup.T • τ) = lambdaRatio τ / (lambdaRatio τ - 1) := by
  let e := Complex.exp (Real.pi * Complex.I / 6) ^ 4
  have he : e ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
  have hphase : Complex.exp (-(Real.pi * Complex.I / 3)) ^ 4 = e := by
    unfold e
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    have harg : (4 : ℂ) * -(Real.pi * Complex.I / 3) =
        4 * (Real.pi * Complex.I / 6) - 2 * Real.pi * Complex.I := by ring
    change Complex.exp ((4 : ℂ) * -(Real.pi * Complex.I / 3)) = _
    rw [harg]
    exact Complex.exp_periodic.sub_eq _
  have h := g0_eq (ModularGroup.T • τ)
  change siegelFunction ![0, 1 / 2] (↑(ModularGroup.T • τ) : ℂ) ^ 4 =
    -lambdaRatio (ModularGroup.T • τ) *
      siegelFunction ![1 / 2, 1 / 2] (↑(ModularGroup.T • τ) : ℂ) ^ 4 at h
  rw [ModularGroup.coe_T_smul, siegelFunction_zero_half_apply_add_one,
    siegelFunction_half_half_apply_add_one, mul_pow, mul_pow, hphase] at h
  change e * g0 τ = -lambdaRatio (ModularGroup.T • τ) * (e * g1 τ) at h
  rw [g0_eq, g1_eq] at h
  apply (eq_div_iff (sub_ne_zero.mpr (lambdaRatio_ne_one τ))).2
  apply mul_right_cancel₀ (mul_ne_zero he (g2_ne_zero τ))
  linear_combination h

private theorem lambdaRatio_ST (τ : ℍ) :
    lambdaRatio (ModularGroup.S • (ModularGroup.T • τ)) = 1 / (1 - lambdaRatio τ) := by
  rw [lambdaRatio_S, lambdaRatio_T]
  have h₁ := sub_ne_zero.mpr (lambdaRatio_ne_one τ)
  have h₂ := sub_ne_zero.mpr (lambdaRatio_ne_one τ).symm
  field_simp
  ring

private theorem lambdaRatio_TS (τ : ℍ) :
    lambdaRatio (ModularGroup.T • (ModularGroup.S • τ)) = (lambdaRatio τ - 1) / lambdaRatio τ := by
  rw [lambdaRatio_T, lambdaRatio_S, show 1 - lambdaRatio τ - 1 = -lambdaRatio τ by ring, div_neg]
  ring

private theorem lambdaRatio_STS (τ : ℍ) :
    lambdaRatio (ModularGroup.S • (ModularGroup.T • (ModularGroup.S • τ))) = 1 / lambdaRatio τ := by
  rw [lambdaRatio_ST, lambdaRatio_S, sub_sub_cancel]

/-- After the punctures are removed each fiber of the rational invariant is an anharmonic orbit. -/
theorem anharmonicInvariant_fiber {a b : ℂ}
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) (hb0 : b ≠ 0) (hb1 : b ≠ 1)
    (h : anharmonicInvariant a = anharmonicInvariant b) :
    a = b ∨ a = 1 - b ∨ a = 1 / b ∨ a = b / (b - 1) ∨
      a = 1 / (1 - b) ∨ a = (b - 1) / b := by
  have ha := mul_ne_zero (pow_ne_zero 2 ha0) (pow_ne_zero 2 (sub_ne_zero.mpr ha1))
  have hb := mul_ne_zero (pow_ne_zero 2 hb0) (pow_ne_zero 2 (sub_ne_zero.mpr hb1))
  have he := (div_eq_div_iff ha hb).mp h
  have hf : (a - b) * (a + b - 1) * (b * a - 1) * ((b - 1) * a - b) *
      ((b - 1) * a + 1) * (b * a - b + 1) = 0 := by
    linear_combination (1 / 256 : ℂ) * he
  simp only [mul_eq_zero] at hf
  rcases hf with (((((h | h) | h) | h) | h) | h)
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (Or.inl (by linear_combination h))
  · exact Or.inr (Or.inr (Or.inl ((eq_div_iff hb0).2 (by linear_combination h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ((eq_div_iff (sub_ne_zero.mpr hb1)).2 (by linear_combination h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ((eq_div_iff (sub_ne_zero.mpr hb1.symm)).2 (by linear_combination -h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ((eq_div_iff hb0).2 (by linear_combination h))))))

/-- The range of the lambda coordinate is the plane with zero and one removed. -/
theorem lambdaRatio_surj {a : ℂ} (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    ∃ τ : ℍ, lambdaRatio τ = a := by
  obtain ⟨τ, hτ⟩ := j_surjective (anharmonicInvariant a)
  rw [j_eq_anharmonicInvariant] at hτ
  rcases anharmonicInvariant_fiber ha0 ha1 (lambdaRatio_ne_zero τ) (lambdaRatio_ne_one τ) hτ.symm
    with h | h | h | h | h | h
  · exact ⟨τ, h.symm⟩
  · exact ⟨ModularGroup.S • τ, (lambdaRatio_S τ).trans h.symm⟩
  · exact ⟨ModularGroup.S • (ModularGroup.T • (ModularGroup.S • τ)),
      (lambdaRatio_STS τ).trans h.symm⟩
  · exact ⟨ModularGroup.T • τ, (lambdaRatio_T τ).trans h.symm⟩
  · exact ⟨ModularGroup.S • (ModularGroup.T • τ), (lambdaRatio_ST τ).trans h.symm⟩
  · exact ⟨ModularGroup.T • (ModularGroup.S • τ), (lambdaRatio_TS τ).trans h.symm⟩

#print axioms lambdaRatio_S
#print axioms lambdaRatio_T
#print axioms anharmonicInvariant_fiber
#print axioms lambdaRatio_surj


private def modTwo : SL(2, ℤ) →* SL(2, ZMod 2) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 2))

private theorem modTwo_cases (g : SL(2, ZMod 2)) :
    g = modTwo 1 ∨ g = modTwo ModularGroup.S ∨ g = modTwo ModularGroup.T ∨
      g = modTwo (ModularGroup.S * ModularGroup.T) ∨
      g = modTwo (ModularGroup.T * ModularGroup.S) ∨
      g = modTwo (ModularGroup.S * ModularGroup.T * ModularGroup.S) := by
  revert g
  decide

private theorem lambdaRatio_modTwo {g h : SL(2, ℤ)} (he : modTwo g = modTwo h) (τ : ℍ) :
    lambdaRatio (g • τ) = lambdaRatio (h • τ) := by
  have hΓ : g * h⁻¹ ∈ CongruenceSubgroup.Gamma 2 := CongruenceSubgroup.Gamma_mem'.2 (by
    change modTwo (g * h⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel])
  simpa only [← mul_smul, mul_assoc, inv_mul_cancel, mul_one] using
    lambdaRatio_gammaTwo hΓ (h • τ)

private def regularLambdaValue (b : ℂ) : Prop :=
  b ≠ 1 - b ∧ b ≠ b / (b - 1) ∧ b ≠ 1 / (1 - b) ∧ b ≠ (b - 1) / b ∧ b ≠ 1 / b

private theorem levelTwo_orbit_of_regular_fiber {τ σ : ℍ}
    (h : lambdaRatio τ = lambdaRatio σ) (hregular : regularLambdaValue (lambdaRatio τ)) :
    ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • τ = σ := by
  have hj : j τ = j σ := by simp only [j_eq_anharmonicInvariant, h]
  obtain ⟨g, rfl⟩ := TauCeti.ModularGroup.j_eq_j_iff.mp hj
  rcases modTwo_cases (modTwo g) with hg | hg | hg | hg | hg | hg
  · exact ⟨g, CongruenceSubgroup.Gamma_mem'.2 (by change modTwo g = 1; simpa only [map_one] using hg), rfl⟩
  · exact (hregular.1 (h.trans ((lambdaRatio_modTwo hg τ).trans (lambdaRatio_S τ)))).elim
  · exact (hregular.2.1 (h.trans ((lambdaRatio_modTwo hg τ).trans (lambdaRatio_T τ)))).elim
  · apply (hregular.2.2.1 _).elim
    simpa only [mul_smul, lambdaRatio_ST] using h.trans (lambdaRatio_modTwo hg τ)
  · apply (hregular.2.2.2.1 _).elim
    simpa only [mul_smul, lambdaRatio_TS] using h.trans (lambdaRatio_modTwo hg τ)
  · apply (hregular.2.2.2.2 _).elim
    simpa only [mul_smul, lambdaRatio_STS] using h.trans (lambdaRatio_modTwo hg τ)

private theorem dense_regularLambdaValue : Dense {b : ℂ | regularLambdaValue b} := by
  let p : Polynomial ℂ :=
    (Polynomial.X + 1) * (2 * Polynomial.X - 1) * (Polynomial.X - 2) *
      (Polynomial.X ^ 2 - Polynomial.X + 1) * Polynomial.X * (Polynomial.X - 1)
  have hp : p ≠ 0 := by
    intro h
    have hval := congrArg (Polynomial.eval (3 : ℂ)) h
    norm_num [p] at hval
  have hd : Dense ({b : ℂ | Polynomial.IsRoot p b}ᶜ : Set ℂ) := by
    simpa only [Set.compl_eq_univ_sdiff] using
      (dense_univ.sdiff_finite (Polynomial.finite_setOfPred_isRoot hp))
  apply hd.mono
  intro b hb
  have hbnn : (b + 1) * (2 * b - 1) * (b - 2) * (b ^ 2 - b + 1) * b * (b - 1) ≠ 0 := by
    simpa [p, Polynomial.IsRoot] using hb
  simp only [mul_ne_zero_iff] at hbnn
  obtain ⟨⟨⟨⟨⟨hp₁, hp₂⟩, hp₃⟩, hp₄⟩, hb0⟩, hb1⟩ := hbnn
  have hb1' : 1 - b ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp hb1).symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hp₂ (by linear_combination h)
  · intro h
    have h' := (eq_div_iff hb1).mp h
    exact mul_ne_zero hb0 hp₃ (by linear_combination h')
  · intro h
    have h' := (eq_div_iff hb1').mp h
    exact hp₄ (by linear_combination -h')
  · intro h
    have h' := (eq_div_iff hb0).mp h
    exact hp₄ (by linear_combination h')
  · intro h
    have h' := (eq_div_iff hb0).mp h
    exact mul_ne_zero hp₁ hb1 (by linear_combination h')

/-- Holomorphic nonconstancy makes the Siegel lambda coordinate an open map. -/
theorem lambdaRatio_isOpenMap : IsOpenMap lambdaRatio := by
  let U : Set ℂ := {z | 0 < z.im}
  let f : ℂ → ℂ := fun z => -(siegelFunction ![0, 1 / 2] z ^ 4) /
    siegelFunction ![1 / 2, 1 / 2] z ^ 4
  have hratio (z : ℍ) : f (z : ℂ) = lambdaRatio z := by
    change -g0 z / g2 z = lambdaRatio z
    rw [g0_eq, neg_mul, neg_neg, mul_div_cancel_right₀ _ (g2_ne_zero z)]
  have hd : DifferentiableOn ℂ f U :=
    ((differentiableOn_siegelFunction ![0, 1 / 2]).pow 4).neg.div
      ((differentiableOn_siegelFunction ![1 / 2, 1 / 2]).pow 4)
      (fun z hz => g2_ne_zero ⟨z, hz⟩)
  have ho : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hc : IsPreconnected U := (convex_halfSpace_im_gt 0).isPreconnected
  rcases (hd.analyticOnNhd ho).is_constant_or_isOpen hc with ⟨c, hconst⟩ | hopen
  · obtain ⟨z, hz⟩ := lambdaRatio_surj (a := 2) (by norm_num) (by norm_num)
    obtain ⟨w, hw⟩ := lambdaRatio_surj (a := 3) (by norm_num) (by norm_num)
    have h := (hratio z).symm.trans ((hconst z z.im_pos).trans
      ((hconst w w.im_pos).symm.trans (hratio w)))
    norm_num [hz, hw] at h
  · intro V hV
    have hVU : ((↑) : ℍ → ℂ) '' V ⊆ U := by
      rintro _ ⟨z, _, rfl⟩
      exact z.im_pos
    have hEq : lambdaRatio = f ∘ ((↑) : ℍ → ℂ) := funext fun z => (hratio z).symm
    rw [hEq]
    change IsOpen ((fun z : ℍ => f (z : ℂ)) '' V)
    simpa only [Set.image_image] using hopen _ hVU (UpperHalfPlane.isOpenEmbedding_coe.isOpenMap V hV)

open Matrix.ProjectiveSpecialLinearGroup MulAction in
/-- The fibers of lambda are exactly the orbits of the principal level-two subgroup. -/
theorem lambdaRatio_fiber {τ σ : ℍ} :
    lambdaRatio τ = lambdaRatio σ ↔ ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • τ = σ := by
  let Γ := (CongruenceSubgroup.Gamma 2).map sl2zToPSL2R
  let p (z : ℍ) : orbitRel.Quotient Γ ℍ := Quotient.mk'' z
  have hp : Continuous p := continuous_quotient_mk'
  have hclosed : IsClosed {w : ℍ × ℍ | p w.1 = p w.2} :=
    isClosed_eq (hp.comp continuous_fst) (hp.comp continuous_snd)
  have horbit {z w : ℍ} : p z = p w ↔ ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • z = w := by
    change Quotient.mk'' z = (Quotient.mk'' w : orbitRel.Quotient Γ ℍ) ↔ _
    rw [eq_comm, Quotient.eq, orbitRel_apply, mem_orbit_iff]
    constructor
    · rintro ⟨⟨_, γ, hγ, rfl⟩, he⟩
      exact ⟨γ, hγ, by simpa [Subgroup.smul_def, UpperHalfPlane.sl2zToPSL2R_smul] using he⟩
    · rintro ⟨γ, hγ, he⟩
      exact ⟨⟨sl2zToPSL2R γ, Subgroup.mem_map_of_mem _ hγ⟩,
        by simpa [Subgroup.smul_def, UpperHalfPlane.sl2zToPSL2R_smul] using he⟩
  constructor
  · intro h
    apply horbit.mp
    by_contra hn
    obtain ⟨U, hU, V, hV, hne⟩ := mem_nhds_prod_iff.mp (hclosed.isOpen_compl.mem_nhds hn)
    have hImageU : lambdaRatio '' U ∈ 𝓝 (lambdaRatio τ) :=
      lambdaRatio_isOpenMap.nhds_le _ (image_mem_map hU)
    have hImageV : lambdaRatio '' V ∈ 𝓝 (lambdaRatio τ) :=
      h ▸ lambdaRatio_isOpenMap.nhds_le _ (image_mem_map hV)
    obtain ⟨a, ha, ⟨z, hz, hza⟩, ⟨w, hw, hwa⟩⟩ :=
      dense_regularLambdaValue.inter_nhds_nonempty (inter_mem hImageU hImageV)
    have hzw := levelTwo_orbit_of_regular_fiber (hza.trans hwa.symm) (hza ▸ ha)
    have hpair : (z, w) ∈ U ×ˢ V := ⟨hz, hw⟩
    exact (hne hpair) (horbit.mpr hzw)
  · rintro ⟨γ, hγ, rfl⟩
    exact (lambdaRatio_gammaTwo hγ τ).symm

#print axioms lambdaRatio_isOpenMap
#print axioms lambdaRatio_fiber

end BelgianChocolate.ModularLambdaRatio







