import ContinuedFractionBound
import Mathlib.Analysis.Normed.Field.Approximation

open Filter Topology Polynomial
namespace BelgianChocolate.Conjectures
open ControlWitness (StrictlyStable)

/-- Near a monic limiting polynomial of fixed positive degree, each prescribed root
has a nearby root of the approximating polynomial. -/
theorem eventually_near_aroot {ι : Type*} {l : Filter ι}
    {p : ι → ℝ[X]} {q : ℝ[X]} {m : ℕ} (hm : 0 < m)
    (hpm : ∀ j, (p j).Monic) (hqm : q.Monic)
    (hpd : ∀ j, (p j).natDegree = m) (hqd : q.natDegree = m)
    (hc : ∀ k, Tendsto (fun j => (p j).coeff k) l (𝓝 (q.coeff k)))
    {z : ℂ} (hz : aeval z q = 0) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ j in l, ∃ w : ℂ, aeval w (p j) = 0 ∧ dist z w < r := by
  let M := max ‖z‖ 1
  let ε := (r/M)^m/((m:ℝ)+1)
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hscale : (((m:ℝ)+1)*ε)^((m:ℝ)⁻¹)*M = r := by
    have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    rw [show ((m:ℝ)+1)*ε = (r/M)^m by dsimp [ε]; field_simp]
    rw [← Real.rpow_natCast,← Real.rpow_mul (by positivity),mul_inv_cancel₀ hmR,
      Real.rpow_one,div_mul_cancel₀ _ hM.ne']
  have hfinit : ∀ᶠ j in l, ∀ k ∈ Finset.range (m+1), ‖(p j).coeff k-q.coeff k‖ < ε := by
    classical
    rw [Filter.eventually_all_finset]
    intro k _
    exact (Metric.tendsto_nhds.mp (hc k) ε hε).mono (fun j hj => by rwa [dist_eq_norm] at hj)
  filter_upwards [hfinit] with j hj
  have hcoeff (k : ℕ) : ‖(p j).coeff k - q.coeff k‖ < ε := by
    by_cases hk : k < m+1
    · exact hj k (Finset.mem_range.mpr hk)
    · have hpzero := coeff_eq_zero_of_natDegree_lt (p := p j) (by rw [hpd]; omega : (p j).natDegree < k)
      have hqzero := coeff_eq_zero_of_natDegree_lt (p := q) (by rw [hqd]; omega : q.natDegree < k)
      simpa [hpzero,hqzero] using hε
  obtain ⟨w,hw,hwr⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt (f:=q) (g:=p j)
    hε hz hqm (hpm j) ((hpd j).trans hqd.symm) hcoeff (IsAlgClosed.splits _)
  rw [hqd,hscale] at hwr
  exact ⟨w,(mem_aroots.mp hw).2,by rwa [dist_eq_norm]⟩

private theorem continuous_phase : Continuous phase := by
  unfold phase
  fun_prop

/-- The angle corresponding to the endpoint δₙ. -/
noncomputable def criticalAngle (n : ℕ) : ℝ := Real.pi/(2*((n:ℝ)+1))

theorem criticalAngle_pos (n : ℕ) : 0 < criticalAngle n := by
  unfold criticalAngle
  positivity

theorem criticalAngle_lt_half_pi {n : ℕ} (hn : 0 < n) : criticalAngle n < Real.pi/2 := by
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  unfold criticalAngle
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [Real.pi_pos]

theorem criticalAngle_mul (n : ℕ) : ((n:ℝ)+1)*criticalAngle n = Real.pi/2 := by
  unfold criticalAngle
  field_simp

theorem delta_pos {n : ℕ} (hn : 0 < n) : 0 < δₙ n := by
  change 0 < Real.cos (criticalAngle n)
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith [criticalAngle_pos n,Real.pi_pos],criticalAngle_lt_half_pi hn⟩

theorem criticalAngle_arccos {n : ℕ} (hn : 0 < n) : Real.arccos (δₙ n) = criticalAngle n := by
  apply Real.arccos_cos (criticalAngle_pos n).le
  linarith [criticalAngle_lt_half_pi hn,Real.pi_pos]

/-- The full complex evaluation identity, whose real part was used in the all-orders bound. -/
theorem loop_rotated_eval (θ y : ℝ) (x : ℝ[X]) :
    phase (-θ)*aeval (phase θ) (loop (Real.cos θ) x y) =
      (phase θ-phase (-θ))*(y:ℂ) := by
  simp only [loop,map_add,map_mul,plant_phase,zero_mul,zero_add,map_sub,map_pow,
    aeval_X,map_one,aeval_C]
  change phase (-θ)*(((phase θ)^2-1)*(y:ℂ)) = _
  linear_combination (phase θ)*(y:ℂ)*phase_pair θ

theorem phase_diff (θ : ℝ) :
    (phase θ-phase (-θ)) = ((2*Real.sin θ : ℝ):ℂ)*Complex.I := by
  apply Complex.ext
  · simp only [Complex.sub_re,phase_re,Real.cos_neg,sub_self,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul]
  · simp only [Complex.sub_im,phase_im,Real.sin_neg,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_im,Complex.I_re,mul_one,zero_mul,add_zero]
    ring

/-- The coefficient limits forced by the cosine balance at the conjectured endpoint. -/
theorem loop_coeff_boundary {n : ℕ} (hn : 0 < n) {ι : Type*} {l : Filter ι}
    {δ : ι → ℝ} {x : ι → ℝ[X]} {y : ι → ℝ}
    (hp : ∀ j, 0 < δ j) (hδ : ∀ j, δ j < 1)
    (ht : Tendsto δ l (𝓝 (δₙ n))) (hm : ∀ j, (x j).Monic)
    (hd : ∀ j, (x j).natDegree = n)
    (hz : ∀ j, StrictlyStable (loop (δ j) (x j) (y j))) :
    (∀ k, Tendsto (fun j => (loop (δ j) (x j) (y j)).coeff k) l
      (𝓝 ((X^(n+2) : ℝ[X]).coeff k))) ∧
    Tendsto y l (𝓝 (1/(2*Real.sin (criticalAngle n)))) := by
  let θ := fun j => Real.arccos (δ j)
  let Z := fun j => loop (δ j) (x j) (y j)
  let w := fun (k : ℕ) (t : ℝ) => Real.cos (((k:ℝ)-1)*t)
  have hθ : Tendsto θ l (𝓝 (criticalAngle n)) := by
    rw [← criticalAngle_arccos hn]
    exact Real.continuous_arccos.continuousAt.tendsto.comp ht
  have hcos (j : ι) : Real.cos (θ j) = δ j := Real.cos_arccos (by linarith [hp j]) (hδ j).le
  have hdeg (j : ι) : (Z j).natDegree = n+2 := by
    rw [(loop_monic_degree (hm j) (by simpa [hd j])).2,hd j]
  have hmon (j : ι) : (Z j).Monic := (loop_monic_degree (hm j) (by simpa [hd j])).1
  have hpos (j : ι) (k : ℕ) (hk : k ≤ n+2) : 0 < (Z j).coeff k :=
    coeff_pos_of_monic_stable (hmon j) (hz j) k (by rwa [hdeg])
  have hlead (j : ι) : (Z j).coeff (n+2) = 1 := by rw [← hdeg j, ← leadingCoeff, hmon j]
  have hbal (j : ι) : ∑ k ∈ Finset.range (n+2), (Z j).coeff k * w k (θ j) = -w (n+2) (θ j) := by
    have he := loop_rotated_re_zero (θ j) (y j) (x j)
    rw [hcos,rotate_eval_re] at he
    change (∑ k ∈ Finset.range ((Z j).natDegree+1), (Z j).coeff k * w k (θ j)) = 0 at he
    rw [hdeg j, Finset.sum_range_succ,hlead j,one_mul] at he
    linarith only [he]
  have hwt (k : ℕ) : Tendsto (fun j => w k (θ j)) l (𝓝 (w k (criticalAngle n))) :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousAt.tendsto.comp hθ
  have hwp (k : ℕ) (hk : k < n+2) : 0 < w k (criticalAngle n) := by
    have hkR : (k:ℝ) ≤ n+1 := by exact_mod_cast (show k ≤ n+1 by omega)
    have hkR0 : 0 ≤ (k:ℝ) := by positivity
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · nlinarith only [mul_nonneg hkR0 (criticalAngle_pos n).le,criticalAngle_lt_half_pi hn]
    · nlinarith only [mul_nonneg (sub_nonneg.mpr hkR) (criticalAngle_pos n).le,
        criticalAngle_pos n, criticalAngle_mul n]
  have hwt_top : w (n+2) (criticalAngle n) = 0 := by
    dsimp [w]
    rw [show ((↑(n+2) : ℝ)-1) = (n:ℝ)+1 by push_cast; ring,
      criticalAngle_mul, Real.cos_pi_div_two]
  have hwp_ev : ∀ᶠ j in l, ∀ k ∈ Finset.range (n+2), 0 < w k (θ j) := by
    classical
    rw [Filter.eventually_all_finset]
    intro k hk
    exact (hwt k).eventually (lt_mem_nhds (hwp k (Finset.mem_range.mp hk)))
  have hct (k : ℕ) : Tendsto (fun j => (Z j).coeff k) l (𝓝 ((X^(n+2):ℝ[X]).coeff k)) := by
    rw [coeff_X_pow]
    rcases lt_trichotomy k (n+2) with hk | rfl | hk
    · rw [ite_eq_right hk.ne]
      have hlim : Tendsto (fun j => -(w (n+2) (θ j))/(w k (θ j))) l (𝓝 0) := by
        have hh := (hwt (n+2)).neg.div (hwt k) (hwp k hk).ne'
        change Tendsto (fun j => -(w (n+2) (θ j))/(w k (θ j))) l
          (𝓝 (-(w (n+2) (criticalAngle n))/(w k (criticalAngle n)))) at hh
        simpa [hwt_top] using hh
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      · exact Filter.Eventually.of_forall (fun j => (hpos j k hk.le).le)
      · filter_upwards [hwp_ev] with j hj
        apply (le_div_iff₀ (hj k (Finset.mem_range.mpr hk))).mpr
        rw [← hbal j]
        exact Finset.single_le_sum (fun i hi =>
          mul_nonneg (hpos j i (Finset.mem_range.mp hi).le).le (hj i hi).le)
          (Finset.mem_range.mpr hk)
    · rw [ite_eq_left rfl]
      exact tendsto_const_nhds.congr (fun j => (hlead j).symm)
    · rw [ite_eq_right hk.ne']
      exact tendsto_const_nhds.congr (fun j => (coeff_eq_zero_of_natDegree_lt (by rwa [hdeg])).symm)
  refine ⟨hct,?_⟩
  have hζ : Tendsto (fun j => phase (θ j)) l (𝓝 (phase (criticalAngle n))) :=
    continuous_phase.continuousAt.tendsto.comp hθ
  have hEv :
      Tendsto (fun j => aeval (phase (θ j)) (Z j)) l (𝓝 ((phase (criticalAngle n))^(n+2))) := by
    rw [← show aeval (phase (criticalAngle n)) (X^(n+2) : ℝ[X]) =
      phase (criticalAngle n)^(n+2) by simp]
    simp only [aeval_def, eval₂_eq_sum_range, hdeg, natDegree_X_pow]
    apply tendsto_finsetSum
    intro k _
    exact (Complex.continuous_ofReal.continuousAt.tendsto.comp (hct k)).mul (hζ.pow k)
  have hE := (continuous_phase.continuousAt.tendsto.comp hθ.neg).mul hEv
  have hcenter : phase (-(criticalAngle n))*phase (criticalAngle n)^(n+2) = Complex.I := by
    rw [phase_pow,← phase_add,
      show -criticalAngle n + (↑(n+2):ℝ)*criticalAngle n = Real.pi/2 by
        push_cast
        linear_combination criticalAngle_mul n]
    apply Complex.ext <;> simp
  rw [hcenter] at hE
  have him := Complex.continuous_im.continuousAt.tendsto.comp hE
  change Tendsto (fun j => (phase (-(θ j))*aeval (phase (θ j)) (Z j)).im) l (𝓝 1) at him
  have hval (j : ι) : (phase (-(θ j))*aeval (phase (θ j)) (Z j)).im =
      (2*Real.sin (θ j))*y j := by
    have h := loop_rotated_eval (θ j) (y j) (x j)
    rw [hcos,phase_diff] at h
    change (phase (-(θ j))*aeval (phase (θ j)) (Z j)).im = _
    rw [h]
    simp only [Complex.mul_im,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_zero,mul_one,sub_self,add_zero,zero_add]
  have hb : Tendsto (fun j => 2*Real.sin (θ j)) l
      (𝓝 (2*Real.sin (criticalAngle n))) :=
    tendsto_const_nhds.mul (Real.continuous_sin.continuousAt.tendsto.comp hθ)
  have hd0 : 0 < 2*Real.sin (criticalAngle n) := mul_pos (by norm_num)
    (Real.sin_pos_of_pos_of_lt_pi (criticalAngle_pos n) (by linarith [criticalAngle_lt_half_pi hn,Real.pi_pos]))
  apply (him.div hb hd0.ne').congr
  intro j
  change (phase (-(θ j))*aeval (phase (θ j)) (Z j)).im/(2*Real.sin (θ j)) = y j
  rw [hval]
  have hθj : 0 < θ j := Real.arccos_pos.mpr (hδ j)
  have hθj' : θ j < Real.pi/2 := Real.arccos_lt_pi_div_two.mpr (hp j)
  have hsj : 0 < Real.sin (θ j) := Real.sin_pos_of_pos_of_lt_pi hθj (by linarith [Real.pi_pos])
  exact (div_eq_iff (mul_pos (by norm_num : (0:ℝ)<2) hsj).ne').mpr (mul_comm _ _)

#print axioms loop_coeff_boundary
end BelgianChocolate.Conjectures

