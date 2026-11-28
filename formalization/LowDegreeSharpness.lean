import PowerLoop
import LowDegreeHurwitz

open Polynomial Filter Topology
namespace BelgianChocolate.Conjectures
open ControlWitness (StrictlyStable)
set_option maxHeartbeats 1800000

private noncomputable def q₀ (n : ℕ) (θ : ℝ) :=
  powerLoopNumerator n θ + powerLoopShift n θ^(n+2)

private noncomputable def q₁ (n : ℕ) (θ : ℝ) :=
  2*Real.cos θ*q₀ n θ + ((n:ℝ)+2)*powerLoopShift n θ^(n+1)

private noncomputable def a (n : ℕ) (θ : ℝ) :=
  2*Real.cos θ+((n:ℝ)+2)*powerLoopShift n θ

private noncomputable def b (n : ℕ) (θ : ℝ) :=
  2*Real.cos θ*a n θ-1+((n+2).choose 2:ℝ)*powerLoopShift n θ^2

private theorem coeff_loop (δ y : ℝ) (x : ℝ[X]) (k : ℕ) :
    (loop δ x y).coeff k =
      (if 2 ≤ k then x.coeff (k-2) else 0) -
      2*δ*(if 1 ≤ k then x.coeff (k-1) else 0)+x.coeff k+
      ((if k=2 then 1 else 0)-(if k=0 then 1 else 0))*y := by
  rw [show loop δ x y = X^2*x-C (2*δ)*(X^1*x)+x+(X^2-1)*C y by
    unfold loop plant
    ring]
  simp only [coeff_add,coeff_sub,coeff_X_pow_mul',coeff_C_mul,coeff_mul_C,coeff_X_pow,coeff_one]

private theorem q₀_eq {n : ℕ} {θ : ℝ} {x : ℝ[X]}
    (h : loop (Real.cos θ) x (powerLoopNumerator n θ) = (X+C (powerLoopShift n θ))^(n+2)) :
    x.coeff 0 = q₀ n θ := by
  have h0 := congrArg (fun p : ℝ[X] => p.coeff 0) h
  simp [coeff_loop,coeff_X_add_C_pow] at h0
  unfold q₀
  linarith only [h0]

private theorem q₁_eq {n : ℕ} {θ : ℝ} {x : ℝ[X]}
    (h : loop (Real.cos θ) x (powerLoopNumerator n θ) = (X+C (powerLoopShift n θ))^(n+2)) :
    x.coeff 1 = q₁ n θ := by
  have h1 := congrArg (fun p : ℝ[X] => p.coeff 1) h
  simp [coeff_loop,coeff_X_add_C_pow,q₀_eq h,show n+2-1=n+1 by omega] at h1
  unfold q₁
  linarith only [h1]

private theorem a_eq {n : ℕ} (hn : 2 ≤ n) {θ : ℝ} {x : ℝ[X]}
    (hm : x.Monic) (hd : x.natDegree = n)
    (h : loop (Real.cos θ) x (powerLoopNumerator n θ) = (X+C (powerLoopShift n θ))^(n+2)) :
    x.coeff (n-1) = a n θ := by
  have hc := congrArg (fun p : ℝ[X] => p.coeff (n+1)) h
  have hhead : x.coeff n = 1 := hd ▸ hm.coeff_natDegree
  have hzero : x.coeff (n+1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  simp [coeff_loop, coeff_X_add_C_pow,show 2 ≤ n+1 by omega,
    show n+1-2=n-1 by omega,show n+1 ≠ 2 by omega,
    show n+2-(n+1)=1 by omega,hhead,hzero] at hc
  unfold a
  linarith only [hc]

private theorem b_eq {n : ℕ} (hn : 3 ≤ n) {θ : ℝ} {x : ℝ[X]}
    (hm : x.Monic) (hd : x.natDegree = n)
    (h : loop (Real.cos θ) x (powerLoopNumerator n θ) = (X+C (powerLoopShift n θ))^(n+2)) :
    x.coeff (n-2) = b n θ := by
  have hc := congrArg (fun p : ℝ[X] => p.coeff n) h
  have hhead : x.coeff n = 1 := hd ▸ hm.coeff_natDegree
  simp [coeff_loop,coeff_X_add_C_pow,show 2 ≤ n by omega,show 1 ≤ n by omega,
    show n ≠ 2 by omega,show n ≠ 0 by omega,hhead,a_eq (by omega) hm hd h,
    show n+2-n=2 by omega] at hc
  rw [Nat.choose_symm_add (a:=n) (b:=2)] at hc
  unfold b
  linarith only [hc]

private theorem expansion {x : ℝ[X]} {n : ℕ} (hm : x.Monic) (hd : x.natDegree = n) :
    x = X^n + ∑ k ∈ Finset.range n, C (x.coeff k)*X^k := by
  conv_lhs => rw [x.as_sum_range_C_mul_X_pow]
  rw [hd,Finset.sum_range_succ,← hd,hm.coeff_natDegree]
  simp [hd,add_comm]

private theorem pos_q₀ {n : ℕ} {θ : ℝ} (hθ : criticalAngle n < θ) (hπ : θ < Real.pi/2) :
    0 < q₀ n θ := by
  have hε := powerLoopShift_pos hθ hπ
  have hy := powerLoopNumerator_pos (n:=n) ((criticalAngle_pos n).trans hθ) hπ
  unfold q₀
  positivity

private theorem pos_δ {n : ℕ} {θ : ℝ} (hθ : criticalAngle n < θ) (hπ : θ < Real.pi/2) :
    0 < Real.cos θ := Real.cos_pos_of_mem_Ioo
  ⟨by linarith [(criticalAngle_pos n).trans hθ,Real.pi_pos],hπ⟩

private theorem pos_q₁ {n : ℕ} {θ : ℝ} (hθ : criticalAngle n < θ) (hπ : θ < Real.pi/2) :
    0 < q₁ n θ := by
  have hd := pos_δ hθ hπ
  have hε := powerLoopShift_pos hθ hπ
  have hq := pos_q₀ hθ hπ
  unfold q₁
  positivity

private theorem q₀_cont {n : ℕ} (hn : 0 < n) : ContinuousAt (q₀ n) (criticalAngle n) :=
  (powerLoopNumerator_continuousAt hn).add ((powerLoopShift_continuousAt hn).pow (n+2))

private theorem q₁_cont {n : ℕ} (hn : 0 < n) : ContinuousAt (q₁ n) (criticalAngle n) := by
  have he : ContinuousAt (fun θ => powerLoopShift n θ^(n+1)) (criticalAngle n) :=
    (powerLoopShift_continuousAt hn).pow (n+1)
  exact ((continuousAt_const.mul Real.continuous_cos.continuousAt).mul (q₀_cont hn)).add
    (continuousAt_const.mul he)

private theorem a_cont {n : ℕ} (hn : 0 < n) : ContinuousAt (a n) (criticalAngle n) :=
  (continuousAt_const.mul Real.continuous_cos.continuousAt).add
    (continuousAt_const.mul (powerLoopShift_continuousAt hn))

private theorem b_cont {n : ℕ} (hn : 0 < n) : ContinuousAt (b n) (criticalAngle n) := by
  have he : ContinuousAt (fun θ => powerLoopShift n θ^2) (criticalAngle n) :=
    (powerLoopShift_continuousAt hn).pow 2
  exact (((continuousAt_const.mul Real.continuous_cos.continuousAt).mul (a_cont hn)).sub
    continuousAt_const).add (continuousAt_const.mul he)

private theorem a_limit (n : ℕ) : a n (criticalAngle n) = 2*δₙ n := by
  unfold a
  rw [powerLoopShift_at_critical]
  simp [δₙ,criticalAngle]

private theorem b_limit (n : ℕ) : b n (criticalAngle n) = 4*(δₙ n)^2-1 := by
  unfold b
  rw [a_limit,powerLoopShift_at_critical]
  simp only [zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero]
  change 2*δₙ n*(2*δₙ n)-1 = 4*(δₙ n)^2-1
  ring

private theorem q₀_limit {n : ℕ} (hn : 0 < n) :
    q₀ n (criticalAngle n) = 1/(2*Real.sin (criticalAngle n)) := by
  simp [q₀,powerLoopShift_at_critical,powerLoopNumerator_at_critical hn]

private theorem q₀_critical_pos {n : ℕ} (hn : 0 < n) : 0 < q₀ n (criticalAngle n) := by
  rw [q₀_limit hn]
  have h := Real.sin_pos_of_pos_of_lt_pi (criticalAngle_pos n)
    (by linarith [criticalAngle_lt_half_pi hn,Real.pi_pos])
  positivity

private theorem q₁_limit (n : ℕ) :
    q₁ n (criticalAngle n) = 2*δₙ n*q₀ n (criticalAngle n) := by
  unfold q₁
  rw [powerLoopShift_at_critical]
  simp [δₙ,criticalAngle]

private theorem b_limit_gt_one {n : ℕ} (hn : 2 ≤ n) :
    1 < b n (criticalAngle n) := by
  rw [b_limit]
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hθ : criticalAngle n < Real.pi/4 := by
    unfold criticalAngle
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [Real.pi_pos,mul_nonneg (sub_nonneg.mpr hnR) Real.pi_pos.le]
  have hcos : Real.cos (Real.pi/4) < δₙ n :=
    Real.strictAntiOn_cos ⟨(criticalAngle_pos n).le,by linarith [criticalAngle_lt_half_pi (show 0 < n by omega),Real.pi_pos]⟩
      ⟨by positivity,by linarith [Real.pi_pos]⟩ hθ
  rw [Real.cos_pi_div_four] at hcos
  have hpos := mul_pos (sub_pos.mpr hcos) (show 0 < δₙ n+Real.sqrt 2/2 by
    have := delta_pos (show 0 < n by omega)
    positivity)
  nlinarith only [hpos,Real.sq_sqrt (by norm_num : 0 ≤ (2:ℝ))]

private theorem a_pos {n : ℕ} {θ : ℝ} (hθ : criticalAngle n < θ) (hπ : θ < Real.pi/2) :
    0 < a n θ := by
  have hd := pos_δ hθ hπ
  have he := powerLoopShift_pos hθ hπ
  unfold a
  positivity

private theorem mu_cubic_at_critical :
    q₀ 3 (criticalAngle 3) < a 3 (criticalAngle 3)*b 3 (criticalAngle 3) := by
  have hn : 0 < (3:ℕ) := by decide
  have hv : criticalAngle 3 = Real.pi/8 := by norm_num [criticalAngle]
  have hs : 0 < Real.sin (criticalAngle 3) := Real.sin_pos_of_pos_of_lt_pi
    (criticalAngle_pos 3) (by linarith [criticalAngle_lt_half_pi hn,Real.pi_pos])
  have hsin : 2*Real.sin (criticalAngle 3)*δₙ 3 = Real.sqrt 2/2 := by
    change 2*Real.sin (criticalAngle 3)*Real.cos (criticalAngle 3) = _
    rw [← Real.sin_two_mul, hv, show 2*(Real.pi/8)=Real.pi/4 by ring,Real.sin_pi_div_four]
  have hsqrt : 1 < Real.sqrt 2 := by
    have hp := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    have hn := Real.sqrt_nonneg (2:ℝ)
    by_contra! hh
    nlinarith only [hp,mul_nonneg (sub_nonneg.mpr hh) (show 0 ≤ Real.sqrt 2+1 by positivity)]
  have hb := b_limit_gt_one (show 2 ≤ (3:ℕ) by decide)
  rw [q₀_limit hn, a_limit, div_lt_iff₀ (by positivity)]
  calc
    1 < Real.sqrt 2*b 3 (criticalAngle 3) := by
      have hmul := mul_lt_mul_of_pos_right hsqrt (zero_lt_one.trans hb)
      rw [one_mul] at hmul
      exact hb.trans hmul
    _ = 2*δₙ 3*b 3 (criticalAngle 3)*(2*Real.sin (criticalAngle 3)) := by
      linear_combination -2*b 3 (criticalAngle 3)*hsin

private noncomputable def mu_quartic (θ : ℝ) :=
  6*(b 4 θ*q₁ 4 θ-a 4 θ*q₀ 4 θ)-20*powerLoopShift 4 θ^2*q₁ 4 θ+
    6*a 4 θ*powerLoopShift 4 θ^4

private theorem mu_quartic_at_critical : 0 < mu_quartic (criticalAngle 4) := by
  have hn : 0 < (4:ℕ) := by decide
  have hp := mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 12) (delta_pos hn))
    (q₀_critical_pos hn)) (sub_pos.mpr (b_limit_gt_one (show 2 ≤ (4:ℕ) by decide)))
  unfold mu_quartic
  rw [q₁_limit,a_limit,powerLoopShift_at_critical]
  norm_num
  nlinarith only [hp]

private theorem sharp_of_eventual_stability {n : ℕ} (hn : 0 < n)
    (h : ∀ᶠ θ in 𝓝 (criticalAngle n), criticalAngle n < θ → θ < Real.pi/2 →
      ∀ x : ℝ[X], x.Monic → x.natDegree = n →
        loop (Real.cos θ) x (powerLoopNumerator n θ) = (X+C (powerLoopShift n θ))^(n+2) →
        StrictlyStable x) : δₙ_star n = δₙ n := by
  apply le_antisymm (conjecture3_sup hn)
  let l := 𝓝[Set.Ioi (criticalAngle n)] (criticalAngle n)
  have : NeBot l := mem_closure_iff_nhdsWithin_neBot.mp
    (show criticalAngle n ∈ closure (Set.Ioi (criticalAngle n)) by
      rw [closure_Ioi]
      exact Set.self_mem_Ici)
  have hθ : ∀ᶠ θ in l, criticalAngle n < θ := eventually_mem_nhdsWithin
  have hπ : ∀ᶠ θ in l, θ < Real.pi/2 :=
    (gt_mem_nhds (criticalAngle_lt_half_pi hn)).filter_mono nhdsWithin_le_nhds
  have hmem : ∀ᶠ θ in l, Real.cos θ ∈ bistableParameters n 0 := by
    filter_upwards [h.filter_mono (nhdsWithin_le_nhds (s:=Set.Ioi (criticalAngle n))),hθ,hπ] with θ hθ' hlow hu
    have hlo := (criticalAngle_pos n).trans hlow
    obtain ⟨x,hm,hd,hx⟩ := powerLoop_factor hn hlo hu
    refine ⟨pos_δ hlow hu,bistable_zero_iff.mpr ⟨x,powerLoopNumerator n θ,hd,
      (powerLoopNumerator_pos hlo hu).ne',hθ' hlow hu x hm hd hx,?_⟩⟩
    rw [hx]
    exact stable_powerLoop _ (powerLoopShift_pos hlow hu)
  have hbdd : BddAbove (bistableParameters n 0) := ⟨1,fun _ hx => (bistable_lt_one hx.2).le⟩
  change Real.cos (criticalAngle n) ≤ sSup (bistableParameters n 0)
  exact le_of_tendsto (Real.continuous_cos.continuousAt.continuousWithinAt (s:=Set.Ioi _))
    (hmem.mono (fun _ hh => le_csSup hbdd hh))

/-- The cosine bound is sharp for each denominator degree from one through four. -/
theorem conjecture3_sharp_of_le_four {n : ℕ} (hn : 0 < n) (h4 : n ≤ 4) :
    δₙ_star n = δₙ n := by
  apply sharp_of_eventual_stability hn
  interval_cases n
  · apply Filter.Eventually.of_forall
    intro θ hθ hπ x hm hd h
    have he := expansion hm hd
    norm_num [Finset.sum_range_succ,q₀_eq h] at he
    rw [he]
    exact stable_linear _ (pos_q₀ hθ hπ)
  · apply Filter.Eventually.of_forall
    intro θ hθ hπ x hm hd h
    have he := expansion hm hd
    norm_num [Finset.sum_range_succ,q₀_eq h,q₁_eq h] at he
    rw [he]
    convert stable_quadratic _ _ (pos_q₁ hθ hπ) (pos_q₀ hθ hπ) using 1; ring
  · have hbc := ((a_cont hn).mul (b_cont hn)).sub (q₀_cont hn)
    have hp : 0 < a 3 (criticalAngle 3)*b 3 (criticalAngle 3)-q₀ 3 (criticalAngle 3) :=
      sub_pos.mpr mu_cubic_at_critical
    have hb := (b_cont hn).tendsto.eventually
      (lt_mem_nhds (zero_lt_one.trans (b_limit_gt_one (show 2 ≤ (3:ℕ) by decide))))
    filter_upwards [hbc.tendsto.eventually (lt_mem_nhds hp),hb] with θ hbc' hb' 
    intro hθ hπ x hm hd h
    have he := expansion hm hd
    have ha := a_eq (by decide : 2 ≤ (3:ℕ)) hm hd h
    have hb := b_eq (by decide : 3 ≤ (3:ℕ)) hm hd h
    norm_num at ha hb
    norm_num [Finset.sum_range_succ,q₀_eq h,ha,hb] at he
    rw [he]
    change 0 < a 3 θ*b 3 θ-q₀ 3 θ at hbc'
    convert stable_cubic _ _ _ (a_pos hθ hπ) hb' (pos_q₀ hθ hπ) (sub_pos.mp hbc') using 1; ring
  · have hs := powerLoopShift_continuousAt hn
    have hmu : ContinuousAt mu_quartic (criticalAngle 4) :=
      ((continuousAt_const.mul (((b_cont hn).mul (q₁_cont hn)).sub
        ((a_cont hn).mul (q₀_cont hn)))).sub
          ((continuousAt_const.mul (hs.pow 2)).mul (q₁_cont hn))).add
            ((continuousAt_const.mul (a_cont hn)).mul (hs.pow 4))
    have hb := (b_cont hn).tendsto.eventually
      (lt_mem_nhds (zero_lt_one.trans (b_limit_gt_one (show 2 ≤ (4:ℕ) by decide))))
    filter_upwards [hmu.tendsto.eventually (lt_mem_nhds mu_quartic_at_critical),hb] with θ hmu' hb'
    intro hθ hπ x hm hd h
    have he := expansion hm hd
    have ha := a_eq (by decide : 2 ≤ (4:ℕ)) hm hd h
    have hb := b_eq (by decide : 3 ≤ (4:ℕ)) hm hd h
    norm_num at ha hb
    norm_num [Finset.sum_range_succ,q₀_eq h,q₁_eq h,ha,hb] at he
    have h3 := congrArg (fun p : ℝ[X] => p.coeff 3) h
    have hchoose : Nat.choose 6 3 = 20 := by decide
    norm_num [coeff_loop,coeff_X_add_C_pow,q₁_eq h,ha,hb,hchoose] at h3
    have hdet : a 4 θ*b 4 θ*q₁ 4 θ-(q₁ 4 θ)^2-(a 4 θ)^2*q₀ 4 θ =
        powerLoopShift 4 θ*mu_quartic θ := by
      have haa : a 4 θ = 2*Real.cos θ+6*powerLoopShift 4 θ := by norm_num [a]
      have hc : q₁ 4 θ = 2*Real.cos θ*q₀ 4 θ+6*powerLoopShift 4 θ^5 := by norm_num [q₁]
      unfold mu_quartic
      linear_combination -q₁ 4 θ*h3 + a 4 θ*hc +
        (b 4 θ*q₁ 4 θ-a 4 θ*q₀ 4 θ)*haa
    rw [he]
    convert stable_quartic _ _ _ _ (a_pos hθ hπ) hb' (pos_q₁ hθ hπ) (pos_q₀ hθ hπ)
      (by rw [hdet]; exact mul_pos (powerLoopShift_pos hθ hπ) hmu') using 1; ring

#print axioms conjecture3_sharp_of_le_four
end BelgianChocolate.Conjectures

