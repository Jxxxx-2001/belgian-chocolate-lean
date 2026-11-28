import BoundaryLimit

open Polynomial Filter Topology
namespace BelgianChocolate.Conjectures
open ControlWitness (StrictlyStable)
set_option maxHeartbeats 1000000

noncomputable def powerLoopPhase (n : ℕ) (θ : ℝ) := (θ+Real.pi/2)/((n:ℝ)+2)

noncomputable def powerLoopShift (n : ℕ) (θ : ℝ) :=
  Real.sin (θ-powerLoopPhase n θ)/Real.sin (powerLoopPhase n θ)

noncomputable def powerLoopNumerator (n : ℕ) (θ : ℝ) :=
  (Real.sin θ/Real.sin (powerLoopPhase n θ))^(n+2)/(2*Real.sin θ)

private theorem phi_bounds {n : ℕ} {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi/2) :
    0 < powerLoopPhase n θ ∧ powerLoopPhase n θ < Real.pi := by
  unfold powerLoopPhase
  constructor
  · positivity
  · rw [div_lt_iff₀ (by positivity)]
    nlinarith [Real.pi_pos,show 0 ≤ (n:ℝ)*Real.pi by positivity]

private theorem phi_at_critical (n : ℕ) :
    powerLoopPhase n (criticalAngle n) = criticalAngle n := by
  unfold powerLoopPhase
  apply (div_eq_iff (by positivity)).mpr
  linear_combination -(criticalAngle_mul n)

theorem powerLoopShift_at_critical (n : ℕ) : powerLoopShift n (criticalAngle n) = 0 := by
  simp [powerLoopShift,phi_at_critical]

theorem powerLoopNumerator_at_critical {n : ℕ} (hn : 0 < n) :
    powerLoopNumerator n (criticalAngle n) = 1/(2*Real.sin (criticalAngle n)) := by
  have h : 0 < Real.sin (criticalAngle n) := Real.sin_pos_of_pos_of_lt_pi
    (criticalAngle_pos n) (by linarith [criticalAngle_lt_half_pi hn,Real.pi_pos])
  simp [powerLoopNumerator,phi_at_critical,h.ne']

theorem powerLoopShift_continuousAt {n : ℕ} (hn : 0 < n) :
    ContinuousAt (powerLoopShift n) (criticalAngle n) := by
  unfold powerLoopShift
  apply ContinuousAt.div
  · unfold powerLoopPhase
    fun_prop
  · unfold powerLoopPhase
    fun_prop
  · rw [phi_at_critical]
    exact (Real.sin_pos_of_pos_of_lt_pi (criticalAngle_pos n)
      (by linarith [criticalAngle_lt_half_pi hn,Real.pi_pos])).ne'

theorem powerLoopNumerator_continuousAt {n : ℕ} (hn : 0 < n) :
    ContinuousAt (powerLoopNumerator n) (criticalAngle n) := by
  have h : 0 < Real.sin (criticalAngle n) := Real.sin_pos_of_pos_of_lt_pi
    (criticalAngle_pos n) (by linarith [criticalAngle_lt_half_pi hn,Real.pi_pos])
  have hsφ : Continuous (fun θ => Real.sin (powerLoopPhase n θ)) := by
    unfold powerLoopPhase
    fun_prop
  have hne : Real.sin (powerLoopPhase n (criticalAngle n)) ≠ 0 := by
    rw [phi_at_critical]
    exact h.ne'
  have ht : ContinuousAt Real.sin (criticalAngle n) := Real.continuous_sin.continuousAt
  exact ((ht.div hsφ.continuousAt hne).pow (n+2)).div
    (continuousAt_const.mul ht) (mul_pos (by norm_num : (0:ℝ)<2) h).ne'

theorem powerLoopShift_pos {n : ℕ} {θ : ℝ} (hθ : criticalAngle n < θ) (hθπ : θ < Real.pi/2) :
    0 < powerLoopShift n θ := by
  have hθ0 : 0 < θ := (criticalAngle_pos n).trans hθ
  obtain ⟨hφ0,hφπ⟩ := phi_bounds (n:=n) hθ0 hθπ
  have hp : powerLoopPhase n θ < θ := by
    unfold powerLoopPhase
    rw [div_lt_iff₀ (by positivity)]
    nlinarith only [criticalAngle_mul n,
      mul_pos (show 0 < (n:ℝ)+1 by positivity) (sub_pos.mpr hθ)]
  exact div_pos (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hp) (by linarith [Real.pi_pos]))
    (Real.sin_pos_of_pos_of_lt_pi hφ0 hφπ)

theorem powerLoopNumerator_pos {n : ℕ} {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi/2) :
    0 < powerLoopNumerator n θ := by
  obtain ⟨hφ0,hφπ⟩ := phi_bounds (n:=n) hθ0 hθπ
  have hp := Real.sin_pos_of_pos_of_lt_pi hφ0 hφπ
  have ht := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  unfold powerLoopNumerator
  positivity

/-- The constant numerator and shift make the prescribed power divisible
by the plant after subtracting the numerator term. -/
theorem powerLoop_factor {n : ℕ} (hn : 0 < n) {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi/2) :
    ∃ x : ℝ[X], x.Monic ∧ x.natDegree = n ∧
      loop (Real.cos θ) x (powerLoopNumerator n θ) = (X+C (powerLoopShift n θ))^(n+2) := by
  let φ := powerLoopPhase n θ
  let ε := powerLoopShift n θ
  let y := powerLoopNumerator n θ
  let r := Real.sin θ/Real.sin φ
  have hφ : 0 < φ ∧ φ < Real.pi := phi_bounds hθ0 hθπ
  have hps := Real.sin_pos_of_pos_of_lt_pi hφ.1 hφ.2
  have hts := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  have hid : phase θ+(ε:ℂ) = (r:ℂ)*phase φ := by
    apply Complex.ext
    · simp only [Complex.add_re,phase_re,Complex.ofReal_re,Complex.mul_re,
        Complex.ofReal_im,zero_mul,sub_zero]
      change Real.cos θ + Real.sin (θ-φ)/Real.sin φ = (Real.sin θ/Real.sin φ)*Real.cos φ
      rw [Real.sin_sub]
      field_simp [hps.ne']
      ring
    · simp only [Complex.add_im,phase_im,Complex.ofReal_im,add_zero,Complex.mul_im,
        Complex.ofReal_re,zero_mul]
      dsimp [r]
      exact (div_mul_cancel₀ _ hps.ne').symm
  have hφm : ((↑(n+2) : ℝ))*φ = θ+Real.pi/2 := by
    dsimp [φ,powerLoopPhase]
    push_cast
    field_simp
  have hI : phase (Real.pi/2) = Complex.I := by apply Complex.ext <;> simp
  have hθI : phase θ^2-1 = phase θ*(((2*Real.sin θ:ℝ):ℂ)*Complex.I) := by
    rw [← phase_diff]
    linear_combination phase_pair θ
  have hy : y*(2*Real.sin θ) = r^(n+2) := div_mul_cancel₀ _ (mul_pos (by norm_num) hts).ne'
  let N : ℝ[X] := (X+C ε)^(n+2)-(X^2-1)*C y
  have heval : aeval (phase θ) N = 0 := by
    simp only [N,map_sub,map_mul,map_add,map_pow,aeval_X,aeval_C,map_one]
    change (phase θ+(ε:ℂ))^(n+2)-(phase θ^2-1)*(y:ℂ)=0
    rw [hid,mul_pow,phase_pow,hφm,phase_add,hI,hθI]
    have hyC := congrArg Complex.ofReal hy
    rw [Complex.ofReal_mul,Complex.ofReal_pow] at hyC
    linear_combination -(phase θ*Complex.I)*hyC
  have hnorm : ‖phase θ‖ = 1 := by
    simp [phase,Complex.norm_exp,Complex.mul_re]
  have hne : (phase θ).im ≠ 0 := by simpa using hts.ne'
  have hdiv : plant (Real.cos θ) ∣ N := by
    simpa [plant,hnorm,sub_eq_add_neg,two_mul] using
      N.quadratic_dvd_of_aeval_eq_zero_im_ne_zero heval hne
  obtain ⟨x,hx⟩ := hdiv
  have hp : (X+C ε : ℝ[X]).Monic := monic_X_add_C ε
  have hpd : ((X+C ε : ℝ[X])^(n+2)).natDegree = n+2 := by
    rw [natDegree_pow,natDegree_X_add_C,mul_one]
  have hydeg : ((X^2-1)*C y : ℝ[X]).natDegree ≤ 2 := by compute_degree
  have hlt : ((X^2-1)*C y : ℝ[X]).degree < ((X+C ε)^(n+2)).degree := by
    rw [degree_eq_natDegree (hp.pow _).ne_zero,hpd]
    exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast (show
      ((X^2-1)*C y : ℝ[X]).natDegree < n+2 by omega))
  have hNm : N.Monic := (hp.pow _).sub_of_left hlt
  have hNd : N.natDegree = n+2 := by
    dsimp only [N]
    rw [natDegree_sub_eq_left_of_natDegree_lt (by omega),hpd]
  have hxm : x.Monic := (plant_monic _).of_mul_monic_left (hx ▸ hNm)
  have hxd : x.natDegree = n := by
    have h := congrArg natDegree hx
    rw [hNd,natDegree_mul (plant_monic _).ne_zero hxm.ne_zero,plant_degree] at h
    omega
  refine ⟨x,hxm,hxd,?_⟩
  change plant (Real.cos θ)*x+(X^2-1)*C y = (X+C ε)^(n+2)
  rw [← hx]
  exact sub_add_cancel _ _

theorem stable_powerLoop (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    StrictlyStable ((X+C ε)^k) := by
  rw [strictStable_iff_no_roots]
  intro z hz
  rw [map_pow]
  exact pow_ne_zero _ ((strictStable_iff_no_roots _).mp (stable_linear ε hε) z hz)

end BelgianChocolate.Conjectures

