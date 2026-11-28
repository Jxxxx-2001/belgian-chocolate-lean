import BoundaryLimit
import BoundaryExtraRoot

open Filter Topology Polynomial
namespace BelgianChocolate.Conjectures
open ControlWitness (StrictlyStable)
set_option maxHeartbeats 1100000

private theorem plant_eval_formula (δ : ℝ) (z : ℂ) :
    aeval z (plant δ) = z^2-((2*δ:ℝ):ℂ)*z+1 := by
  simp only [plant,map_add,map_sub,map_mul,map_pow,aeval_X,aeval_C,map_one]
  rw [← map_mul (algebraMap ℝ ℂ)]
  rfl

/-- In every degree at least five the constant-numerator supremum is strictly
below the conjectured upper bound. -/
theorem conjecture3_strict_of_five_le {n : ℕ} (hn : 5 ≤ n) :
    δₙ_star n < δₙ n := by
  have hn0 : 0 < n := by omega
  by_contra! hbad
  have heq : δₙ_star n = δₙ n := le_antisymm (conjecture3_sup hn0) hbad
  have hnon : (bistableParameters n 0).Nonempty := by
    by_contra! h
    rw [δₙ_star,h,Real.sSup_empty] at heq
    exact (delta_pos hn0).ne' heq.symm
  have hbdd : BddAbove (bistableParameters n 0) :=
    ⟨1,fun _ hm => (bistable_lt_one hm.2).le⟩
  obtain ⟨δ,_,ht,hmem⟩ := exists_seq_tendsto_sSup hnon hbdd
  change Tendsto δ atTop (𝓝 (δₙ_star n)) at ht
  rw [heq] at ht
  have hxys (j : ℕ) := monic_constant_witness (bistable_zero_iff.mp (hmem j).2)
  choose x y hm hd hy hx hz using hxys
  let Z := fun j => loop (δ j) (x j) (y j)
  let N := fun j => Z j - (X^2-1)*C (y j)
  let c := 1/(2*Real.sin (criticalAngle n))
  let Q : ℝ[X] := X^(n+2)-(X^2-1)*C c
  have hc : 0 < c := by
    dsimp [c]
    apply one_div_pos.mpr
    exact mul_pos (by norm_num) (Real.sin_pos_of_pos_of_lt_pi
      (criticalAngle_pos n) (by linarith [criticalAngle_lt_half_pi hn0,Real.pi_pos]))
  obtain ⟨hZt,hyt⟩ := loop_coeff_boundary hn0 (fun j => (hmem j).1)
    (fun j => bistable_lt_one (hmem j).2) ht hm hd hz
  have hN (j : ℕ) : N j = plant (δ j)*x j := by simp [N,Z,loop]
  have hNm (j : ℕ) : (N j).Monic := by rw [hN]; exact (plant_monic _).mul (hm j)
  have hNd (j : ℕ) : (N j).natDegree = n+2 := by
    rw [hN,natDegree_mul (plant_monic _).ne_zero (hm j).ne_zero,plant_degree,hd j,add_comm]
  have hdeg : ((X^2-1)*C c : ℝ[X]).natDegree ≤ 2 := by compute_degree
  have hQd : Q.natDegree = n+2 := by
    dsimp [Q]
    rw [natDegree_sub_eq_left_of_natDegree_lt,natDegree_X_pow]
    rw [natDegree_X_pow]
    omega
  have hQm : Q.Monic := (monic_X_pow _).sub_of_left (by
    rw [degree_X_pow]
    exact lt_of_le_of_lt degree_le_natDegree
      (by exact_mod_cast (show ((X^2-1)*C c : ℝ[X]).natDegree < n+2 by omega)))
  have hcoef (k : ℕ) : Tendsto (fun j => (N j).coeff k) atTop (𝓝 (Q.coeff k)) := by
    simp only [N,Q,coeff_sub,coeff_mul_C]
    exact (hZt k).sub (tendsto_const_nhds.mul hyt)
  obtain ⟨z,hzr,hzn,hplant⟩ := boundary_numerator_extra_root (m:=n+2) (by omega) hc
  rw [Nat.add_sub_cancel] at hplant
  have hzQ : aeval z Q = 0 := by
    simp only [Q,map_sub,map_mul,map_pow,map_one,aeval_X,aeval_C]
    change z^(n+2)-(z^2-1)*(c:ℂ)=0
    rw [hzn]
    ring
  let F : ℝ × ℂ → ℂ := fun p => p.2^2-((2*p.1:ℝ):ℂ)*p.2+1
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hpos : IsOpen {p : ℝ × ℂ | 0 < p.2.re} :=
    (isOpen_Ioi (a:=(0:ℝ))).preimage (Complex.continuous_re.comp continuous_snd)
  have hnz : IsOpen {p : ℝ × ℂ | F p ≠ 0} :=
    isOpen_ne_fun hF (continuous_const (y:=(0:ℂ)))
  have hOp : IsOpen {p : ℝ × ℂ | 0 < p.2.re ∧ F p ≠ 0} := hpos.inter hnz
  have hcenter : (δₙ n,z) ∈ {p : ℝ × ℂ | 0 < p.2.re ∧ F p ≠ 0} := by
    refine ⟨hzr,?_⟩
    convert hplant using 1
    exact (plant_eval_formula _ _).symm
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hOp (δₙ n,z) hcenter
  have hroot := eventually_near_aroot (show 0 < n+2 by omega) hNm hQm hNd hQd hcoef hzQ hr
  have hclose := Metric.tendsto_nhds.mp ht r hr
  obtain ⟨j,hj⟩ := (hroot.and hclose).exists
  obtain ⟨⟨w,hw,hzw⟩,hj⟩ := hj
  have hmemb : (δ j,w) ∈ Metric.ball (δₙ n,z) r := by
    rw [Metric.mem_ball,Prod.dist_eq,max_lt_iff]
    exact ⟨hj,by rwa [dist_comm]⟩
  have hw' := hball hmemb
  rw [hN,map_mul] at hw
  rcases mul_eq_zero.mp hw with hp | hp
  · exact hw'.2 (by simpa only [F,plant_eval_formula] using hp)
  · exact (not_lt_of_ge hw'.1.le) ((hx j).2 w hp)

#print axioms conjecture3_strict_of_five_le
end BelgianChocolate.Conjectures

