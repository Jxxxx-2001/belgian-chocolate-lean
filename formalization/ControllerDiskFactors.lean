import SourceDiskCompetitor
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace BelgianChocolate.ControlWitness

set_option backward.isDefEq.respectTransparency false

open Complex Metric Set Filter
open scoped Topology
open BelgianChocolate.SourceDiskPaths

private theorem deriv_unit_factor {v : ℂ} {g : ℂ → ℂ}
    (hg : DifferentiableAt ℂ g v) (hzero : g v ≠ 0) :
    ∃ d, HasDerivAt (fun w => (w-v)*g w) d v ∧ d ≠ 0 := by
  refine ⟨g v,?_,hzero⟩
  have h : HasDerivAt (fun w : ℂ => w-v) 1 v := (hasDerivAt_id v).sub_const v
  simpa [Pi.mul_def] using h.mul hg.hasDerivAt

theorem marked_of_disk_factors {t : ℝ} (ht : 0 < t) (ht' : t < 1)
    (f a b : ℂ → ℂ)
    (ha : ∀ z ∈ ball (0:ℂ) 1, DifferentiableAt ℂ a z ∧ a z ≠ 0)
    (hb : ∀ z ∈ ball (0:ℂ) 1, DifferentiableAt ℂ b z ∧ b z ≠ 0)
    (hf : ∀ z ∈ ball (0:ℂ) 1, f z = z*a z)
    (hg : ∀ z ∈ ball (0:ℂ) 1, f z = 1 + (z-(t:ℂ)*I)*(z+(t:ℂ)*I)*b z) :
    MarkedCompetitor t f := by
  let u : ℂ := (t:ℂ)*I
  have hu : u ≠ 0 := mul_ne_zero (by exact_mod_cast ht.ne') I_ne_zero
  have h0 : (0:ℂ) ∈ ball 0 1 := by simp
  have hp : u ∈ ball (0:ℂ) 1 := by simpa [u,Complex.norm_real,abs_of_pos ht] using ht'
  have hm : -u ∈ ball (0:ℂ) 1 := by simpa using hp
  have ef {z : ℂ} (hz : z ∈ ball (0:ℂ) 1) :
      f =ᶠ[𝓝 z] (fun w => w*a w) := Filter.mem_of_superset (isOpen_ball.mem_nhds hz) fun w hw => hf w hw
  have eg {z : ℂ} (hz : z ∈ ball (0:ℂ) 1) :
      f =ᶠ[𝓝 z] (fun w => 1 + (w-u)*(w+u)*b w) :=
    Filter.mem_of_superset (isOpen_ball.mem_nhds hz) fun w hw => hg w hw
  have hdiff {z : ℂ} (hz : z ∈ ball (0:ℂ) 1) : DifferentiableAt ℂ f z :=
    (differentiableAt_id.mul (ha z hz).1).congr_of_eventuallyEq (ef hz)
  refine ⟨fun z hz => (hdiff hz).differentiableWithinAt,?_,?_,?_,?_,?_,?_,?_⟩
  · intro z hz
    obtain ⟨hz,hz0,hzp,hzm⟩ := hz
    have hball : z ∈ ball (0:ℂ) 1 := by simpa using hz
    have f0 : f z ≠ 0 := by rw [hf z hball]; exact mul_ne_zero hz0 (ha z hball).2
    have fp : z-u ≠ 0 := sub_ne_zero.mpr hzp
    have fm : z+u ≠ 0 := by
      intro h
      apply hzm
      rw [neg_mul]
      exact eq_neg_of_add_eq_zero_left h
    have f1 : f z ≠ 1 := by
      rw [hg z hball]
      intro e
      exact (mul_ne_zero (mul_ne_zero fp fm) (hb z hball).2) (by linear_combination e)
    simpa [Set.mem_insert_iff,Set.mem_singleton_iff] using And.intro f0 f1
  · simp [hf 0 h0]
  · simp [hg u hp,u]
  · rw [neg_mul]
    simp [hg (-u) hm,u]
  · refine ⟨_,?_,(ha 0 h0).2⟩
    apply HasDerivAt.congr_of_eventuallyEq _ (ef h0)
    simpa [Pi.mul_def] using (hasDerivAt_id (0:ℂ)).mul (ha 0 h0).1.hasDerivAt
  · obtain ⟨d,hd,hdn⟩ := deriv_unit_factor
      ((differentiableAt_id.add_const u).mul (hb u hp).1)
      (mul_ne_zero (by simpa [two_mul] using (mul_ne_zero (two_ne_zero: (2:ℂ) ≠ 0) hu)) (hb u hp).2)
    refine ⟨d,?_,hdn⟩
    apply HasDerivAt.congr_of_eventuallyEq _ (eg hp)
    have hh : HasDerivAt (fun w => 1 + (w-u)*((w+u)*b w)) (0+d) u :=
      HasDerivAt.add (hasDerivAt_const u (1:ℂ)) hd
    simpa [Pi.add_def,Pi.mul_def,mul_assoc] using hh
  · rw [neg_mul]
    obtain ⟨d,hd,hdn⟩ := deriv_unit_factor
      ((differentiableAt_id.sub_const u).mul (hb (-u) hm).1)
      (mul_ne_zero (by intro e; change -u-u=0 at e; apply hu; linear_combination -(1/2:ℂ)*e) (hb (-u) hm).2)
    refine ⟨d,?_,hdn⟩
    apply HasDerivAt.congr_of_eventuallyEq _ (eg hm)
    have hh : HasDerivAt (fun w => 1 + (w- -u)*((w-u)*b w)) (0+d) (-u) :=
      HasDerivAt.add (hasDerivAt_const (-u) (1:ℂ)) hd
    simpa [Pi.add_def,Pi.mul_def,sub_neg_eq_add,mul_assoc,mul_left_comm,mul_comm] using hh

end BelgianChocolate.ControlWitness

