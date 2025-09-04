import LyapunovLean.Common

/-- Suppose we have a solution to a system dx/dt = f(x) defined for all time,
    and a Lyapunov function V such that
    f⬝∇ V ≤ 0 and V ≥ x^2.
    Then the trajectory is bounded forwards in time. -/
theorem Lyapunov
   {n : ℕ}
   (f : C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n)))
   (V : Observable n 1)
   (hV_inequality_1 : ∀ x, LieDerivative V f x ≤ 0) (hV_inequality_2 : ∀ x, V x ≥ ‖x‖ ^ 2)
   (x : ℝ → EuclideanSpace ℝ (Fin n)) (hx : ∀ t, HasDerivAt x (f (x t)) t) :
   ∃ C, ∀ t > 0, ‖x t‖^2 ≤ C := by

  have h_integrable (T : ℝ) : IntervalIntegrable (deriv  (V ∘ x)) MeasureTheory.volume 0 T := by
    have hxcont := (continuous_iff_continuousAt.mpr (fun t:ℝ => (hx t).continuousAt))

    rw [time_deriv_eq_lie_deriv V f x hx]
    exact observable_integrable (LieDerivative V f) x (hasderivat_diffable hx) T

  have h_V_decreasing : ∀ t, -(deriv (V ∘ x) t) ≥ 0 := by
    intro t
    rw [time_deriv_eq_lie_deriv V f x hx, Function.comp_apply]
    simp only [ge_iff_le, Left.nonneg_neg_iff]
    exact hV_inequality_1 (x t)

  let C := V (x 0)
  use C
  intro T ht

  have int_inequality : ∫ t in 0..T, -(deriv (V ∘ x) t) ≥ 0 :=
    intervalIntegral.integral_nonneg_of_forall ht.le h_V_decreasing

  have h_diff : ∀ t ∈ Set.uIcc 0 T, DifferentiableAt ℝ (V ∘ x) t := by
    intro t ht
    exact DifferentiableAt.comp t
      (V.contDiff.differentiable le_rfl).differentiableAt
      (hx t).differentiableAt

  calc
    ‖x T‖ ^ 2 ≤ V (x T) := by grw [hV_inequality_2 (x T)]
    _ = V (x 0) + ((V ∘ x) T - (V ∘ x) 0) := by
      simp only [Function.comp_apply, add_sub_cancel]
    _ = V (x 0) +∫ t in 0..T, (deriv (V ∘ x) t) := by
      rw[intervalIntegral.integral_deriv_eq_sub h_diff (h_integrable T)]
    _ = V (x 0) -∫ t in 0..T, -(deriv (V ∘ x) t) := by
      rw [intervalIntegral.integral_neg,sub_neg_eq_add]
    _ = C -∫ t in 0..T, -(deriv (V ∘ x) t) := by ring
  exact sub_le_self _ int_inequality
