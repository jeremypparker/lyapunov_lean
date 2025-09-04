import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

structure Observable (n : ℕ) (k : ℕ) where
  (func : EuclideanSpace ℝ (Fin n) → ℝ)
  (contDiff : ContDiff ℝ k func)

instance {n : ℕ} {k : ℕ} : CoeFun (Observable n k) (fun _ => EuclideanSpace ℝ (Fin n) → ℝ) :=
  ⟨Observable.func⟩

noncomputable def Observable.add {n k : ℕ} (f g : Observable n k) : Observable n k :=
  let sum_func := fun x => f.func x + g.func x
  have sum_contDiff : ContDiff ℝ k sum_func := ContDiff.add f.contDiff g.contDiff
  Observable.mk sum_func sum_contDiff

noncomputable instance {n k : ℕ} : Add (Observable n k) :=
  ⟨Observable.add⟩

theorem observable_integrable {n : ℕ} {k : ℕ} (Φ : Observable n k)
  (x : ℝ → EuclideanSpace ℝ (Fin n)) (hx : Differentiable ℝ x)
  : ∀ T : ℝ, IntervalIntegrable (fun t ↦ Φ (x t)) MeasureTheory.volume 0 T := by
    intro T
    exact Continuous.intervalIntegrable
      (Φ.contDiff.continuous.comp hx.continuous) 0 T

noncomputable def LieDerivative
    {n : ℕ}
    {k : ℕ} [Fact (0 < k)]
    (V : Observable n k)
    (f : C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n)))
  : Observable n 0 :=
    let g := fun x => fderiv ℝ V x (f x)
    have hk : ContDiff ℝ 0 g := by
      have := V.contDiff.continuous_fderiv (by
        exact_mod_cast Nat.one_le_of_lt (Fact.out : 0 < k))
      subst g
      simp
      fun_prop

    Observable.mk g hk

theorem time_deriv_eq_lie_deriv
    {n : ℕ}
    (V : Observable n 1)
    (f : C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n)))
    (x : ℝ → EuclideanSpace ℝ (Fin n)) (hx : ∀ t, HasDerivAt x (f (x t)) t)
  : deriv  (V ∘ x) = (LieDerivative V f) ∘ x
  := by
    have h : ∀ t, HasDerivAt (V ∘ x) (fderiv ℝ V (x t) (f (x t))) t := by
      intro t
      convert (HasFDerivAt.comp t
        (V.contDiff.differentiable le_rfl (x t)).hasFDerivAt (hx t)).hasDerivAt
      simp
    rw [LieDerivative]
    simp
    apply deriv_eq
    exact h

lemma hasderivat_diffable
    {n : ℕ}
    {f : ℝ → EuclideanSpace ℝ (Fin n)}
    {f' : ℝ → EuclideanSpace ℝ (Fin n)}
    (h : ∀ t, HasDerivAt f (f' t) t)
    : Differentiable ℝ f := by
      rw [Differentiable]
      intro t
      exact (h t).differentiableAt
