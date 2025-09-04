import LyapunovLean.Common
import Canonical
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Instances.EReal.Lemmas

open Topology Filter

noncomputable def TimeAverage
    {n : ℕ}
    (Φ : Observable n 0)
    (x : ℝ → EuclideanSpace ℝ (Fin n)) : EReal
  := limsup (fun (T : ℝ) => ↑(T⁻¹ * (∫ t in 0..T, Φ (x t)))) atTop

lemma f_le_sup_compact {n : ℕ} {B : Set (EuclideanSpace ℝ (Fin n))} {x : EuclideanSpace ℝ (Fin n)}
  (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf_cont : Continuous f) (hB_compact : IsCompact B)
  (hx : x ∈ B) :
  f x ≤ sSup (f '' B) := by
    apply le_csSup
    · exact (hB_compact.image hf_cont).isBounded.bddAbove
    · exact Set.mem_image_of_mem f hx

lemma limsup_add_vanishes {f g : ℝ → EReal} (hg : Tendsto g atTop (𝓝 0)) :
  limsup (f + g) atTop = limsup f atTop := by
  have h1 : limsup g atTop ≠ ⊤ := by
    rw [hg.limsup_eq]
    exact EReal.zero_ne_top
  have h2 : limsup g atTop ≠ ⊥ := by
    rw [hg.limsup_eq]
    exact EReal.zero_ne_bot

  apply le_antisymm
  · grw [EReal.limsup_add_le (Or.inr h1) (Or.inr h2)]
    rw [hg.limsup_eq]
    simp only [add_zero, le_refl]
  · grw [←EReal.le_limsup_add]
    rw [hg.liminf_eq]
    simp only [add_zero, le_refl]

theorem lie_deriv_tendsto_zero
    {n : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin n))}
    (V : Observable n 1)
    (f : C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n)))
    (x : ℝ → EuclideanSpace ℝ (Fin n)) (hx : ∀ t, HasDerivAt x (f (x t)) t)
    (hxb : ∀ t, x t ∈ B) (hB : IsCompact B)
  : Tendsto (fun T ↦ T⁻¹ * ∫ (t : ℝ) in 0..T, (LieDerivative V f).func (x t)) atTop (𝓝 0)
  := by
  have h_integrable (T : ℝ) : IntervalIntegrable (deriv  (V ∘ x)) MeasureTheory.volume 0 T := by
      have hxcont := (continuous_iff_continuousAt.mpr (fun t:ℝ => (hx t).continuousAt))
      have h2 : ∀ T, IntervalIntegrable ((LieDerivative V f) ∘ x) MeasureTheory.volume 0 T := by
        intro T
        have hcont : Continuous ((LieDerivative V f) ∘ x) :=
          Continuous.comp (LieDerivative V f).contDiff.continuous hxcont
        exact Continuous.intervalIntegrable hcont 0 T

      rw [time_deriv_eq_lie_deriv V f x hx]
      apply h2
  have h_diff (T : ℝ) : ∀ t ∈ Set.uIcc 0 T, DifferentiableAt ℝ (V ∘ x) t := by
    intro t ht
    exact DifferentiableAt.comp t
      (V.contDiff.differentiable le_rfl).differentiableAt
      (hx t).differentiableAt

  have hftc : (fun T ↦ T⁻¹ * ∫ (t : ℝ) in 0..T, (deriv  (V ∘ x)) t)
      = fun T ↦ T⁻¹ * ((V∘x) T - (V∘x) 0) := by
    refine funext ?_
    intro T
    rw [intervalIntegral.integral_deriv_eq_sub (h_diff T) (h_integrable T)]

  let Vmax := sSup ((fun x => |V x|) '' B)
  have hV_bounded (x) (hx : x∈B) : |V x| ≤ Vmax := by
    have hfun : Continuous (fun x => |V x|) := by
      have := V.contDiff.continuous
      fun_prop
    exact f_le_sup_compact (fun x => |V x|) hfun hB hx

  have hVx_bounded : ∀ T, |(V∘x) T - (V∘x) 0| ≤ 2*Vmax := by
    intro T
    calc
      _ = |((V∘x) T) + (-(V∘x) 0)| := by ring_nf
      _ ≤ |(V∘x) T| + |-(V∘x) 0| := by grw [abs_add_le]
      _ = |V (x T)| + |V (x 0)| := by simp only [Function.comp_apply, abs_neg]
      _ ≤ Vmax + Vmax := by grw[hV_bounded (x T) (hxb T)]; grw[hV_bounded (x 0) (hxb 0)]
      _ = 2*Vmax := by ring

  have h_eventually :
    ∀ᶠ (T : ℝ) in atTop,
      |(V.func ∘ x) T - (V.func ∘ x) 0| ≤ (2 * Vmax : ℝ) := by
    exact Eventually.of_forall hVx_bounded

  conv =>
    change Tendsto (fun T ↦ T⁻¹ * ∫ (t : ℝ) in 0..T, ((LieDerivative V f) ∘ x) t) atTop (𝓝 0)
    rw [←time_deriv_eq_lie_deriv V f x hx]
    rw [hftc]
    congr
    ext T
    simp only [Function.comp_apply]
    rw [mul_comm]
  exact (bdd_le_mul_tendsto_zero' (2*Vmax) h_eventually tendsto_inv_atTop_zero)

theorem time_ave_add_zero
    {n : ℕ}
    (Φ : Observable n 0)
    (Ψ : Observable n 0)
    (x : ℝ → EuclideanSpace ℝ (Fin n)) (hx : Differentiable ℝ x)
    (hΨ : Tendsto (fun (T : ℝ) => T⁻¹ * (∫ t in 0..T, Ψ (x t))) atTop (𝓝 0))
  : TimeAverage (Φ+Ψ) x = TimeAverage Φ x := by
  simp only [TimeAverage]
  conv in (fun T ↦ ↑(T⁻¹  * ∫ (t : ℝ) in 0..T, (Φ + Ψ).func (x t))) =>
    ext T
    congr
    conv in (Φ + Ψ).func (x _) =>
      change (Φ.func + Ψ.func) (x _)
    simp only [Pi.add_apply]
    rw [intervalIntegral.integral_add
          (observable_integrable Φ x hx T)
          (observable_integrable Ψ x hx T)]
    ring_nf
  simp only [EReal.coe_add, EReal.coe_mul]
  rw [←Pi.add_def]
  rw [←EReal.tendsto_coe] at hΨ
  exact limsup_add_vanishes hΨ


theorem time_ave_pointwise
    {n : ℕ} {B : Set (EuclideanSpace ℝ (Fin n))}
    (Φ : Observable n 0)
    (x : ℝ → EuclideanSpace ℝ (Fin n)) (hx : Differentiable ℝ x)
    (hxb : ∀ t, x t ∈ B) (hB : IsCompact B) :
    TimeAverage Φ x ≤ sSup (Φ '' B) := by

  have h_upper (T) : ∀ t ∈ Set.Ioo 0 T, Φ (x t) ≤ sSup (Φ '' B) :=
    fun t _ ↦ le_csSup (hB.image Φ.contDiff.continuous).isBounded.bddAbove
      (Set.mem_image_of_mem _ (hxb t))
  have h_lower (T) : ∀ t ∈ Set.Ioo 0 T, Φ (x t) ≥ sInf (Φ '' B) :=
    fun t _ ↦ csInf_le (hB.image Φ.contDiff.continuous).isBounded.bddBelow
      (Set.mem_image_of_mem _ (hxb t))

  have hu {T} (hT : 0 < T) :
      T⁻¹ * ∫ t in 0..T, Φ (x t) ≤ sSup (Φ '' B) := by
    rw [inv_mul_le_iff₀ hT]
    grw [intervalIntegral.integral_mono_on_of_le_Ioo
          (le_of_lt hT) (observable_integrable Φ x hx T) intervalIntegrable_const (h_upper T)]
    rw [intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul, le_refl]

  have hl {T} (hT : 0 < T) :
      sInf (Φ '' B) ≤ T⁻¹ * ∫ t in 0..T, Φ (x t) := by
    rw [le_inv_mul_iff₀' hT]
    rw [←sub_zero T, ←smul_eq_mul]
    rw [←intervalIntegral.integral_const (sInf (Φ '' B))]
    grw [intervalIntegral.integral_mono_on_of_le_Ioo
        (le_of_lt hT) intervalIntegrable_const (observable_integrable Φ x hx T) (h_lower T)]
    simp only [sub_zero, le_refl]

  rw [TimeAverage]
  apply limsup_le_of_le
  · apply isCoboundedUnder_le_of_eventually_le atTop
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      apply EReal.coe_le_coe
      exact hl hT
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    apply EReal.coe_le_coe
    exact hu hT

theorem time_ave_add_lie_deriv
    {n : ℕ}
    (Φ : Observable n 0)
    (V : Observable n 1)
    (f : C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n)))
    (x : ℝ → EuclideanSpace ℝ (Fin n)) (hx : ∀ t, HasDerivAt x (f (x t)) t)
    {B : Set (EuclideanSpace ℝ (Fin n))}
    (hxb : ∀ t, x t ∈ B) (hB : IsCompact B)
  : TimeAverage (Φ + LieDerivative V f) x = TimeAverage Φ x
  := by
    apply time_ave_add_zero
    · exact hasderivat_diffable hx
    · exact lie_deriv_tendsto_zero V f x hx hxb hB

/-- Suppose we have a solution to a system dx/dt = f(x) defined for all time,
    and an auxiliary function V.
   Then the time average of Φ is at most sup (Φ + f⬝∇V) over the domain. -/
theorem V_gives_upper_bound
    {n : ℕ}
    (Φ : Observable n 0)
    (V : Observable n 1)
    (f : C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n)))
    (x : ℝ → EuclideanSpace ℝ (Fin n)) (hx : ∀ t, HasDerivAt x (f (x t)) t)
    {B : Set (EuclideanSpace ℝ (Fin n))}
    (hxb : ∀ t, x t ∈ B) (hB : IsCompact B) :
  TimeAverage Φ x ≤ sSup ((Φ + LieDerivative V f) '' B) := by
  rw [←time_ave_add_lie_deriv Φ V f x hx hxb hB]
  exact time_ave_pointwise (Φ + LieDerivative V f) x (hasderivat_diffable hx) hxb hB
