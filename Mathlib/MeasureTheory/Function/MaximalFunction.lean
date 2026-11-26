/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# The Hardy–Littlewood maximal function

The (centered) Hardy–Littlewood maximal function of a function `f` on a
normed space `E` over `ℝ`, with respect to a measure `μ`, is

`maximalFunction μ f x = sup over r > 0 of the average of ‖f‖ over ball x r`.

It is valued in `ℝ≥0∞`, the averages being taken with `laverage`.
This file sets up the definition and its basic API, and proves that
the maximal function of a locally integrable function is measurable,
via continuity (hence lower semicontinuity) of ball averages, and
proves the weak type `(1, 1)` inequality via the Besicovitch covering
theorem. The strong type `(p, p)` inequality is developed separately.
-/

public section

open MeasureTheory ENNReal Metric Filter Topology Function

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
  {F : Type*} [SeminormedAddCommGroup F]


/-- The centered Hardy–Littlewood maximal function of `f` with respect to
the measure `μ`: at each point `x`, the supremum over all radii `r > 0` of
the average of `‖f‖` over the ball of radius `r` centered at `x`. -/
noncomputable def maximalFunction (μ : Measure E) (f : E → F) (x : E) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (_ : 0 < r), ⨍⁻ y in Metric.ball x r, ‖f y‖ₑ ∂μ

theorem maximalFunction_zero (μ : Measure E) :
    maximalFunction μ (0 : E → F) = 0 := by
  funext x
  simp [maximalFunction]

theorem maximalFunction_congr_ae {μ : Measure E} {f g : E → F}
    (h : f =ᵐ[μ] g) : maximalFunction μ f = maximalFunction μ g := by
  funext x
  refine iSup_congr fun r => iSup_congr fun _ => ?_
  exact laverage_congr ((h.filter_mono ae_restrict_le).mono fun y hy => by
    change ‖f y‖ₑ = ‖g y‖ₑ
    rw [hy])

theorem maximalFunction_mono {μ : Measure E} {f g : E → F}
    (h : ∀ x, ‖f x‖ ≤ ‖g x‖) (x : E) :
    maximalFunction μ f x ≤ maximalFunction μ g x := by
  refine iSup_mono fun r => iSup_mono fun _ => ?_
  refine laverage_mono_ae (Filter.Eventually.of_forall fun y => ?_)
  change ‖f y‖ₑ ≤ ‖g y‖ₑ
  rw [← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (h y)

/-- Working abbreviation for B2: the average of `‖f‖` over `ball x r`. -/
noncomputable def ballAverage (μ : Measure E) (f : E → F) (r : ℝ) (x : E) : ℝ≥0∞ :=
  ⨍⁻ y in Metric.ball x r, ‖f y‖ₑ ∂μ

/-- [GLUE] `maximalFunction` is the supremum of the ball averages. -/
theorem maximalFunction_eq_iSup_ballAverage (μ : Measure E) (f : E → F) (x : E) :
    maximalFunction μ f x = ⨆ (r : ℝ) (_ : 0 < r), ballAverage μ f r x := by
  simp only [maximalFunction, ballAverage]


/-- The ball average of a sum is at most the sum of the ball averages:
the `ℝ≥0∞` triangle inequality for `ballAverage`. -/
theorem ballAverage_add_le (μ : Measure E) {f g : E → F}
    (hf : AEStronglyMeasurable f μ) (r : ℝ) (x : E) :
    ballAverage μ (f + g) r x ≤ ballAverage μ f r x + ballAverage μ g r x := by
  rw [ballAverage, ballAverage, ballAverage, setLAverage_eq, setLAverage_eq,
    setLAverage_eq, ENNReal.div_add_div_same]
  refine ENNReal.div_le_div_right ?_ _
  calc ∫⁻ y in Metric.ball x r, ‖(f + g) y‖ₑ ∂μ
      ≤ ∫⁻ y in Metric.ball x r, (‖f y‖ₑ + ‖g y‖ₑ) ∂μ :=
        lintegral_mono_ae (Filter.Eventually.of_forall fun y => eNorm_add_le _ _)
    _ = ∫⁻ y in Metric.ball x r, ‖f y‖ₑ ∂μ
          + ∫⁻ y in Metric.ball x r, ‖g y‖ₑ ∂μ :=
        lintegral_add_left' hf.eNorm.restrict _

/-- The maximal function is subadditive. -/
theorem maximalFunction_add_le (μ : Measure E) {f g : E → F}
    (hf : AEStronglyMeasurable f μ) (x : E) :
    maximalFunction μ (f + g) x ≤ maximalFunction μ f x + maximalFunction μ g x := by
  rw [maximalFunction_eq_iSup_ballAverage, maximalFunction_eq_iSup_ballAverage,
    maximalFunction_eq_iSup_ballAverage]
  refine iSup_le fun r => iSup_le fun hr => le_trans (ballAverage_add_le μ hf r x) ?_
  have hf_le : ballAverage μ f r x ≤ ⨆ (r : ℝ) (_ : 0 < r), ballAverage μ f r x :=
    (le_iSup (fun _ : 0 < r => ballAverage μ f r x) hr).trans
      (le_iSup (fun r => ⨆ _ : 0 < r, ballAverage μ f r x) r)
  have hg_le : ballAverage μ g r x ≤ ⨆ (r : ℝ) (_ : 0 < r), ballAverage μ g r x :=
    (le_iSup (fun _ : 0 < r => ballAverage μ g r x) hr).trans
      (le_iSup (fun r => ⨆ _ : 0 < r, ballAverage μ g r x) r)
  exact add_le_add hf_le hg_le

variable [BorelSpace E]

/-- [GLUE] The translation identity for set integrals over balls, for a
Haar measure: integrating over `ball x r` is integrating the translated
function over the fixed `ball 0 r`. -/
theorem lintegral_ball_translate (μ : Measure E)
    [MeasureTheory.Measure.IsAddHaarMeasure μ] (F : E → ℝ≥0∞) (r : ℝ) (x : E) :
    ∫⁻ y in Metric.ball x r, F y ∂μ
      = ∫⁻ z in Metric.ball 0 r, F (z + x) ∂μ := by
  have hpt : ∀ z, (Metric.ball x r).indicator F (x + z)
      = (Metric.ball 0 r).indicator (fun z => F (z + x)) z := by
    intro z
    by_cases hz : z ∈ Metric.ball 0 r
    · have hx : x + z ∈ Metric.ball x r := by
        simpa [Metric.mem_ball, dist_eq_norm] using hz
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hz, add_comm]
    · have hx : x + z ∉ Metric.ball x r := by
        simpa [Metric.mem_ball, dist_eq_norm] using hz
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hz]
  rw [← lintegral_indicator Metric.isOpen_ball.measurableSet,
    ← lintegral_indicator Metric.isOpen_ball.measurableSet,
    ← lintegral_add_left_eq_self ((Metric.ball x r).indicator F) x]
  exact lintegral_congr_ae (Filter.Eventually.of_forall hpt)

/-- [GLUE] Route B change of variables: for a Haar measure the average
over `ball x r` is the average over the FIXED ball `ball 0 r` of the
translated function, and the normalizing factor does not depend on `x`
(it is the `F = 1` case of `lintegral_ball_translate`). -/
theorem ballAverage_translate (μ : Measure E)
    [MeasureTheory.Measure.IsAddHaarMeasure μ] (f : E → F)
    (r : ℝ) (x : E) :
    ballAverage μ f r x
      = (∫⁻ z in Metric.ball 0 r, ‖f (z + x)‖ₑ ∂μ) / μ (Metric.ball 0 r) := by
  have hden : μ (Metric.ball x r) = μ (Metric.ball 0 r) := by
    have h := lintegral_ball_translate μ (fun _ => 1) r x
    simpa [lintegral_const] using h
  unfold ballAverage
  rw [laverage_eq, Measure.restrict_apply_univ,
    lintegral_ball_translate μ (fun y => ‖f y‖ₑ) r x, hden]

-- From Step 1 on, the target is a normed space over `ℝ`: the `Lp`
-- density API (`BoundedContinuousFunction.toLp_denseRange`) is stated
-- for normed targets, and the cutoff argument multiplies by real
-- scalars. Steps 2 and the glue above only need a seminormed target.
variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Step 1 (David's architecture): approximation on the fixed compact
`closedBall x₀ (r + 1)`. Derivation: BCF density in L¹ of the restricted
(finite, weakly regular) measure on `closedBall x₀ (r + 2)`, bridge to
`∫⁻` of the enorm, then cut off by `max 0 (1 - infDist · K₁)`, which is
`1` on `K₁ = closedBall x₀ (r + 1)` and supported in `K₂`. The
hypothesis lives on `r + 2` because the cutoff needs the shell
`r + 1 < dist < r + 2` to fall in (David's adjustment, 2026-11-26). -/
theorem exists_continuous_approx (μ : Measure E)
    [MeasureTheory.Measure.IsAddHaarMeasure μ]
    {f : E → F} {x₀ : E} {r : ℝ}
    (hr : 0 < r)
    (hf : IntegrableOn f (Metric.closedBall x₀ (r + 2)) μ)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : E → F, Continuous g ∧ HasCompactSupport g ∧
      ∫⁻ y in Metric.closedBall x₀ (r + 1), ‖f y - g y‖ₑ ∂μ < ε := by
  set K₁ := Metric.closedBall x₀ (r + 1) with hK₁def
  set K₂ := Metric.closedBall x₀ (r + 2) with hK₂def
  have hK₂lt : μ K₂ < ∞ := (isCompact_closedBall x₀ (r + 2)).measure_lt_top
  have hK₂fin : μ K₂ ≠ ∞ := hK₂lt.ne
  have : IsFiniteMeasure (μ.restrict K₂) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  have : (μ.restrict K₂).WeaklyRegular :=
    MeasureTheory.Measure.WeaklyRegular.restrict_of_measure_ne_top hK₂fin
  have : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩
  obtain ⟨δ, hδpos, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ≤ ε := by
    by_cases hεtop : ε = ∞
    · exact ⟨1, one_pos, by simp [hεtop]⟩
    · exact ⟨ε.toReal, ENNReal.toReal_pos hε hεtop, by rw [ENNReal.ofReal_toReal hεtop]⟩
  have hfMem : MemLp f 1 (μ.restrict K₂) := memLp_one_iff_integrable.mpr hf
  obtain ⟨g, hgδ⟩ : ∃ g : BoundedContinuousFunction E F,
      ‖hfMem.toLp f - BoundedContinuousFunction.toLp 1 (μ.restrict K₂) ℝ g‖ < δ := by
    have hd := BoundedContinuousFunction.toLp_denseRange F (μ.restrict K₂) ℝ
      (p := 1) ENNReal.one_ne_top
    have hmem : hfMem.toLp f ∈ closure
        (Set.range (BoundedContinuousFunction.toLp 1 (μ.restrict K₂) ℝ)) := by
      rw [hd.closure_range]; trivial
    obtain ⟨y, hy, hdist⟩ := (Metric.mem_closure_iff.mp hmem) δ hδpos
    obtain ⟨g, rfl⟩ := hy
    exact ⟨g, by rwa [dist_eq_norm] at hdist⟩
  have hnorm : eLpNorm (fun y => f y - g y) 1 (μ.restrict K₂)
      = ENNReal.ofReal ‖hfMem.toLp f
          - BoundedContinuousFunction.toLp 1 (μ.restrict K₂) ℝ g‖ := by
    have h1 : eLpNorm (fun y => f y - g y) 1 (μ.restrict K₂)
        = eLpNorm (hfMem.toLp f
            - BoundedContinuousFunction.toLp 1 (μ.restrict K₂) ℝ g)
          1 (μ.restrict K₂) := by
      refine eLpNorm_congr_ae ?_
      exact ((hfMem.coeFn_toLp).sub
        (BoundedContinuousFunction.coeFn_toLp 1 (μ.restrict K₂) ℝ g)).symm.trans
        (Lp.coeFn_sub _ _).symm
    rw [h1, ← ENNReal.ofReal_toReal (Lp.memLp _).eLpNorm_lt_top.ne, Lp.norm_def]
  -- the cutoff: 1 on K₁, supported in K₂
  set φ : E → ℝ := fun y => max 0 (1 - Metric.infDist y K₁) with hφdef
  have hφcont : Continuous φ :=
    Continuous.max continuous_const
      (continuous_const.sub (Metric.continuous_infDist_pt K₁))
  have hφ1 : ∀ y ∈ K₁, φ y = 1 := by
    intro y hy
    simp [hφdef, Metric.infDist_zero_of_mem hy]
  set gcut : E → F := fun y => φ y • g y with hgcutdef
  have hgcutcont : Continuous gcut := hφcont.smul g.continuous
  have hgcutsupp : HasCompactSupport gcut := by
    refine IsCompact.of_isClosed_subset (isCompact_closedBall x₀ (r + 2))
      (isClosed_tsupport gcut) (closure_minimal ?_ Metric.isClosed_closedBall)
    intro y hy
    rw [Function.mem_support] at hy
    have hφy : φ y ≠ 0 := by
      intro h
      exact hy (by simp [hgcutdef, h])
    have hlt : Metric.infDist y K₁ < 1 := by
      by_contra hcon
      push Not at hcon
      exact hφy (by simp [hφdef, sub_nonpos.mpr hcon])
    obtain ⟨z, hzK₁, hzy⟩ := (Metric.infDist_lt_iff
      ⟨x₀, by rw [hK₁def]; exact Metric.mem_closedBall_self (by linarith)⟩).mp hlt
    rw [Metric.mem_closedBall]
    calc dist y x₀ ≤ dist y z + dist z x₀ := dist_triangle y z x₀
      _ ≤ 1 + (r + 1) := add_le_add (le_of_lt hzy)
          (by rwa [hK₁def, Metric.mem_closedBall] at hzK₁)
      _ = r + 2 := by ring
  refine ⟨gcut, hgcutcont, hgcutsupp, ?_⟩
  calc ∫⁻ y in K₁, ‖f y - gcut y‖ₑ ∂μ
      = ∫⁻ y in K₁, ‖f y - g y‖ₑ ∂μ := by
        refine lintegral_congr_ae ?_
        refine Set.EqOn.aeEq_restrict (s := K₁) (μ := μ) ?_
          (Metric.isClosed_closedBall.measurableSet)
        intro y hy
        rw [hgcutdef]
        simp [hφ1 y hy]
    _ ≤ ∫⁻ y in K₂, ‖f y - g y‖ₑ ∂μ := by
        refine lintegral_mono_set ?_
        intro y hy
        rw [hK₁def, Metric.mem_closedBall] at hy
        rw [hK₂def, Metric.mem_closedBall]
        linarith
    _ = eLpNorm (fun y => f y - g y) 1 (μ.restrict K₂) :=
        (eLpNorm_one_eq_lintegral_eNorm
          (hfMem.aestronglyMeasurable.sub g.continuous.aestronglyMeasurable)).symm
    _ = ENNReal.ofReal ‖hfMem.toLp f
          - BoundedContinuousFunction.toLp 1 (μ.restrict K₂) ℝ g‖ := hnorm
    _ < ENNReal.ofReal δ :=
        (ENNReal.ofReal_lt_ofReal_iff hδpos).mpr hgδ
    _ ≤ ε := hδε

omit [NormedSpace ℝ F] in
/-- Step 2, route B (David's mathematics): continuity of the average for
continuous compactly supported `g`. Via `ballAverage_translate` the
domain and the normalizing factor are fixed; the integrand
`z ↦ ‖g (z + x)‖ₑ` converges pointwise as `x → x₀` (continuity of `g`
and of the enorm), and is dominated by the constant `ofReal C` where
`C` bounds `‖g‖` (compact support); conclude by the filter form of
dominated convergence, `tendsto_lintegral_filter_of_dominated_convergence'`,
and `ENNReal.Tendsto.const_mul` for the constant normalizing factor. -/
theorem continuousAt_ballAverage_of_continuous (μ : Measure E)
    [MeasureTheory.Measure.IsAddHaarMeasure μ] {g : E → F} (hg : Continuous g)
    (hgc : HasCompactSupport g) {r : ℝ} (hr : 0 < r) (x₀ : E) :
    ContinuousAt (ballAverage μ g r) x₀ := by
  have hK : IsCompact (tsupport g) := hgc
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ z, ‖g z‖ ≤ C := by
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
    refine ⟨max C 0, fun z => ?_⟩
    by_cases hz : z ∈ tsupport g
    · exact le_trans (hC z hz) (le_max_left _ _)
    · have hgz : g z = 0 := by
        by_contra hne
        exact hz (subset_tsupport _ (Function.mem_support.mpr hne))
      rw [hgz]
      simp only [norm_zero]
      exact le_max_right C 0
  have hfin : μ (Metric.ball (0 : E) r) ≠ ∞ :=
    ne_top_of_le_ne_top (isCompact_closedBall (0 : E) r).measure_lt_top.ne
      (measure_mono Metric.ball_subset_closedBall)
  have hInt : Filter.Tendsto (fun x => ∫⁻ z in Metric.ball 0 r, ‖g (z + x)‖ₑ ∂μ)
      (𝓝 x₀) (𝓝 (∫⁻ z in Metric.ball 0 r, ‖g (z + x₀)‖ₑ ∂μ)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence' (fun _ => ENNReal.ofReal C)
      (Filter.Eventually.of_forall fun x => ?_)
      (Filter.Eventually.of_forall fun x => Filter.Eventually.of_forall fun z => ?_)
      ?_ (Filter.Eventually.of_forall fun z => ?_)
    · exact (ContinuousENorm.continuous_eNorm.comp
        (hg.comp (Homeomorph.addRight x).continuous)).aemeasurable
    · rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hC _)
    · rw [lintegral_const, Measure.restrict_apply_univ]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
    · exact (ContinuousENorm.continuous_eNorm.comp
        (hg.comp (Homeomorph.addLeft z).continuous)).tendsto x₀
  have htr : ballAverage μ g r
      = fun x => (∫⁻ z in Metric.ball 0 r, ‖g (z + x)‖ₑ ∂μ)
          / μ (Metric.ball 0 r) :=
    funext fun x => ballAverage_translate μ g r x
  rw [htr]
  have hpos : μ (Metric.ball (0 : E) r) ≠ 0 :=
    ne_of_gt (Metric.isOpen_ball.measure_pos μ (Metric.nonempty_ball.mpr hr))
  have hmul := ENNReal.Tendsto.const_mul hInt (Or.inr (ENNReal.inv_ne_top.mpr hpos))
  change Filter.Tendsto (fun x => (∫⁻ z in Metric.ball 0 r, ‖g (z + x)‖ₑ ∂μ)
      / μ (Metric.ball 0 r)) (𝓝 x₀)
    (𝓝 ((∫⁻ z in Metric.ball 0 r, ‖g (z + x₀)‖ₑ ∂μ) / μ (Metric.ball 0 r)))
  simpa only [ENNReal.div_eq_inv_mul] using hmul

/-- Step 3 (David's mathematics): the squeeze. For `x` within `1` of
`x₀`, `ball x r ⊆ closedBall x₀ (r + 1)`, and pointwise
`‖f‖ₑ ≤ ‖g‖ₑ + ‖f - g‖ₑ` (and symmetrically) with `laverage_mono_ae`
bounds both `ballAverage f x` and `ballAverage f x₀` against
`ballAverage g` up to the fixed error of Step 1; order-topology
characterization of `Tendsto` in `ℝ≥0∞` closes it. -/
theorem continuousAt_ballAverage (μ : Measure E)
    [MeasureTheory.Measure.IsAddHaarMeasure μ]
    {f : E → F} {r : ℝ} (hr : 0 < r)
    (x₀ : E) (hf : LocallyIntegrable f μ) :
    ContinuousAt (ballAverage μ f r) x₀ := by
  have hfK₂ : IntegrableOn f (Metric.closedBall x₀ (r + 2)) μ :=
    hf.integrableOn_isCompact (isCompact_closedBall x₀ (r + 2))
  have hc0 : μ (Metric.ball (0 : E) r) ≠ 0 :=
    ne_of_gt (Metric.isOpen_ball.measure_pos μ (Metric.nonempty_ball.mpr hr))
  have hcfin : μ (Metric.ball (0 : E) r) ≠ ∞ :=
    ne_top_of_le_ne_top (isCompact_closedBall (0 : E) r).measure_lt_top.ne
      (measure_mono Metric.ball_subset_closedBall)
  -- One-sided bound: for `x` within `1` of `x₀`, the average of `u` over
  -- `ball x r` is at most the average of `v` plus the fixed `K₁`-error
  -- of `u - v`, over the constant denominator. Pointwise enorm triangle
  -- inequality, `lintegral_mono`, and monotonicity in the set; the only
  -- hypothesis on `v` is the integrability that makes its enorm
  -- a.e. measurable on the small ball.
  have hbound : ∀ u v : E → F, IntegrableOn v (Metric.closedBall x₀ (r + 2)) μ →
      ∀ x : E, dist x x₀ < 1 →
      ballAverage μ u r x ≤ ballAverage μ v r x
        + (∫⁻ y in Metric.closedBall x₀ (r + 1), ‖u y - v y‖ₑ ∂μ)
          / μ (Metric.ball 0 r) := by
    intro u v hv x hx
    have hsub : Metric.ball x r ⊆ Metric.closedBall x₀ (r + 1) := by
      intro y hy
      rw [Metric.mem_closedBall]
      exact le_trans (dist_triangle y x x₀)
        (le_of_lt (add_lt_add (Metric.mem_ball.mp hy) hx))
    have hsub₂ : Metric.ball x r ⊆ Metric.closedBall x₀ (r + 2) :=
      hsub.trans (Metric.closedBall_subset_closedBall (by linarith : r + 1 ≤ r + 2))
    have hvm : AEMeasurable (fun y => ‖v y‖ₑ) (μ.restrict (Metric.ball x r)) :=
      (hv.mono_set hsub₂).aestronglyMeasurable.eNorm
    have hInt : ∫⁻ y in Metric.ball x r, ‖u y‖ₑ ∂μ
        ≤ ∫⁻ y in Metric.ball x r, ‖v y‖ₑ ∂μ
          + ∫⁻ y in Metric.closedBall x₀ (r + 1), ‖u y - v y‖ₑ ∂μ := by
      calc ∫⁻ y in Metric.ball x r, ‖u y‖ₑ ∂μ
          ≤ ∫⁻ y in Metric.ball x r, (‖v y‖ₑ + ‖u y - v y‖ₑ) ∂μ := by
            apply lintegral_mono
            intro y
            have h : v y + (u y - v y) = u y := by abel
            calc ‖u y‖ₑ = ‖v y + (u y - v y)‖ₑ := by rw [h]
              _ ≤ ‖v y‖ₑ + ‖u y - v y‖ₑ := eNorm_add_le _ _
        _ = ∫⁻ y in Metric.ball x r, ‖v y‖ₑ ∂μ
            + ∫⁻ y in Metric.ball x r, ‖u y - v y‖ₑ ∂μ :=
            lintegral_add_left' hvm _
        _ ≤ ∫⁻ y in Metric.ball x r, ‖v y‖ₑ ∂μ
            + ∫⁻ y in Metric.closedBall x₀ (r + 1), ‖u y - v y‖ₑ ∂μ :=
            add_le_add le_rfl (lintegral_mono_set hsub)
    rw [lintegral_ball_translate μ (fun y => ‖u y‖ₑ) r x,
      lintegral_ball_translate μ (fun y => ‖v y‖ₑ) r x] at hInt
    rw [ballAverage_translate μ u r x, ballAverage_translate μ v r x]
    simp only [ENNReal.div_eq_inv_mul]
    calc (μ (Metric.ball 0 r))⁻¹ * ∫⁻ z in Metric.ball 0 r, ‖u (z + x)‖ₑ ∂μ
        ≤ (μ (Metric.ball 0 r))⁻¹
            * (∫⁻ z in Metric.ball 0 r, ‖v (z + x)‖ₑ ∂μ
              + ∫⁻ y in Metric.closedBall x₀ (r + 1), ‖u y - v y‖ₑ ∂μ) :=
          mul_le_mul' le_rfl hInt
      _ = (μ (Metric.ball 0 r))⁻¹ * ∫⁻ z in Metric.ball 0 r, ‖v (z + x)‖ₑ ∂μ
            + (μ (Metric.ball 0 r))⁻¹
              * ∫⁻ y in Metric.closedBall x₀ (r + 1), ‖u y - v y‖ₑ ∂μ :=
          mul_add _ _ _
  -- The squeeze, in the `Icc` characterization of convergence in `ℝ≥0∞`.
  apply ENNReal.tendsto_nhds_of_Icc
  intro ε hε
  by_cases hεtop : ε = ∞
  · subst hεtop
    filter_upwards with x
    refine Set.mem_Icc.mpr ⟨?_, ?_⟩
    · rw [tsub_eq_zero_of_le le_top]
      exact bot_le
    · calc ballAverage μ f r x ≤ ∞ := le_top
        _ = ballAverage μ f r x₀ + ∞ := by simp
  · have hε3 : (0 : ℝ≥0∞) < ε / 3 :=
      ENNReal.div_pos (ne_of_gt hε) (by norm_num)
    have hε3fin : ε / 3 ≠ ∞ := ENNReal.div_ne_top hεtop (by norm_num)
    obtain ⟨g, hg, hgc, hD⟩ := exists_continuous_approx μ hr hfK₂
      (ε := μ (Metric.ball 0 r) * (ε / 3))
      (mul_ne_zero hc0 (ne_of_gt hε3))
    have hgK₂ : IntegrableOn g (Metric.closedBall x₀ (r + 2)) μ :=
      (hg.integrable_of_hasCompactSupport hgc).integrableOn
    have hDc : (∫⁻ y in Metric.closedBall x₀ (r + 1), ‖f y - g y‖ₑ ∂μ)
        / μ (Metric.ball 0 r) < ε / 3 := by
      rw [ENNReal.div_lt_iff (Or.inl hc0) (Or.inl hcfin), mul_comm]
      exact hD
    obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ z, ‖g z‖ ≤ C := by
      obtain ⟨C, hC⟩ := hgc.isCompact.exists_bound_of_continuousOn hg.continuousOn
      refine ⟨max C 0, fun z => ?_⟩
      by_cases hz : z ∈ tsupport g
      · exact le_trans (hC z hz) (le_max_left _ _)
      · have hgz : g z = 0 := by
          by_contra hne
          exact hz (subset_tsupport _ (Function.mem_support.mpr hne))
        rw [hgz]
        simp only [norm_zero]
        exact le_max_right C 0
    have hle : (∫⁻ z in Metric.ball 0 r, ‖g (z + x₀)‖ₑ ∂μ)
        ≤ ∫⁻ _ in Metric.ball 0 r, ENNReal.ofReal C ∂μ :=
      lintegral_mono fun z => by
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hC _)
    have hIg₀ : (∫⁻ z in Metric.ball 0 r, ‖g (z + x₀)‖ₑ ∂μ) ≠ ∞ :=
      ne_top_of_le_ne_top (by
        rw [lintegral_const, Measure.restrict_apply_univ]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hcfin) hle
    have hAg₀ : ballAverage μ g r x₀ ≠ ∞ := by
      rw [ballAverage_translate μ g r x₀]
      exact ENNReal.div_ne_top hIg₀ hc0
    have hmid := (ENNReal.tendsto_nhds hAg₀).mp
      (continuousAt_ballAverage_of_continuous μ hg hgc hr x₀) (ε / 3) hε3
    have hsum : ε / 3 + ε / 3 + ε / 3 = ε := by
      have h3 : (3 : ℝ≥0∞) ≠ 0 := by norm_num
      have h3' : (3 : ℝ≥0∞) ≠ ∞ := by norm_num
      calc ε / 3 + ε / 3 + ε / 3 = (ε / 3) * 3 := by ring
        _ = ε := ENNReal.div_mul_cancel h3 h3'
    have hDsymm : (∫⁻ y in Metric.closedBall x₀ (r + 1), ‖g y - f y‖ₑ ∂μ)
        = ∫⁻ y in Metric.closedBall x₀ (r + 1), ‖f y - g y‖ₑ ∂μ :=
      lintegral_congr fun y => eNorm_sub_rev _ _
    filter_upwards [Metric.ball_mem_nhds x₀ (show (0 : ℝ) < 1 by norm_num), hmid]
      with x hx hxm
    have hdx : dist x x₀ < 1 := Metric.mem_ball.mp hx
    have hfgx := hbound f g hgK₂ x hdx
    have hfgx₀ := hbound f g hgK₂ x₀ (by simp)
    have hgf : ballAverage μ g r x₀ ≤ ballAverage μ f r x₀
        + (∫⁻ y in Metric.closedBall x₀ (r + 1), ‖f y - g y‖ₑ ∂μ)
          / μ (Metric.ball 0 r) := by
      have h := hbound g f hfK₂ x₀ (by simp)
      rwa [hDsymm] at h
    have hgfx : ballAverage μ g r x ≤ ballAverage μ f r x
        + (∫⁻ y in Metric.closedBall x₀ (r + 1), ‖f y - g y‖ₑ ∂μ)
          / μ (Metric.ball 0 r) := by
      have h := hbound g f hfK₂ x hdx
      rwa [hDsymm] at h
    have hrearr : ∀ a b c d : ℝ≥0∞, ((a + b) + c) + d = a + ((b + c) + d) :=
      fun a b c d => by rw [add_assoc, add_assoc, add_assoc]
    refine Set.mem_Icc.mpr ⟨?_, ?_⟩
    · -- lower bound: `A f x₀ - ε ≤ A f x`
      have hgx₀ : ballAverage μ g r x₀ ≤ ballAverage μ g r x + ε / 3 := by
        have h := tsub_le_iff_left.mp hxm.1
        rwa [add_comm] at h
      have hchain : ballAverage μ f r x₀ ≤ ballAverage μ f r x + ε := by
        calc ballAverage μ f r x₀
            ≤ ballAverage μ g r x₀
              + (∫⁻ y in Metric.closedBall x₀ (r + 1), ‖f y - g y‖ₑ ∂μ)
                / μ (Metric.ball 0 r) := hfgx₀
          _ ≤ (ballAverage μ g r x + ε / 3)
              + (∫⁻ y in Metric.closedBall x₀ (r + 1), ‖f y - g y‖ₑ ∂μ)
                / μ (Metric.ball 0 r) := add_le_add_left hgx₀ _
          _ ≤ (ballAverage μ f r x
              + (∫⁻ y in Metric.closedBall x₀ (r + 1), ‖f y - g y‖ₑ ∂μ)
                / μ (Metric.ball 0 r) + ε / 3)
              + (∫⁻ y in Metric.closedBall x₀ (r + 1), ‖f y - g y‖ₑ ∂μ)
                / μ (Metric.ball 0 r) := add_le_add_left (add_le_add_left hgfx _) _
          _ = ballAverage μ f r x
              + (((∫⁻ y in Metric.closedBall x₀ (r + 1), ‖f y - g y‖ₑ ∂μ)
                  / μ (Metric.ball 0 r) + ε / 3)
                + (∫⁻ y in Metric.closedBall x₀ (r + 1), ‖f y - g y‖ₑ ∂μ)
                  / μ (Metric.ball 0 r)) := hrearr _ _ _ _
          _ ≤ ballAverage μ f r x + (ε / 3 + ε / 3 + ε / 3) :=
              add_le_add le_rfl (add_le_add (add_le_add hDc.le le_rfl) hDc.le)
          _ = ballAverage μ f r x + ε := by rw [hsum]
      exact tsub_le_iff_right.mpr hchain
    · -- upper bound: `A f x ≤ A f x₀ + ε`
      have hchain : ballAverage μ f r x ≤ ballAverage μ f r x₀ + ε := by
        calc ballAverage μ f r x
            ≤ ballAverage μ g r x
              + (∫⁻ y in Metric.closedBall x₀ (r + 1), ‖f y - g y‖ₑ ∂μ)
                / μ (Metric.ball 0 r) := hfgx
          _ ≤ (ballAverage μ g r x₀ + ε / 3)
              + (∫⁻ y in Metric.closedBall x₀ (r + 1), ‖f y - g y‖ₑ ∂μ)
                / μ (Metric.ball 0 r) := add_le_add_left hxm.2 _
          _ ≤ (ballAverage μ f r x₀
              + (∫⁻ y in Metric.closedBall x₀ (r + 1), ‖f y - g y‖ₑ ∂μ)
                / μ (Metric.ball 0 r) + ε / 3)
              + (∫⁻ y in Metric.closedBall x₀ (r + 1), ‖f y - g y‖ₑ ∂μ)
                / μ (Metric.ball 0 r) := add_le_add_left (add_le_add_left hgf _) _
          _ = ballAverage μ f r x₀
              + (((∫⁻ y in Metric.closedBall x₀ (r + 1), ‖f y - g y‖ₑ ∂μ)
                  / μ (Metric.ball 0 r) + ε / 3)
                + (∫⁻ y in Metric.closedBall x₀ (r + 1), ‖f y - g y‖ₑ ∂μ)
                  / μ (Metric.ball 0 r)) := hrearr _ _ _ _
          _ ≤ ballAverage μ f r x₀ + (ε / 3 + ε / 3 + ε / 3) :=
              add_le_add le_rfl (add_le_add (add_le_add hDc.le le_rfl) hDc.le)
          _ = ballAverage μ f r x₀ + ε := by rw [hsum]
      exact hchain

/-- [GLUE] Assembly: a supremum of continuous functions into `ℝ≥0∞`
whose superlevel sets are open is lower semicontinuous.
SKETCH (fill when Step 3 lands; a first attempt timed out in `whnf`
on the `hid` simp — revisit then): `lowerSemicontinuous_iff_isOpen_preimage`,
`{x | t < M f x} = ⋃ r, ⋃ _ : 0 < r, {x | t < A_r x}` via `lt_iSup_iff`
plus the empty-index case (`iSup_of_empty`), then `isOpen_iUnion` of
`isOpen_lt continuous_const (continuous_iff_continuousAt.mpr
fun x₀ => continuousAt_ballAverage μ hr x₀ hf)`. -/
theorem lowerSemicontinuous_maximalFunction (μ : Measure E)
    [MeasureTheory.Measure.IsAddHaarMeasure μ] {f : E → F}
    (hf : LocallyIntegrable f μ) :
    LowerSemicontinuous (maximalFunction μ f) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro t
  have hset : (maximalFunction μ f) ⁻¹' Set.Ioi t
      = ⋃ r : ℝ, ⋃ _ : 0 < r, (ballAverage μ f r) ⁻¹' Set.Ioi t := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_iUnion]
    constructor
    · intro h
      rw [maximalFunction_eq_iSup_ballAverage] at h
      obtain ⟨r, hr'⟩ := lt_iSup_iff.mp h
      obtain ⟨hr, hrt⟩ := lt_iSup_iff.mp hr'
      exact ⟨r, hr, hrt⟩
    · rintro ⟨r, hr, hrt⟩
      rw [maximalFunction_eq_iSup_ballAverage]
      exact lt_of_lt_of_le hrt
        ((le_iSup (fun _ : 0 < r => ballAverage μ f r x) hr).trans
          (le_iSup (fun r => ⨆ _ : 0 < r, ballAverage μ f r x) r))
  rw [hset]
  apply isOpen_iUnion
  intro r
  apply isOpen_iUnion
  intro hr
  exact isOpen_lt continuous_const (continuous_iff_continuousAt.mpr fun x₀ =>
    continuousAt_ballAverage μ hr x₀ hf)

/-- B2's deliverable: measurability of the maximal function. -/
theorem measurable_maximalFunction (μ : Measure E)
    [MeasureTheory.Measure.IsAddHaarMeasure μ] {f : E → F}
    (hf : LocallyIntegrable f μ) :
    Measurable (maximalFunction μ f) :=
  (lowerSemicontinuous_maximalFunction μ hf).measurable

/-- On a compact subset `K` of the level set, good radii can be
chosen with a uniform bound: at each `x ∈ K` a good radius stays good
on a neighborhood of `x`, by continuity of the ball average in the
center; finitely many of these neighborhoods cover `K`; take `R` the
largest of the finitely many radii, and let each point inherit the
radius of a neighborhood covering it. -/
theorem exists_bounded_good_radii (μ : Measure E)
    [MeasureTheory.Measure.IsAddHaarMeasure μ] {f : E → F}
    (hf : LocallyIntegrable f μ) {t : ℝ≥0∞} {K : Set E} (hK : IsCompact K)
    (hKlevel : ∀ x ∈ K, t < maximalFunction μ f x) :
    ∃ R : ℝ, 0 < R ∧ ∃ r : K → ℝ,
      (∀ x : K, 0 < r x ∧ r x ≤ R) ∧
      (∀ x : K, t < ballAverage μ f (r x) (x : E)) := by
  by_cases hKempty : K = ∅
  · subst hKempty
    refine ⟨1, one_pos, fun _ => 1, ?_, ?_⟩ <;> intro x <;>
      exact (Set.notMem_empty (x : E) x.property).elim
  -- A good radius at each point of `K`.
  have hgood_ex : ∀ x ∈ K, ∃ ρ : ℝ, 0 < ρ ∧ t < ballAverage μ f ρ x := by
    intro x hx
    have hlt := hKlevel x hx
    rw [maximalFunction_eq_iSup_ballAverage, lt_iSup_iff] at hlt
    obtain ⟨ρ, hρ⟩ := hlt
    rw [lt_iSup_iff] at hρ
    obtain ⟨hρpos, hρgood⟩ := hρ
    exact ⟨ρ, hρpos, hρgood⟩
  have hgood_sub : ∀ x : K, ∃ ρ : ℝ, 0 < ρ ∧ t < ballAverage μ f ρ (x : E) :=
    fun x => hgood_ex x x.property
  choose ρ hρpos hρgood using hgood_sub
  -- The good radius at `x` stays good on a neighborhood of `x`.
  have hU_open : ∀ x : K, IsOpen {y : E | t < ballAverage μ f (ρ x) y} := by
    intro x
    have hcont : Continuous (ballAverage μ f (ρ x)) :=
      continuous_iff_continuousAt.mpr fun y =>
        continuousAt_ballAverage μ (hρpos x) y hf
    exact hcont.isOpen_preimage _ isOpen_Ioi
  -- A finite subcover of `K` by these neighborhoods.
  have hcover : K ⊆ ⋃ x : K, {y : E | t < ballAverage μ f (ρ x) y} := by
    intro y hy
    exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hρgood ⟨y, hy⟩⟩
  obtain ⟨S, hS_cover⟩ := hK.elim_finite_subcover _ hU_open hcover
  -- `R` is the largest of the finitely many radii.
  have hS_ne : S.Nonempty := by
    obtain ⟨y, hy⟩ := Set.ne_empty_iff_nonempty.mp hKempty
    have hmem := hS_cover hy
    rw [Set.mem_iUnion₂] at hmem
    obtain ⟨x, hxS, -⟩ := hmem
    exact ⟨x, hxS⟩
  have hR_ub : ∀ x ∈ S, ρ x ≤ S.sup' hS_ne ρ :=
    fun x hx => Finset.le_sup' ρ hx
  have hR_pos : 0 < S.sup' hS_ne ρ := by
    obtain ⟨x₀, hx₀⟩ := hS_ne
    exact (hρpos x₀).trans_le (Finset.le_sup' ρ hx₀)
  -- Each point inherits the radius of a covering neighborhood.
  have hchoice : ∀ y : K, ∃ i ∈ S,
      (y : E) ∈ {z : E | t < ballAverage μ f (ρ i) z} := by
    intro y
    have hmem := hS_cover y.property
    rw [Set.mem_iUnion₂] at hmem
    obtain ⟨i, hiS, hiy⟩ := hmem
    exact ⟨i, hiS, hiy⟩
  choose idx hidxS hidx_good using hchoice
  exact ⟨S.sup' hS_ne ρ, hR_pos, ρ ∘ idx,
    fun y => ⟨hρpos (idx y), hR_ub (idx y) (hidxS y)⟩,
    fun y => hidx_good y⟩

/-- The weak-type bound on a compact subset of the level set, with
the Besicovitch constant `N` as the witness. -/
theorem measure_isCompact_subset_levelSet_le (μ : Measure E)
    [MeasureTheory.Measure.IsAddHaarMeasure μ] {f : E → F}
    (hf : Integrable f μ)
    {N : ℕ} {τ : ℝ} (hτ : 1 < τ)
    (hN : IsEmpty (Besicovitch.SatelliteConfig E N τ))
    {t : ℝ≥0∞} (ht : t ≠ 0) {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ {x | t < maximalFunction μ f x}) :
    μ K ≤ ((N : ℝ≥0∞) / t) * ∫⁻ y, ‖f y‖ₑ ∂μ := by
  -- Package the bounded good radii on `K` over `↥K`.
  obtain ⟨R, hR, r, hr, hgoodavg⟩ :=
    exists_bounded_good_radii μ hf.locallyIntegrable hK (fun x hx => hKsub hx)
  let q : Besicovitch.BallPackage K E :=
    { c := fun x => x
      r := fun x => r x
      rpos := fun x => (hr x).1
      r_bound := R
      r_le := fun x => (hr x).2 }
  -- Apply the Besicovitch covering theorem.
  obtain ⟨s, hsdisj, hscover⟩ :=
    Besicovitch.exist_disjoint_covering_families hτ hN q
  -- Sum the good-ball estimates over the `Fin N` families.
  have hgoodopen : ∀ j : K, μ (Metric.ball (q.c j) (q.r j))
      ≤ t⁻¹ * ∫⁻ y in Metric.ball (q.c j) (q.r j), ‖f y‖ₑ ∂μ := by
    intro j
    have hc0 : μ (Metric.ball (q.c j) (q.r j)) ≠ 0 :=
      ne_of_gt (Metric.isOpen_ball.measure_pos μ
        (Metric.nonempty_ball.mpr (q.rpos j)))
    have hcfin : μ (Metric.ball (q.c j) (q.r j)) ≠ ∞ :=
      ne_top_of_le_ne_top (isCompact_closedBall _ _).measure_lt_top.ne
        (measure_mono Metric.ball_subset_closedBall)
    have hj : t * μ (Metric.ball (q.c j) (q.r j))
        < ∫⁻ y in Metric.ball (q.c j) (q.r j), ‖f y‖ₑ ∂μ := by
      have h := hgoodavg j
      simp only [ballAverage, laverage_eq, Measure.restrict_apply_univ] at h
      exact (ENNReal.lt_div_iff_mul_lt (Or.inl hc0) (Or.inl hcfin)).mp h
    by_cases htfin : t = ∞
    · have hμ0 : μ (Metric.ball (q.c j) (q.r j)) = 0 := by
        by_contra hne
        rw [htfin, ENNReal.top_mul hne] at hj
        exact not_lt_of_ge le_top hj
      rw [hμ0]
      exact bot_le
    · have hteq : μ (Metric.ball (q.c j) (q.r j))
          = t⁻¹ * (t * μ (Metric.ball (q.c j) (q.r j))) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel ht htfin, one_mul]
      rw [hteq]
      exact mul_le_mul' le_rfl hj.le
  have hdisjopen : ∀ i : Fin N, (s i).PairwiseDisjoint
      fun j => Metric.ball (q.c j) (q.r j) := by
    intro i a ha b hb hab
    exact Disjoint.mono Metric.ball_subset_closedBall
      Metric.ball_subset_closedBall ((hsdisj i) ha hb hab)
  have hcount : ∀ i : Fin N, (s i).Countable := fun i =>
    (hdisjopen i).countable_of_isOpen (fun j _ => Metric.isOpen_ball)
      (fun j _ => Metric.nonempty_ball.mpr (q.rpos j))
  have hfam : ∀ i : Fin N, ∑' j : s i, μ (Metric.ball (q.c j) (q.r j))
      ≤ t⁻¹ * ∫⁻ y, ‖f y‖ₑ ∂μ := by
    intro i
    have : Countable (s i) := (hcount i).to_subtype
    have hdisjsub : Pairwise (Disjoint on
        fun j : s i => Metric.ball (q.c j) (q.r j)) := by
      intro a b hab
      exact (hdisjopen i) a.property b.property
        (fun h => hab (Subtype.ext h))
    calc ∑' j : s i, μ (Metric.ball (q.c j) (q.r j))
        ≤ ∑' j : s i, (t⁻¹ * ∫⁻ y in Metric.ball (q.c j) (q.r j),
            ‖f y‖ₑ ∂μ) :=
          tsum_le_tsum fun j => hgoodopen j
      _ = t⁻¹ * ∑' j : s i, ∫⁻ y in Metric.ball (q.c j) (q.r j),
            ‖f y‖ₑ ∂μ := by
          rw [ENNReal.tsum_mul_left]
      _ = t⁻¹ * ∫⁻ y in ⋃ j : s i, Metric.ball (q.c j) (q.r j),
            ‖f y‖ₑ ∂μ := by
          rw [← lintegral_iUnion (fun j => measurableSet_ball) hdisjsub]
      _ ≤ t⁻¹ * ∫⁻ y, ‖f y‖ₑ ∂μ := by
          refine mul_le_mul' le_rfl ?_
          have hmono : ∫⁻ y in ⋃ j : s i, Metric.ball (q.c j) (q.r j),
                ‖f y‖ₑ ∂μ
              ≤ ∫⁻ y in (Set.univ : Set E), ‖f y‖ₑ ∂μ :=
            lintegral_mono_set (Set.subset_univ _)
          rwa [setLIntegral_univ] at hmono
  have hKr : Set.range q.c = K := by
    ext y
    constructor
    · rintro ⟨x, hx⟩
      rw [← hx]
      exact x.property
    · intro hy
      exact ⟨⟨y, hy⟩, rfl⟩
  have hcover : μ K ≤ ∑' i : Fin N, ∑' j : s i,
      μ (Metric.ball (q.c j) (q.r j)) := by
    calc μ K = μ (Set.range q.c) := by rw [hKr]
      _ ≤ μ (⋃ i, ⋃ j ∈ s i, Metric.ball (q.c j) (q.r j)) :=
          measure_mono hscover
      _ ≤ ∑' i : Fin N, μ (⋃ j ∈ s i, Metric.ball (q.c j) (q.r j)) :=
          measure_iUnion_le _
      _ ≤ ∑' i : Fin N, ∑' j : s i, μ (Metric.ball (q.c j) (q.r j)) :=
          tsum_le_tsum fun i => by
            have : Countable (s i) := (hcount i).to_subtype
            rw [Set.biUnion_eq_iUnion]
            exact measure_iUnion_le _
  calc μ K ≤ ∑' i : Fin N, (t⁻¹ * ∫⁻ y, ‖f y‖ₑ ∂μ) :=
        hcover.trans (tsum_le_tsum fun i => hfam i)
    _ = ((N : ℝ≥0∞) / t) * ∫⁻ y, ‖f y‖ₑ ∂μ := by
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, div_eq_mul_inv, mul_assoc]

/-- The Hardy–Littlewood maximal operator is of weak type (1,1):
there is a constant `C` (the Besicovitch constant of `E`) such that
for every integrable `f` and every `t ≠ 0`,
`μ {x | t < maximalFunction μ f x} ≤ (C / t) * ∫⁻ y, ‖f y‖ₑ ∂μ`. -/
theorem weakType_one_one (μ : Measure E)
    [MeasureTheory.Measure.IsAddHaarMeasure μ] {f : E → F}
    (hf : Integrable f μ) :
    ∃ C : ℝ≥0∞, ∀ t : ℝ≥0∞, t ≠ 0 →
      μ {x | t < maximalFunction μ f x} ≤ (C / t) * ∫⁻ y, ‖f y‖ₑ ∂μ := by
  -- Unpack the Besicovitch constant.
  obtain ⟨N, τ, hτ, hN⟩ := HasBesicovitchCovering.no_satelliteConfig (α := E)
  refine ⟨N, fun t ht => ?_⟩
  -- Measurability and inner regularity reduce to compact subsets.
  have hmeas : MeasurableSet {x | t < maximalFunction μ f x} :=
    (measurable_maximalFunction μ hf.locallyIntegrable) measurableSet_Ioi
  rw [hmeas.measure_eq_iSup_isCompact μ]
  refine iSup_le fun K => iSup_le fun hKsub => iSup_le fun hK => ?_
  exact measure_isCompact_subset_levelSet_le μ hf hτ hN ht hK hKsub


omit [BorelSpace E] [NormedSpace ℝ F] in
/-- The maximal function of an a.e.-bounded function is bounded by the same
constant, at *every* point: a single null set works for all balls at once. -/
theorem maximalFunction_le_of_ae_enorm_le {μ : Measure E}
    [MeasureTheory.Measure.IsAddHaarMeasure μ] {f : E → F} {C : ℝ≥0∞}
    (hf : ∀ᵐ y ∂μ, ‖f y‖ₑ ≤ C) (x : E) :
    maximalFunction μ f x ≤ C := by
  rw [maximalFunction_eq_iSup_ballAverage]
  refine iSup_le fun r => iSup_le fun hr => ?_
  have hpos : 0 < μ (Metric.ball x r) :=
    Metric.isOpen_ball.measure_pos μ (Metric.nonempty_ball.mpr hr)
  have hfin : μ (Metric.ball x r) < ∞ :=
    lt_of_le_of_lt (measure_mono Metric.ball_subset_closedBall)
      (isCompact_closedBall x r).measure_lt_top
  have hInt : ∫⁻ y in Metric.ball x r, ‖f y‖ₑ ∂μ ≤ C * μ (Metric.ball x r) := by
    calc ∫⁻ y in Metric.ball x r, ‖f y‖ₑ ∂μ
        ≤ ∫⁻ _y in Metric.ball x r, C ∂μ :=
          lintegral_mono_ae ((hf.filter_mono ae_restrict_le).mono fun _y hy => hy)
      _ = C * μ (Metric.ball x r) := setLIntegral_const _ _
  rw [ballAverage, setLAverage_eq, ENNReal.div_le_iff hpos.ne' hfin.ne]
  exact hInt

omit [BorelSpace E] [NormedSpace ℝ F] in
/-- The maximal function is bounded by the essential supremum of `‖f‖ₑ`. -/
theorem maximalFunction_le_essSup {μ : Measure E}
    [MeasureTheory.Measure.IsAddHaarMeasure μ] {f : E → F}
    (_hf : MemLp f ∞ μ) (x : E) :
    maximalFunction μ f x ≤ essSup (fun y => ‖f y‖ₑ) μ :=
  maximalFunction_le_of_ae_enorm_le (ENNReal.ae_le_essSup _) x


/-- The distribution-function bound behind strong type: for `f ∈ L^p`,
the level set of the maximal function is controlled by the `L^1` mass of
the part of `f` above half the height. The constant is twice the
Besicovitch constant, from applying weak type `(1,1)` to that part. -/
theorem measure_levelSet_le_rpow (μ : Measure E)
    [MeasureTheory.Measure.IsAddHaarMeasure μ] {f : E → F} {p : ℝ} (hp : 1 < p)
    (hf : StronglyMeasurable f)
    (hfLp : ∫⁻ y, ‖f y‖ₑ ^ p ∂μ < ∞) :
    ∃ C : ℝ≥0∞, ∀ t : ℝ≥0∞, t ≠ 0 →
      μ {x | t < maximalFunction μ f x} ≤
        (C / t) * ∫⁻ y in {y | t / 2 < ‖f y‖ₑ}, ‖f y‖ₑ ∂μ := by
  obtain ⟨N, τ, hτ, hN⟩ := HasBesicovitchCovering.no_satelliteConfig (α := E)
  refine ⟨2 * (N : ℝ≥0∞), fun t ht => ?_⟩
  have hhalf : ∀ a : ℝ≥0∞, a / 2 + a / 2 = a := by
    intro a
    rw [ENNReal.div_add_div_same, ← two_mul, ENNReal.div_eq_inv_mul, ← mul_assoc,
      ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
  by_cases ht_top : t = ∞
  · subst ht_top
    have hempty : {x | (∞ : ℝ≥0∞) < maximalFunction μ f x} = ∅ :=
      Set.eq_empty_of_forall_notMem fun x hx => by
        have hx' : (∞ : ℝ≥0∞) < maximalFunction μ f x := hx
        exact not_lt.mpr (le_top : maximalFunction μ f x ≤ ∞) hx'
    rw [hempty]
    simp
  -- The split of `f` at height `t / 2`.
  set s : Set E := {y | t / 2 < ‖f y‖ₑ} with hs_def
  have hs : MeasurableSet s := hf.eNorm measurableSet_Ioi
  set f₁ : E → F := s.indicator f with hf₁_def
  set f₂ : E → F := f - f₁ with hf₂_def
  have hsum : f₁ + f₂ = f := by
    funext y
    by_cases hy : y ∈ s <;> simp [hf₁_def, hf₂_def, Set.indicator_of_mem,
      Set.indicator_of_notMem, hy]
  have hf₁SM : StronglyMeasurable f₁ := hf.indicator hs
  have ht2 : t / 2 ≠ 0 := by
    intro h
    exact ht (by rw [← hhalf t, h, add_zero])
  have ht2fin : t / 2 < ∞ :=
    (ENNReal.half_lt_self ht ht_top).trans (lt_top_iff_ne_top.mpr ht_top)
  -- `B4` applied to the small part: `M f₂ ≤ t / 2` everywhere.
  have hf₂_le : ∀ x, maximalFunction μ f₂ x ≤ t / 2 := by
    intro x
    apply maximalFunction_le_of_ae_enorm_le (μ := μ) _ x
    refine Filter.Eventually.of_forall fun y => ?_
    by_cases hy : y ∈ s
    · have h0 : f₂ y = 0 := by
        simp [hf₂_def, hf₁_def, Set.indicator_of_mem hy]
      rw [h0]
      simp
    · have hfy : f₂ y = f y := by
        simp [hf₂_def, hf₁_def, Set.indicator_of_notMem hy]
      rw [hfy]
      exact le_of_not_gt hy
  -- The level-set inclusion, pointwise.
  have hsub : {x | t < maximalFunction μ f x} ⊆
      {x | t / 2 < maximalFunction μ f₁ x} := by
    intro x hx
    by_contra hcon
    have hcon' : maximalFunction μ f₁ x ≤ t / 2 := le_of_not_gt hcon
    have h1 : maximalFunction μ f x ≤ t := by
      calc maximalFunction μ f x = maximalFunction μ (f₁ + f₂) x := by rw [hsum]
        _ ≤ maximalFunction μ f₁ x + maximalFunction μ f₂ x :=
          maximalFunction_add_le μ hf₁SM.aestronglyMeasurable x
        _ ≤ t / 2 + t / 2 := add_le_add hcon' (hf₂_le x)
        _ = t := hhalf t
    exact (not_lt.mpr h1) hx
  -- The large part is integrable: on `s`, `‖f‖ₑ ≤ ‖f‖ₑ ^ p / (t / 2) ^ (p - 1)`.
  have hf₁_int : Integrable f₁ μ := by
    refine ⟨hf₁SM.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_eNorm]
    have hne0 : (t / 2) ^ (p - 1) ≠ 0 :=
      (ENNReal.rpow_pos (pos_iff_ne_zero.mpr ht2) ht2fin.ne).ne'
    have hneTop : (t / 2) ^ (p - 1) ≠ ∞ :=
      (ENNReal.rpow_lt_top_of_nonneg (by linarith) ht2fin.ne).ne
    have hpt : ∀ y, ‖f₁ y‖ₑ ≤ ‖f y‖ₑ ^ p / (t / 2) ^ (p - 1) := by
      intro y
      by_cases hy : y ∈ s
      · have hfy : ‖f₁ y‖ₑ = ‖f y‖ₑ := by
          simp [hf₁_def, Set.indicator_of_mem hy]
        rw [hfy]
        have ha : t / 2 < ‖f y‖ₑ := hy
        have ha0 : ‖f y‖ₑ ≠ 0 :=
          ne_of_gt (lt_trans (pos_iff_ne_zero.mpr ht2) ha)
        by_cases ha_top : ‖f y‖ₑ = ∞
        · rw [ha_top]
          have hfin : (t / 2) ^ (p - 1) ≠ ∞ :=
            (ENNReal.rpow_lt_top_of_nonneg (by linarith) ht2fin.ne).ne
          simp [ENNReal.top_rpow_of_pos (by linarith : (0 : ℝ) < p), hfin]
        · have hle : (t / 2) ^ (p - 1) ≤ ‖f y‖ₑ ^ (p - 1) :=
            ENNReal.rpow_le_rpow ha.le (by linarith)
          have hsplit : ‖f y‖ₑ ^ p = ‖f y‖ₑ ^ (p - 1) * ‖f y‖ₑ := by
            conv_lhs => rw [← sub_add_cancel p 1]
            rw [ENNReal.rpow_add (p - 1) 1 ha0 ha_top, ENNReal.rpow_one]
          rw [hsplit, ENNReal.le_div_iff_mul_le (Or.inl hne0) (Or.inl hneTop),
            mul_comm (‖f y‖ₑ ^ (p - 1)) (‖f y‖ₑ)]
          gcongr
      · have hfy : ‖f₁ y‖ₑ = 0 := by
          simp [hf₁_def, Set.indicator_of_notMem hy]
        rw [hfy]
        exact zero_le
    calc ∫⁻ y, ‖f₁ y‖ₑ ∂μ ≤ ∫⁻ y, ‖f y‖ₑ ^ p / (t / 2) ^ (p - 1) ∂μ :=
          lintegral_mono hpt
      _ = ((t / 2) ^ (p - 1))⁻¹ * ∫⁻ y, ‖f y‖ₑ ^ p ∂μ := by
          rw [lintegral_congr_ae (Filter.Eventually.of_forall fun y =>
              ENNReal.div_eq_inv_mul),
            lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hne0)]
      _ < ∞ :=
          ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr hne0)) hfLp
  -- Weak type `(1,1)` for `f₁` at height `t / 2`, with the explicit constant.
  have hmeas₁ : MeasurableSet {x | t / 2 < maximalFunction μ f₁ x} :=
    (measurable_maximalFunction μ hf₁_int.locallyIntegrable) measurableSet_Ioi
  have hcore : μ {x | t / 2 < maximalFunction μ f₁ x} ≤
      ((N : ℝ≥0∞) / (t / 2)) * ∫⁻ y, ‖f₁ y‖ₑ ∂μ := by
    rw [hmeas₁.measure_eq_iSup_isCompact μ]
    refine iSup_le fun K => iSup_le fun hKsub => iSup_le fun hK => ?_
    exact measure_isCompact_subset_levelSet_le μ hf₁_int hτ hN ht2 hK hKsub
  have hInt₁ : ∫⁻ y, ‖f₁ y‖ₑ ∂μ = ∫⁻ y in s, ‖f y‖ₑ ∂μ := by
    have hfun : (fun y => ‖f₁ y‖ₑ) = s.indicator (fun y => ‖f y‖ₑ) := by
      funext y
      by_cases hy : y ∈ s <;> simp [hf₁_def, Set.indicator_of_mem,
        Set.indicator_of_notMem, hy]
    rw [hfun, lintegral_indicator hs]
  have hN2 : (N : ℝ≥0∞) / (t / 2) = 2 * (N : ℝ≥0∞) / t := by
    conv_lhs => rw [ENNReal.div_eq_inv_mul, ENNReal.inv_div (Or.inr ht_top) (Or.inr ht),
      ENNReal.div_eq_inv_mul]
    rw [ENNReal.div_eq_inv_mul]
    exact mul_assoc _ _ _
  calc μ {x | t < maximalFunction μ f x}
      ≤ μ {x | t / 2 < maximalFunction μ f₁ x} := measure_mono hsub
    _ ≤ ((N : ℝ≥0∞) / (t / 2)) * ∫⁻ y, ‖f₁ y‖ₑ ∂μ := hcore
    _ = (2 * (N : ℝ≥0∞) / t) * ∫⁻ y in s, ‖f y‖ₑ ∂μ := by rw [hN2, hInt₁]


/-- The Tonelli step of the strong-type proof: the layer-cake integral of
the distribution bound, with the order of integration swapped. The inner
integral `∫₀^{2‖g y‖ₑ} t ^ (p - 2) dt = (2‖g y‖ₑ) ^ (p - 1) / (p - 1)`
produces the factor `2 ^ (p - 1) / (p - 1)`; together with the `2` in the
distribution bound's constant this gives the overall `2 ^ p`. -/
theorem strongType (μ : Measure E)
    [MeasureTheory.Measure.IsAddHaarMeasure μ] {f : E → F} {p : ℝ} (hp : 1 < p)
    (hf : MemLp f (.ofReal p) μ) :
    ∃ C : ℝ≥0∞, ∫⁻ x, (maximalFunction μ f x) ^ p ∂μ ≤
      C * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
  -- Work with a strongly measurable representative of `f`.
  obtain ⟨g, hgSM, hfg⟩ := hf.aestronglyMeasurable
  have hfMg : MemLp g (.ofReal p) μ := by
    have hf' : eLpNorm f (.ofReal p) μ < ∞ := memLp_iff.mp hf
    rwa [eLpNorm_congr_ae hfg] at hf'
  have hloc : LocallyIntegrable g μ := hfMg.locallyIntegrable (by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith))
  have hge : Measurable fun y => ‖g y‖ₑ := hgSM.eNorm
  have hmeasMg : Measurable (maximalFunction μ g) := measurable_maximalFunction μ hloc
  have hfLp : ∫⁻ y, ‖g y‖ₑ ^ p ∂μ < ∞ := by
    have h := lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top
      (p := ENNReal.ofReal p) (f := g) (μ := μ)
      ((ENNReal.ofReal_pos.mpr (by linarith : (0 : ℝ) < p)).ne')
      ENNReal.ofReal_ne_top hfMg.eLpNorm_lt_top
    rwa [ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ p)] at h
  obtain ⟨C₁, hC₁⟩ := measure_levelSet_le_rpow μ hp hgSM hfLp
  have hge' : AEMeasurable (fun y => ‖g y‖ₑ ^ p) μ := by fun_prop
  -- The distribution bound, integrated against the layer-cake density.
  have hTon : ∫⁻ t in Set.Ioi 0, μ {a | ENNReal.ofReal t < maximalFunction μ g a} *
        ENNReal.ofReal (p * t ^ (p - 1)) ∂volume ≤
      (C₁ * ENNReal.ofReal p * 2 ^ (p - 1) / ENNReal.ofReal (p - 1)) *
        ∫⁻ y, ‖g y‖ₑ ^ p ∂μ := by
    have step1 : ∫⁻ t in Set.Ioi 0, μ {a | ENNReal.ofReal t < maximalFunction μ g a} *
          ENNReal.ofReal (p * t ^ (p - 1)) ∂volume ≤
        ∫⁻ t in Set.Ioi 0, (C₁ / ENNReal.ofReal t) * ENNReal.ofReal (p * t ^ (p - 1)) *
          ∫⁻ y in {y | ENNReal.ofReal t / 2 < ‖g y‖ₑ}, ‖g y‖ₑ ∂μ ∂volume := by
      refine lintegral_mono_ae ?_
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall fun t ht => ?_
      have ht0 : (0 : ℝ) < t := ht
      have h := hC₁ (ENNReal.ofReal t) (ENNReal.ofReal_pos.mpr ht0).ne'
      calc μ {a | ENNReal.ofReal t < maximalFunction μ g a} *
            ENNReal.ofReal (p * t ^ (p - 1))
          ≤ ((C₁ / ENNReal.ofReal t) *
              ∫⁻ y in {y | ENNReal.ofReal t / 2 < ‖g y‖ₑ}, ‖g y‖ₑ ∂μ) *
              ENNReal.ofReal (p * t ^ (p - 1)) := mul_le_mul_left h _
        _ = (C₁ / ENNReal.ofReal t) * ENNReal.ofReal (p * t ^ (p - 1)) *
              ∫⁻ y in {y | ENNReal.ofReal t / 2 < ‖g y‖ₑ}, ‖g y‖ₑ ∂μ := by ring
    refine step1.trans ?_
    -- The inner integral over `y`, for fixed `t`, evaluated after the swap.
    have hinner : ∀ y, ∫⁻ t in Set.Ioi 0, (C₁ / ENNReal.ofReal t) *
          ENNReal.ofReal (p * t ^ (p - 1)) *
          ({y' | ENNReal.ofReal t / 2 < ‖g y'‖ₑ}.indicator (fun y' => ‖g y'‖ₑ)) y
          ∂volume =
        (C₁ * ENNReal.ofReal p * 2 ^ (p - 1) / ENNReal.ofReal (p - 1)) * ‖g y‖ₑ ^ p := by
      intro y
      set a : ℝ≥0∞ := ‖g y‖ₑ with ha_def
      have ha_top : a ≠ ∞ := eNorm_ne_top
      have hsupp : ∀ t : ℝ, 0 < t →
          (C₁ / ENNReal.ofReal t) * ENNReal.ofReal (p * t ^ (p - 1)) *
              ({y' | ENNReal.ofReal t / 2 < ‖g y'‖ₑ}.indicator (fun y' => ‖g y'‖ₑ)) y =
            (Set.Ioo 0 ((2 * a).toReal)).indicator
              (fun t => C₁ * ENNReal.ofReal p * a * ENNReal.ofReal (t ^ (p - 2))) t := by
        intro t ht
        have hT0 : ENNReal.ofReal t ≠ 0 := (ENNReal.ofReal_pos.mpr ht).ne'
        have hTtop : ENNReal.ofReal t ≠ ∞ := ENNReal.ofReal_ne_top
        by_cases hcase : ENNReal.ofReal t / 2 < a
        · have ht2 : t < (2 * a).toReal :=
            (ENNReal.ofReal_lt_iff_lt_toReal ht.le (by finiteness)).mp (by
              have h2 : ENNReal.ofReal t / 2 < a := hcase
              rw [ENNReal.div_lt_iff (Or.inr hT0) (Or.inr hTtop)] at h2
              rwa [mul_comm] at h2)
          rw [Set.indicator_of_mem hcase,
            Set.indicator_of_mem (Set.mem_Ioo.mpr ⟨ht, ht2⟩)]
          have e1 : ENNReal.ofReal (p * t ^ (p - 1)) =
              ENNReal.ofReal p * (ENNReal.ofReal t) ^ (p - 1) := by
            rw [ENNReal.ofReal_mul (by linarith),
              ENNReal.ofReal_rpow_of_pos ht]
          have e2 : (ENNReal.ofReal t)⁻¹ * (ENNReal.ofReal t) ^ (p - 1) =
              (ENNReal.ofReal t) ^ (p - 2) := by
            have h := ENNReal.rpow_sub (p - 1) 1 hT0 hTtop (x := ENNReal.ofReal t)
            rw [ENNReal.rpow_one, ENNReal.div_eq_inv_mul,
              show (p - 1) - 1 = p - 2 by ring] at h
            exact h.symm
          calc (C₁ / ENNReal.ofReal t) * ENNReal.ofReal (p * t ^ (p - 1)) * a
              = C₁ * ENNReal.ofReal p * a *
                  ((ENNReal.ofReal t)⁻¹ * (ENNReal.ofReal t) ^ (p - 1)) := by
                rw [e1, ENNReal.div_eq_inv_mul]; ring
            _ = C₁ * ENNReal.ofReal p * a * (ENNReal.ofReal t) ^ (p - 2) := by
                rw [e2]
            _ = C₁ * ENNReal.ofReal p * a * ENNReal.ofReal (t ^ (p - 2)) := by
                rw [ENNReal.ofReal_rpow_of_pos ht]
        · have ht2 : ¬ t < (2 * a).toReal := by
            intro hlt
            apply hcase
            have h1 : ENNReal.ofReal t < 2 * a :=
              (ENNReal.ofReal_lt_iff_lt_toReal ht.le (by finiteness)).mpr hlt
            rw [ENNReal.div_lt_iff (Or.inr hT0) (Or.inr hTtop), mul_comm]
            exact h1
          rw [Set.indicator_of_notMem hcase,
            Set.indicator_of_notMem (fun h => ht2 (Set.mem_Ioo.mp h).2), mul_zero]
      have hIntForm : ∫⁻ t in Set.Ioi 0, (C₁ / ENNReal.ofReal t) *
            ENNReal.ofReal (p * t ^ (p - 1)) *
            ({y' | ENNReal.ofReal t / 2 < ‖g y'‖ₑ}.indicator (fun y' => ‖g y'‖ₑ)) y
            ∂volume =
          ∫⁻ t in Set.Ioo 0 ((2 * a).toReal), C₁ * ENNReal.ofReal p * a *
            ENNReal.ofReal (t ^ (p - 2)) ∂volume := by
        rw [← lintegral_indicator measurableSet_Ioi,
          ← lintegral_indicator measurableSet_Ioo]
        refine lintegral_congr fun t => ?_
        by_cases ht : t ∈ Set.Ioi (0 : ℝ)
        · rw [Set.indicator_of_mem ht]
          exact hsupp t ht
        · have ht0 : t ∉ Set.Ioo 0 ((2 * a).toReal) := fun h => ht h.1
          rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht0]
      rw [hIntForm]
      have hIntReal : ∫⁻ t in Set.Ioo 0 ((2 * a).toReal), C₁ * ENNReal.ofReal p * a *
            ENNReal.ofReal (t ^ (p - 2)) ∂volume =
          (C₁ * ENNReal.ofReal p * a) *
            ENNReal.ofReal ((2 * a).toReal ^ (p - 1) / (p - 1)) := by
        rw [lintegral_const_mul'' (C₁ * ENNReal.ofReal p * a)
          (by fun_prop : AEMeasurable (fun t => ENNReal.ofReal (t ^ (p - 2)))
            (volume.restrict (Set.Ioo 0 ((2 * a).toReal))))]
        congr 1
        rw [← ofReal_integral_eq_lintegral_ofReal]
        · congr 1
          have hrw : p - 2 + 1 = p - 1 := by ring
          rw [← integral_Ioc_eq_integral_Ioo,
            ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ (2 * a).toReal),
            integral_rpow (Or.inl (by linarith : (-1 : ℝ) < p - 2)), hrw,
            Real.zero_rpow (by linarith : (p - 1) ≠ 0), sub_zero]
        · exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le
            ENNReal.toReal_nonneg).mp
            (intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < p - 2))).mono_set
            Set.Ioo_subset_Ioc_self
        · exact (ae_restrict_iff' measurableSet_Ioo).mpr
            (Filter.Eventually.of_forall fun t ht => Real.rpow_nonneg ht.1.le _)
      rw [hIntReal]
      have e3 : ENNReal.ofReal ((2 * a).toReal ^ (p - 1) / (p - 1)) =
          (2 ^ (p - 1) * a ^ (p - 1)) * (ENNReal.ofReal (p - 1))⁻¹ := by
        rw [div_eq_inv_mul,
          ENNReal.ofReal_mul (inv_nonneg.mpr (by linarith : (0 : ℝ) ≤ p - 1)),
          ENNReal.ofReal_inv_of_pos (by linarith : (0 : ℝ) < p - 1),
          ← ENNReal.ofReal_rpow_of_nonneg
            (ENNReal.toReal_nonneg (a := 2 * a)) (by linarith : (0 : ℝ) ≤ p - 1),
          ENNReal.ofReal_toReal (show (2 * a) ≠ ∞ by finiteness),
          ENNReal.mul_rpow_of_nonneg _ _ (by linarith : (0 : ℝ) ≤ p - 1)]
        ring
      rw [e3]
      have e4 : a * a ^ (p - 1) = a ^ p := by
        by_cases ha0 : a = 0
        · simp [ha0, ENNReal.zero_rpow_of_pos (by linarith : (0 : ℝ) < p - 1),
            ENNReal.zero_rpow_of_pos (by linarith : (0 : ℝ) < p)]
        · nth_rewrite 1 [← ENNReal.rpow_one a]
          rw [← ENNReal.rpow_add 1 (p - 1) ha0 ha_top,
            show (1 : ℝ) + (p - 1) = p by ring]
      rw [ENNReal.div_eq_inv_mul, ← e4]
      ring
    -- Assemble: indicator form, swap, inner integral, pull the constant out.
    have step2 : ∀ t : ℝ,
        ∫⁻ y in {y | ENNReal.ofReal t / 2 < ‖g y‖ₑ}, ‖g y‖ₑ ∂μ =
        ∫⁻ y, ({y | ENNReal.ofReal t / 2 < ‖g y‖ₑ}.indicator
          (fun y => ‖g y‖ₑ)) y ∂μ :=
      fun t => (lintegral_indicator (hge measurableSet_Ioi) (fun y => ‖g y‖ₑ)).symm
    calc ∫⁻ t in Set.Ioi 0, (C₁ / ENNReal.ofReal t) * ENNReal.ofReal (p * t ^ (p - 1)) *
            ∫⁻ y in {y | ENNReal.ofReal t / 2 < ‖g y‖ₑ}, ‖g y‖ₑ ∂μ ∂volume
        = ∫⁻ t in Set.Ioi 0, (C₁ / ENNReal.ofReal t) * ENNReal.ofReal (p * t ^ (p - 1)) *
            ∫⁻ y, ({y | ENNReal.ofReal t / 2 < ‖g y‖ₑ}.indicator
              (fun y => ‖g y‖ₑ)) y ∂μ ∂volume :=
          lintegral_congr fun t => by rw [step2 t]
      _ = ∫⁻ y, ∫⁻ t in Set.Ioi 0, (C₁ / ENNReal.ofReal t) *
            ENNReal.ofReal (p * t ^ (p - 1)) *
            ({y | ENNReal.ofReal t / 2 < ‖g y‖ₑ}.indicator (fun y => ‖g y‖ₑ)) y
            ∂volume ∂μ := by
          have h1 : ∀ t : ℝ, (C₁ / ENNReal.ofReal t) * ENNReal.ofReal (p * t ^ (p - 1)) *
                ∫⁻ y, ({y | ENNReal.ofReal t / 2 < ‖g y‖ₑ}.indicator
                  (fun y => ‖g y‖ₑ)) y ∂μ =
              ∫⁻ y, (C₁ / ENNReal.ofReal t) * ENNReal.ofReal (p * t ^ (p - 1)) *
                ({y | ENNReal.ofReal t / 2 < ‖g y‖ₑ}.indicator (fun y => ‖g y‖ₑ)) y
                ∂μ :=
            fun t => (lintegral_const_mul'' _
              (Measurable.indicator hge (hge measurableSet_Ioi)).aemeasurable).symm
          rw [lintegral_congr h1]
          have hK : Measurable fun t : ℝ => (C₁ / ENNReal.ofReal t) *
              ENNReal.ofReal (p * t ^ (p - 1)) :=
            (measurable_const.div ENNReal.measurable_ofReal).mul
              (ENNReal.measurable_ofReal.comp
                (measurable_const.mul (by fun_prop : Measurable fun t : ℝ => t ^ (p - 1))))
          have hsetM : MeasurableSet
              {q : ℝ × E | ENNReal.ofReal q.1 / 2 < ‖g q.2‖ₑ} :=
            measurableSet_lt ((ENNReal.measurable_ofReal.comp measurable_fst).div_const 2)
              (hge.comp measurable_snd)
          have hJoint : Measurable fun q : ℝ × E =>
              (C₁ / ENNReal.ofReal q.1) * ENNReal.ofReal (p * q.1 ^ (p - 1)) *
                ({q : ℝ × E | ENNReal.ofReal q.1 / 2 < ‖g q.2‖ₑ}.indicator
                  (fun q => ‖g q.2‖ₑ)) q :=
            (hK.comp measurable_fst).mul
              (Measurable.indicator (hge.comp measurable_snd) hsetM)
          exact lintegral_lintegral_swap (μ := volume.restrict (Set.Ioi 0)) (ν := μ)
            hJoint.aemeasurable
      _ = ∫⁻ y, (C₁ * ENNReal.ofReal p * 2 ^ (p - 1) / ENNReal.ofReal (p - 1)) *
            ‖g y‖ₑ ^ p ∂μ := lintegral_congr hinner
      _ ≤ (C₁ * ENNReal.ofReal p * 2 ^ (p - 1) / ENNReal.ofReal (p - 1)) *
            ∫⁻ y, ‖g y‖ₑ ^ p ∂μ := le_of_eq (lintegral_const_mul'' _ hge')
  refine ⟨C₁ * ENNReal.ofReal p * 2 ^ (p - 1) / ENNReal.ofReal (p - 1), ?_⟩
  have hInt : ∫⁻ x, ‖f x‖ₑ ^ p ∂μ = ∫⁻ x, ‖g x‖ₑ ^ p ∂μ :=
    lintegral_congr_ae (hfg.mono fun x hx => congrArg (fun z => ‖z‖ₑ ^ p) hx)
  rw [maximalFunction_congr_ae hfg, hInt]
  -- Truncate the maximal function and pass to the supremum over `n`.
  have hpt : ∀ x, (maximalFunction μ g x) ^ p =
      ⨆ n : ℕ, (min (maximalFunction μ g x) (n : ℝ≥0∞)) ^ p := by
    intro x
    apply le_antisymm
    · by_cases hx : maximalFunction μ g x = ∞
      · rw [hx, ENNReal.top_rpow_of_pos (by linarith : (0 : ℝ) < p)]
        by_contra hlt
        obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt (not_le.mp hlt).ne
        have hle : (m : ℝ≥0∞) ≤
            ⨆ n : ℕ, (min (∞ : ℝ≥0∞) (n : ℝ≥0∞)) ^ p :=
          le_iSup_of_le (m + 1) (by
            calc (m : ℝ≥0∞) ≤ ((m + 1 : ℕ) : ℝ≥0∞) := by
                  exact_mod_cast Nat.le_succ m
              _ = (((m + 1 : ℕ) : ℝ≥0∞)) ^ (1 : ℝ) := (ENNReal.rpow_one _).symm
              _ ≤ (((m + 1 : ℕ) : ℝ≥0∞)) ^ p :=
                  ENNReal.rpow_le_rpow_of_exponent_le
                    (show (1 : ℝ≥0∞) ≤ ((m + 1 : ℕ) : ℝ≥0∞) by
                      exact_mod_cast Nat.le_add_left 1 m) (by linarith)
              _ = (min (∞ : ℝ≥0∞) ((m + 1 : ℕ) : ℝ≥0∞)) ^ p := by
                  rw [min_eq_right le_top])
        exact lt_irrefl _ (lt_of_le_of_lt hle hm)
      · obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hx
        exact le_iSup_of_le N (by rw [min_eq_left hN.le])
    · refine iSup_le fun n => ENNReal.rpow_le_rpow (min_le_left _ _) (by linarith)
  have hsup : ∫⁻ x, (maximalFunction μ g x) ^ p ∂μ =
      ⨆ n : ℕ, ∫⁻ x, (min (maximalFunction μ g x) (n : ℝ≥0∞)) ^ p ∂μ := by
    rw [lintegral_congr hpt]
    exact lintegral_iSup (fun n => by fun_prop)
      (fun i j hij x => ENNReal.rpow_le_rpow
        (min_le_min le_rfl (by exact_mod_cast hij)) (by linarith))
  rw [hsup]
  refine iSup_le fun n => ?_
  have hfin_n : ∀ x, min (maximalFunction μ g x) (n : ℝ≥0∞) ≠ ∞ :=
    fun x => ne_top_of_le_ne_top (ENNReal.natCast_ne_top n)
      (min_le_right (maximalFunction μ g x) (n : ℝ≥0∞))
  have key := lintegral_comp_eq_lintegral_meas_lt_mul μ
    (f := fun x => (min (maximalFunction μ g x) (n : ℝ≥0∞)).toReal)
    (g := fun t => p * t ^ (p - 1))
    (Filter.Eventually.of_forall fun x => ENNReal.toReal_nonneg)
    ((hmeasMg.min measurable_const).ennreal_toReal).aemeasurable
    (fun t _ht => IntervalIntegrable.const_mul
      (intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < p - 1)) p)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using
      mul_nonneg (by linarith) (Real.rpow_nonneg ht.le _))
  have hinnerInt : ∀ ω, (∫ t in 0..((min (maximalFunction μ g ω) (n : ℝ≥0∞)).toReal),
        p * t ^ (p - 1)) =
      ((min (maximalFunction μ g ω) (n : ℝ≥0∞)).toReal) ^ p := by
    intro ω
    rw [intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by linarith : (-1 : ℝ) < p - 1)),
      Real.zero_rpow (by linarith : p - 1 + 1 ≠ 0), sub_zero,
      show p - 1 + 1 = p by ring]
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    field_simp
  rw [lintegral_congr_ae (Filter.Eventually.of_forall fun ω => by
    rw [hinnerInt ω,
      ← ENNReal.ofReal_rpow_of_nonneg
        (ENNReal.toReal_nonneg (a := min (maximalFunction μ g ω) (n : ℝ≥0∞)))
        (by linarith : (0 : ℝ) ≤ p),
      ENNReal.ofReal_toReal (hfin_n ω)])] at key
  refine key.le.trans ?_
  refine (lintegral_mono_ae ?_).trans hTon
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Filter.Eventually.of_forall fun t ht => ?_
  have ht0 : (0 : ℝ) < t := ht
  have hset : {a | t < (min (maximalFunction μ g a) (n : ℝ≥0∞)).toReal} =
      {a | ENNReal.ofReal t < min (maximalFunction μ g a) (n : ℝ≥0∞)} := by
    ext a
    simp only [Set.mem_ofPred_eq]
    exact (ENNReal.ofReal_lt_iff_lt_toReal ht0.le (hfin_n a)).symm
  rw [hset]
  refine mul_le_mul_left ?_ _
  apply measure_mono
  intro a ha
  have ha' : ENNReal.ofReal t < min (maximalFunction μ g a) (n : ℝ≥0∞) := ha
  exact lt_of_lt_of_le ha' (min_le_left _ _)

/-- The strong-type bound in `eLpNorm` form: the conversion is `rpow`
algebra, `(∫⁻ (Mf) ^ p) ^ (1 / p) ≤ (C ∫⁻ ‖f‖ₑ ^ p) ^ (1 / p)`, and
`‖Mf‖ₑ = Mf` since the maximal function is `ℝ≥0∞`-valued. -/
theorem eLpNorm_maximalFunction_le (μ : Measure E)
    [MeasureTheory.Measure.IsAddHaarMeasure μ] {f : E → F} {p : ℝ} (hp : 1 < p)
    (hf : MemLp f (.ofReal p) μ) :
    ∃ C : ℝ≥0∞, eLpNorm (maximalFunction μ f) (.ofReal p) μ ≤
      C * eLpNorm f (.ofReal p) μ := by
  obtain ⟨C, hC⟩ := strongType μ hp hf
  refine ⟨C ^ (1 / p), ?_⟩
  have hp0 : ENNReal.ofReal p ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (by linarith : (0 : ℝ) < p)).ne'
  have hMf : AEStronglyMeasurable (maximalFunction μ f) μ :=
    (measurable_maximalFunction μ (hf.locallyIntegrable (by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by linarith)))).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 ENNReal.ofReal_ne_top hMf,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 ENNReal.ofReal_ne_top
      hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ p)]
  simp only [eNorm_eq_self]
  have h := ENNReal.rpow_le_rpow hC (by positivity : (0 : ℝ) ≤ 1 / p)
  rwa [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / p)] at h

end MeasureTheory
