/-
Copyright (c) 2026 B. J. Ridenhour. Released under Apache 2.0 license as described in the file LICENSE.

# Basin of attraction (Section 3): Theorem 3.1

In the paper, `E_{c,x̄}` is the component of `O_{c,x̄} = {x̄} ∪ {c < f < M}` containing `x̄`.
We first prove the theorem (`basin`) for any set `U` with the properties of `E_{c,x̄}` that the
proof uses:
* `U` is open and contains `x̄`;
* `c < f` on `U` and `f < f x̄` on `U \ {x̄}` (because `U ⊆ O_{c,x̄}`);
* **H4**: `closure U` is compact and lies in the domain where `f` has the continuous gradient `g`;
* **H5**: `f = c` on `frontier U`;
* **H6**: `g ≠ 0` on `closure U \ {x̄}`;
* **H3**: the eigenvalue condition (EC).
H1 and H2 at `x̄` follow from these, so they are not listed separately.

We then prove that `O_{c,x̄}` is open (`isOpen_Oc`), define `E_{c,x̄}` as its connected component
containing `x̄` (`Ec`), and deduce the paper's statement for `E_{c,x̄}` itself (`basin_Ec`).
-/
import ContinuousStability.Stability
import Mathlib.Topology.Algebra.Module.LocallyConvex

open scoped RealInnerProductSpace Topology
open Set Metric Filter

namespace ContinuousStability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {f : E → ℝ} {g : E → E} {xbar : E} {c : ℝ} {P : ℝ → E →L[ℝ] E} {lo : ℝ → ℝ}

/-- **Forward invariance of `E_{c,x̄}`.** Under H5, a solution started in `U` at a time
`t₀ ≥ 0` stays in `U` for as long as it exists (on any time interval `I` starting at `t₀`).
Because `closure U` is compact (H4), this is the a priori bound that gives existence for all
`t ≥ t₀`. -/
theorem basin_invariant {U : Set E} (hU : IsOpen U)
    (hgrad : ∀ z ∈ closure U, HasFDerivAt f (innerSL ℝ (g z)) z)
    (hc : ∀ y ∈ U, c < f y) (hH5 : ∀ y ∈ frontier U, f y = c)
    (hP : ∀ t ≥ (0 : ℝ), EigBound (P t) (lo t)) :
    ∀ t₀ ≥ (0 : ℝ), ∀ (I : Set ℝ) (x : ℝ → E), Convex ℝ I → t₀ ∈ I → I ⊆ Ici t₀ →
      IsSolutionOn P g I x → x t₀ ∈ U → ∀ t ∈ I, x t ∈ U := by
  intro t₀ ht₀ I x hI ht₀I hIt₀ hx hx0 t ht
  by_contra hout
  have htt₀ : t₀ ≤ t := hIt₀ ht
  have hIcc : Icc t₀ t ⊆ I := hI.ordConnected.out ht₀I ht
  obtain ⟨s, hs, hsU, hscl, hbefore⟩ :=
    first_exit hU htt₀ (hx.continuousOn.mono hIcc) hx0 hout
  -- the first exit point lies on `∂U`, where `f = c` (H5)
  have hfront : x s ∈ frontier U := by
    rw [frontier, hU.interior_eq]; exact ⟨hscl, hsU⟩
  -- on `[t₀, s]` the solution stays in `closure U`, so `f ∘ x` is nondecreasing there
  have hsub : Icc t₀ s ⊆ I := (Icc_subset_Icc_right hs.2).trans hIcc
  have hmono := ascent (S := closure U) (lo := lo) (convex_Icc t₀ s) (hx.mono hsub)
    (fun τ hτ => by
      rcases hτ.2.lt_or_eq with h | h
      · exact subset_closure (hbefore τ ⟨hτ.1, h⟩)
      · rw [h]; exact hscl)
    hgrad (fun τ hτ => hP τ (ht₀.trans hτ.1))
  have hle : f (x t₀) ≤ f (x s) := hmono ⟨le_rfl, hs.1.le⟩ ⟨hs.1.le, le_rfl⟩ hs.1.le
  have := hc _ hx0
  rw [hH5 _ hfront] at hle
  linarith

/-- **Theorem 3.1 (for a set with the properties of `E_{c,x̄}`).** Every solution of (E) started
in `U` at a time `t₀ ≥ 0` stays in `U` and converges to `x̄`; that is, `U` lies in the basin of
attraction of `x̄`. -/
theorem basin {U : Set E} (hU : IsOpen U) (hxU : xbar ∈ U) (hcomp : IsCompact (closure U))
    (hgrad : ∀ z ∈ closure U, HasFDerivAt f (innerSL ℝ (g z)) z)
    (hgc : ContinuousOn g (closure U))
    (hc : ∀ y ∈ U, c < f y) (hM : ∀ y ∈ U, y ≠ xbar → f y < f xbar)
    (hH5 : ∀ y ∈ frontier U, f y = c) (hH6 : ∀ y ∈ closure U, y ≠ xbar → g y ≠ 0)
    (hP : ∀ t ≥ (0 : ℝ), EigBound (P t) (lo t)) (hlo : Continuous lo)
    (hH3 : EigenvalueCondition lo) :
    ∀ t₀ ≥ (0 : ℝ), ∀ x : ℝ → E, IsSolution P g t₀ x → x t₀ ∈ U →
      (∀ t ≥ t₀, x t ∈ U) ∧ Tendsto x atTop (𝓝 xbar) := by
  intro t₀ ht₀ x hx hx0
  have hinU : ∀ t ≥ t₀, x t ∈ U := fun t ht =>
    basin_invariant hU hgrad hc hH5 hP t₀ ht₀ (Ici t₀) x (convex_Ici t₀) self_mem_Ici subset_rfl
      hx hx0 t ht
  refine ⟨hinU, ?_⟩
  have hfront : ∀ y ∈ closure U, y ∉ U → y ∈ frontier U := fun y hy hyU => by
    rw [frontier, hU.interior_eq]; exact ⟨hy, hyU⟩
  have hcM : c < f xbar := hc xbar hxU
  -- convergence: the argument of Theorem 2.1(ii) on the compact set `closure U`
  refine tendsto_of_weighted_ascent hcomp (subset_closure hxU)
    (fun z hz => (hgrad z hz).continuousAt.continuousWithinAt) hgc ?_ hH6
    (w := lo) (fun t ht => (hP t (ht₀.trans ht)).lo_nonneg)
    (fun t _ => hasDerivWithinAt_integral hlo _ t) hH3
    (fun t ht => subset_closure (hinU t ht))
    (fun t ht => trajectory_deriv hx ht (hgrad _ (subset_closure (hinU t ht))))
    (fun t ht => trajectory_deriv_ge (hP t (ht₀.trans ht)))
  intro y hy hne
  by_cases hyU : y ∈ U
  · exact hM y hyU hne
  · rw [hH5 y (hfront y hy hyU)]; exact hcM

/-! ### The sets `O_{c,x̄}` and `E_{c,x̄}` -/

/-- `O_{c,x̄} = {x̄} ∪ {x ∈ D : c < f(x) < f(x̄)}`. -/
def Oc (f : E → ℝ) (D : Set E) (c : ℝ) (xbar : E) : Set E :=
  {xbar} ∪ (D ∩ f ⁻¹' Ioo c (f xbar))

/-- `E_{c,x̄}`, the connected component of `O_{c,x̄}` containing `x̄`. -/
def Ec (f : E → ℝ) (D : Set E) (c : ℝ) (xbar : E) : Set E :=
  connectedComponentIn (Oc f D c xbar) xbar

omit [InnerProductSpace ℝ E] in
/-- **`O_{c,x̄}` is open** (first part of the proof of Theorem 3.1), for `D` open, `f`
continuous on `D`, H1 at `x̄ ∈ D` and `c < f(x̄)`. -/
theorem isOpen_Oc {D : Set E} (hD : IsOpen D) (hxD : xbar ∈ D) (hf : ContinuousOn f D)
    (hH1 : IsolatedMax f xbar) (hc : c < f xbar) : IsOpen (Oc f D c xbar) := by
  have hopen : IsOpen (D ∩ f ⁻¹' Ioo c (f xbar)) := hf.isOpen_inter_preimage hD isOpen_Ioo
  obtain ⟨r₁, hr₁, hmax⟩ := hH1
  obtain ⟨r₂, hr₂, hball⟩ := Metric.isOpen_iff.mp hD xbar hxD
  obtain ⟨δ', hδ', hδ'f⟩ :=
    Metric.continuousAt_iff.mp ((hf xbar hxD).continuousAt (hD.mem_nhds hxD)) (f xbar - c)
      (by linarith)
  set δ := min δ' (min r₁ r₂)
  have hδ : 0 < δ := lt_min hδ' (lt_min hr₁ hr₂)
  -- `B_δ(x̄) ⊆ O_{c,x̄}`
  have hsub : ball xbar δ ⊆ Oc f D c xbar := by
    intro y hy
    by_cases hyx : y = xbar
    · exact Or.inl hyx
    · right
      have hy' : dist y xbar < δ := mem_ball.mp hy
      refine ⟨hball (mem_ball.mpr (hy'.trans_le ((min_le_right _ _).trans (min_le_right _ _)))),
        ?_, hmax y hyx (hy'.le.trans ((min_le_right _ _).trans (min_le_left _ _)))⟩
      have := hδ'f (hy'.trans_le (min_le_left _ _))
      rw [Real.dist_eq] at this
      linarith [neg_abs_le (f y - f xbar)]
  rw [isOpen_iff_mem_nhds]
  rintro y (hy | hy)
  · rw [mem_singleton_iff.mp hy]
    exact Filter.mem_of_superset (ball_mem_nhds xbar hδ) hsub
  · exact Filter.mem_of_superset (hopen.mem_nhds hy) subset_union_right

/-- `E_{c,x̄}` is open. -/
theorem isOpen_Ec {D : Set E} (hD : IsOpen D) (hxD : xbar ∈ D) (hf : ContinuousOn f D)
    (hH1 : IsolatedMax f xbar) (hc : c < f xbar) : IsOpen (Ec f D c xbar) :=
  (isOpen_Oc hD hxD hf hH1 hc).connectedComponentIn

omit [InnerProductSpace ℝ E] in
/-- `x̄ ∈ E_{c,x̄}`. -/
theorem mem_Ec {D : Set E} : xbar ∈ Ec f D c xbar :=
  mem_connectedComponentIn (Or.inl rfl)

/-- **Theorem 3.1.** Suppose H0–H3 hold on the open domain `D`, `c < M = f(x̄)`, and
* **H4**: `E_{c,x̄}` is bounded and its closure is contained in `D`;
* **H5**: `f = c` on `∂E_{c,x̄}`;
* **H6**: `f` has no critical points other than `x̄` in the closure of `E_{c,x̄}`.

Then every solution of (E) started in `E_{c,x̄}` at a time `t₀ ≥ 0` stays in `E_{c,x̄}` and
converges to `x̄`: `E_{c,x̄}` is contained in the basin of attraction of `x̄`. -/
theorem basin_Ec [FiniteDimensional ℝ E] {D : Set E} (hD : IsOpen D) (hxD : xbar ∈ D)
    (hgrad : ∀ z ∈ D, HasFDerivAt f (innerSL ℝ (g z)) z) (hgc : ContinuousOn g D)
    (hH1 : IsolatedMax f xbar) (hc : c < f xbar)
    (hH4b : Bornology.IsBounded (Ec f D c xbar)) (hH4D : closure (Ec f D c xbar) ⊆ D)
    (hH5 : ∀ y ∈ frontier (Ec f D c xbar), f y = c)
    (hH6 : ∀ y ∈ closure (Ec f D c xbar), y ≠ xbar → g y ≠ 0)
    (hP : ∀ t ≥ (0 : ℝ), EigBound (P t) (lo t)) (hlo : Continuous lo)
    (hH3 : EigenvalueCondition lo) :
    ∀ t₀ ≥ (0 : ℝ), ∀ x : ℝ → E, IsSolution P g t₀ x → x t₀ ∈ Ec f D c xbar →
      (∀ t ≥ t₀, x t ∈ Ec f D c xbar) ∧ Tendsto x atTop (𝓝 xbar) := by
  have hf : ContinuousOn f D := fun z hz => (hgrad z hz).continuousAt.continuousWithinAt
  have hsubO : Ec f D c xbar ⊆ Oc f D c xbar := connectedComponentIn_subset _ _
  refine basin (isOpen_Ec hD hxD hf hH1 hc) mem_Ec
    (Metric.isCompact_of_isClosed_isBounded isClosed_closure hH4b.closure)
    (fun z hz => hgrad z (hH4D hz)) (hgc.mono hH4D) ?_ ?_ hH5 hH6 hP hlo hH3
  · intro y hy
    rcases hsubO hy with h | h
    · rw [mem_singleton_iff.mp h]; exact hc
    · exact h.2.1
  · intro y hy hne
    rcases hsubO hy with h | h
    · exact absurd (mem_singleton_iff.mp h) hne
    · exact h.2.2

end ContinuousStability
