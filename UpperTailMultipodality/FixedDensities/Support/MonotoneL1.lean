import UpperTailMultipodality.Preliminaries.Graphons.Basic

/-!
# `L¹` approximation of monotone kernels (`lem:ordered-compact`)

A graphon with a representative that is nondecreasing in each variable is approximated in `L¹`
by the step kernel that reads off its values on a `k × k` grid, with an error `O(1/k)`.  The
bound needs no decomposition into cells: the difference is dominated by

`f (x + 1/k, y + 1/k) - f (x - 1/k, y - 1/k)`,

and a one-dimensional monotone function `g` with values in `[0,1]` satisfies
`∫₀¹ (g (x+h) - g (x-h)) dx ≤ 2h`, because the integral telescopes into the two boundary
windows of width `2h`.

This file proves that one-dimensional estimate; `lem:ordered-compact` uses it twice, once in each
variable.
-/

namespace UpperTailMultipodality.FixedDensities

open MeasureTheory Set

/-- The integral against `unitμ` is the integral over `[0,1]`. -/
theorem integral_unitμ_eq_intervalIntegral (g : ℝ → ℝ) :
    ∫ x, g x ∂unitμ = ∫ x in (0:ℝ)..1, g x := by
  rw [unitμ, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- **The translation estimate for a monotone function.**  If `g` is nondecreasing with values in
`[0,1]` and `0 < h ≤ 1/2`, then `∫₀¹ (g (x+h) - g (x-h)) dx ≤ 2h`. -/
theorem integral_sub_translate_le {g : ℝ → ℝ} (hmono : Monotone g)
    (hmem : ∀ x, g x ∈ Icc (0:ℝ) 1) {h : ℝ} (hh0 : 0 < h) :
    (∫ x in (0:ℝ)..1, (g (x + h) - g (x - h))) ≤ 2 * h := by
  have hint : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun _ _ =>
    hmono.intervalIntegrable
  have hshift : ∀ c : ℝ, (∫ x in (0:ℝ)..1, g (x + c)) = ∫ x in c..(1 + c), g x := by
    intro c
    rw [intervalIntegral.integral_comp_add_right (fun x => g x) c]
    norm_num
  have hsub : ∀ c : ℝ, (∫ x in (0:ℝ)..1, g (x - c)) = ∫ x in (-c)..(1 - c), g x := by
    intro c
    have := hshift (-c)
    simp only [sub_eq_add_neg]
    convert this using 2
  have hsplit : (∫ x in (0:ℝ)..1, (g (x + h) - g (x - h)))
      = (∫ x in h..(1 + h), g x) - ∫ x in (-h)..(1 - h), g x := by
    rw [intervalIntegral.integral_sub (by simpa using (hint h (1 + h)).comp_add_right h)
      (by simpa [sub_eq_add_neg] using (hint (-h) (1 - h)).comp_add_right (-h)), hshift h, hsub h]
  -- the two integrals share the middle piece `[h, 1-h]`
  have hmid : (∫ x in h..(1 + h), g x)
      = (∫ x in h..(1 - h), g x) + ∫ x in (1 - h)..(1 + h), g x :=
    (intervalIntegral.integral_add_adjacent_intervals (hint h (1 - h)) (hint (1 - h) (1 + h))).symm
  have hmid' : (∫ x in (-h)..(1 - h), g x)
      = (∫ x in (-h)..h, g x) + ∫ x in h..(1 - h), g x :=
    (intervalIntegral.integral_add_adjacent_intervals (hint (-h) h) (hint h (1 - h))).symm
  have hupper : (∫ x in (1 - h)..(1 + h), g x) ≤ 2 * h := by
    have hle : (1:ℝ) - h ≤ 1 + h := by linarith
    have := intervalIntegral.integral_mono_on hle (hint (1 - h) (1 + h))
      (intervalIntegrable_const (c := (1:ℝ))) (fun x _ => (hmem x).2)
    simpa [mul_comm] using this.trans_eq (by simp; ring)
  have hlower : 0 ≤ ∫ x in (-h)..h, g x := by
    have hle : -h ≤ h := by linarith
    have := intervalIntegral.integral_mono_on hle (intervalIntegrable_const (c := (0:ℝ)))
      (hint (-h) h) (fun x _ => (hmem x).1)
    simpa using this
  rw [hsplit, hmid, hmid']
  linarith

end UpperTailMultipodality.FixedDensities
