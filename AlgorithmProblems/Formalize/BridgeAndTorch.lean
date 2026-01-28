/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Algorithm Problems Lean
-/
import Mathlib.Data.List.Sort
import Mathlib.Data.List.MinMax
import Mathlib.Tactic

/-!
# Bridge and Torch Problem

Given `n` people who need to cross a bridge at night with a single torch:
- At most 2 people can cross at once
- Crossing time for a pair is the maximum of their individual times
- The torch must be carried back for others to cross

Goal: Find the minimum total time for everyone to cross.

## Main definitions

* `minCrossingTime`: The minimum time for `n` people (with sorted times) to cross

## Main results

* `minCrossingTime_eq_optimalTime`: The optimal time follows a specific recurrence relation
-/

namespace BridgeAndTorch

/-- The minimum crossing time for a sorted list of crossing times (ascending).
    f(0) = 0, f(1) = t₁, f(2) = t₂, f(3) = t₁ + t₂ + t₃
    f(n) = min(f(n-1) + t₁ + tₙ, f(n-2) + t₁ + 2t₂ + tₙ) for n ≥ 4 -/
noncomputable def minCrossingTime : List ℕ → ℕ
  | [] => 0
  | [a] => a
  | [_, b] => b
  | [a, b, c] => a + b + c
  | a :: b :: c :: d :: rest =>
    let times := a :: b :: c :: d :: rest
    let tₙ := times.getLast!
    let strategy1 := minCrossingTime times.dropLast + a + tₙ
    let strategy2 := minCrossingTime times.dropLast.dropLast + a + 2 * b + tₙ
    min strategy1 strategy2
termination_by l => l.length

/-- A crossing schedule is a sequence of moves (forward crossings and returns). -/
inductive Move (n : ℕ) where
  | forward : Fin n → Option (Fin n) → Move n  -- one or two people cross forward
  | back : Fin n → Move n                       -- one person returns with torch

/-- A valid schedule gets everyone across. -/
def isValidSchedule (times : Fin n → ℕ) (moves : List (Move n)) : Prop := sorry

/-- The total time of a schedule. -/
def scheduleTime (times : Fin n → ℕ) (moves : List (Move n)) : ℕ := sorry

/-- The optimal crossing time is the minimum over all valid schedules. -/
noncomputable def optimalTime (times : Fin n → ℕ) : ℕ :=
  sInf { t | ∃ moves, isValidSchedule times moves ∧ scheduleTime times moves = t }

/-! ## Main Theorems -/

/-- For sorted times, our formula gives the optimal crossing time. -/
theorem minCrossingTime_eq_optimalTime (times : List ℕ) (hsorted : times.SortedLE) :
    minCrossingTime times = optimalTime (fun i => times.get i) := sorry

/-- The classic instance: 4 people with times [1, 2, 5, 10] need 17 minutes. -/
theorem classic_example : minCrossingTime [1, 2, 5, 10] = 17 := sorry

/-- Strategy 1 is optimal when t₁ + tₙ₋₁ < 2·t₂ -/
theorem strategy1_optimal {times : List ℕ} (hsorted : times.SortedLE)
    (h : times.length ≥ 4)
    (hcond : times[0]! + times[times.length - 2]! < 2 * times[1]!) :
    minCrossingTime times =
      minCrossingTime times.dropLast + times[0]! + times.getLast! := sorry

/-- Strategy 2 is optimal when t₁ + tₙ₋₁ ≥ 2·t₂ -/
theorem strategy2_optimal {times : List ℕ} (hsorted : times.SortedLE)
    (h : times.length ≥ 4)
    (hcond : times[0]! + times[times.length - 2]! ≥ 2 * times[1]!) :
    minCrossingTime times =
      minCrossingTime (times.dropLast.dropLast) +
      times[0]! + 2 * times[1]! + times.getLast! := sorry

end BridgeAndTorch
