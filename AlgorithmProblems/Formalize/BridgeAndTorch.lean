/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wudizhe001
-/
import Mathlib

/-!
# Bridge and Torch Problem

There are `n` people who need to cross a bridge at night.
They have one torch.
- The bridge supports at most two people at once.
- Any group crossing must carry the torch.
- The time taken for a group is the maximum of their individual times.
- The torch must be carried back if there are people left to cross.

Given a list of crossing times, find the minimum total time required.
-/

namespace BridgeAndTorch

open Multiset

/-- State of the crossing: people on the left side and torch position.
    true = Torch on Left, false = Torch on Right. -/
structure State where
  left : Multiset ℕ
  torchOnLeft : Bool
deriving DecidableEq

/-- Valid moves in the state space.
    `total` is required to determine who is on the right side for return trips. -/
inductive Move (total : Multiset ℕ) : State → State → ℕ → Prop
  | cross (s : Multiset ℕ) (l : Multiset ℕ) :
      s ≤ l → s.card ∈ ({1, 2} : Set ℕ) →
      Move total ⟨l, true⟩ ⟨l - s, false⟩ (s.fold max 0)
  | back (s : Multiset ℕ) (l : Multiset ℕ) :
      s ≤ total - l → s.card ∈ ({1, 2} : Set ℕ) →
      Move total ⟨l, false⟩ ⟨l + s, true⟩ (s.fold max 0)

/-- Reachability predicate tracking accumulated cost. -/
inductive Reachable (total : Multiset ℕ) : State → ℕ → Prop
  | start : Reachable total ⟨total, true⟩ 0
  | step {s₁ s₂ c dc} :
      Reachable total s₁ c →
      Move total s₁ s₂ dc →
      Reachable total s₂ (c + dc)

/-- The optimal time is the minimum cost to move everyone to the right (left set empty). -/
noncomputable def minCrossingTime (people : Multiset ℕ) : ℕ :=
  sInf {c | Reachable people ⟨0, false⟩ c}

/--
The standard recursive solution for the problem.
Assumes the input list is sorted and handles the two smallest times `t1, t2`
to ferry the largest times `tn, tn-1`.
-/
def greedyAlgo (people : List ℕ) : ℕ :=
  let l := people.mergeSort (·≤·)
  let n := l.length
  let t1 := l.getD 0 0
  let t2 := l.getD 1 0
  let rec solve : ℕ → ℕ
    | 0 => 0
    | 1 => t1
    | 2 => t2
    | 3 => t1 + t2 + l.getD 2 0
    | k + 4 =>
      let tn := l.getD (k + 3) 0
      -- Strategy 1: t1 escorts tn
      let strat1 := solve (k + 3) + t1 + tn
      -- Strategy 2: t1, t2 escort tn, tn-1
      let strat2 := solve (k + 2) + t1 + 2 * t2 + tn
      min strat1 strat2
  termination_by k => k
  decreasing_by all_goals omega
  solve n

/-- The greedy algorithm computes the minimum crossing time. -/
theorem greedyAlgo_eq_minCrossingTime (people : List ℕ) :
    greedyAlgo people = minCrossingTime people := by
  sorry

end BridgeAndTorch
