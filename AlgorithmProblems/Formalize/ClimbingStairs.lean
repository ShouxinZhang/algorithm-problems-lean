/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wudizhe001
-/
import Mathlib

/-!
# Climbing Stairs Problem

There are `n` steps. Each move climbs either 1 or 2 steps.
The goal is to count the number of distinct ways to reach step `n`.

This file formalizes the problem statement and the claim that the
recursive algorithm converges to the optimal (correct) count.
-/

namespace ClimbingStairs

/-- A single move: climb 1 or 2 steps. -/
inductive Step where
  | one : Step
  | two : Step
  deriving DecidableEq, Repr

/-- Numeric value of a move. -/
def stepValue : Step → ℕ
  | Step.one => 1
  | Step.two => 2

/-- The recursive algorithm for counting ways. -/
def waysAlg : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => waysAlg (n + 1) + waysAlg n

/-- The recursive algorithm converges to the optimal answer. -/
theorem waysAlg_eq_optimalWays (n : ℕ) :
    waysAlg n = Nat.card {p : List Step // (p.map stepValue).sum = n} := by

  sorry

end ClimbingStairs
