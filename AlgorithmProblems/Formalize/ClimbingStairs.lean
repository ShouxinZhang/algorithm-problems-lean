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

/-- Paths with total stepValue sum n. -/
def paths (n : ℕ) := {p : List Step // (p.map stepValue).sum = n}

lemma sum_stepValue_eq_zero_nil {p : List Step} :
    (p.map stepValue).sum = 0 → p = [] := by
  cases p with
  | nil => intro; rfl
  | cons a p =>
      intro h
      cases a <;> simp [stepValue, List.sum_cons] at h

lemma sum_stepValue_eq_one_singleton {p : List Step} :
    (p.map stepValue).sum = 1 → p = [Step.one] := by
  cases p with
  | nil => intro h; simp at h
  | cons a p =>
      intro h
      cases a
      · -- a = one
        have h0 := h
        simp [stepValue, List.sum_cons] at h0
        have hp : p = [] := sum_stepValue_eq_zero_nil h0
        simp [hp]
      · -- a = two
        have h0 := h
        simp [stepValue, List.sum_cons] at h0
        have : False := by omega
        exact (False.elim this)

def paths0_equiv : paths 0 ≃ PUnit.{1} := by
  refine
    { toFun := fun _ => PUnit.unit
      invFun := fun _ => ⟨[], by simp⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    rcases x with ⟨p, hp⟩
    apply Subtype.ext
    simp [sum_stepValue_eq_zero_nil hp]
  · intro u
    cases u
    rfl

def paths1_equiv : paths 1 ≃ PUnit.{1} := by
  refine
    { toFun := fun _ => PUnit.unit
      invFun := fun _ => ⟨[Step.one], by simp [stepValue]⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    rcases x with ⟨p, hp⟩
    apply Subtype.ext
    simp [sum_stepValue_eq_one_singleton hp]
  · intro u
    cases u
    rfl

-- split paths by first step
def pathsSplit (n : ℕ) : paths (n + 2) → paths (n + 1) ⊕ paths n := by
  intro x
  rcases x with ⟨p, hp⟩
  cases p with
  | nil =>
      have : (n + 2) = 0 := by
        simpa using hp.symm
      exact (False.elim ((Nat.succ_ne_zero (n + 1)) this))
  | cons a p =>
      cases a
      · have h1 := hp
        simp [stepValue, List.sum_cons] at h1
        have hsum : (p.map stepValue).sum = n + 1 := by omega
        exact Sum.inl ⟨p, hsum⟩
      · have h1 := hp
        simp [stepValue, List.sum_cons] at h1
        have hsum : (p.map stepValue).sum = n := by omega
        exact Sum.inr ⟨p, hsum⟩

-- join paths by prepending step
def pathsJoin (n : ℕ) : paths (n + 1) ⊕ paths n → paths (n + 2) := by
  intro x
  cases x with
  | inl p =>
      rcases p with ⟨p, hp⟩
      refine ⟨Step.one :: p, ?_⟩
      simp [List.sum_cons, stepValue, hp]
      omega
  | inr p =>
      rcases p with ⟨p, hp⟩
      refine ⟨Step.two :: p, ?_⟩
      simp [List.sum_cons, stepValue, hp]
      omega

lemma pathsSplit_pathsJoin_left (n : ℕ) :
    Function.LeftInverse (pathsSplit n) (pathsJoin n) := by
  intro x
  cases x with
  | inl p =>
      rcases p with ⟨p, hp⟩
      -- split (join (inl p)) = inl p
      simp [pathsJoin, pathsSplit]
  | inr p =>
      rcases p with ⟨p, hp⟩
      simp [pathsJoin, pathsSplit]

lemma pathsSplit_pathsJoin_right (n : ℕ) :
    Function.RightInverse (pathsSplit n) (pathsJoin n) := by
  intro x
  rcases x with ⟨p, hp⟩
  cases p with
  | nil =>
      have : (n + 2) = 0 := by
        simpa using hp.symm
      exact (False.elim ((Nat.succ_ne_zero (n + 1)) this))
  | cons a p =>
      cases a
      · -- one
        have h1 := hp
        simp [stepValue, List.sum_cons] at h1
        have hsum : (p.map stepValue).sum = n + 1 := by omega
        apply Subtype.ext
        simp [pathsSplit, pathsJoin]
      · -- two
        have h1 := hp
        simp [stepValue, List.sum_cons] at h1
        have hsum : (p.map stepValue).sum = n := by omega
        apply Subtype.ext
        simp [pathsSplit, pathsJoin]

def pathsEquivSum (n : ℕ) : paths (n + 2) ≃ paths (n + 1) ⊕ paths n := by
  refine
    { toFun := pathsSplit n
      invFun := pathsJoin n
      left_inv := pathsSplit_pathsJoin_right n
      right_inv := pathsSplit_pathsJoin_left n }

lemma paths_finite_pair : ∀ n, Finite (paths n) ∧ Finite (paths (n + 1)) := by
  classical
  refine Nat.rec ?base ?step
  · -- n = 0
    have h0 : Finite (paths 0) := Finite.of_equiv PUnit paths0_equiv.symm
    have h1 : Finite (paths 1) := Finite.of_equiv PUnit paths1_equiv.symm
    exact ⟨h0, h1⟩
  · intro n ih
    have hFinN : Finite (paths n) := ih.1
    have hFinN1 : Finite (paths (n + 1)) := ih.2
    have hsum : Finite (paths (n + 1) ⊕ paths n) := by infer_instance
    have hFinN2 : Finite (paths (n + 2)) :=
      Finite.of_equiv (paths (n + 1) ⊕ paths n) (pathsEquivSum n).symm
    exact ⟨hFinN1, hFinN2⟩

lemma waysAlg_eq_optimalWays_pair :
    ∀ n, waysAlg n = Nat.card (paths n) ∧ waysAlg (n + 1) = Nat.card (paths (n + 1)) := by
  classical
  refine Nat.rec ?base ?step
  · -- n = 0
    have h0 : Nat.card (paths 0) = 1 := by
      calc
        Nat.card (paths 0) = Nat.card (PUnit.{1}) := Nat.card_congr paths0_equiv
        _ = 1 := by simp
    have h1 : Nat.card (paths 1) = 1 := by
      calc
        Nat.card (paths 1) = Nat.card (PUnit.{1}) := Nat.card_congr paths1_equiv
        _ = 1 := by simp
    refine ⟨?h0, ?h1⟩
    · simp [waysAlg, h0]
    · simp [waysAlg, h1]
  · intro n ih
    refine ⟨ih.2, ?_⟩
    have hFin := paths_finite_pair n
    have hFinN : Finite (paths n) := hFin.1
    have hFinN1 : Finite (paths (n + 1)) := hFin.2
    calc
      waysAlg (n + 2) = waysAlg (n + 1) + waysAlg n := by
        simp [waysAlg]
      _ = Nat.card (paths (n + 1)) + Nat.card (paths n) := by
        simp [ih.1, ih.2]
      _ = Nat.card (paths (n + 1) ⊕ paths n) := by
        symm
        simp [Nat.card_sum]
      _ = Nat.card (paths (n + 2)) := by
        symm
        exact Nat.card_congr (pathsEquivSum n)

/-- The recursive algorithm converges to the optimal answer. -/
theorem waysAlg_eq_optimalWays (n : ℕ) :
    waysAlg n = Nat.card {p : List Step // (p.map stepValue).sum = n} := by
  -- use the pair induction lemma
  simpa [paths] using (waysAlg_eq_optimalWays_pair n).1

end ClimbingStairs
