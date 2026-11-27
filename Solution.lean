module
/-
Copyright 2025 The Formal Conjectures Authors.
Copyright 2026 Ellweb3.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

public import Blueprint107
public import ErdosSzekeresLower107

/-!
# Solution: the Erdős–Szekeres bounds (Erdős Problem 107)

* Upper bound and `cardSet n ≠ ∅`: `Erdos107.f_le_erdosSzekeresUpper` and
  `Erdos107.nonempty_cardSet` from Linmiao Xu's formalization
  (`Proofs/`, see `THIRD_PARTY.md`).
* Lower bound: `Erdos107Lower.lower_construction` (`Proofs/ErdosSzekeresLower107.lean`), the
  construction of Erdős and Szekeres of `2^(n-2)` points with no convex `n`-gon.
-/

@[expose] public section

namespace Set

protected def Triplewise {α : Type*} (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s → x ≠ y → y ≠ z → x ≠ z → r x y z

end Set

open Filter
open EuclideanGeometry

namespace EuclideanGeometry

def NonTrilinear (A : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  A.Triplewise (fun x y z ↦ ¬ Collinear ℝ {x, y, z})

def ConvexIndep (S : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ a ∈ S, a ∉ convexHull ℝ (S \ {a})

def HasConvexNGon (n : ℕ) (P : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ S : Finset (EuclideanSpace ℝ (Fin 2)), S.card = n ∧ ↑S ⊆ P ∧ ConvexIndep S

end EuclideanGeometry

namespace Erdos107.Palomar

/-- The set of $N$ such that any $N$ points in the plane, no three on a line,
contain a convex $n$-gon. -/
def cardSet (n : ℕ) := { N | ∀ (pts : Finset (EuclideanSpace ℝ (Fin 2))), pts.card = N → NonTrilinear (pts : Set (EuclideanSpace ℝ (Fin 2))) →
  HasConvexNGon n pts }

/-- The function $f(n)$ specified in `erdos_107`. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf (cardSet n)

private lemma cardSet_eq (n : ℕ) : cardSet n = Erdos107.cardSet n := rfl

private lemma f_eq (n : ℕ) : f n = Erdos107.f n := rfl

lemma lower_bound (n : ℕ) (hn : 3 ≤ n) : 2 ^ (n - 2) + 1 ≤ f n := by
  have hne : (cardSet n).Nonempty := by
    rw [cardSet_eq]; exact Erdos107.nonempty_cardSet n hn
  refine le_csInf hne fun N hN => ?_
  by_contra hlt
  obtain ⟨pts, hcard, hgen, hfree⟩ :=
    Erdos107Lower.lower_construction n hn N (by omega)
  obtain ⟨S, hS, hsub, hconv⟩ :=
    hN pts hcard fun x hx y hy z hz hxy hyz hxz => hgen x hx y hy z hz hxy hyz hxz
  have := hfree S (Finset.coe_subset.1 hsub) hconv
  omega

/-- Erdős and Szekeres proved the bounds
$$
  2^{n-2} + 1 ≤ f(n) ≤ \binom{2n-4}{n-2} + 1
$$
([ErSz60] and [ErSz35] respectively). -/
theorem ersz_bounds :
    ∀ n ≥ 3, 2^(n - 2) + 1 ≤ f n ∧ f n ≤ Nat.choose (2 * n - 4) (n - 2) + 1 := by
  intro n hn
  refine ⟨lower_bound n hn, ?_⟩
  rw [f_eq]
  exact Erdos107.f_le_erdosSzekeresUpper (by omega : 2 ≤ n)

end Erdos107.Palomar
