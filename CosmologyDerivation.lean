/-!
# Abstract Cosmology — theorem-derivation style

The abstract cosmology of the F-Theory formalization, written as a
*theorem-derivation machine*: principles go in, equations come out.
The cosmos itself is abstract — no stars fly in it. What the machine
must do is run, and produce its answers consistently.

The model:

* A **state** of the cosmos carries two facets — the Obverse (material
  aspect) and the Reverse (mathematical aspect) — plus a mass and a
  consistency error.
* The **action** `L` of a state is the sum of its two facets.
* The **mirror** swaps the two facets (the Obverse–Reverse
  correspondence `Φ`).
* A **cosmos** is a finite list of states.

Principles, and what is derived from them (no `sorry` anywhere):

* *Extremal principle* → `extremal_exists`: a finite cosmos has an
  extremal state, and `extremum_minimal`: the discrete variational
  inequality `L e ≤ L s` for every state `s` (no reachable state has
  lower action — the discrete form of `δA = 0`).
* *Correspondence* → `L_mirror`: the action is invariant under the
  mirror, and `mirror_extremal`: the mirror of an extremal state is
  itself extremal — the two facets extremize together.
* *Hierarchy* → `totalEnergy_eq`: with the correspondence factor
  `K = c²`, the total energy of the macro cosmos equals the total
  mass times `K` — the mass–energy identity, derived by summing the
  micro level.
* *Consistency* → `macroErr_eq_zero`: if every micro state is
  error-free, the macro cosmos is error-free.
* `cosmic_coherence` assembles all of the above for one finite,
  consistent cosmos.

Honest note: this is an abstract model. The "equations" are formal
analogues derived inside the system; the derivations are machine
checked (Q.E.D.), and judgement of what they say about the physical
universe is left to the reader — the same position as the original
Cosmology.lean.

Author: Takeo Yamamoto (GitHub: Takeo140)
License: Apache-2.0
-/

namespace CosmologyDerivation

/-- A state of the abstract cosmos: an Obverse value, a Reverse
    value, a mass, and a consistency error. -/
structure CState where
  /-- Obverse facet (material aspect). -/
  obv : Nat
  /-- Reverse facet (mathematical aspect). -/
  rev : Nat
  /-- Mass of the state. -/
  mass : Nat
  /-- Consistency error `C` of the state (`0` means consistent). -/
  err : Nat
deriving DecidableEq, Repr

/-- The action functional: `L s = obv + rev`. -/
def L (s : CState) : Nat := s.obv + s.rev

/-- The mirror correspondence `Φ`: swap Obverse and Reverse. -/
def mirror (s : CState) : CState :=
  { obv := s.rev, rev := s.obv, mass := s.mass, err := s.err }

theorem mirror_involutive (s : CState) : mirror (mirror s) = s := by
  cases s
  rfl

/-- Correspondence invariance: the action does not change under the
    mirror. -/
theorem L_mirror (s : CState) : L (mirror s) = L s := by
  show s.rev + s.obv = s.obv + s.rev
  exact Nat.add_comm _ _

/-- Of two states, keep the one with smaller action (ties keep the
    first). -/
def pick (a b : CState) : CState :=
  if L b ≤ L a then b else a

theorem pick_eq (a b : CState) : pick a b = a ∨ pick a b = b := by
  unfold pick
  by_cases h : L b ≤ L a
  · simp [h]
  · simp [h]

theorem L_pick_le_left (a b : CState) : L (pick a b) ≤ L a := by
  unfold pick
  by_cases h : L b ≤ L a
  · simp [h]
  · simp [h]

theorem L_pick_le_right (a b : CState) : L (pick a b) ≤ L b := by
  unfold pick
  by_cases h : L b ≤ L a
  · simp [h]
  · simp only [h, ite_false]
    exact Nat.le_of_not_ge h

/-- Fold a finite cosmos down to its extremal state, starting from
    the seed state `a`. -/
def extremumAux : CState → List CState → CState
  | a, [] => a
  | a, s :: ss => extremumAux (pick a s) ss

theorem extremumAux_mem (a : CState) (ss : List CState) :
    extremumAux a ss = a ∨ extremumAux a ss ∈ ss := by
  induction ss generalizing a with
  | nil => exact Or.inl rfl
  | cons s ss ih =>
    unfold extremumAux
    cases pick_eq a s with
    | inl h =>
      rw [h]
      cases ih (a := a) with
      | inl h2 => exact Or.inl h2
      | inr h2 => exact Or.inr (List.Mem.tail _ h2)
    | inr h =>
      rw [h]
      cases ih (a := s) with
      | inl h2 => exact Or.inr (by rw [h2]; exact List.Mem.head _)
      | inr h2 => exact Or.inr (List.Mem.tail _ h2)

theorem extremumAux_min (a : CState) (ss : List CState) :
    L (extremumAux a ss) ≤ L a ∧
    ∀ s ∈ ss, L (extremumAux a ss) ≤ L s := by
  induction ss generalizing a with
  | nil => exact ⟨Nat.le_refl _, fun s hs => by cases hs⟩
  | cons s ss ih =>
    rw [extremumAux]
    cases ih (a := pick a s) with
    | intro h1 h2 =>
      refine ⟨Nat.le_trans h1 (L_pick_le_left a s), fun t ht => ?_⟩
      cases ht with
      | head => exact Nat.le_trans h1 (L_pick_le_right a s)
      | tail _ ht' => exact h2 t ht'

/-- The extremal state of a finite cosmos, if it has any states. -/
def extremum : List CState → Option CState
  | [] => none
  | s :: ss => some (extremumAux s ss)

theorem extremum_mem {ss : List CState} {e : CState} :
    extremum ss = some e → e ∈ ss := by
  cases ss with
  | nil => intro h; cases h
  | cons s ss =>
    intro h
    simp only [extremum, Option.some.injEq] at h
    rw [← h]
    cases extremumAux_mem s ss with
    | inl h2 => rw [h2]; exact List.Mem.head _
    | inr h2 => exact List.Mem.tail _ h2

/-- The variational inequality: no state of the cosmos has lower
    action than the extremal state. -/
theorem extremum_minimal {ss : List CState} {e : CState} :
    extremum ss = some e → ∀ s ∈ ss, L e ≤ L s := by
  cases ss with
  | nil => intro h; cases h
  | cons s ss =>
    intro h t ht
    simp only [extremum, Option.some.injEq] at h
    rw [← h]
    cases ht with
    | head => exact (extremumAux_min s ss).1
    | tail _ ht' => exact (extremumAux_min s ss).2 t ht'

/-- Extremal existence: every nonempty finite cosmos has an extremal
    state, and it satisfies the variational inequality. -/
theorem extremal_exists {ss : List CState} (hne : ss ≠ []) :
    ∃ e, e ∈ ss ∧ ∀ s ∈ ss, L e ≤ L s := by
  cases ss with
  | nil => exact absurd rfl hne
  | cons s ss =>
    exact ⟨extremumAux s ss,
      extremum_mem (ss := s :: ss) rfl,
      extremum_minimal (ss := s :: ss) rfl⟩

/-- The mirror of an extremal state has the same action and is
    itself extremal: the two facets extremize together. -/
theorem mirror_extremal {ss : List CState} {e : CState}
    (h : extremum ss = some e) :
    L (mirror e) = L e ∧ ∀ s ∈ ss, L (mirror e) ≤ L s := by
  refine ⟨L_mirror e, fun s hs => ?_⟩
  rw [L_mirror]
  exact extremum_minimal h s hs

/-- Sum a quantity over a finite cosmos. -/
def foldSum (f : CState → Nat) : List CState → Nat
  | [] => 0
  | s :: ss => f s + foldSum f ss

/-- Total mass of the macro cosmos (sum over the micro states). -/
def totalMass (ss : List CState) : Nat := foldSum (fun s => s.mass) ss

/-- The correspondence factor `K = c²` (toy units, `c = 3`). -/
def K : Nat := 3 * 3

/-- Total energy of the macro cosmos: each micro mass contributes
    `mass * K` through the correspondence. -/
def totalEnergy (ss : List CState) : Nat :=
  foldSum (fun s => s.mass * K) ss

/-- Mass–energy identity, derived through the hierarchy: the total
    energy of the whole equals the total mass times `K`. -/
theorem totalEnergy_eq (ss : List CState) :
    totalEnergy ss = totalMass ss * K := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    show s.mass * K + totalEnergy ss = (s.mass + totalMass ss) * K
    rw [ih, Nat.add_mul]

/-- Total consistency error of the macro cosmos. -/
def macroErr (ss : List CState) : Nat := foldSum (fun s => s.err) ss

/-- Consistency propagates up the hierarchy: if every micro state is
    error-free, the macro cosmos is error-free. -/
theorem macroErr_eq_zero {ss : List CState}
    (h : ∀ s ∈ ss, s.err = 0) : macroErr ss = 0 := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    show s.err + macroErr ss = 0
    rw [h s (List.Mem.head _),
        ih (fun t ht => h t (List.Mem.tail _ ht))]

/-- The assembled coherence of a finite, consistent cosmos: an
    extremal state exists and is mirror-stable, the macro error
    vanishes, and the mass–energy identity holds. -/
theorem cosmic_coherence {ss : List CState} (hne : ss ≠ [])
    (hcons : ∀ s ∈ ss, s.err = 0) :
    ∃ e, e ∈ ss ∧ (∀ s ∈ ss, L e ≤ L s) ∧ L (mirror e) = L e ∧
      macroErr ss = 0 ∧ totalEnergy ss = totalMass ss * K := by
  cases extremal_exists hne with
  | intro e he =>
    exact ⟨e, he.1, he.2,
      L_mirror e, macroErr_eq_zero hcons, totalEnergy_eq ss⟩

/-- A concrete three-state cosmos, with actions 5, 2, 7. -/
def demo : List CState :=
  [⟨3, 2, 10, 0⟩, ⟨1, 1, 4, 0⟩, ⟨5, 2, 7, 0⟩]

-- The extremal state is the second one (action 2).
#eval extremum demo

example : extremum demo = some ⟨1, 1, 4, 0⟩ := by decide

-- Its mirror has the same action, and it is extremal in the mirror.
example : L (mirror ⟨1, 1, 4, 0⟩) = L ⟨1, 1, 4, 0⟩ :=
  L_mirror _

-- The macro quantities: mass 21, energy 21 * 9 = 189, error 0.
#eval (totalMass demo, totalEnergy demo, macroErr demo)

example : totalEnergy demo = 189 := by decide
example : macroErr demo = 0 := by decide

end CosmologyDerivation
