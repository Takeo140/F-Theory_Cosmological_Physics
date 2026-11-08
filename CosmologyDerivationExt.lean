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
 
namespace CosmologyDerivationExt
 
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
 
 
 
/-! ## Part II — the next ring of theorems
 
The derivation machine does not stop at `cosmic_coherence`. From the
same four principles, the following further theorems come out:
 
* *Extremal principle, continued* → `pick_L_of_min`, `extremal_stable`:
  an extremal state does not move under further selection; the
  selection process is already at rest there.
* *Correspondence, continued* → `pick_mirror`, `extremum_mirrorCosmos`,
  `extremum_L_mirror`: selection commutes with the mirror, so the
  extremum computed in the mirrored description is the mirror of the
  extremum — the two descriptions agree (path independence of the
  correspondence).
* *Hierarchy, continued* → `totalEnergyH_eq`, `hierarchy_identity`:
  the mass–energy identity holds at the second hierarchy level too,
  and flattening a hierarchy of cosmoses preserves it.
* *Consistency, continued* → `macroErr_filter`: any subsystem of a
  consistent cosmos is consistent; and under the mirror evolution
  (`evolve`, `evolveN`) mass, energy and error are all preserved, so
  coherence persists for all times (`eternal_coherence`). -/
 
/-- Selection does not move an extremal candidate: if `L e ≤ L s`,
    selecting between `e` and `s` leaves the action at `L e`. -/
theorem pick_L_of_min {e s : CState} (hmin : L e ≤ L s) :
    L (pick e s) = L e := by
  by_cases hc : L s ≤ L e
  · have hp : pick e s = s := by simp [pick, hc]
    rw [hp]
    exact Nat.le_antisymm hc hmin
  · have hp : pick e s = e := by simp [pick, hc]
    rw [hp]
 
/-- The selection process is at rest at an extremal state: folding
    the whole cosmos starting from a minimal seed cannot lower the
    action below the seed's — it stays exactly there. -/
theorem extremal_stable {e : CState} {ss : List CState}
    (hmin : ∀ s ∈ ss, L e ≤ L s) :
    L (extremumAux e ss) = L e := by
  induction ss generalizing e with
  | nil => rfl
  | cons s ss ih =>
    rw [extremumAux]
    have hps : L (pick e s) = L e :=
      pick_L_of_min (hmin s (List.Mem.head _))
    have hrest : ∀ t ∈ ss, L (pick e s) ≤ L t := by
      intro t ht
      rw [hps]
      exact hmin t (List.Mem.tail _ ht)
    rw [ih hrest, hps]
 
/-- Selection commutes with the mirror correspondence. -/
theorem pick_mirror (a b : CState) :
    pick (mirror a) (mirror b) = mirror (pick a b) := by
  unfold pick
  by_cases h : L b ≤ L a
  · have h2 : L (mirror b) ≤ L (mirror a) := by
      rw [L_mirror, L_mirror]; exact h
    simp [h, h2]
  · have h2 : ¬ L (mirror b) ≤ L (mirror a) := by
      rw [L_mirror, L_mirror]; exact h
    simp [h, h2]
 
/-- Conservation form of the correspondence: mirroring the inputs of
    a selection does not change the action of the outcome. -/
theorem L_pick_mirror (a b : CState) :
    L (pick (mirror a) (mirror b)) = L (pick a b) := by
  rw [pick_mirror, L_mirror]
 
/-- Folding commutes with mirroring the whole cosmos. -/
theorem extremumAux_mirror (a : CState) (ss : List CState) :
    extremumAux (mirror a) (ss.map mirror) = mirror (extremumAux a ss) := by
  induction ss generalizing a with
  | nil => rfl
  | cons s ss ih =>
    show extremumAux (pick (mirror a) (mirror s)) (ss.map mirror)
        = mirror (extremumAux (pick a s) ss)
    rw [pick_mirror]
    exact ih (a := pick a s)
 
/-- The extremum of the mirrored cosmos is the mirror of the
    extremum: the correspondence carries the extremal state across
    the two descriptions. -/
theorem extremum_mirrorCosmos (ss : List CState) :
    extremum (ss.map mirror) = (extremum ss).map mirror := by
  cases ss with
  | nil => rfl
  | cons s ss =>
    show some (extremumAux (mirror s) (ss.map mirror))
        = (some (extremumAux s ss)).map mirror
    rw [extremumAux_mirror]
    rfl
 
/-- Path independence of the correspondence: whichever description
    the extremum is computed in, its action is the same. -/
theorem extremum_L_mirror {ss : List CState} {e : CState}
    (h : extremum ss = some e) :
    extremum (ss.map mirror) = some (mirror e) ∧
    L (mirror e) = L e := by
  refine ⟨?_, L_mirror e⟩
  rw [extremum_mirrorCosmos, h]
  rfl
 
/-- Summation splits over concatenation of cosmoses. -/
theorem foldSum_append (f : CState → Nat) (xs ys : List CState) :
    foldSum f (xs ++ ys) = foldSum f xs + foldSum f ys := by
  induction xs with
  | nil =>
    show foldSum f ys = 0 + foldSum f ys
    rw [Nat.zero_add]
  | cons s ss ih =>
    show f s + foldSum f (ss ++ ys) = (f s + foldSum f ss) + foldSum f ys
    rw [ih, Nat.add_assoc]
 
/-- Flatten a hierarchy of cosmoses into one cosmos. -/
def flatten : List (List CState) → List CState
  | [] => []
  | ss :: sss => ss ++ flatten sss
 
/-- Total mass at the second hierarchy level. -/
def totalMassH : List (List CState) → Nat
  | [] => 0
  | ss :: sss => totalMass ss + totalMassH sss
 
/-- Total energy at the second hierarchy level. -/
def totalEnergyH : List (List CState) → Nat
  | [] => 0
  | ss :: sss => totalEnergy ss + totalEnergyH sss
 
/-- Total mass splits over concatenation. -/
theorem totalMass_append (xs ys : List CState) :
    totalMass (xs ++ ys) = totalMass xs + totalMass ys :=
  foldSum_append _ _ _
 
/-- Total energy splits over concatenation. -/
theorem totalEnergy_append (xs ys : List CState) :
    totalEnergy (xs ++ ys) = totalEnergy xs + totalEnergy ys :=
  foldSum_append _ _ _
 
/-- Flattening preserves total mass. -/
theorem totalMass_flatten (sss : List (List CState)) :
    totalMass (flatten sss) = totalMassH sss := by
  induction sss with
  | nil => rfl
  | cons ss sss ih =>
    show totalMass (ss ++ flatten sss) = totalMass ss + totalMassH sss
    rw [totalMass_append, ih]
 
/-- Flattening preserves total energy. -/
theorem totalEnergy_flatten (sss : List (List CState)) :
    totalEnergy (flatten sss) = totalEnergyH sss := by
  induction sss with
  | nil => rfl
  | cons ss sss ih =>
    show totalEnergy (ss ++ flatten sss) = totalEnergy ss + totalEnergyH sss
    rw [totalEnergy_append, ih]
 
/-- The mass–energy identity at the second hierarchy level. -/
theorem totalEnergyH_eq (sss : List (List CState)) :
    totalEnergyH sss = totalMassH sss * K := by
  induction sss with
  | nil => rfl
  | cons ss sss ih =>
    show totalEnergy ss + totalEnergyH sss
        = (totalMass ss + totalMassH sss) * K
    rw [totalEnergy_eq, ih, Nat.add_mul]
 
/-- The identity seen from the flattened cosmos: summing the micro
    level directly, or descending through the hierarchy, gives the
    same mass–energy relation. -/
theorem hierarchy_identity (sss : List (List CState)) :
    totalEnergy (flatten sss) = totalMass (flatten sss) * K ∧
    totalEnergyH sss = totalMassH sss * K :=
  ⟨totalEnergy_eq _, totalEnergyH_eq _⟩
 
/-- Subsystem consistency: any filtered subsystem of a consistent
    cosmos is itself error-free. -/
theorem macroErr_filter {ss : List CState} (p : CState → Bool)
    (h : ∀ s ∈ ss, s.err = 0) : macroErr (ss.filter p) = 0 := by
  apply macroErr_eq_zero
  intro s hs
  exact h s (List.mem_filter.mp hs).1
 
/-- One step of the mirror evolution: every state is replaced by its
    mirror. -/
def evolve (ss : List CState) : List CState := ss.map mirror
 
/-- The mirror evolution is an involution: two steps return the
    cosmos to itself. -/
theorem evolve_involutive (ss : List CState) :
    evolve (evolve ss) = ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    show mirror (mirror s) :: evolve (evolve ss) = s :: ss
    rw [mirror_involutive, ih]
 
/-- Mass is preserved by the evolution. -/
theorem totalMass_evolve (ss : List CState) :
    totalMass (evolve ss) = totalMass ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    show s.mass + totalMass (evolve ss) = s.mass + totalMass ss
    rw [ih]
 
/-- Energy is preserved by the evolution. -/
theorem totalEnergy_evolve (ss : List CState) :
    totalEnergy (evolve ss) = totalEnergy ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    show s.mass * K + totalEnergy (evolve ss)
        = s.mass * K + totalEnergy ss
    rw [ih]
 
/-- Error is preserved by the evolution: the evolution neither
    creates nor repairs inconsistency. -/
theorem macroErr_evolve (ss : List CState) :
    macroErr (evolve ss) = macroErr ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    show s.err + macroErr (evolve ss) = s.err + macroErr ss
    rw [ih]
 
/-- Total action is preserved by the evolution. -/
theorem action_evolve (ss : List CState) :
    foldSum L (evolve ss) = foldSum L ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    show L (mirror s) + foldSum L (evolve ss) = L s + foldSum L ss
    rw [L_mirror, ih]
 
/-- `n` steps of the mirror evolution. -/
def evolveN : Nat → List CState → List CState
  | 0, ss => ss
  | n + 1, ss => evolveN n (evolve ss)
 
/-- The evolution preserves the size of the cosmos. -/
theorem evolveN_length (n : Nat) (ss : List CState) :
    (evolveN n ss).length = ss.length := by
  induction n generalizing ss with
  | zero => rfl
  | succ n ih =>
    show (evolveN n (evolve ss)).length = ss.length
    rw [ih]
    show (ss.map mirror).length = ss.length
    rw [List.length_map]
 
/-- Error after any number of steps equals the initial error:
    inconsistency is never amplified by the evolution. -/
theorem macroErr_evolveN (n : Nat) (ss : List CState) :
    macroErr (evolveN n ss) = macroErr ss := by
  induction n generalizing ss with
  | zero => rfl
  | succ n ih =>
    show macroErr (evolveN n (evolve ss)) = macroErr ss
    rw [ih, macroErr_evolve]
 
/-- Consistency is preserved pointwise for all times: every state of
    the evolved cosmos is error-free if every initial state is. -/
theorem coherence_preserved (n : Nat) {ss : List CState}
    (h : ∀ s ∈ ss, s.err = 0) :
    ∀ s ∈ evolveN n ss, s.err = 0 := by
  induction n generalizing ss with
  | zero => exact h
  | succ n ih =>
    apply ih
    intro s hs
    rw [evolve, List.mem_map] at hs
    cases hs with
    | intro t ht =>
      cases ht with
      | intro htmem hteq =>
        rw [← hteq]
        exact h t htmem
 
/-- Eternal coherence: run the derivation machine all the way. For
    every number of evolution steps, a consistent cosmos still has
    an extremal state, vanishing macro error, and the mass–energy
    identity. The derivation does not terminate — it closes for all
    times at once, by induction. -/
theorem eternal_coherence (n : Nat) {ss : List CState} (hne : ss ≠ [])
    (hcons : ∀ s ∈ ss, s.err = 0) :
    ∃ e, e ∈ evolveN n ss ∧ (∀ s ∈ evolveN n ss, L e ≤ L s) ∧
      L (mirror e) = L e ∧ macroErr (evolveN n ss) = 0 ∧
      totalEnergy (evolveN n ss) = totalMass (evolveN n ss) * K := by
  have hne' : evolveN n ss ≠ [] := by
    intro hempty
    have hlen := evolveN_length n ss
    rw [hempty] at hlen
    cases ss with
    | nil => exact hne rfl
    | cons a tl =>
      rw [List.length_cons] at hlen
      change (0 : Nat) = tl.length + 1 at hlen
      omega
  cases extremal_exists hne' with
  | intro e he =>
    exact ⟨e, he.1, he.2, L_mirror e,
      by rw [macroErr_evolveN]; exact macroErr_eq_zero hcons,
      totalEnergy_eq _⟩
 
-- Two evolution steps return the demo cosmos to itself.
example : evolve (evolve demo) = demo := evolve_involutive demo
 
-- Coherence at time 3, checked concretely.
example : macroErr (evolveN 3 demo) = 0 := by decide
example : totalEnergy (evolveN 3 demo) = 189 := by decide
 
#print axioms eternal_coherence
#print axioms extremum_mirrorCosmos
#print axioms totalEnergyH_eq
#print axioms extremal_stable
 
end CosmologyDerivationExt
