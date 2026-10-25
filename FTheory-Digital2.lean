-- License Apache-2.0 Takeo Yamamoto

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Basic

namespace FTheoryDigital

abbrev U64 := ZMod (2^64)

variable {X : Type*} [Fintype X] [DecidableEq X]

/- 1. デジタル Obverse（離散密度・圧力） -/
structure Obverse (X : Type*) where
  rho : X → U64
  p   : X → U64

/- 2. デジタル Reverse（離散法則制約） -/
structure Reverse (X : Type*) where
  Law : (X → U64) → Prop

/- 3. 結合状態 (Psi) -/
structure Psi (X : Type*) where
  phys : Obverse X
  math : Reverse X

/- 4. 離散変分原理（極小値の定義） -/
def Extremal (A : Psi X → ℕ) (Ψ₀ : Psi X) : Prop :=
  ∀ Ψ, A Ψ₀ ≤ A Ψ

/- 5. デジタル無矛盾性 -/
def Consistent (Ψ : Psi X) : Prop :=
  Ψ.math.Law Ψ.phys.rho

/- 6. 完全デジタル F-Theory モデル -/
structure DigitalFTheoryModel (X : Type*) [Fintype X] [DecidableEq X] where
  A : Psi X → ℕ
  Ψ₀ : Psi X
  extremal_condition : Extremal A Ψ₀
  consistency_condition : Consistent Ψ₀

-- =================================================================
-- デジタル定理・導出ブロック
-- =================================================================

/-- 定理 1：基底状態のアクションは、いかなる任意の状態よりも小さいか等しい -/
lemma action_le_of_extremal (M : DigitalFTheoryModel X) (Ψ : Psi X) :
    M.A M.Ψ₀ ≤ M.A Ψ :=
  M.extremal_condition Ψ

/-- 定理 2：基底状態の密度場は、必ず対応するデジタル法則を満たしている -/
lemma ground_state_satisfies_law (M : DigitalFTheoryModel X) :
    M.Ψ₀.math.Law M.Ψ₀.phys.rho :=
  M.consistency_condition

/-- 定理 3：アクション全体に定数 `c` を足し合わせても、極値（基底状態）の性質は崩れない -/
lemma extremal_shift (A : Psi X → ℕ) (Ψ₀ : Psi X) (c : ℕ)
    (h : Extremal A Ψ₀) :
    Extremal (fun Ψ => A Ψ + c) Ψ₀ := by
  intro Ψ
  exact add_le_add_right (h Ψ) c

/-- 定理 4：基底状態よりアクションが厳密に小さい「存在し得ない状態」の排除証明 -/
lemma no_state_below_extremal (M : DigitalFTheoryModel X) (Ψ : Psi X) :
    ¬ (M.A Ψ < M.A M.Ψ₀) := by
  intro h_lt
  have h_le := M.extremal_condition Ψ
  linarith

end FTheoryDigital
