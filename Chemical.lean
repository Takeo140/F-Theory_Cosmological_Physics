License Apache-2.0  Takeo Yamamoto
import Mathlib.Tactic

namespace ChemicalSynthesisLean

/-- 化学種（反応物・生成物・溶媒や官能基ブロックなど）を表す型 -/
inductive Species where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- 1ステップの化学反応：
    `reactantCoef`（消費する化学量論係数、非負）と
    `productCoef`（生成する化学量論係数、非負）を持つ -/
structure ReactionStep where
  reactantCoef : Species → Nat
  productCoef  : Species → Nat
  deriving Repr

/-- 初期仕込み量（モル数やスケールされた非負整数量） -/
def MolarAmount := Species → Nat

/-- 進行度 `xi` だけ反応が進んだときの残量・生成量（反応物消費分を引いた量） -/
def advanceAmount (init : MolarAmount) (step : ReactionStep) (xi : Nat) : MolarAmount :=
  fun s => init s + step.productCoef s * xi - step.reactantCoef s * xi

/-- 進行度 `xi` が、指定した律速種 `lim` に関して物理的に実行可能か
    （消費量 `coef * xi` が初期量 `init lim` 以下であること） -/
def FeasibleForSpecies (init : MolarAmount) (step : ReactionStep) (lim : Species) (xi : Nat) : Prop :=
  step.reactantCoef lim * xi ≤ init lim

/-- 律速種 `lim` の化学量論係数が正（`c > 0`）のとき、
    最大進行度 `init lim / c` は実行可能であることを証明 -/
theorem max_extent_feasible {init : MolarAmount} {step : ReactionStep} {lim : Species}
    (hpos : 0 < step.reactantCoef lim) :
    FeasibleForSpecies init step lim (init lim / step.reactantCoef lim) := by
  dsimp [FeasibleForSpecies]
  rw [Nat.mul_comm]
  exact Nat.div_mul_le_self (init lim) (step.reactantCoef lim)

/-- `init lim / c` を超える進行度 `xi` をとると、律速種 `lim` の必要消費量が初期量を超えること -/
theorem exceed_limiting_reagent {init : MolarAmount} {step : ReactionStep} {lim : Species}
    {xi : Nat} (hpos : 0 < step.reactantCoef lim)
    (hgt : init lim / step.reactantCoef lim < xi) :
    init lim < step.reactantCoef lim * xi := by
  by_contra hle
  have hnot_lt : ¬ init lim < step.reactantCoef lim * xi := hle
  have hle' : step.reactantCoef lim * xi ≤ init lim := Nat.not_lt.mp hnot_lt
  have hdiv : xi ≤ init lim / step.reactantCoef lim := by
    exact (Nat.le_div_iff_mul_le hpos).mpr (by simpa [Nat.mul_comm] using hle')
  omega

/-- 化学種 `s` の消費量が初期量以下のとき、`advanceAmount` で `init s + prod * xi` から
    `reactant * xi` を引く際に `Nat` の打ち切り減算（`0` 張り付き）が起きないことの補題 -/
theorem advance_no_underflow {init : MolarAmount} {step : ReactionStep} {s xi : Nat}
    (hcons : step.reactantCoef s * xi ≤ init s) :
    step.reactantCoef s * xi ≤ init s + step.productCoef s * xi := by
  omega

/-- 二段階逐次合成（Step 1 の出力を Step 2 の初期仕込みとして引き継ぐ）における
    進行度の組 `(xi1, xi2)` が両ステップで消費超過を起こさない条件 -/
def TwoStageFeasible (init : MolarAmount) (r1 r2 : ReactionStep) (xi1 xi2 : Nat) : Prop :=
  (∀ s, r1.reactantCoef s * xi1 ≤ init s) ∧
  (∀ s, r2.reactantCoef s * xi2 ≤ advanceAmount init r1 xi1 s)

/-- 二段階逐次合成が実行可能なとき、第1段の生成物増分が第2段の仕込みに正しく反映されること -/
theorem two_stage_intermediate_amount {init : MolarAmount} {r1 r2 : ReactionStep}
    {xi1 xi2 : Nat} (hfeas : TwoStageFeasible init r1 r2 xi1 xi2) (s : Species) :
    advanceAmount init r1 xi1 s = init s + r1.productCoef s * xi1 - r1.reactantCoef s * xi1 := by
  rfl

/-- 例：A + 2B -> C のような反応系を定義するヘルパー -/
def exampleStepABtoC : ReactionStep where
  reactantCoef
    | .A => 1
    | .B => 2
    | _  => 0
  productCoef
    | .C => 1
    | _  => 0

/-- `A = 5`, `B = 7` のとき、`B`（係数 2）を基準にした最大進行度は `7 / 2 = 3` であり、
    `xi = 3` では `B` の消費量 `2 * 3 = 6 ≤ 7` となることの具体検証 -/
theorem example_limiting_B :
    let init : MolarAmount := fun s => match s with
      | .A => 5
      | .B => 7
      | _  => 0
    FeasibleForSpecies init exampleStepABtoC .B (init .B / exampleStepABtoC.reactantCoef .B) ∧
      init .B / exampleStepABtoC.reactantCoef .B = 3 := by
  constructor
  · exact max_extent_feasible (by decide)
  · decide

end ChemicalSynthesisLean
