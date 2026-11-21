License Apache-2.0  Takeo Yamamoto
import Mathlib.Tactic

namespace PhysicalAIChemLean

/-- 化学合成リアクターの物理状態（離散スケール：例として温度・液位・残量などを `Int` で表現） -/
structure ReactorState where
  temp      : Int  -- 反応槽温度（例：0.1℃単位やスケール整数）
  level     : Int  -- 液位・反応液量
  reagentA  : Int  -- 試薬A残量
  deriving DecidableEq, Repr

/-- センサー観測値（ノイズ・量子化誤差を含む観測） -/
structure SensorReading where
  obsTemp     : Int
  obsLevel    : Int
  obsReagentA : Int
  deriving DecidableEq, Repr

/-- 物理AI（制御ポリシー）が出力する制御アクション -/
structure ControlAction where
  deltaTemp : Int  -- 加熱・冷却の目標変化量
  addVol    : Int  -- 試薬・溶媒の添加量
  deriving DecidableEq, Repr

/-- 物理環境の安全制約（過熱上限・液位上限・試薬残量の非負制約） -/
structure SafetySpec where
  maxTemp    : Int
  maxLevel   : Int
  minReagent : Int
  deriving Repr

/-- センサー観測誤差の許容幅（各チャネルの最大誤差 `eps`） -/
structure SensorBound where
  epsTemp    : Int
  epsLevel   : Int
  epsReagent : Int
  nonneg_temp    : 0 ≤ epsTemp
  nonneg_level   : 0 ≤ epsLevel
  nonneg_reagent : 0 ≤ epsReagent
  deriving Repr

/-- 実状態 `s` に対して観測 `obs` が許容誤差内に収まっていること -/
def WithinSensorBound (b : SensorBound) (s : ReactorState) (obs : SensorReading) : Prop :=
  (obs.obsTemp - s.temp ≤ b.epsTemp ∧ s.temp - obs.obsTemp ≤ b.epsTemp) ∧
  (obs.obsLevel - s.level ≤ b.epsLevel ∧ s.level - obs.obsLevel ≤ b.epsLevel) ∧
  (obs.obsReagentA - s.reagentA ≤ b.epsReagent ∧ s.reagentA - obs.obsReagentA ≤ b.epsReagent)

/-- 状態 `s` が安全仕様 `spec` を満たすこと -/
def IsSafeState (spec : SafetySpec) (s : ReactorState) : Prop :=
  s.temp ≤ spec.maxTemp ∧
  s.level ≤ spec.maxLevel ∧
  spec.minReagent ≤ s.reagentA

/-- 1ステップの物理遷移モデル（制御アクションと外乱/消費による状態更新）
    - `heatCoupling`：添加や反応に伴う温度寄与の係数（非負）
    - `flowCoupling`：添加量から液位へ反映される係数（非負）
    - `consumeA`：1ステップあたりの試薬A消費量（非負） -/
def stepReactor (heatCoupling flowCoupling consumeA : Int)
    (s : ReactorState) (act : ControlAction) : ReactorState where
  temp     := s.temp + act.deltaTemp + heatCoupling * act.addVol
  level    := s.level + flowCoupling * act.addVol
  reagentA := s.reagentA + act.addVol - consumeA

/-- 物理AIの提案アクション `rawAct` に対し、最悪ケースの観測誤差を考慮して
    安全領域内に収まるようクランプする「安全シールド（Action Shield）」 -/
def shieldAction (spec : SafetySpec) (b : SensorBound)
    (heatCoupling flowCoupling consumeA : Int)
    (obs : SensorReading) (rawAct : ControlAction) : ControlAction :=
  -- 実際の温度は最大で `obs.obsTemp + b.epsTemp + deltaTemp + heatCoupling * addVol` に達し得る
  let maxPossibleTemp := obs.obsTemp + b.epsTemp + rawAct.deltaTemp + heatCoupling * rawAct.addVol
  let safeDeltaTemp :=
    if spec.maxTemp < maxPossibleTemp then
      rawAct.deltaTemp - (maxPossibleTemp - spec.maxTemp)
    else
      rawAct.deltaTemp
  -- 実際の液位は最大で `obs.obsLevel + b.epsLevel + flowCoupling * addVol` に達し得る
  -- ただし `addVol` は非負（`0 ≤ addVol`）を基本とする
  let nonnegAddVol := if rawAct.addVol < 0 then 0 else rawAct.addVol
  let maxPossibleLevel := obs.obsLevel + b.epsLevel + flowCoupling * nonnegAddVol
  let safeAddVol :=
    if spec.maxLevel < maxPossibleLevel ∧ 0 < flowCoupling then
      0
    else
      nonnegAddVol
  { deltaTemp := safeDeltaTemp, addVol := safeAddVol }

/-- 温度に関するシールドの健全性補題：
    センサー誤差が境界内にあり、`0 ≤ heatCoupling` かつ `safeAddVol = rawAct.addVol` のとき、
    シールド後の温度は `spec.maxTemp` を超えない -/
theorem shield_temp_safe {spec : SafetySpec} {b : SensorBound}
    {heatCoupling flowCoupling consumeA : Int}
    {s : ReactorState} {obs : SensorReading} {rawAct : ControlAction}
    (hobs : WithinSensorBound b s obs)
    (hheat : 0 ≤ heatCoupling)
    (hadd : (shieldAction spec b heatCoupling flowCoupling consumeA obs rawAct).addVol = rawAct.addVol) :
    (stepReactor heatCoupling flowCoupling consumeA s
      (shieldAction spec b heatCoupling flowCoupling consumeA obs rawAct)).temp ≤ spec.maxTemp := by
  dsimp [stepReactor, shieldAction] at *
  rcases hobs with ⟨⟨_, htemp_lo⟩, _⟩
  -- `htemp_lo : s.temp - obs.obsTemp ≤ b.epsTemp`
  by_cases hcap : spec.maxTemp <
      obs.obsTemp + b.epsTemp + rawAct.deltaTemp + heatCoupling * rawAct.addVol
  · simp [hcap, hadd]
    omega
  · simp [hcap, hadd]
    omega

/-- 液位に関するシールドの健全性補題：
    センサー誤差が境界内にあり、`0 ≤ flowCoupling` かつ `0 ≤ rawAct.addVol` のとき、
    シールド後の液位は `spec.maxLevel` を超えない -/
theorem shield_level_safe {spec : SafetySpec} {b : SensorBound}
    {heatCoupling flowCoupling consumeA : Int}
    {s : ReactorState} {obs : SensorReading} {rawAct : ControlAction}
    (hobs : WithinSensorBound b s obs)
    (hflow : 0 ≤ flowCoupling)
    (hraw_nonneg : 0 ≤ rawAct.addVol) :
    (stepReactor heatCoupling flowCoupling consumeA s
      (shieldAction spec b heatCoupling flowCoupling consumeA obs rawAct)).level ≤ spec.maxLevel := by
  dsimp [stepReactor, shieldAction] at *
  rcases hobs with ⟨_, ⟨_, hlevel_lo⟩, _⟩
  have hnot_neg : ¬ rawAct.addVol < 0 := by omega
  simp only [hnot_neg, ↓reduceIte]
  by_cases hcap : spec.maxLevel <
      obs.obsLevel + b.epsLevel + flowCoupling * rawAct.addVol
  · by_cases hfc : 0 < flowCoupling
    · simp only [hcap, hfc, ↓reduceIte, mul_zero, add_zero]
      omega
    · simp only [hcap, hfc, ↓reduceIte]
      have hfc_zero : flowCoupling = 0 := by omega
      subst hfc_zero
      simp only [zero_mul] at hcap ⊢
      omega
  · simp only [hcap, ↓reduceIte]
    have hmul : flowCoupling * rawAct.addVol ≤
        flowCoupling * rawAct.addVol := le_rfl
    omega

end PhysicalAIChemLean
