License Apache-2.0  Takeo Yamamoto
import Mathlib.Tactic

namespace DigitalTwinProof

/-- システムの内部状態（例：カウンタ、モード、積算量などの離散状態） -/
structure TwinState where
  counter : Int
  energy  : Int
  deriving DecidableEq, Repr

/-- 外部から与えられる入力イベント（コマンド・外乱・制御入力） -/
inductive Event where
  | tick (stepVal : Int)
  | charge (deltaE : Int)
  | reset
  deriving DecidableEq, Repr

/-- 実機（物理側）の1ステップ遷移関数 -/
def physicalStep (s : TwinState) (ev : Event) : TwinState :=
  match ev with
  | .tick k     => ⟨s.counter + k, s.energy⟩
  | .charge d   => ⟨s.counter, s.energy + d⟩
  | .reset      => ⟨0, 0⟩

/-- デジタルツイン（仮想モデル側）の1ステップ遷移関数
    （例：カウンタは実機と同一、エネルギーはモデル上の損失 `loss` を差し引いた近似値を保持） -/
def twinStep (loss : Int) (t : TwinState) (ev : Event) : TwinState :=
  match ev with
  | .tick k     => ⟨t.counter + k, t.energy⟩
  | .charge d   => ⟨t.counter, t.energy + d - loss⟩
  | .reset      => ⟨0, 0⟩

/-- 実機状態 `s` とデジタルツイン状態 `t` が「同期不変式」を満たす条件
    1. カウンタは完全に一致する（`s.counter = t.counter`）
    2. エネルギーはツイン側のモデル誤差・オフセット許容幅 `tol` 以内に収まる -/
def SyncInvariant (tol : Int) (s : TwinState) (t : TwinState) : Prop :=
  s.counter = t.counter ∧
  t.energy - s.energy ≤ tol ∧
  s.energy - t.energy ≤ tol

/-- 定理1：単一イベント遷移におけるデジタルツインの同期保存
    実機とツインが初期同期しており、イベントごとのエネルギー変化のズレが許容幅 `tol` に収まるなら、
    1ステップ後の状態も `SyncInvariant tol` を満たす。 -/
theorem sync_step_preserved {tol loss : Int} {s t : TwinState} (ev : Event)
    (hsync : SyncInvariant tol s t)
    (htol_nonneg : 0 ≤ tol)
    (hcharge_ok : ∀ d, -tol ≤ loss ∧ loss ≤ tol) :
    SyncInvariant tol (physicalStep s ev) (twinStep loss t ev) := by
  rcases hsync with ⟨hcnt, hlo, hhi⟩
  cases ev with
  | tick k =>
    simp [SyncInvariant, physicalStep, twinStep, hcnt, hlo, hhi]
  | charge d =>
    rcases hcharge_ok d with ⟨hloss_lo, hloss_hi⟩
    dsimp [SyncInvariant, physicalStep, twinStep] at *
    refine ⟨hcnt, ?_, ?_⟩ <;> omega
  | reset =>
    simp [SyncInvariant, physicalStep, twinStep, htol_nonneg]

/-- イベント列（リスト）を順次適用したときの両系の状態遷移 -/
def runPhysical (s : TwinState) : List Event → TwinState
  | []      => s
  | e :: es => runPhysical (physicalStep s e) es

def runTwin (loss : Int) (t : TwinState) : List Event → TwinState
  | []      => t
  | e :: es => runTwin loss (twinStep loss t e) es

/-- 定理2：任意のイベント列に対するデジタルツイン同期の帰納的保存定理
    初期状態で `SyncInvariant tol s0 t0` が成り立つならば、任意のイベント列 `evs` を
    実行した後も `SyncInvariant tol (runPhysical s0 evs) (runTwin loss t0 evs)` が成り立つ。 -/
theorem sync_trace_preserved {tol loss : Int} {s0 t0 : TwinState}
    (evs : List Event)
    (hsync0 : SyncInvariant tol s0 t0)
    (htol_nonneg : 0 ≤ tol)
    (hcharge_ok : ∀ d, -tol ≤ loss ∧ loss ≤ tol) :
    SyncInvariant tol (runPhysical s0 evs) (runTwin loss t0 evs) := by
  induction evs generalizing s0 t0 with
  | nil =>
    simpa [runPhysical, runTwin] using hsync0
  | cons e es ih =>
    dsimp [runPhysical, runTwin]
    apply ih
    exact sync_step_preserved e hsync0 htol_nonneg hcharge_ok

/-- 具体例：初期状態 `(0, 0)` から `[.tick 3, .charge 10, .tick 2]` を実行したとき、
    `loss = 1`, `tol = 2` ならば最終状態でも同期不変式が保たれることの検証 -/
example :
    let s0 : TwinState := ⟨0, 0⟩
    let t0 : TwinState := ⟨0, 0⟩
    let evs : List Event := [.tick 3, .charge 10, .tick 2]
    SyncInvariant 2 (runPhysical s0 evs) (runTwin 1 t0 evs) := by
  apply sync_trace_preserved
  · simp [SyncInvariant]
  · omega
  · intro _
    omega

end DigitalTwinProof
