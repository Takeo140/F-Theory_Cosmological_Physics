License Apache 2.0  Takeo Yamamoto
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Basic
import Mathlib.Logic.Basic

namespace FTheory.WM

/-!
# F-Theory Cosmological Physics — 64-bit 世界モデル（完全版）

位置づけ：数理（Reverse）と物理（Obverse）のデジタルツイン。
  物理側の状態が数理側の法則を満たすこと（Consistent）が双子としての同期条件。
  ℝ 版との近似誤差は未評価（構造を保った離散版）。

元の構造（Obverse / Reverse / Psi / Extremal / Consistent / FTheoryModel /
internal_coherence）はそのまま保ち、世界モデルに必要な要素を足してある。

| 世界モデルの要素 | 実装 |
|---|---|
| 状態       | `World n` = `Psi n`（ρ, p, Law）＋ 運動量 `m` |
| 動力学     | 1 次元周期格子の音響系 ρ_t = -m_x, m_t = -p_x, p = wρ（保存型・界面フラックス） |
| 行動       | 外力 `f : Fin n → Q64`（運動量への入力） |
| 観測       | `observe`：ブロック和（A4：ミクロ → マクロ） |
| A1 極値    | 同じ物理時間 T を進める刻み幅の候補のうち、エネルギー変化が最小のものを選ぶ |
| A3 整合性  | Law（密度の範囲）と状態方程式 p = wρ を満たさない候補は棄却。全滅なら据え置き |
| 同期       | `sync`：観測 y で密度を補正（Law を破る補正は棄却）。`twinStep` = 予測 → 補正 |
| 検査       | `stepOK`, `massOf`, `momOf`, `macroOK`（保存則とマクロ整合） |

数値は Q32.32 固定小数点（BitVec 64）で、加減乗は Int64 範囲に飽和する（ラップしない）。
質量・運動量はフラックスの望遠鏡和なので、飽和が起きない限り丸めても厳密に保存される。
-/

/-! ## Q32.32 固定小数点（飽和演算） -/

structure Q64 where
  raw : BitVec 64
  deriving DecidableEq, Repr

namespace Q64
def fracBits : Nat := 32
def minI : Int := -(2 ^ 63)
def maxI : Int := 2 ^ 63 - 1
def toInt (a : Q64) : Int := a.raw.toInt
def ofInt (z : Int) : Q64 := ⟨BitVec.ofInt 64 z⟩
/-- Int64 範囲に飽和させてから Q64 にする -/
def sat (z : Int) : Q64 := ofInt (max minI (min maxI z))
def ofNat' (k : Nat) : Q64 := sat ((k : Int) * 2 ^ fracBits)
def zero : Q64 := ⟨0⟩
def one : Q64 := ofNat' 1
def half (a : Q64) : Q64 := ofInt (a.toInt / 2)
def absQ (a : Q64) : Q64 := if a.toInt < 0 then sat (-a.toInt) else a

instance : Inhabited Q64 := ⟨zero⟩
instance : LE Q64 := ⟨fun a b => a.toInt ≤ b.toInt⟩
instance : LT Q64 := ⟨fun a b => a.toInt < b.toInt⟩
instance (a b : Q64) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.toInt ≤ b.toInt))
instance (a b : Q64) : Decidable (a < b) := inferInstanceAs (Decidable (a.toInt < b.toInt))
instance : Add Q64 := ⟨fun a b => sat (a.toInt + b.toInt)⟩
instance : Sub Q64 := ⟨fun a b => sat (a.toInt - b.toInt)⟩
instance : Mul Q64 := ⟨fun a b => sat ((a.toInt * b.toInt) / 2 ^ fracBits)⟩
end Q64

/-! ## 元の構造（離散・64bit 版） -/

structure Obverse (n : Nat) where
  ρ : Fin n → Q64   -- density
  p : Fin n → Q64   -- pressure

structure Reverse (n : Nat) where
  Law : (Fin n → Q64) → Bool   -- 決定可能な法則制約

structure Psi (n : Nat) where
  phys : Obverse n
  math : Reverse n

/-- 有限候補集合上の最小性（一般の状態型版） -/
def ExtremalOn {α : Type} (A : α → Q64) (x₀ : α) (cands : List α) : Prop :=
  ∀ x ∈ cands, A x₀ ≤ A x

instance {α : Type} (A : α → Q64) (x₀ : α) (cands : List α) :
    Decidable (ExtremalOn A x₀ cands) := by
  unfold ExtremalOn; infer_instance

/-- 元の `Extremal`（Psi 上の変分原理） -/
def Extremal {n : Nat} (A : Psi n → Q64) (Ψ₀ : Psi n) (cands : List (Psi n)) : Prop :=
  ExtremalOn A Ψ₀ cands

instance {n : Nat} (A : Psi n → Q64) (Ψ₀ : Psi n) (cands : List (Psi n)) :
    Decidable (Extremal A Ψ₀ cands) := by
  unfold Extremal; infer_instance

def Consistent {n : Nat} (Ψ : Psi n) : Prop :=
  Ψ.math.Law Ψ.phys.ρ = true

instance {n : Nat} (Ψ : Psi n) : Decidable (Consistent Ψ) := by
  unfold Consistent; infer_instance

structure FTheoryModel (n : Nat) where
  A : Psi n → Q64
  cands : List (Psi n)
  Ψ₀ : Psi n
  extremal_condition : Extremal A Ψ₀ cands
  consistency_condition : Consistent Ψ₀

theorem internal_coherence {n : Nat} (M : FTheoryModel n) :
    Extremal M.A M.Ψ₀ M.cands ∧ Consistent M.Ψ₀ :=
  ⟨M.extremal_condition, M.consistency_condition⟩

/-! ## 世界モデルの状態 -/

/-- 世界の状態：結合状態 Ψ（物理 ρ,p ＋ 数理 Law）と運動量 m -/
structure World (n : Nat) where
  Ψ : Psi n
  m : Fin n → Q64

def sumQ {n : Nat} (f : Fin n → Q64) : Q64 :=
  (List.finRange n).foldl (fun acc i => acc + f i) Q64.zero

/-- 評価を 1 回に抑える（関数の入れ子による指数的な再計算を避ける） -/
def memo {n : Nat} (f : Fin n → Q64) : Fin n → Q64 :=
  let t := Array.ofFn f
  fun i => t[i.val]!

def zeroF {n : Nat} : Fin n → Q64 := fun _ => Q64.zero

/-- 法則：各セルが [lo, hi] に収まる -/
def boundedLaw {n : Nat} (lo hi : Q64) : Reverse n :=
  ⟨fun f => (List.finRange n).all fun i => decide (lo ≤ f i ∧ f i ≤ hi)⟩

/-- 状態方程式 p = wρ を満たす世界を作る -/
def mkWorld {n : Nat} (w : Q64) (law : Reverse n) (ρ m : Fin n → Q64) : World n :=
  ⟨⟨⟨ρ, fun i => w * ρ i⟩, law⟩, m⟩

/-- 保存量：質量・運動量 -/
def massOf {n : Nat} (W : World n) : Q64 := sumQ W.Ψ.phys.ρ
def momOf {n : Nat} (W : World n) : Q64 := sumQ W.m

/-- エネルギー（音響系の保存量）：Σ (wρ² + m²) -/
def energy {n : Nat} (w : Q64) (W : World n) : Q64 :=
  sumQ fun i => w * W.Ψ.phys.ρ i * W.Ψ.phys.ρ i + W.m i * W.m i

/-- 動力学パラメータ -/
structure Dyn (n : Nat) where
  w      : Q64                              -- 状態方程式 p = w ρ
  sched  : List (Q64 × Nat)                 -- 候補：(刻み dt, 回数 N)。N·dt は同じ物理時間 T にそろえる
  action : World n → World n → Q64          -- 作用 A(現在, 候補)

/-! ## 動力学・予測・観測・同期 -/

section Dynamics
variable {n : Nat} [NeZero n]

/-- 1 刻み：運動量を圧力の界面インパルスで更新 → 新しい運動量の界面フラックスで密度を更新。
    各界面の項は 2 つのセルに ± で現れるので、質量・運動量は厳密に保存される。 -/
def stepWith (D : Dyn n) (dt : Q64) (f : Fin n → Q64) (W : World n) : World n :=
  let ρ := W.Ψ.phys.ρ
  let p := W.Ψ.phys.p
  let g : Fin n → Q64 := memo fun i => dt * Q64.half (p i + p (i + 1))
  let m' : Fin n → Q64 := memo fun i => W.m i - (g i - g (i - 1)) + dt * f i
  let q : Fin n → Q64 := memo fun i => dt * Q64.half (m' i + m' (i + 1))
  let ρ' : Fin n → Q64 := memo fun i => ρ i - (q i - q (i - 1))
  ⟨⟨⟨ρ', memo fun i => D.w * ρ' i⟩, W.Ψ.math⟩, m'⟩

def advance (D : Dyn n) (dt : Q64) (k : Nat) (f : Fin n → Q64) (W : World n) : World n :=
  (List.range k).foldl (fun s _ => stepWith D dt f s) W

/-- A3：Reverse の法則を満たすか -/
def lawOK (W : World n) : Bool := W.Ψ.math.Law W.Ψ.phys.ρ

/-- A3：状態方程式 p = wρ を満たすか -/
def eosOK (D : Dyn n) (W : World n) : Bool :=
  (List.finRange n).all fun i => decide (W.Ψ.phys.p i = D.w * W.Ψ.phys.ρ i)

/-- 提案：各候補（dt, N）で同じ物理時間だけ進めた状態 -/
def proposals (D : Dyn n) (f : Fin n → Q64) (W : World n) : List (World n) :=
  D.sched.map fun c => advance D c.1 c.2 f W

/-- 整合する候補だけを残す -/
def admissible (D : Dyn n) (f : Fin n → Q64) (W : World n) : List (World n) :=
  (proposals D f W).filter fun W' => lawOK W' && eosOK D W'

/-- 作用最小の候補（同値なら先頭） -/
def argminBy {α : Type} (A : α → Q64) : List α → Option α
  | []      => none
  | x :: xs => some (xs.foldl (fun best y => if A y < A best then y else best) x)

/-- 1 ステップ予測（行動 f を入力）。整合する候補がなければ据え置く -/
def step (D : Dyn n) (f : Fin n → Q64) (W : World n) : World n :=
  match argminBy (D.action W) (admissible D f W) with
  | some W' => W'
  | none    => W

/-- 行動列に沿った多ステップ予測 -/
def rollout (D : Dyn n) (fs : List (Fin n → Q64)) (W : World n) : World n :=
  fs.foldl (fun s f => step D f s) W

/-- 外力なしで k ステップ -/
def rolloutFree (D : Dyn n) (k : Nat) (W : World n) : World n :=
  (List.range k).foldl (fun s _ => step D zeroF s) W

/-- 実行時検査：出力が整合し、かつ整合候補の中で作用最小 -/
def stepOK (D : Dyn n) (f : Fin n → Q64) (W : World n) : Bool :=
  let cs := admissible D f W
  let out := step D f W
  cs.isEmpty || (lawOK out && eosOK D out && decide (ExtremalOn (D.action W) out cs))

/-- A4：観測（k セルずつのブロック和＝マクロ量） -/
def observe (k m : Nat) (f : Fin n → Q64) : Fin m → Q64 :=
  fun b => (List.range k).foldl (fun acc j =>
    let idx := b.val * k + j
    if h : idx < n then acc + f ⟨idx, h⟩ else acc) Q64.zero

/-- A4：マクロ質量とミクロ質量の一致（k·m = n のとき成立するはず） -/
def macroOK (k m : Nat) (W : World n) : Bool :=
  decide (sumQ (observe k m W.Ψ.phys.ρ) = massOf W)

/-- 同期：観測 y（密度）で補正。Law を破る補正は棄却して元の状態を保つ -/
def sync (D : Dyn n) (gain : Q64) (y : Fin n → Q64) (W : World n) : World n :=
  let ρ' : Fin n → Q64 := memo fun i => W.Ψ.phys.ρ i + gain * (y i - W.Ψ.phys.ρ i)
  let W' : World n := ⟨⟨⟨ρ', memo fun i => D.w * ρ' i⟩, W.Ψ.math⟩, W.m⟩
  if lawOK W' then W' else W

/-- デジタルツインの 1 周期：予測 → 補正 -/
def twinStep (D : Dyn n) (gain : Q64) (f y : Fin n → Q64) (W : World n) : World n :=
  sync D gain y (step D f W)

/-- 観測との L1 誤差 -/
def l1err (y : Fin n → Q64) (W : World n) : Q64 :=
  sumQ fun i => Q64.absQ (y i - W.Ψ.phys.ρ i)

end Dynamics

def dump {n : Nat} (f : Fin n → Q64) : List Int := (List.finRange n).map fun i => (f i).toInt

/-! ## 実行例（n = 8, 背景密度 1 に山 +1, w = 1/4, T = 1/2） -/

def wQ : Q64 := Q64.ofInt (2 ^ 30)   -- 1/4

/-- 候補：(1/2, 1 回), (1/4, 2 回), (1/8, 4 回)。作用 = エネルギー変化の大きさ -/
def D0 : Dyn 8 :=
  ⟨wQ,
   [(Q64.ofInt (2 ^ 31), 1), (Q64.ofInt (2 ^ 30), 2), (Q64.ofInt (2 ^ 29), 4)],
   fun cur cand => Q64.absQ (energy wQ cand - energy wQ cur)⟩

def law0 : Reverse 8 := boundedLaw Q64.zero (Q64.ofNat' 4)

def rho0 : Fin 8 → Q64 :=
  fun i => if i.val == 3 || i.val == 4 then Q64.ofNat' 2 else Q64.ofNat' 1

def W0 : World 8 := mkWorld wQ law0 rho0 zeroF

#eval (massOf W0).toInt                                  -- 42949672960（= 10.0）
#eval dump (rolloutFree D0 4 W0).Ψ.phys.ρ
-- 期待値（Python 参照実装）:
--   [4318759717, 4816962898, 4816962899, 7522150969, 7522150968, 4816962898, 4816962899, 4318759712]
#eval (massOf (rolloutFree D0 4 W0)).toInt               -- 42949672960（厳密に保存）
#eval (momOf (rolloutFree D0 4 W0)).toInt                -- 0
#eval stepOK D0 zeroF W0                                 -- true
#eval macroOK 2 4 (rolloutFree D0 4 W0)                  -- true
#eval dump (observe 2 4 (rolloutFree D0 4 W0).Ψ.phys.ρ)
-- 期待値: [9135722615, 12339113868, 12339113866, 9135722611]

-- 行動：セル 0 に外力 f = 1/8 → 運動量の増分は T·f = 1/16 = 2^28
def fForce : Fin 8 → Q64 := fun i => if i.val == 0 then Q64.ofInt (2 ^ 29) else Q64.zero
#eval (momOf (step D0 fForce W0)).toInt                  -- 268435456

-- 同期：ずれたツイン（山の位置が 1 セルずれ）を、観測 y = rho0 で補正（gain = 1/2）
def rhoT : Fin 8 → Q64 :=
  fun i => if i.val == 2 || i.val == 4 then Q64.ofNat' 2 else Q64.ofNat' 1
def WT : World 8 := mkWorld wQ law0 rhoT zeroF
#eval (l1err rho0 WT).toInt                              -- 8589934592（= 2.0）
#eval (l1err rho0 (sync D0 (Q64.ofInt (2 ^ 31)) rho0 WT)).toInt   -- 4294967296（= 1.0）

end FTheory.WM
