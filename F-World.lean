License Apache 2.0  Takeo Yamamoto
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Basic
import Mathlib.Logic.Basic

namespace FTheory.CosmoWM

/-!
# F-Theory Cosmological Physics — 64-bit 世界モデル版
元の構造（Obverse / Reverse / Psi / Extremal / Consistent / FTheoryModel）を保ち、
「状態が満たすべき条件」だけだった定式化に遷移則を追加する。

遷移則 = 元の公理そのもの
  1. 提案：拡散（隣接差の最小化）と宇宙膨張による希釈で次状態の候補を作る
  2. Reverse（Law）で整合しない候補を棄却（Consistent）
  3. 残った候補から作用 A が最小のものを選ぶ（Extremal）
-/

/-! ## Q32.32 固定小数点 -/

structure Q64 where
  raw : BitVec 64
  deriving DecidableEq, Repr

namespace Q64
def fracBits : Nat := 32
def toInt (a : Q64) : Int := a.raw.toInt
def ofInt (z : Int) : Q64 := ⟨BitVec.ofInt 64 z⟩
def ofNat' (k : Nat) : Q64 := ofInt ((k : Int) * 2 ^ fracBits)
def zero : Q64 := ⟨0⟩
def one : Q64 := ofNat' 1

instance : LE Q64 := ⟨fun a b => a.toInt ≤ b.toInt⟩
instance : LT Q64 := ⟨fun a b => a.toInt < b.toInt⟩
instance (a b : Q64) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.toInt ≤ b.toInt))
instance (a b : Q64) : Decidable (a < b) := inferInstanceAs (Decidable (a.toInt < b.toInt))
instance : Add Q64 := ⟨fun a b => ⟨a.raw + b.raw⟩⟩   -- 64bit ラップ
instance : Sub Q64 := ⟨fun a b => ⟨a.raw - b.raw⟩⟩
instance : Mul Q64 := ⟨fun a b => ofInt ((a.toInt * b.toInt) / 2 ^ fracBits)⟩
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

/-- 有限候補集合上の最小性（変分原理） -/
def Extremal {n : Nat} (A : Psi n → Q64) (Ψ₀ : Psi n) (cands : List (Psi n)) : Prop :=
  ∀ Ψ ∈ cands, A Ψ₀ ≤ A Ψ

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

/-! ## 世界モデル：遷移則の追加 -/

section Dynamics
variable {n : Nat} [NeZero n]

/-- 動力学パラメータ -/
structure Dyn (n : Nat) where
  A    : Psi n → Q64    -- 作用
  w    : Q64            -- 状態方程式 p = w ρ
  H    : Q64            -- ハッブル率（希釈：dρ = -3H(ρ+p)dt）
  etas : List Q64       -- 拡散ステップ幅の候補

/-- 周期境界の離散ラプラシアン -/
def lap (f : Fin n → Q64) (i : Fin n) : Q64 :=
  f (i - 1) + f (i + 1) - (f i + f i)

/-- 作用：隣接差の二乗和（平滑さ） -/
def energy (f : Fin n → Q64) : Q64 :=
  (List.finRange n).foldl
    (fun acc i => acc + (f (i + 1) - f i) * (f (i + 1) - f i)) Q64.zero

/-- 提案 1：拡散（A2：近傍のみに依存）。圧力は状態方程式で更新 -/
def diffuse (D : Dyn n) (η : Q64) (Ψ : Psi n) : Psi n :=
  let ρ' : Fin n → Q64 := fun i => Ψ.phys.ρ i + η * lap Ψ.phys.ρ i
  ⟨⟨ρ', fun i => D.w * ρ' i⟩, Ψ.math⟩

/-- 提案 2：宇宙膨張による希釈（連続の式 dρ/dt = -3H(ρ+p)） -/
def dilute (D : Dyn n) (Ψ : Psi n) : Psi n :=
  let ρ' : Fin n → Q64 := fun i =>
    Ψ.phys.ρ i - Q64.ofNat' 3 * D.H * (Ψ.phys.ρ i + Ψ.phys.p i)
  ⟨⟨ρ', fun i => D.w * ρ' i⟩, Ψ.math⟩

def proposals (D : Dyn n) (Ψ : Psi n) : List (Psi n) :=
  D.etas.map fun η => dilute D (diffuse D η Ψ)

/-- 作用最小の候補を選ぶ（同値なら先頭を優先） -/
def argminBy (A : Psi n → Q64) : List (Psi n) → Option (Psi n)
  | []      => none
  | x :: xs => some (xs.foldl (fun best y => if A y < A best then y else best) x)

/-- 法則に整合する候補だけを残す（Consistent） -/
def admissible (D : Dyn n) (Ψ : Psi n) : List (Psi n) :=
  (proposals D Ψ).filter fun Ψ' => Ψ'.math.Law Ψ'.phys.ρ

/-- 1 ステップ予測。整合する候補がなければ状態を据え置く -/
def step (D : Dyn n) (Ψ : Psi n) : Psi n :=
  match argminBy D.A (admissible D Ψ) with
  | some Ψ' => Ψ'
  | none    => Ψ

def rollout (D : Dyn n) (Ψ : Psi n) (k : Nat) : Psi n :=
  (List.range k).foldl (fun s _ => step D s) Ψ

/-- 実行時検査：出力が Consistent かつ候補内で Extremal -/
def stepOK (D : Dyn n) (Ψ : Psi n) : Bool :=
  let cs := admissible D Ψ
  let out := step D Ψ
  cs.isEmpty || (decide (Consistent out) && decide (Extremal D.A out cs))

end Dynamics

/-! ## 実行例（n = 4, ρ = [4,0,0,0]） -/

def nonnegLaw {n : Nat} : Reverse n :=
  ⟨fun f => (List.finRange n).all fun i => decide (Q64.zero ≤ f i)⟩

def D0 : Dyn 4 :=
  ⟨fun Ψ => energy Ψ.phys.ρ, Q64.zero, Q64.zero,
   [Q64.zero, Q64.ofInt (2 ^ 29), Q64.ofInt (2 ^ 30)]⟩   -- η ∈ {0, 1/8, 1/4}

def Ψ0 : Psi 4 :=
  ⟨⟨fun i => if i.val == 0 then Q64.ofNat' 4 else Q64.zero, fun _ => Q64.zero⟩, nonnegLaw⟩

def dump {n : Nat} (f : Fin n → Q64) : List Int := (List.finRange n).map fun i => (f i).toInt

#eval dump (rollout D0 Ψ0 2).phys.ρ
-- 期待値（手計算）: [6442450944, 4294967296, 2147483648, 4294967296] = [1.5, 1, 0.5, 1]
#eval stepOK D0 Ψ0     -- true
#eval stepOK D0 (step D0 Ψ0)   -- true

-- 宇宙膨張あり（H = 1/64, w = 1/3）：総質量が単調に減る様子を見る（期待値は未計算）
def D1 : Dyn 4 := { D0 with H := Q64.ofInt (2 ^ 26), w := Q64.ofInt (2 ^ 32 / 3) }
#eval dump (rollout D1 Ψ0 3).phys.ρ

end FTheory.CosmoWM
