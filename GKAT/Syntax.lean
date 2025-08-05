import Mathlib.Data.Set.Defs

universe u v w

inductive BExp (T : Type u) : Type u
  | zero : BExp T
  | one : BExp T
  | prim : T → BExp T
  | and : BExp T → BExp T → BExp T
  | or : BExp T → BExp T → BExp T
  | not : BExp T → BExp T
deriving Repr

inductive Exp (σ : Type u) (T : Type v) : Type (max u v)
  | do : σ → Exp σ T
  | assert : BExp T → Exp σ T
  | seq : Exp σ T → Exp σ T → Exp σ T
  | if : BExp T → Exp σ T → Exp σ T → Exp σ T
  | while : BExp T → Exp σ T → Exp σ T
deriving Repr

def Atom (T : Type u) := T → Bool

inductive GuardedString (σ : Type u) (T : Type v)
  | final (state : Atom T) : GuardedString σ T
  | cons (state : Atom T) (action : σ) (next : GuardedString σ T) : GuardedString σ T



inductive G_aux (σ : Type u) (X : Type v) : Type (max u v)
  | zero : G_aux σ X
  | one : G_aux σ X
  | move : (σ × X) → G_aux σ X
deriving DecidableEq

def G (σ : Type u) (T : Type v ) (X : Type w) := (Atom T) → G_aux σ X

structure GCoalgebra (σ : Type u) (T : Type v) (X : Type w) where
  states: Set X
  map : X → G σ T X

structure GAutomaton (σ : Type u) (T : Type v) (X : Type w) where
  states: Set X
  map : X → G σ T X
  start : X

def accept (χ : GAutomaton σ T X) (s : X) : GuardedString σ T → Prop
  | .final α => χ.map s α = .one
  | .cons α p x => ∃ (t : X), t ∈ χ.states ∧ χ.map s α = .move (p, t) ∧ accept χ t x

def const_one (σ : Type u) (T : Type v ) (X : Type w) : G σ T X := fun _ ↦ .one


def uniform_continuation
  (χ : GCoalgebra σ T X)
  (Y : Set X)
  (yss : Y ⊆ χ.states)
  (h : G σ T X) : GCoalgebra σ T X :=
  ⟨ χ.states,
    fun x α ↦
    --(if ((x ∈ Y) ∧ ((χ.map x α) = G_aux.one)) then h α else χ.map x α
    sorry⟩

def coproduct (𝓧 𝓨 : GCoalgebra σ T X) : GCoalgebra σ T X :=
  ⟨ (𝓧.states ∪ 𝓨.states),
    fun x α ↦
    --(if (x ∈ 𝓧.states) then 𝓧.map x α else 𝓨.map x α
    sorry⟩
