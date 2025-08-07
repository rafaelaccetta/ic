import Batteries.Data.List.Basic
import Mathlib.Data.Set.Defs

universe u v w

section
variable
  {σ : Type u}
  {T : Type v}

inductive BExp (T : Type v) : Type v
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

def At (T : Type u) := T → Bool

inductive GuardedString (σ : Type u) (T : Type v)
  | final (state : At T) : GuardedString σ T
  | cons (state : At T) (action : σ) (next : GuardedString σ T) : GuardedString σ T



inductive two where
  | zero : two
  | one : two
deriving DecidableEq, BEq

instance : Zero two where
  zero := two.zero

instance : One two where
  one := two.one



def G (σ : Type u) (T : Type v) (X : Type w) := At T → (two ⊕ σ × X)

structure GCoalgebra (σ : Type u) (T : Type v) where
  states : Type w
  map : states → G σ T states

structure GAutomaton (σ : Type u) (T : Type v) where
  states : Type w
  map : states → G σ T states
  start : states

def accept (X : GAutomaton σ T) (s : X.states) : GuardedString σ T → Prop
  | .final α => X.map s α = Sum.inl 1
  | .cons α p x => ∃ (t : X.states), X.map s α = Sum.inr (p, t) ∧ accept X t x

def l (X : GAutomaton σ T) (s : X.states) := {α : GuardedString σ T // accept X s α}

def language (X : GAutomaton σ T) := l X X.start


def coproduct (X : GCoalgebra σ T) (Y : GCoalgebra σ T) : GCoalgebra σ T :=
  ⟨ (X.states ⊕ Y.states),
    fun z α ↦ match z with
    | .inl x => match (X.map x α) with
                | .inl 0 => .inl 0
                | .inl 1 => .inl 1
                | .inr (a, b) => .inr (a, .inl b)
    | .inr y => match (Y.map y α) with
                | .inl 0 => .inl 0
                | .inl 1 => .inl 1
                | .inr (a, b) => .inr (a, .inr b) ⟩
