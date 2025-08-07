import Mathlib.Data.Set.Defs

universe u v w

section
variable
  {σ : Type u}
  {T : Type v}
  {X : Type w}
  [DecidableEq σ]

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

def G (σ : Type u) (T : Type v) (X : Type w) := At T → (two ⊕ σ × X)

instance : Zero (two ⊕ σ × X) where
  zero := Sum.inl two.zero

instance : One (two ⊕ σ × X) where
  one := Sum.inl two.one

structure GCoalgebra (σ : Type u) (T : Type v) where
  states : Type w
  map : states → G σ T states

structure GAutomaton (σ : Type u) (T : Type v) where
  states : (Type w)
  map : states → G σ T states
  start : states

def accept (X : GAutomaton σ T) (s : X.states) : GuardedString σ T → Prop
  | .final α => X.map s α = 1
  | .cons α p x => ∃ (t : X.states), X.map s α = Sum.inr (p, t) ∧ accept X t x

def l (X : GAutomaton σ T) (s : X.states) := {α : GuardedString σ T // accept X s α}

def language (X : GAutomaton σ T) := l X X.start


instance : One (G σ T X) where
  one := fun _ ↦ 1


def uniform_continuation (X : GCoalgebra σ T)
  (Y : Set X.states) [DecidablePred (. ∈ Y)]
  [DecidableEq X.states]
  (h : G σ T X.states) : GCoalgebra σ T :=
  ⟨ X.states,
    fun x α ↦
      if x ∈ Y ∧ (X.map x α) = 1
      then h α
      else X.map x α ⟩



def coproduct (X : GCoalgebra σ T) (Y : GCoalgebra σ T) : GCoalgebra σ T :=
  ⟨ (X.states ⊕ Y.states),
    fun z α ↦ match z with
    | .inl x => match (X.map x α) with
                | 0 => 0
                | 1 => 1
                | .inr (a, b) => .inr (a, .inl b)
    | .inr y => match (Y.map y α) with
                | 0 => 0
                | 1 => 1
                | .inr (a, b) => .inr (a, .inr b) ⟩
