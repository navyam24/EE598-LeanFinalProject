/- Lean Final project - Formalizing FSMs and Arithmetic Circuits in Lean.

1. Boolean / bit logic
2. Basic logic gates and small proofs
3. Abstract FSM definitions
4. Arithmetic circuits as concrete machines
5. A first connection between adders and FSM-style execution
-/
namespace EE598final

-- Foundational

-- custom bit type to make hardware interpretation explicit for hardware style binary signals
inductive Bit : Type where
    | O : Bit
    | I : Bit

namespace Bit
-- Logical NOT on bits
-- Flip if 0 then I, if I then 0
def bnot : Bit → Bit
  | O => I
  | I => O
-- Logical AND on bits
-- truth table : if 1&1 then 1 otherwise 0
def band : Bit → Bit → Bit
  | I, I => I
  | _, _ => O

def bxor : Bit → Bit → Bit
  | O, O => O
  | O, I => I
  | I, O => I
  | I, I => O

def bor : Bit → Bit → Bit
  | O, O => O
  | _, _ => I

-- NOR on bits
def bnor (a b : Bit) : Bit := bnot (bor a b)

--A bit is true when it is exactly I and false at 0
def denote : Bit → Prop
  | O => False
  | I => True

-- interpret Bit as Nat
def toNat : Bit → Nat
  | O => 0
  | I => 1

@[simp] theorem bnot_O : bnot O = I := rfl
@[simp] theorem bnot_I : bnot I = O := rfl
@[simp] theorem band_O_left (b : Bit) : band O b = O := by cases b <;> rfl
@[simp] theorem band_I_left (b : Bit) : band I b = b := by cases b <;> rfl
@[simp] theorem bor_O_left (b : Bit) : bor O b = b := by cases b <;> rfl
@[simp] theorem bor_I_left (b : Bit) : bor I b = I := by cases b <;> rfl
@[simp] theorem bxor_self (b : Bit) : bxor b b = O := by cases b <;> rfl
@[simp] theorem bxor_comm (a b : Bit) : bxor a b = bxor b a := by cases a <;> cases b <;> rfl
@[simp] theorem band_comm (a b : Bit) : band a b = band b a := by cases a <;> cases b <;> rfl
@[simp] theorem bor_comm (a b : Bit) : bor a b = bor b a := by cases a <;> cases b <;> rfl

-- De Morgan's at the bit level
@[simp] theorem demorgan (a b : Bit) :
    bnot (band a b) = bor (bnot a )(bnot b) := by
  cases a <;> cases b <;> rfl

@[simp] theorem demorgan2 (a b : Bit) :
    bnot (bor a b) = band (bnot a) (bnot b) := by
  cases a <;> cases b <;> rfl

@[simp] theorem bor_assoc (a b c : Bit) :
    bor (bor a b ) c = bor a (bor b c ) := by
  cases a <;> cases b <;> cases c <;> rfl

@[simp] theorem band_assoc (a b c : Bit) :
    band (band a b ) c = band a (band b c ) := by
  cases a <;> cases b <;> cases c <;> rfl

end Bit

-- Abstract FSM Portion

-- Mealy machine: output which depends on current state + input
structure MealyMachine (State Input Output : Type) where
  step : State → Input → State
  out : State → Input → Output

-- Moore machine: output which depends only on the current state
structure MooreMachine (State Input Output : Type) where
  step : State → Input → State
  out : State → Output

namespace MealyMachine

variable {State Input Output : Type}

-- Running Mealy machine for one input step
def oneStep (M : MealyMachine State Input Output)
    (s : State) (i : Input) : State × Output :=
  (M.step s i, M.out s i)

def runList (M : MealyMachine State Input Output)
    : State → List Input → State × List Output
  | s, [] => (s, [])
  | s, i :: is =>
      let s' := M.step s i
      let o := M.out s i
      let (sf, os) := runList M s' is
      (sf, o :: os)

@[simp] theorem runList_null (M : MealyMachine State Input Output) (s : State) :
    runList M s [] = (s, []) := rfl

@[simp] theorem runList_cons (M : MealyMachine State Input Output)
    (s : State) (i : Input) (is : List Input) :
    runList M s (i :: is) =
      let s' := M.step s i
      let o  := M.out s i
      let (sf, os) := runList M s' is
      (sf, o :: os) := rfl

end MealyMachine

namespace MooreMachine

variable {State Input Output : Type}

-- Run a moore machine o ver a list of inputs and return the final state
def runState (M : MooreMachine State Input Output)
    : State → List Input → State
  | s, [] => s
  | s, i :: is => runState M (M.step s i) is

@[simp] theorem runState_null(M : MooreMachine State Input Output) (s : State) :
    runState M s [] = s := rfl

@[simp] theorem runState_cons(M : MooreMachine State Input Output)
    (s : State) (i : Input) (is : List Input) :
    runState M s (i :: is) = runState M (M.step s i) is := rfl

end MooreMachine

-- Arithmetic Circuits

namespace Circuits
open Bit

-- Half adder output: sum + carry
structure HalfAdderOut where
  sum : Bit
  carry : Bit
  deriving DecidableEq, Repr

-- Half adder circuit built frofrom XOR and AND gates
def halfAdder (a b : Bit) : HalfAdderOut :=
  { sum := bxor a b, carry := band a b }

@[simp] theorem halfAdder_OO : halfAdder O O = ⟨O, O⟩ := rfl
@[simp] theorem halfAdder_OI : halfAdder O I = ⟨I, O⟩ := rfl
@[simp] theorem halfAdder_IO : halfAdder I O = ⟨I, O⟩ := rfl
@[simp] theorem halfAdder_II : halfAdder I I = ⟨O, I⟩ := rfl

-- full adder output: sum + carry out
structure FullAdderOut where
  sum : Bit
  carry : Bit
  deriving DecidableEq, Repr

-- the full adder circuit built from XOR, AND and OR gates
def fullAdder (a b cin : Bit) : FullAdderOut :=
  let s1 := bxor a b
  let c1 := band a b
  let s2 := bxor s1 cin
  let c2 := band cin s1
  {sum := s2, carry := bor c1 c2}

-- truth table spec for the full adder carry
def carrySpec (a b cin : Bit) : Bit :=
  bor (band a b) (bor (band a cin) (band b cin))

@[simp] theorem fullAdder_carry_matches_spec (a b cin : Bit) :
    (fullAdder a b cin).carry = carrySpec a b cin := by
  cases a <;> cases b <;> cases cin <;> rfl


-- numeric value for half adder output
def halfAdderValue (o : HalfAdderOut) : Nat :=
  Bit.toNat o.sum + 2 * Bit.toNat o.carry

@[simp] theorem halfAdder_correct_value (a b : Bit) :
    halfAdderValue (halfAdder a b) = Bit.toNat a + Bit.toNat b := by
  cases a <;> cases b <;> rfl

-- numeric val for a full adder output
def fullAdderValue (o : FullAdderOut) : Nat :=
  Bit.toNat o.sum + 2 * Bit.toNat o.carry

@[simp] theorem fullAdder_correct_value (a b cin : Bit) :
    fullAdderValue (fullAdder a b cin) = Bit.toNat a + Bit.toNat b + Bit.toNat cin := by
  cases a <;> cases b <;> cases cin <;> rfl

end Circuits

-- adders as FSM style machines
namespace FSMExamples
open Bit
open Circuits

-- full adder modeled as a mealy machine with the carry as the state
def fullAdderMachine : MealyMachine Bit (Bit × Bit) Circuits.FullAdderOut where
  step := fun cin (ab : Bit × Bit) =>
    let (a, b) := ab
    (Circuits.fullAdder a b cin).carry
  out :=fun cin (ab : Bit × Bit) =>
    let (a, b ) := ab
    Circuits.fullAdder a b cin

@[simp] theorem fullAdderMachine_step_eq
    (cin a b : Bit) :
    fullAdderMachine.step cin (a, b) = (Circuits.fullAdder a b cin).carry := rfl


@[simp] theorem fullAdderMachine_out_eq
    (cin a b : Bit) :
    fullAdderMachine.out cin (a, b) = Circuits.fullAdder a b cin := rfl

/-- An n-bit ripple carry adder over lists of equal length, threading carry left-to-right.
    This is a simple executable model for later proofs. -/

-- nbit ripple carryb adder over lists of equal length + threading carry left to right
def rippleCarry : Bit → List (Bit × Bit) → Bit × List Bit
  | cin, [] => (cin, [])
  | cin, (a, b) :: xs =>
      let o := Circuits.fullAdder a b cin
      let (cout, ys) := rippleCarry o.carry xs
      (cout, o.sum :: ys)

@[simp] theorem rippleCarry_nil (cin : Bit) :
    rippleCarry cin [] = (cin, []) := rfl

@[simp] theorem rippleCarry_cons (cin a b : Bit) (xs : List (Bit × Bit)) :
    rippleCarry cin ((a, b) :: xs) =
      let o := Circuits.fullAdder a b cin
      let (cout, ys) := rippleCarry o.carry xs
      (cout, o.sum :: ys) := rfl
@[simp] theorem fullAdderMachine_oneStep
    (cin a b : Bit) :
    MealyMachine.oneStep fullAdderMachine cin (a, b) =
      ((Circuits.fullAdder a b cin).carry, Circuits.fullAdder a b cin) := rfl

end FSMExamples
end EE598final
