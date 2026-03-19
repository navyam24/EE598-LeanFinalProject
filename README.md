# EE598-LeanFinalProject

# Formalizing finite state machines and arthmetic circuits in Lean - from X.1 feedback 

This project should formalize finite state machines (FSMs) as an abstract mathematical object in Lean. It should then show how arithmetic circuits such as adders, multipliers, etc. can be modeled as more concrete implementations of these machines using logical operations. The goal is to bridge the digital hardware design and the formal proff by proving properties of the arithmetic circuits relative to their FSM specs. This should connect hardware reasoning, boolean logic, and formal verification within the Lean framework. 

The goal of this project is to formalize finite state machines (FSMs) and arithmetic circuits in Lean, and to show how digital hardware logic and reasoning can be expressed and verified with a theorem prover. The project initializes by defining a custom bit type and basic logic gates, then proves several Boolean algebra properties (such as DeMorgans). Next, it introduces abstract Mealy and Moore machine definitions and finally models arithmetic circuits such as half adders, full adders, and ripple-carry adders. One of the  key goals is to connect the circuit level computation with state-machine execution by treating the carry propagation as a machine state.

## Main Definitions:
### 'Bit'
This is a custom inductive type with the constructors O and I representing binary hardware signals.

### 'Bit.bnot'
This is a bitwise logical NOT

### 'Bit.band'
This is a bitwise logical AND 

### 'Bit.bxor'
This is a bitwise logical XOR

### 'Bit.bor'
This is a bitwise logical OR 

### 'Bit.bnor'
This is a bitwise logical NOR (negation of OR)

### 'Bit.denote'
This interprets a Bit value as a proposition where O corresponds to False, and I corresponds to True.

### 'Bit.toNat' 
This interprets a Bit value numerically/as a Nat where O = 0 and I = 1

### 'MealyMachine'
This is an abstract finite state machine structure in which the output depends on the current state as well as the input

### 'MooreMachine'
This is an abstract finite state machine in which the output depends only on the current state.

### 'MealyMachine.oneStep'
One transition of tyhe Mealy machine is executed which produces the next state + output

### 'MealyMachine.runList'
A Mealy machine is executed over a list of inputs

### 'MooreMachine.runState'
A Moore machine is executed over a list of inputs and returns the final state

### 'Circuits.HalfAdderOut'
Stores the output (is a structure) of a half adder which is: sum and carry

### 'Circuits.halfAdder'
Definition of a half adder using XOR and AND gates

### 'Circuits.FullAdderOut'
Structure which stores the output of a full adder (sum and carry)

### 'Circuits.fullAdder'
Definition of a full adder which uses XOR AND and OR gates 

### 'Circuits.carrySpec'
A truth table style spec of the full adder carry output

### 'Circuits.halfAdderValue'
This interprets a half adders output numerically

### 'Circuits.fullAdderValue'
This interprets a full adders output numerically 

### 'FSMExamples.fullAdderMachine'
Models a full adder as a Mealy machine where the state is the carry bit and the input is a pair of bits

### 'FSMExamples.rippleCarry'
Defines an n-bit ripple-carry adder recursively over a list of input bit pairs

## Main Theorems:

### 'Bit.bxor_self'
Theorem which proves that XOR of a bit with itself is always O

### 'Bit.bxor_comm'
Theorem which proves that XOR is commutative

### 'Bit.band_comm'
Theorem which proves that AND is commutative

### 'Bit.bor_comm'
Theorem which proves that OR is commutative

### 'Bit.demorgan' 
The initial/first bit level form of De Morgans law is:
¬(a ∧ b) = ¬a ∨ ¬b

### 'Bit.demorgan2'
The second bit level form of De Morgans law which is:
¬(a ∨ b) = ¬a ∧ ¬b

### 'Bit.bor_assoc'
Theorem which proves that OR is associative

### 'Bit.band_assoc'
Theorem which proves that AND is associative

### 'Circuits.fullAdder_carry_matches_spec'
This proves that the carry output of the implemented full adder matches the carry specification

### 'Circuits.halfAdder_correct_value'
This proves that the half adder correcly computes the correct numeric al sum of the two input bits

### 'Circuits.fullAdder_correct_value'
This prves that the full adder correctly computes the numerical sum of the two input bits + a carry in bit

### 'FSMExamples.fullAdderMachine_step_eq'
Shows that the state transition of theh Mealy machine matches the carry output of the full adder

### 'FSMExamples.fullAdderMachine_out_eq'
Shows that the Mealy machine output matches the output of the full adder

### 'FSMExamples.fullAdderMachine_oneStep'
SHowing that the one Mealy machine step is the exact equivalent of the one full adder computation

### 'FSMExamples.rippleCarry_nil'
Proves the base case of the ripple carry adder on an empty input list

### 'FSMExamples.rippleCarry_cons'
Proves the recursive unfolding of the ripple carry adder

## References: 
### The Lean Language Reference
### Course Lecture Notes + Slide Deck 
### Chipverify.com for adder/half adder references + standard digital logic references
example: https://www.chipverify.com/digital-fundamentals/digital-full-adder-circuit

## Future Work :
1. Prove stronger correctness properties for rippleCarry + a full numeric correctness theorem over a list of bits 
2. Define bit vectors more explicitly and prove arithmetic correctness at vector level
3. Move forward into modeling additional arithmetic circuits such as multipliers
4. Prove that ripple carry addition corresponds to repeated Mealy machine execution over a sequence of inputs
5. Extend the FSM framework to model more general sequential digital systems beyond arithmetic circuits


