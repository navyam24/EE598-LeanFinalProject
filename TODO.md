#TODO:
*NOTE* Still deciding whether to treat adders as stateless combinational FSMs w a single transition or treat ripple carry as sequential 
Part 1: 

First, the foundations should be established. 
a) Define a type for the boolean signals (use Bool or some custom inductive type)
b) Define basic logical gates such as OR AND NOR, etc. as functions
c) Prove basic boolean identifies such as D'Morgan, distributive, associative, etc. 

Part 2: 
Second, should define a generic FSM structure
a) A genetric FSM structure should be defined using: 
  - State type
  - Input type
  - Transition function
  - Output for Mealy/Moore
b) Define an FSM running on an input sequence
c) Proving basic properties of FSM execution

Part 3: 

Develop arithmetic circuits as FSMs
a) Define a half-adder using the logic gates
b) Define full adder using logic gates
c) Prove adders work according to truth tables
d) Define ripple carry adder (n-bit) throiugh recursion
e) Prove correctness of ripple carry adder

Part 4: 
Connect the circuits to the FSM abstraction
a) Show that ripple carry adder fits the FSM abstraction structure
b) Prove the equivalence between the abstract adition specs. and circuit implementation
c) Maybe also define simple multiplier and prove correctness 
