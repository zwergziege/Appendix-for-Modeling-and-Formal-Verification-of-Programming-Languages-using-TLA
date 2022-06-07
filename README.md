# Modeling-and-Formal-Verification-of-Programming-Languages-using-TLA
TLA+ specifications related to the masters thesis "Modeling and Formal Verification of Programming Languages using TLA+"

The specifications provided in this repository are intended to be used in conjunction with the TLA+ toolbox. The set up is as follows:
- install the TLA+ toolbox
- install the TLA+ proof manager
- install the TLA+ community modules
- configure the toolbox to add the following files and directories to its library path
  - the library directory of TLAPS
  - the library directory in this repository (`./Lib`)
  - the community modules both as jar (for Java overrides) and regular files (for TLAPS)

The important modules already come with models that define important overrides, which can be run from the toolbox. The two variants on SOS can be found in the folders `ExplicitRuleSOS` and `TinyStepSOS`. The three case studies are (as ordered in the thesis) 
1. `./ListNatExp`
2. `./AExp`
3. `./Imp`
