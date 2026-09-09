/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public meta import FormalConjecturesForMathlib.Computability.ThreeSATEncoding
public import FormalConjecturesForMathlib.Computability.ThreeSATEncoding

/-! # Regression proofs for canonical 3-CNF parsing -/

@[expose] public section

namespace Computability.ThreeSAT.EncodingTest

open BitstringEncoding

def emptyInstance : Instance := ⟨0, []⟩
def emptyClauseInstance : Instance := ⟨0, [⟨[], by decide⟩]⟩
def satInstance : Instance := ⟨1, [⟨[⟨0, true⟩], by decide⟩]⟩
def unsatInstance : Instance := ⟨1,
  [⟨[⟨0, true⟩], by decide⟩, ⟨[⟨0, false⟩], by decide⟩]⟩
def sparseInstance : Instance := ⟨5, [⟨[⟨4, true⟩, ⟨1, false⟩], by decide⟩]⟩
def repeatedInstance : Instance := ⟨1, [⟨[⟨0, true⟩, ⟨0, true⟩, ⟨0, true⟩], by decide⟩]⟩

example (problem : Instance) : Instance.decode problem.encode = some problem := by simp
example (problem : Instance) :
    Instance.check problem.encode = some true ↔ Satisfiable problem.formula := by simp

example : Instance.check emptyInstance.encode = some true := by decide
example : Instance.check emptyClauseInstance.encode = some false := by decide
example : Instance.check satInstance.encode = some true := by decide
example : Instance.check unsatInstance.encode = some false := by decide
example : Instance.check sparseInstance.encode = some true := by decide
example : Instance.check repeatedInstance.encode = some true := by decide
example : (Instance.decode sparseInstance.encode).map Instance.numVars = some 5 := by decide
example : emptyInstance.encode ≠ (⟨5, []⟩ : Instance).encode := by decide

-- Malformed framing and trailing incomplete blocks.
example : Instance.decode [] = none := rfl
example : Instance.decode [true] = none := rfl
example : Instance.decode (emptyInstance.encode ++ [true]) = none := rfl

-- Zero variables cannot support a literal; the upper index bound is strict.
example : Instance.decode (bitEncode ((0, [[(0, true)]]) : ℕ × RawFormula)) = none := rfl
example : Instance.decode (bitEncode ((1, [[(1, true)]]) : ℕ × RawFormula)) = none := rfl
example : Instance.decode (bitEncode ((5, [[(5, false)]]) : ℕ × RawFormula)) = none := rfl
example : Instance.decode
    (bitEncode ((1, [[(0, true), (0, true), (0, false), (0, false)]]) :
      ℕ × RawFormula)) = none := rfl

-- The underlying natural decoder accepts aliases; canonical parsing rejects them.
-- In Mathlib's decoder, [false, false] is a noncanonical encoding of 4, not 0.
def aliasedEmpty : List Bool := delimit [false, false]
example : (bitDecode aliasedEmpty : Option Instance).map Instance.numVars = some 4 := by decide
example : Instance.decode aliasedEmpty = none := rfl
example : Instance.check aliasedEmpty = none := by decide

def aliasedLiteral : List Bool :=
  delimit (bitEncode (5 : ℕ)) ++ delimit (delimit (delimit [false, false] ++ [true]))
example : (bitDecode aliasedLiteral : Option Instance).map Instance.numVars = some 5 := by decide
example : Instance.decode aliasedLiteral = none := rfl

-- A sign must be exactly one bit.
example : Instance.decode (delimit (bitEncode (1 : ℕ)) ++
    delimit (delimit (delimit (bitEncode (0 : ℕ)) ++ [false, false]))) = none := rfl

-- Invalid encodings are not reported as UNSAT.
example : Instance.check [] ≠ some false := by decide
example : Instance.check emptyClauseInstance.encode ≠ none := by decide
example : Instance.check (bitEncode ((0, [[(0, true)]]) : ℕ × RawFormula)) = none := by decide

/-- info: (some true, some false, none) -/
#guard_msgs in
#eval (Instance.check satInstance.encode, Instance.check unsatInstance.encode, Instance.check [])

/-- info: (some 5, none) -/
#guard_msgs in
#eval ((Instance.decode sparseInstance.encode).map Instance.numVars, Instance.check aliasedEmpty)

end Computability.ThreeSAT.EncodingTest
