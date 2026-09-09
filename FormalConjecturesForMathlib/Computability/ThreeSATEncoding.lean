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

public import FormalConjecturesForMathlib.Computability.BitstringEncoding
public import FormalConjecturesForMathlib.Computability.ThreeSAT

/-!
# Canonical binary encoding of 3-CNF instances

An instance carries its ambient variable count, including unused variables. Its raw representation
is a natural number paired with a list of clauses, each a list of natural-index/sign pairs.
We use the existing binary natural-number and self-delimiting pair/list encodings.

Parsing validates every index and clause length, then rejects noncanonical encodings by
re-encoding. Malformed input is distinct from a valid unsatisfiable formula. Round trips and
reference-check correctness are proved; no running-time bound is claimed.
Canonicality concerns this representation; it does not reorder clauses, deduplicate literals,
or remove unused variables.

The decision/search background is Aaronson, *P =? NP*, §2.2.1,
https://www.scottaaronson.com/papers/pnp.pdf. This binary format is an implementation choice,
not the arithmetic formula coding of Oliveira, ECCC TR25-041, §5.1.2,
https://eccc.weizmann.ac.il/report/2025/041/.
-/

@[expose] public section

namespace Computability.ThreeSAT

open BitstringEncoding

/-- Untyped clauses, whose indices and lengths have not yet been validated. -/
abbrev RawFormula := List (List (ℕ × Bool))

/-- A formula together with its explicit ambient variable count. -/
structure Instance where
  numVars : ℕ
  formula : Formula numVars

def Literal.toRaw {n : ℕ} (literal : Literal n) : ℕ × Bool :=
  (literal.index.val, literal.positive)

/-- A literal is valid only when its index is strictly below the declared variable count. -/
def Literal.ofRaw (n : ℕ) (raw : ℕ × Bool) : Option (Literal n) :=
  if h : raw.1 < n then some ⟨⟨raw.1, h⟩, raw.2⟩ else none

@[simp]
theorem Literal.ofRaw_toRaw {n : ℕ} (literal : Literal n) :
    Literal.ofRaw n literal.toRaw = some literal := by
  simp [ofRaw, toRaw, literal.index.isLt]

def Clause.toRaw {n : ℕ} (clause : Clause n) : List (ℕ × Bool) :=
  clause.literals.map Literal.toRaw

/-- Validate every index and reject clauses containing more than three literals. -/
def Clause.ofRaw (n : ℕ) (raw : List (ℕ × Bool)) : Option (Clause n) :=
  (raw.mapM (Literal.ofRaw n)).bind fun literals ↦
    if h : literals.length ≤ 3 then some ⟨literals, h⟩ else none

private theorem literals_roundtrip {n : ℕ} (literals : List (Literal n)) :
    (literals.map Literal.toRaw).mapM (Literal.ofRaw n) = some literals := by
  induction literals with
  | nil => rfl
  | cons literal rest ih => simp [ih]

@[simp]
theorem Clause.ofRaw_toRaw {n : ℕ} (clause : Clause n) :
    Clause.ofRaw n clause.toRaw = some clause := by
  rw [ofRaw, toRaw, literals_roundtrip]
  simp [clause.length_le]

def Instance.toRaw (problem : Instance) : ℕ × RawFormula :=
  (problem.numVars, problem.formula.map Clause.toRaw)

def Instance.ofRaw (raw : ℕ × RawFormula) : Option Instance :=
  (raw.2.mapM (Clause.ofRaw raw.1)).map fun formula ↦ ⟨raw.1, formula⟩

private theorem clauses_roundtrip {n : ℕ} (formula : Formula n) :
    (formula.map Clause.toRaw).mapM (Clause.ofRaw n) = some formula := by
  induction formula with
  | nil => rfl
  | cons clause rest ih => simp [ih]

@[simp]
theorem Instance.ofRaw_toRaw (problem : Instance) :
    Instance.ofRaw problem.toRaw = some problem := by
  unfold ofRaw toRaw
  rw [clauses_roundtrip]
  rfl

instance : BitstringEncoding Instance :=
  BitstringEncoding.ofLeftInverse Instance.toRaw Instance.ofRaw Instance.ofRaw_toRaw

namespace Instance

/-- The canonical encoding contains the variable count as well as the entire formula. -/
def encode (problem : Instance) : List Bool := bitEncode problem

theorem encode_eq (problem : Instance) :
    encode problem = delimit (bitEncode problem.numVars) ++
      bitEncode (problem.formula.map Clause.toRaw) := rfl

/-- Both the declared variable count and the formula contribute to input size. -/
theorem encoded_length (problem : Instance) :
    (encode problem).length = 2 * (bitEncode problem.numVars).length + 1 +
      (bitEncode (problem.formula.map Clause.toRaw)).length := by
  simp only [encode_eq, List.length_append, length_delimit]

/-- Parse only canonical encodings of valid instances. -/
def decode (bits : List Bool) : Option Instance :=
  (bitDecode bits).filter fun problem ↦ encode problem == bits

@[simp]
theorem decode_eq_some {bits : List Bool} {problem : Instance} :
    decode bits = some problem ↔ encode problem = bits := by
  constructor
  · intro h
    simpa [decode] using (Option.filter_eq_some_iff.mp h).2
  · rintro rfl
    simp [decode, encode]

@[simp]
theorem decode_encode (problem : Instance) : decode (encode problem) = some problem :=
  decode_eq_some.mpr rfl

theorem encode_injective : Function.Injective encode :=
  bitEncode_injective

/-- Invalid syntax gives `none`; `some false` means a valid, unsatisfiable instance. -/
def check (bits : List Bool) : Option Bool :=
  (decode bits).map fun problem ↦ referenceCheck problem.formula

@[simp]
theorem check_encode (problem : Instance) :
    check (encode problem) = some (referenceCheck problem.formula) := by
  simp [check]

theorem check_eq_some {bits : List Bool} {answer : Bool} :
    check bits = some answer ↔
      ∃ problem : Instance, encode problem = bits ∧ referenceCheck problem.formula = answer := by
  simp [check, Option.map_eq_some_iff]

@[simp]
theorem check_eq_none {bits : List Bool} : check bits = none ↔ decode bits = none := by
  simp [check]

theorem check_eq_some_true {bits : List Bool} :
    check bits = some true ↔
      ∃ problem : Instance, encode problem = bits ∧ Satisfiable problem.formula := by
  simp [check_eq_some]

theorem check_eq_some_false {bits : List Bool} :
    check bits = some false ↔
      ∃ problem : Instance, encode problem = bits ∧ ¬ Satisfiable problem.formula := by
  simp [check_eq_some, Bool.eq_false_iff]

end Instance

end Computability.ThreeSAT
