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
import FormalConjecturesTest.ForMathlib.Computability.ThreeSATEncoding

#print axioms Computability.ThreeSAT.RawFormula
#print axioms Computability.ThreeSAT.Instance
#print axioms Computability.ThreeSAT.Literal.toRaw
#print axioms Computability.ThreeSAT.Literal.ofRaw
#print axioms Computability.ThreeSAT.Literal.ofRaw_toRaw
#print axioms Computability.ThreeSAT.Clause.toRaw
#print axioms Computability.ThreeSAT.Clause.ofRaw
#print axioms Computability.ThreeSAT.Clause.ofRaw_toRaw
#print axioms Computability.ThreeSAT.Instance.toRaw
#print axioms Computability.ThreeSAT.Instance.ofRaw
#print axioms Computability.ThreeSAT.Instance.ofRaw_toRaw
#print axioms Computability.ThreeSAT.Instance.encode
#print axioms Computability.ThreeSAT.Instance.encode_eq
#print axioms Computability.ThreeSAT.Instance.encoded_length
#print axioms Computability.ThreeSAT.Instance.decode
#print axioms Computability.ThreeSAT.Instance.decode_eq_some
#print axioms Computability.ThreeSAT.Instance.decode_encode
#print axioms Computability.ThreeSAT.Instance.encode_injective
#print axioms Computability.ThreeSAT.Instance.check
#print axioms Computability.ThreeSAT.Instance.check_encode
#print axioms Computability.ThreeSAT.Instance.check_eq_some
#print axioms Computability.ThreeSAT.Instance.check_eq_none
#print axioms Computability.ThreeSAT.Instance.check_eq_some_true
#print axioms Computability.ThreeSAT.Instance.check_eq_some_false
#print axioms Computability.ThreeSAT.EncodingTest.emptyInstance
#print axioms Computability.ThreeSAT.EncodingTest.emptyClauseInstance
#print axioms Computability.ThreeSAT.EncodingTest.satInstance
#print axioms Computability.ThreeSAT.EncodingTest.unsatInstance
#print axioms Computability.ThreeSAT.EncodingTest.sparseInstance
#print axioms Computability.ThreeSAT.EncodingTest.repeatedInstance
#print axioms Computability.ThreeSAT.EncodingTest.aliasedEmpty
#print axioms Computability.ThreeSAT.EncodingTest.aliasedLiteral
