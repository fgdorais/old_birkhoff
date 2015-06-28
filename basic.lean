-- birkhoff/basic.lean --
-- Copyright Ⓒ 2015 François G. Dorais. All rights reserved.
-- Relesed under the MIT License as described in the file LICENSE.

import data
open nat

structure SIG [class] :=
  (index : Type)
  (arity : index → nat)

attribute SIG.index [coercion]

definition func.arity [sig : SIG] : sig → nat := SIG.arity

inductive term [sig : SIG] : nat → Type :=
| proj : ∀ {n : nat}, fin n → term n
| appl : ∀ {n : nat} (i : sig), (fin (func.arity i) → term n) → term n

definition const [sig : SIG] : Type := term 0
