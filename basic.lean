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

definition const.appl [sig : SIG] (i : sig) : (fin (func.arity i) → const) → const :=
  term.appl i

namespace sig

  definition const [instance] (I : Type) : SIG :=
    SIG.mk I (λ i, 0)

  definition add [instance] (sig₁ sig₂ : SIG) : SIG :=
    SIG.mk (sum sig₁ sig₂) (sum.rec (@func.arity sig₁) (@func.arity sig₂))

  definition sum [instance] {I : Type} (sig : I → SIG) : SIG :=
    SIG.mk (sigma sig) (sigma.rec (λ i, @func.arity (sig i)))

end sig
