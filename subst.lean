-- birkhoff/subst.lean --
-- Copyright Ⓒ 2015 François G. Dorais. All rights reserved.
-- Relesed under the MIT License as described in the file LICENSE.

import data .basic .algebras
open nat

definition subst [sig : SIG] (m n : nat) : Type := fin m → term n

namespace subst
  open alg
  variable [sig : SIG]
  include sig

  definition alg [instance] (n : nat) : ALG (term n) :=
    ALG.mk (λ i xs, term.appl i xs)

  definition apply {m n : nat} :
    subst m n → term m → term n :=
    take us t, @term.value sig (term n) (subst.alg n) m t us

  lemma apply_proj {m n : nat} {us : subst m n} (i : fin m) :
    subst.apply us (term.proj i) = us i :=
    term.value_proj

  lemma apply_func {m n : nat} {us : subst m n} (i : sig) {ts : fin (func.arity i) → term m} :
    subst.apply us (term.appl i ts) = term.appl i (λ k, subst.apply us (ts k)) :=
    term.value_appl

  definition hom [instance]
    {m n : nat} (us : subst m n) :
    @HOM sig (term m) (subst.alg m) (term n) (subst.alg n) (subst.apply us) :=
    HOM.mk (take i ts, subst.apply_func i)

  definition single {n : nat} (i : fin n) (t : term n) : subst n n :=
    λ j : fin n, decidable.rec_on (fin.has_decidable_eq n i j)
      (take Heq, t)
      (take Hne, term.proj j)

  definition comp {m n p : nat} : subst n p → subst m n → subst m p :=
    take us vs k, subst.apply us (vs k)

  theorem comp_apply {m n p : nat} {us : subst n p} {vs : subst m n} {t : term m} :
    subst.apply (comp us vs) t = subst.apply us (subst.apply vs t) :=
    @hom.term sig _ (subst.alg n) _ (subst.alg p) _ (subst.hom us) _ t vs

  theorem comp_assoc {m n p q : nat} {us : subst p q} {vs : subst n p} {ws : subst m n} :
    comp us (comp vs ws) = comp (comp us vs) ws :=
    funext (take k, calc
      comp us (comp vs ws) k
          = subst.apply us (comp vs ws k)               : rfl
      ... = subst.apply us (subst.apply vs (ws k))      : rfl
      ... = subst.apply (comp us vs) (ws k)             : comp_apply
      ... = comp (comp us vs) ws k                      : rfl)

  definition id {n : nat} : subst n n :=
    λ k : fin n, term.proj k

  theorem id_apply {n : nat} {t : term n} : subst.apply id t = t :=
    term.induction_on t
      (take n i, apply_proj i)
      (take n i ts IH,
       have IH' : (λ k, subst.apply id (ts k)) = ts,
       from funext IH,
       calc
        subst.apply id (term.appl i ts)
            = term.appl i (λ k, subst.apply id (ts k)) : apply_func
        ... = term.appl i ts : IH')

  theorem comp_id_left {m n : nat} {us : subst m n} :
    comp id us = us :=
    funext (take k, id_apply)

  theorem comp_id_right {m n : nat} {us : subst m n} :
    comp us id = us :=
    funext (take k, apply_proj k)

  definition map {m n : nat} (f : fin m → fin n) : subst m n :=
    λ k : fin m, term.proj (f k)

  theorem map_id {n : nat} : map (λ k : fin n, k) = id := rfl

  theorem map_comp {m n p : nat} (f : fin n → fin p) (g : fin m → fin n) :
    comp (map f) (map g) = map (λ k, f (g k)) :=
    let h := λ k, f (g k) in
    funext (take k, calc
      comp (map f) (map g) k
          = subst.apply (map f) (map g k)         : rfl
      ... = subst.apply (map f) (term.proj (g k)) : rfl
      ... = (map f) (g k)                         : apply_proj
      ... = term.proj (h k)                       : rfl
      ... = map h k                               : rfl)

end subst
