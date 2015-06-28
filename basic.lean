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

structure ALG [class] [sig : SIG] (A : Type) :=
  (value : ∀ i : sig, (fin (func.arity i) → A) → A)

section
  variables [sig : SIG] {A : Type} [alg : ALG A]
  include sig A alg

  definition func.value :
    ∀ i : sig, (fin (func.arity i) → A) → A := ALG.value

  definition term.value :
    ∀ {n : nat}, term n → (fin n → A) → A :=
    @term.rec sig _
      (take n i xs, xs i)
      (take n i ts IH xs, func.value i (λ j, IH j xs))

  definition const.value : const → A :=
    λ t, term.value t fin.elim0

  definition term.value₁ : term 1 → A → A :=
    λ t x, term.value t (λ j, x)

  lemma term.value_proj {n : nat} {i : fin n} :
    ∀ {xs : fin n → A}, term.value (term.proj i) xs
                        = xs i :=
    take xs, rfl

  lemma term.value_appl {n : nat} {i : sig} {ts : fin (func.arity i) → term n} :
    ∀ {xs : fin n → A}, term.value (term.appl i ts) xs
                        = func.value i (λ j, term.value (ts j) xs) :=
    take xs, rfl

end

namespace alg
  open prod
  variable [sig : SIG]
  include sig

  definition trivial [instance] : ALG unit :=
    ALG.mk (λ i xs, unit.star)

  definition initial [instance] : ALG const :=
    ALG.mk (λ i cs, term.appl i cs)

  definition subst [instance] (n : nat) : ALG (term n) :=
    ALG.mk (λ i xs, term.appl i xs)

  definition prod [instance]
    (A : Type) [alga : ALG A]
    (B : Type) [algb : ALG B] :
    ALG (A × B) :=
    ALG.mk (λ i xs, (func.value i (λ j, pr₁ (xs j)), func.value i (λ j, pr₂ (xs j))))

  definition depprod [instance]
    {J : Type} (A : J → Type) [alg : ∀ j : J, ALG (A j)] :
    ALG (Π j : J, A j) :=
    ALG.mk (λ i xs, (λ j : J, func.value i (λ i, xs i j)))

end alg

structure HOM [class] [sig : SIG]
  {A : Type} [alga : ALG A]
  {B : Type} [algb : ALG B]
  (h : A → B) :=
  (ident : ∀ i : sig, ∀ xs : fin (func.arity i) → A,
             func.value i (λ j, h (xs j)) = h (func.value i xs))

theorem func.hom [sig : SIG]
  {A : Type} [alga : ALG A]
  {B : Type} [algb : ALG B]
  (h : A → B) [hom : HOM h] :
  ∀ {i : sig} {xs : fin (func.arity i) → A},
    func.value i (λ j, h (xs j)) = h (func.value i xs) :=
  @HOM.ident sig A alga B algb h hom

theorem hom.term [sig : SIG]
  {A : Type} [alga : ALG A]
  {B : Type} [algb : ALG B]
  (h : A → B) [hom : HOM h] :
  ∀ {n : nat} {t : term n} {xs : fin n → A},
    term.value t (λ j, h (xs j)) = h (term.value t xs) :=
  @term.rec _ _
    (take n i xs, rfl)
    (take n i ts IH xs,
     let ys := λ j : fin n, h (xs j) in
     have IH' : (λ k, term.value (ts k) ys)
                = (λ k, h (term.value (ts k) xs)),
     from funext (λ k, IH k xs),
     calc
      term.value (term.appl i ts) ys
          = func.value i (λ j, term.value (ts j) ys)     : rfl
      ... = func.value i (λ j, h (term.value (ts j) xs)) : IH'
      ... = h (func.value i (λ j, term.value (ts j) xs)) : func.hom h
      ... = h (term.value (term.appl i ts) xs)           : term.value_appl)

namespace hom
  open prod
  variable [sig : SIG]
  include sig

  definition id [instance] {A : Type} [alg : ALG A] : HOM (λ a : A, a) :=
    HOM.mk (take i xs, rfl)

  definition comp [instance]
    {A : Type} [alga : ALG A]
    {B : Type} [algb : ALG B]
    {C : Type} [algc : ALG C]
    (f : A → B) [homg : HOM f]
    (g : B → C) [homf : HOM g] :
    HOM (λ x, g (f x)) :=
    HOM.mk (take i xs, let ys := (λ j : fin (func.arity i), f (xs j)) in
            by rewrite [func.hom g, func.hom f])

  definition trivial [instance]
    {A : Type} [alg : ALG A] :
    @HOM sig A alg unit alg.trivial (λ x, unit.star) :=
    HOM.mk (take i xs, unit.eq _ _)

  definition initial [instance]
    {A : Type} [alg : ALG A] :
    @HOM sig _ alg.initial A alg term.value₀ :=
    HOM.mk (take i xs, term.value_appl)

  definition subst [instance]
    {A : Type} [alg : ALG A] {n : nat} (xs : fin n → A) :
    @HOM sig _ (alg.subst n) A alg (λ t, term.value t xs) :=
    HOM.mk (take i xs, term.value_appl)

  definition generator [instance]
    {A : Type} [alg : ALG A] {n : nat} (x : A) :
    @HOM sig _ (alg.subst 1) A alg (λ t, term.value₁ t x) :=
    HOM.mk (take i xs, term.value_appl)

  definition proj₁ [instance]
    {A₁ : Type} [alg₁ : ALG A₁]
    {A₂ : Type} [alg₂ : ALG A₂] :
    @HOM sig _ (alg.prod A₁ A₂) _ alg₁ pr₁ :=
    HOM.mk (take i xs, rfl)

  definition proj₂ [instance]
    {A₁ : Type} [alg₁ : ALG A₁]
    {A₂ : Type} [alg₂ : ALG A₂] :
    @HOM sig _ (alg.prod A₁ A₂) _ alg₂ pr₂ :=
    HOM.mk (take i xs, rfl)

  definition prod [instance]
    {A : Type} [alg : ALG A]
    {B₁ : Type} [alg₁ : ALG B₁] (h₁ : A → B₁) [hom₁ : HOM h₁]
    {B₂ : Type} [alg₂ : ALG B₂] (h₂ : A → B₂) [hom₂ : HOM h₂] :
    @HOM sig _ alg _ (alg.prod B₁ B₂) (λ x : A, (h₁ x, h₂ x)) :=
    HOM.mk (take i xs, prod.eq (func.hom h₁) (func.hom h₂))

  definition depproj [instance]
    {J : Type} {A : J → Type} [alg : Π j : J, ALG (A j)] (j : J) :
    @HOM sig _ (alg.depprod A) _ (alg j) (λ (x : Π j : J, A j), x j) :=
    HOM.mk (take i xs, rfl)

  definition depprod [instance]
    {A : Type} [alg : ALG A]
    {J : Type} {B : J → Type} [algb : Π j : J, ALG (B j)]
    (h : Π j : J, A → B j) [hom : Π j : J, HOM (h j)] :
    @HOM sig _ alg _ (alg.depprod B) (λ (x : A) (j : J), h j x) :=
    HOM.mk (take i xs, funext (take j, func.hom (h j)))

end hom

definition subst [sig : SIG] (m n : nat) : Type := fin m → term n

namespace subst
  open alg
  variable [sig : SIG]
  include sig

  check decidable.rec

  definition single {n : nat} (i : fin n) (t : term n) : subst n n :=
    λ j : fin n, decidable.rec_on (fin.has_decidable_eq n i j)
      (take Heq, t)
      (take Hne, term.proj j)

  definition apply {m n : nat} :
    subst m n → term m → term n :=
    take us t, @term.value sig _ (alg.subst n) _ t us

  lemma apply_proj {m n : nat} {us : subst m n} (i : fin m) :
    subst.apply us (term.proj i) = us i :=
    term.value_proj

  lemma apply_func {m n : nat} {us : subst m n} (i : sig) {ts : fin (func.arity i) → term m} :
    subst.apply us (term.appl i ts) = term.appl i (λ k, subst.apply us (ts k)) :=
    term.value_appl

  definition comp {m n p : nat} : subst n p → subst m n → subst m p :=
    take us vs k, subst.apply us (vs k)

  theorem comp_apply {m n p : nat} {us : subst n p} {vs : subst m n} {t : term m} :
    subst.apply (comp us vs) t = subst.apply us (subst.apply vs t) :=
    @hom.term sig _ (alg.subst n) _ (alg.subst p) _ (hom.subst us) _ t vs

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
