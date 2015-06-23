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

  definition term.value₀ : term 0 → A :=
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

  definition subst [instance] (n : nat) : ALG (term n) :=
    ALG.mk (λ i xs, term.appl i xs)

  definition initial [instance] : ALG (term 0) := alg.subst 0

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
    HOM.mk (take i xs, sorry)

  definition proj₂ [instance]
    {A₁ : Type} [alg₁ : ALG A₁]
    {A₂ : Type} [alg₂ : ALG A₂] :
    @HOM sig _ (alg.prod A₁ A₂) _ alg₂ pr₂ :=
    HOM.mk (take i xs, sorry)

  definition prod [instance]
    {A : Type} [alg : ALG A]
    {B₁ : Type} [alg₁ : ALG B₁] (h₁ : A → B₁) [hom₁ : HOM h₁]
    {B₂ : Type} [alg₂ : ALG B₂] (h₂ : A → B₂) [hom₂ : HOM h₂] :
    @HOM sig _ alg _ (alg.prod B₁ B₂) (λ x : A, (h₁ x, h₂ x)) :=
    HOM.mk (take i xs, prod.eq (func.hom h₁) (func.hom h₂))

  definition depproj [instance]
    {J : Type} {A : J → Type} [alg : Π j : J, ALG (A j)] (j : J) :
    @HOM sig _ (alg.depprod A) _ (alg j) (λ (x : Π j : J, A j), x j) :=
    HOM.mk (take i xs, sorry)

  definition depprod [instance]
    {A : Type} [alg : ALG A]
    {J : Type} {B : J → Type} [algb : Π j : J, ALG (B j)]
    (h : Π j : J, A → B j) [hom : Π j : J, HOM (h j)] :
    @HOM sig _ alg _ (alg.depprod B) (λ (x : A) (j : J), h j x) :=
    HOM.mk (take i xs, sorry)

end hom

section
  open alg
  variable [sig : SIG]
  include sig

  definition subst {n m : nat} :
    (fin m → term n) → term m → term n :=
    take us t,
    @term.value sig _ (alg.subst n) _ t us

  theorem subst.assoc {n m p : nat}
    {t : term p} {us : fin p → term m} {vs : fin m → term n} :
    subst (λ i, subst vs (us i)) t = subst vs (subst us t) :=
    @hom.term sig _ (alg.subst m) _ (alg.subst n) _ (hom.subst vs) _ _ _

end
