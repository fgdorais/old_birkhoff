-- birkhoff/algebras.lean --
-- Copyright Ⓒ 2015 François G. Dorais. All rights reserved.
-- Relesed under the MIT License as described in the file LICENSE.

import data .basic
open nat

structure ALG [class] [sig : SIG] (A : Type) :=
  (value : ∀ i : sig, (fin (func.arity i) → A) → A)

section
  variables [sig : SIG] (A : Type) [alg : ALG A]
  include sig A alg

  definition func.value :
    ∀ i : sig, (fin (func.arity i) → A) → A := ALG.value

  definition term.value :
    ∀ {n : nat}, term n → (fin n → A) → A :=
    @term.rec sig _
      (take n i xs, xs i)
      (take n i ts IH xs, func.value A i (λ j, IH j xs))

  definition const.value : const → A :=
    λ t, term.value A t fin.elim0

  definition term.value₁ : term 1 → A → A :=
    λ t x, term.value A t (λ j, x)

  lemma term.value_proj {n : nat} {i : fin n} :
    ∀ {xs : fin n → A}, term.value A (term.proj i) xs
                        = xs i :=
    take xs, rfl

  lemma term.value_appl {n : nat} {i : sig} {ts : fin (func.arity i) → term n} :
    ∀ {xs : fin n → A}, term.value A (term.appl i ts) xs
                        = func.value A i (λ j, term.value A (ts j) xs) :=
    take xs, rfl

  lemma const.value_appl (i : sig) {ts : fin (func.arity i) → const} :
    const.value A (term.appl i ts) = func.value A i (λ j, const.value A (ts j)) :=
    rfl

end

namespace alg
  open prod
  variable [sig : SIG]
  include sig

  definition trivial [instance] : ALG unit :=
    ALG.mk (λ i xs, unit.star)

  definition prod [instance]
    (A : Type) [alga : ALG A]
    (B : Type) [algb : ALG B] :
    ALG (A × B) :=
    ALG.mk (λ i xs, (func.value A i (λ j, pr₁ (xs j)), func.value B i (λ j, pr₂ (xs j))))

  definition depprod [instance]
    {J : Type} (A : J → Type) [alg : ∀ j : J, ALG (A j)] :
    ALG (Π j : J, A j) :=
    ALG.mk (λ i xs, (λ j : J, func.value (A j) i (λ i, xs i j)))

end alg

structure HOM [class] [sig : SIG]
  {A : Type} [alga : ALG A]
  {B : Type} [algb : ALG B]
  (h : A → B) :=
  (ident : ∀ i : sig, ∀ xs : fin (func.arity i) → A,
             func.value B i (λ j, h (xs j)) = h (func.value A i xs))

theorem hom.func [sig : SIG]
  {A : Type} [alga : ALG A]
  {B : Type} [algb : ALG B]
  (h : A → B) [hom : HOM h] :
  ∀ {i : sig} {xs : fin (func.arity i) → A},
    func.value B i (λ j, h (xs j)) = h (func.value A i xs) :=
  @HOM.ident sig A alga B algb h hom

theorem hom.term [sig : SIG]
  {A : Type} [alga : ALG A]
  {B : Type} [algb : ALG B]
  (h : A → B) [hom : HOM h] :
  ∀ {n : nat} {t : term n} {xs : fin n → A},
    term.value B t (λ j, h (xs j)) = h (term.value A t xs) :=
  @term.rec _ _
    (take n i xs, rfl)
    (take n i ts IH xs,
     let ys := λ j : fin n, h (xs j) in
     have IH' : (λ k, term.value B (ts k) ys)
                = (λ k, h (term.value A (ts k) xs)),
     from funext (λ k, IH k xs),
     calc
      term.value B (term.appl i ts) ys
          = func.value B i (λ j, term.value B (ts j) ys)     : rfl
      ... = func.value B i (λ j, h (term.value A (ts j) xs)) : IH'
      ... = h (func.value A i (λ j, term.value A (ts j) xs)) : hom.func h
      ... = h (term.value A (term.appl i ts) xs)             : term.value_appl)

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
            by rewrite [hom.func g, hom.func f])

  definition trivial [instance]
    {A : Type} [alg : ALG A] :
    @HOM sig A alg unit alg.trivial (λ x, unit.star) :=
    HOM.mk (take i xs, unit.eq _ _)

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
    HOM.mk (take i xs, prod.eq (hom.func h₁) (hom.func h₂))

  definition depproj [instance]
    {J : Type} {A : J → Type} [alg : Π j : J, ALG (A j)] (j : J) :
    @HOM sig _ (alg.depprod A) _ (alg j) (λ (x : Π j : J, A j), x j) :=
    HOM.mk (take i xs, rfl)

  definition depprod [instance]
    {A : Type} [alg : ALG A]
    {J : Type} {B : J → Type} [algb : Π j : J, ALG (B j)]
    (h : Π j : J, A → B j) [hom : Π j : J, HOM (h j)] :
    @HOM sig _ alg _ (alg.depprod B) (λ (x : A) (j : J), h j x) :=
    HOM.mk (take i xs, funext (take j, hom.func (h j)))

end hom
