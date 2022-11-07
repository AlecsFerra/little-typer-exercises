#lang pie

(claim Maybe
  (→ U
    U))
(define Maybe
  (λ (E)
    (Either E Trivial)))

(claim nothing
  (Π ([E U])
    (Maybe E)))
(define nothing
  (λ (_)
    (right sole)))

(claim just
  (Π ([E U]
      [_ E])
    (Maybe E)))
(define just
  (λ (_ v)
    (left v)))

(claim maybe-head
  (Π ([E U]
      [_ (List E)])
    (Maybe E)))
(define maybe-head
  (λ (E es)
    (ind-List es
      (λ (_)
        (Maybe E))
      (nothing E)
      (λ (e _ _)
        (just E e)))))

(claim maybe-tail
  (Π ([E U]
      [_ (List E)])
    (Maybe (List E))))
(define maybe-tail
  (λ (E es)
    (ind-List es
      (λ (_)
        (Maybe (List E)))
      (nothing (List E))
      (λ (_ es _)
        (just (List E) es)))))

(claim maybe-right
  (Π ([T U]
      [K U]
      [_ (Either T K)])
    (Maybe K)))
(define maybe-right
  (λ (_ K e)
    (ind-Either e
      (λ (_)
        (Maybe K))
      (λ (_) (nothing K))
      (λ (v) (just K v)))))



(claim Two
  U)
(define Two
  (Either Trivial Trivial))
(claim Two-Fun
  (→ Nat
    U))
(define Two-Fun
  (λ (n)
    (iter-Nat n
      Two
      (λ (type)
        (→ Two
          type)))))
(claim both-left
  (→ Two Two
    Two))
(define both-left
  (λ (a b)
    (ind-Either a
      (λ (c)
        Two)
      (λ (left-sole)
        b)
      (λ (right-sole)
        (right sole)))))
(claim step-taut
  (Π ((n-1 Nat))
    (→ (→ (Two-Fun n-1)
         Two)
      (→ (Two-Fun (add1 n-1))
        Two))))
(define step-taut
  (λ (n-1 tautn-1)
    (λ (f )
      (both-left
        (tautn-1
          (f (left sole)))
        (tautn-1
          (f (right sole)))))))
(claim taut
  (Π ((n Nat))
    (→ (Two-Fun n)
      Two)))
(define taut
  (λ (n)
    (ind-Nat n
      (λ (k)
        (→ (Two-Fun k)
          Two))
      (λ (x)
        x)
      step-taut)))