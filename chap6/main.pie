#lang pie

(claim avec (Vec Atom 2))
(define avec (vec:: 'a
               (vec:: 'b vecnil)))

(claim em (Vec Atom 0))
(define em vecnil)

(claim fst (Π ((Of U)
               (L-1 Nat))
             (-> (Vec Of (add1 L-1)) Of)))
(define fst (λ (Of L-1)
              (λ (v)
                (head v))))

;(fst Nat 2 (vec:: 1 (vec:: 2 (vec:: 3 vecnil))))

(claim res (Π ((Of U)
               (L-1 Nat)
               (vec (Vec Of (add1 L-1))))
             (Vec Of L-1)))
(define res (λ (Of L-1 vec) (tail vec)))