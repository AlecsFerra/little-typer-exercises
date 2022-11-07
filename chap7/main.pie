#lang pie

(claim peas
  (Π ((many Nat))
    (Vec Atom many)))
(define peas
  (λ (many)
    (ind-Nat many
      (λ (n) (Vec Atom n)) ; Motive
      vecnil
      (λ (many-1 peas)
        (vec:: 'pea peas)))))

; last
(claim last
  (Π ((Of U)
      (many-1 Nat)
      (vec (Vec Of (add1 many-1))))
    Of))
(define last
  (λ (Of many-1 vec)
    ((ind-Nat many-1
      (λ (many-1)
        (-> (Vec Of (add1 many-1))
              Of))
      (λ (vec1)
        (head vec1))
      (λ (n-1 f-1 arg)
        (f-1 (tail arg)))) vec)))

; (last Nat 0 (vec:: 1 vecnil))
; (last Nat 1 (vec:: 1 (vec:: 2 vecnil)))
; (last Nat 2 (vec:: 1 (vec:: 2 (vec:: 3 vecnil))))

; drop last
(claim drop-last
  (Π ((Of U)
      (many-1 Nat)
      (vec (Vec Of (add1 many-1))))
    (Vec Of many-1)))
(define drop-last
  (λ (Of many-1 vec)
    ((ind-Nat many-1
       (λ (n)
         (-> (Vec Of (add1 n))
             (Vec Of n)))
       (λ (vec1)
         vecnil)
       (λ (n-1 f-1 vecn)
         (vec:: (head vecn)
           (f-1
             (tail vecn))))) vec)))