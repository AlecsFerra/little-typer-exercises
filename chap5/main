#lang pie
(claim expectations (List Atom))
(define expectations
  (:: 'a
    (:: 'b
      (:: 'c nil))))

(claim len (Π ((X U))
             (-> (List X) Nat)))
(define len
  (λ (X)
    (λ (xs)
      (rec-List xs
        0
        (λ (x xs acc) (add1 acc))))))

(claim append (Π ((X U))
                (-> (List X) (List X) (List X))))
(define append
  (λ (X)
    (λ (xs ys)
      (rec-List xs
        ys
        (λ (x xs acc) (:: x acc))))))

; bla bla haskell