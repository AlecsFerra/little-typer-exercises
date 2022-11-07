#lang pie

;(claim kar (-> (Pair Nat Nat) Nat))
;(define kar
;  (λ (nm)
;    (elim-Pair
;      Nat Nat
;      Nat
;      nm
;      (λ (n m) n))))

;(kar (cons 1 2))

(claim flip
  (Π ((A U)
      (D U))
    (-> (Pair A D)
        (Pair D A))))
(define flip
  (λ (A D)
    (λ (p)
      (cons (cdr p) (car p)))))

(claim elim-Pair
  (Π ((A U)
      (D U)
      (X U))
    (-> (Pair A D)
        (-> A D
            X)
        X)))
(define elim-Pair
  (λ (A D X)
    (λ (pad ad->x)
      (ad->x (car pad) (cdr pad)))))

(claim kar (-> (Pair Nat Nat) Nat))
(define kar
  (λ (nm)
    (elim-Pair
      Nat Nat
      Nat
      nm
      (λ (n m) n))))