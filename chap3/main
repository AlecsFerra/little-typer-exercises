#lang pie

(claim + (-> Nat Nat Nat))
(define +
  (λ (l r)
    (iter-Nat r
      l
      (λ (r)
        (add1 r)))))

(claim gauss (-> Nat Nat))
(define gauss
  (λ (n)
    (rec-Nat n
      0
      (λ (n-1 gaussacc)
        (+ (add1 n-1) gaussacc)))))

(claim * (-> Nat Nat Nat))
(define *
  (λ (l r)
    (rec-Nat l
      0
      (λ (r-1 acc)
        (+ acc l)))))