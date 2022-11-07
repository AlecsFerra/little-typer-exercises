#lang pie


(claim +
  (-> Nat Nat
    Nat))
(define +
  (λ (a b)
    (rec-Nat a
      b
      (λ (_ b+a-k)
        (add1 b+a-k)))))

(claim double
  (-> Nat
    Nat))
(define double
  (λ (n)
    (iter-Nat n
      0
      (+ 2))))

(claim Even
  (→ Nat
    U))
(define Even
  (λ (n)
    (Σ ([half Nat])
      (= Nat n (double half)))))

(claim e10 (Even 10))
(define e10
  (cons 5
    (same 10)))

(claim +2even→even
  (Π ([n Nat]
      [_ (Even n)])
    (Even (+ 2 n))))
(define +2even→even
  (λ (n neven)
    (cons (+ 1 (car neven))
      (cong (cdr neven) (+ 2)))))

(claim Odd
  (→ Nat
    U))
(define Odd
  (λ (n)
    (Σ ([half Nat])
      (= Nat n (add1 (double half))))))

(claim o1
  (Odd 1))
(define o1
  (cons 0
    (same 1)))

(claim +1even→odd
  (Π ([n Nat]
      [_ (Even n)])
    (Odd (add1 n))))
(define +1even→odd
  (λ (n neven)
    (cons (car neven)
      (cong (cdr neven) (+ 1)))))

(claim +1odd→even
  (Π ([n Nat]
      [_ (Odd n)])
    (Even (add1 n))))
(define +1odd→even
  (λ (n nodd)
    (cons (+ 1 (car nodd))
      (cong (cdr nodd) (+ 1)))))

(claim even-or-odd
  (Π ([n Nat])
    (Either (Even n) (Odd n))))
(define even-or-odd
  (λ (n)
    (ind-Nat n
      (λ (n)
        (Either (Even n) (Odd n)))
      (left (cons 0 (same 0)))
      (λ (n-1 n-1eod)
        (ind-Either n-1eod
          (λ (_)
            (Either (Even (add1 n-1)) (Odd (add1 n-1))))
            (λ (evenn-1)
              (right (+1even→odd n-1 evenn-1)))
            (λ (oddn-1)
              (left (+1odd→even n-1 oddn-1))))))))