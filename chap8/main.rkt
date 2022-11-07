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

(claim inc (-> Nat Nat))
(define inc
  (λ (n)
    (iter-Nat n
      1
      (+ 1))))

(claim add1=inc
  (Π ((n Nat))
    (= Nat (add1 n) (inc n))))
(define add1=inc
  (λ (n)
    (ind-Nat n
      (λ (n) (= Nat (add1 n) (inc n)))
      (same 1)
      (λ (n-1 add1=inc-1)
        (cong add1=inc-1 (+ 1))))))

;; ESERCIZI VARI

;; Exercise 8.1
;; Define a function called zero+n=n that states and proves that
;; 0+n = n for all Nat n.

(claim zero+n=n
  (Π ((n Nat))
    (= Nat (+ 0 n) n)))
(define zero+n=n
  (λ (n)
    (same n)))

(claim n+zero=n
  (Π ((n Nat))
    (= Nat (+ n 0) n)))
(define n+zero=n
  (λ (n)
    (ind-Nat n
      (λ (n)
        (= Nat (+ n 0) n))
      (same 0)
      (λ (n-1 =n-1)
        (cong =n-1 (+ 1))))))

;; Exercise 8.2
;;
;; Define a function called a=b->a+n=b+n that states and proves that
;; a = b implies a+n = b+n for all Nats a, b, n.
(claim a=n->a+n=b+n
  (Π ((a Nat)
      (b Nat)
      (n Nat)
      (_ (= Nat a b)))
    (= Nat (+ a n) (+ b n))))

(define a=n->a+n=b+n
  (λ (a b n a=b)
    (cong a=b
      (the (-> Nat Nat)
        (λ (x) (+ x n))))))

;; Exercise 8.3
;;
;; Define a function called plusAssociative that states and proves that
;; + is associative.
(claim assoc+
  (Π ((a Nat)
      (b Nat)
      (c Nat))
    (= Nat (+ a (+ b c)) (+ (+ a b) c))))
(define assoc+
  (λ (a b c)
    (ind-Nat a
      (λ (n)
        (= Nat (+ n (+ b c)) (+ (+ n b) c)))
      (same (+ b c))
      (λ (n-1 pn-1)
        (cong pn-1 (+ 1))))))