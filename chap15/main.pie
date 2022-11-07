#lang pie

(claim =consequence
  (→ Nat Nat
    U))
(define =consequence
  (λ (a b)
    (which-Nat a
      (which-Nat b
        Trivial
        (λ (_)
          Absurd))
      (λ (a-1)
        (which-Nat b
          Absurd
          (λ (b-1)
            (= Nat a-1 b-1)))))))

(claim =consequence-same
  (Π ([n Nat])
    (=consequence n n)))
(define =consequence-same
  (λ (n)
    (ind-Nat n
      (λ (n) (=consequence n n))
      sole
      (λ (n-1 _)
        (same n-1)))))

(claim use-Nat=
  (Π ([n Nat]
      [j Nat]
      [_ (= Nat n j)])
    (=consequence n j)))
(define use-Nat=
  (λ (n j n=j)
    (replace n=j
      (λ (j) (=consequence n j))
      (=consequence-same n))))

(claim 0=6→a=b
  (→ (= Nat 0 6)
    (= Atom 'a 'b)))
(define 0=6→a=b
  (λ (0=6)
    (ind-Absurd
      (use-Nat= 0 6 0=6)
      (= Atom 'a 'b))))

(claim n/=n+1
  (Π ([n Nat]
      [_ (= Nat n (add1 n))])
    Absurd))
(define n/=n+1
  (λ (n)
    (ind-Nat n
      (λ (n) (→ (= Nat n (add1 n))
               Absurd))
      (λ (0=1)
        (use-Nat= 0 1 0=1))
      (λ (n-1 n-1=n→⊥ n=n+1)
        (n-1=n→⊥ (use-Nat= (add1 n-1)
                   (add1 (add1 n-1))
                   n=n+1))))))

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
    (rec-Nat n
      0
      (λ (_ n+n-2)
        (+ 2 n+n-2)))))

(claim Even
  (-> Nat
    U))

(define Even
  (λ (n)
    (Σ ([half Nat])
      (= Nat n (double half)))))

(claim Odd
  (-> Nat
    U))

(define Odd
  (λ (n)
    (Σ ([haf Nat])
      (= Nat n (add1 (double haf))))))

(claim <=
  (-> Nat Nat
    U))

(define <=
  (λ (a b)
    (Σ ([k Nat])
      (= Nat (+ k a) b))))

;; Exercise 15.1
;;
;; State and prove that 3 is not less than 1.

(claim add1t
  (Π ([a Nat]
      [b Nat])
    (= Nat (add1 (+ a b)) (+ a (add1 b)))))
(define add1t
  (λ (a b)
    (ind-Nat a
      (λ (a) (= Nat (add1 (+ a b)) (+ a (add1 b))))
      (same (add1 b))
      (λ (a-1 p-1)
        (cong p-1 (+ 1))))))

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

(claim comm+
  (Π ([a Nat]
      [b Nat])
    (= Nat (+ a b) (+ b a))))
(define comm+
  (λ (a b)
    (ind-Nat b
      (λ (b) (= Nat (+ a b) (+ b a)))
      (n+zero=n a)
      (λ (b-1 p-1)
        (trans (symm (add1t a b-1))
          (cong p-1 (+ 1)))))))

(claim k+3/=1
  (Π ([k Nat]
      [_ (= Nat (+ k 3) 1)])
    Absurd))
(define k+3/=1
  (λ (k)
    (ind-Nat k
      (λ (k)
        (→ (= Nat (+ k 3) 1)
          Absurd))
      (λ (3=1)
        (use-Nat= 2 0 (use-Nat= 3 1 3=1)))
      (λ (k-1 k-1+3=1→⊥ 1+k-1+3=1)
        (replace (comm+ k-1 3)
          (λ (k-1+3) (=consequence k-1+3 0))
          (use-Nat= (+ k-1 3) 0 (use-Nat= (add1 (+ k-1 3)) 1 1+k-1+3=1)))))))

(claim not-3<=1
  (-> (<= 3 1)
    Absurd))
(define not-3<=1
  (λ (3<=1)
    (k+3/=1 (car 3<=1) (cdr 3<=1))))

;; Exercise 15.2
;;
;; State and prove that any natural number is not equal to its successor.

(claim n<>Sn
  (Π ([n Nat])
    (-> (= Nat n (add1 n))
      Absurd)))
;sopra

;; Exercise 15.3
;;
;; State and prove that for every Nat n, the successor of n is not less than
;; or equal to n.

(claim Sn-not<=-n
  (Π ([n Nat])
    (-> (<= (add1 n) n)
      Absurd)))
(define Sn-not<=-n
  (λ (n)
    (ind-Nat n
      (λ (n)
        (-> (<= (add1 n) n)
          Absurd))
      (λ (1<=0)
        (replace (comm+ (car 1<=0) 1)
          (λ (k+1) (=consequence k+1 0))
          (use-Nat= (+ (car 1<=0) 1) 0 (cdr 1<=0))))
      (λ (n-1 n<=n-1→⊥ n+1<=n)
        (n<=n-1→⊥
          ; (k, (= Nat (+ k (+ 1 n-1))      n-1)) -> Bot
          ; (k, (= Nat (+ k (+ 2 n-1)) (+ 1 n-1)))
          (TODO (use-Nat= )))))