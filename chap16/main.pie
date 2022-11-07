#lang pie

(claim pem
  (Π ([X U])
    (Either X (→ X Absurd))))

(claim pem-not-false
  (Π ([X U])
    (→ (→ (Either X
            (→ X
              Absurd))
         Absurd)
      Absurd)))
(define pem-not-false
  (λ (X pem-false)
    (pem-false
      (right (λ (x)
               (pem-false
                 (left x)))))))

(claim Dec
  (→ U U))
(define Dec
  (λ (X)
    (Either X
      (→ X Absurd))))

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

(claim +
  (-> Nat Nat
    Nat))

(define +
  (λ (a b)
    (rec-Nat a
      b
      (λ (_ b+a-k)
        (add1 b+a-k)))))

;; now chap 16
(claim zero?
  (Π ([n Nat])
    (Dec (= Nat 0 n))))
(define zero?
  (λ (n)
    (ind-Nat n
      (λ (n)
        (Dec (= Nat 0 n)))
      (left (same 0))
      (λ (n-1 _)
        (right (λ (1+n=0)
                 (use-Nat= 0 (add1 n-1) 1+n=0)))))))

(claim zerof?
  (Π ([n Nat])
    (Dec (= Nat n 0))))
(define zerof?
  (λ (n)
    (ind-Nat n
      (λ (n)
        (Dec (= Nat n 0)))
      (left (same 0))
      (λ (n-1 _)
        (right (λ (1+n=0)
                 (use-Nat= (add1 n-1) 0 1+n=0)))))))

(claim sub1=
  (Π ([n Nat]
      [m Nat]
      [_ (= Nat (add1 n) (add1 m))])
    (= Nat n m)))
(define sub1=
  (λ (n m 1+n=1+m)
    (use-Nat= (+ 1 n) (+ 1 m) 1+n=1+m))) 

(claim nat=?
  (Π([n Nat]
     [m Nat])
    (Dec (= Nat n m))))
(define nat=?
  (λ (n m)
    ((ind-Nat n
       (λ (n)
         (Π ([m Nat])
           (Dec (= Nat n m))))
       (λ (m)
         (zero? m))
       (λ (n-1 m→tar m)
         (ind-Nat m
           (λ (m)
             (Dec (= Nat (add1 n-1) m)))
           (zerof? (add1 n-1))
           (λ (m-1 n→tar)
             (ind-Either (m→tar m-1)
               (λ (_)
                 (Dec (= Nat (add1 n-1) (add1 m-1))))
               (λ (n-1=m-1)
                 (left (cong n-1=m-1 (+ 1))))
               (λ (n-1=m-1→abs)
                 (right (λ (n=m)
                          (n-1=m-1→abs (sub1= n-1 m-1 n=m))))))))))
      m)))

;; ex
