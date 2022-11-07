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

(claim twice
  (-> Nat
    Nat))
(define twice
  (λ (n)
    (+ n n)))

(claim add1+=+add1
  (Π ((n Nat)
      (m Nat))
    (= Nat (add1 (+ n m)) (+ n (add1 m)))))
(define add1+=+add1
  (λ (n m)
    (ind-Nat n
      (λ (n) (= Nat (add1 (+ n m)) (+ n (add1 m))))
      (same (add1 m))
      (λ (n-1 pn-1)
        (cong pn-1
          (the (-> Nat Nat)
            (+ 1)))))))

(claim twice=double
  (Π ((n Nat))
    (= Nat (twice n) (double n))))
(define twice=double
  (λ (n)
    (ind-Nat n
      (λ (n) (= Nat (twice n) (double n)))
      (same 0)
      (λ (n-1 pn-1)
        (replace (add1+=+add1 n-1 n-1)
          (λ (k)
            (= Nat
              (add1 k)
              (add1 (add1 (double n-1)))))
          (cong pn-1 (+ 2)))))))


(claim double-Vec
  (Π ((Of U)
      (len Nat)
      (_ (Vec Of len)))
    (Vec Of (double len))))
(define double-Vec
  (λ (Of len)
    (ind-Nat len
      (λ (len)
        (-> (Vec Of len)
          (Vec Of (double len))))
      (λ (v0)
        vecnil)
      (λ (_ fvn-1 vn)
        (vec:: (head vn)
          (vec:: (head vn)
            (fvn-1 (tail vn))))))))

(claim twice-Vec
  (Π ((Of U)
      (len Nat)
      (_ (Vec Of len)))
    (Vec Of (twice len))))
(define twice-Vec
  (λ (Of len v)
    (replace (symm (twice=double len))
      (λ (k) (Vec Of k))
      (double-Vec Of len v))))

; Replace
; La prova che definisce la sostituzione, es se voglio sostituire a
;   con b in un tipo devo fornire (= T b a)
; Dato un un b qualsiasi (quindi un T) come costruisco il nuovo tipo
; La mia expressione in cui effettuare la sostituzione

;; Exercise 9.1
;;
;; Define a function called same-cons that states and proves that
;; if you cons the same value to the front of two equal Lists then
;; the resulting Lists are also equal.
(claim same-cons
  (Π ([E U]
      [l1 (List E)]
      [l2 (List E)]
      [e E])
    (-> (= (List E) l1 l2)
      (= (List E) (:: e l1) (:: e l2)))))
(define same-cons
  (λ (E l1 l2 e l1=l2)
    (replace l1=l2
      (λ (l) (= (List E) (:: e l1) (:: e l)))
      (same (:: e l1)))))

(claim same-lists
  (Π ([E U]
      [l1 (List E)]
      [l2 (List E)]
      [e1 E]
      [e2 E])
    (-> (= E e1 e2) (= (List E) l1 l2)
      (= (List E) (:: e1 l1) (:: e2 l2)))))
(define same-lists
  (λ (E l1 l2 e1 e2 e1=e2 l1=l2)
    (replace e1=e2
      (λ (e) (= (List E) (:: e1 l1) (:: e l2)))
      (same-cons E l1 l2 e1 l1=l2))))
      
;; Some proofs about pairs
;; ∀ a b c. a = b → (a, c) = (b, c)
(claim a=b→ac=bc
  (Π ([T U]
      [K U]
      [a T]
      [b T]
      [c K]
      [_ (= T a b)])
    (= (Pair T K) (cons a c) (cons b c))))
(define a=b→ac=bc
  (λ (T K a b c a=b)
    (replace a=b
      (λ (b)
        (= (Pair T K) (cons a c) (cons b c)))
      (same (cons a c)))))

;; ∀ a b c d. a = b & c = d → (a, c) = (b, d)
(claim a=bc=d→ac=bd
  (Π ([T U]
      [K U]
      [a T]
      [b T]
      [c K]
      [d K]
      [_ (= T a b)]
      [_ (= K c d)])
    (= (Pair T K) (cons a c) (cons b d))))
(define a=bc=d→ac=bd
  (λ (T K a b c d a=b c=d)
    (replace c=d
      (λ (d)
        (= (Pair T K) (cons a c) (cons b d)))
      (a=b→ac=bc T K a b c a=b))))

;; ∀ a b c d. (a, c) = (b, d) → a = b & c = d
(claim ac=bd→a=bc=d
  (Π ([T U]
      [K U]
      [a T]
      [b T]
      [c K]
      [d K]
      [_ (= (Pair T K) (cons a c) (cons b d))])
    (Pair (= T a b) (= K c d))))
(define ac=bd→a=bc=d
  (λ (T K a b c d ac=bd)
    (cons
      (replace ac=bd
        (λ (bd)
          (= T a (car bd)))
        (same a))
      (replace ac=bd
        (λ (bd)
          (= K c (cdr bd)))
        (same c)))))