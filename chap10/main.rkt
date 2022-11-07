#lang pie

;(claim list→vec
;  (Π ([E U]
;      [_ (List E)])
;    (Σ ([l Nat])
;       (Vec E l))))
;(define list→vec
;  (λ (E list)
;    (rec-List list
;      (the (Σ ([l Nat])
;             (Vec E l))
;        (cons 0 vecnil))
;      (λ (l _ acc)
;        (cons (add1 (car acc))
;          (vec:: l (cdr acc)))))))
; But
; (define list→vec
;   (λ (E l)
;     (cons 0 vecnil)))

(claim length
  (Π ([E U]
      [_ (List E)])
    Nat))
(define length
  (λ (E es)
    (rec-List es
      0
      (λ (_ _ acc)
        (add1 acc)))))

(claim list→vec
  (Π ([E U]
      [es (List E)])
    (Vec E (length E es))))
(define list→vec
  (λ (E es)
    (ind-List es
      (λ (es)
        (Vec E (length E es)))
      vecnil
      (λ (e es acc)
        (vec:: e acc)))))

;; Still subject to the replicate bug

;; Exercises on ind-Nat from Chapter 10 of The Little Typer

(claim +
  (-> Nat Nat
    Nat))

(define +
  (λ (a b)
    (rec-Nat a
      b
      (λ (_ b+a-k)
        (add1 b+a-k)))))

(claim step-append
  (Π ([E U])
    (-> E (List E) (List E)
      (List E))))

(define step-append
  (λ (E)
    (λ (e es append-es)
      (:: e append-es))))

(claim append
  (Π ([E U])
    (-> (List E) (List E)
      (List E))))

(define append
  (λ (E)
    (λ (start end)
      (rec-List start
        end
        (step-append E)))))

(claim filter-list
  (Π ([E U])
    (-> (-> E Nat) (List E)
      (List E))))

(claim filter-list-step
  (Π ([E U])
    (-> (-> E Nat)
      (-> E (List E) (List E)
        (List E)))))

(claim if
  (Π ([A U])
    (-> Nat A A
      A)))

(define if
  (λ (A)
    (λ (e if-then if-else)
      (which-Nat e
        if-else
        (λ (_) if-then)))))

(define filter-list-step
  (λ (E)
    (λ (p)
      (λ (e es filtered-es)
        (if (List E) (p e)
          (:: e filtered-es)
          filtered-es)))))

(define filter-list
  (λ (E)
    (λ (p es)
      (rec-List es
        (the (List E) nil)
        (filter-list-step E p)))))

;; Exercise 10.1
;;
;; Define a function called list-length-append-dist that states and proves that
;; if you append two lists, l1 and l2, and then the length of the result is
;; equal to the sum of the lengths of l1 and l2.

(claim list-length-append-dist
  (Π ([E U]
      [l1 (List E)]
      [l2 (List E)])
    (= Nat
       (length E (append E l1 l2))
       (+ (length E l1) (length E l2)))))
(define list-length-append-dist
  (λ (E l1 l2)
    (ind-List l1
      (λ (l1)
        (= Nat
          (length E (append E l1 l2))
          (+ (length E l1) (length E l2))))
      (same (length E l2))
      (λ (l1 l1s p-1)
        (cong p-1 (+ 1))))))

;; Exercise 10.2
;;
;; In the following exercises we'll use the function called <= that takes two
;; Nat arguments a, b and evaluates to a type representing the proposition
;; that a is less than or equal to b.

(claim <=
  (-> Nat Nat
    U))

(define <=
  (λ (a b)
    (Σ ([k Nat])
      (= Nat (+ k a) b))))

;; Exercise 10.2.1
;;
;; Using <=, state and prove that 1 is less than or equal to 2.
(claim 1<=2 (<= 1 2))
(define 1<=2
  (cons 1 (same 2)))

;; Exercise 10.2.2
;;
;; Define a funciton called <=-simplify to state and prove that for all
;; Nats a, b, n we have that n+a <= b implies a <= b
;;
;; NB: You may need to use plusAssociative that was proved in Exercise 8.3.
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

(claim swap+
  (Π ([a Nat]
      [b Nat]
      [c Nat])
    (= Nat (+ (+ a b) c) (+ (+ a c) b))))
(define swap+
  (λ (a b c)
    (ind-Nat a
      (λ (a) (= Nat (+ (+ a b) c) (+ (+ a c) b)))
      (comm+ b c)
      (λ (a-1 p-1)
        (cong p-1 (+ 1))))))

(claim <=-simplify-step
  (Π ([k Nat]
      [n Nat]
      [a Nat])
    (= Nat (+ k (+ n a)) (+ (+ n k) a))))
(define <=-simplify-step
  (λ (k n a)
    (replace (comm+ k n)
      (λ (+kn) (= Nat (+ k (+ n a)) (+ +kn a)))
      (assoc+ k n a))))
 
(claim <=-simplify
  (Π ([a Nat]
      [b Nat]
      [n Nat]
      [_ (<= (+ n a) b)])
    (<= a b)))
(define <=-simplify
  (λ (a b n n+a<=b)
    (cons (+ n (car n+a<=b))
      ; let k = (car n+a<=b
      ; GOAL
      ; (= Nat
      ;    (+ (+ n k) a)
      ;    b)
      ; ORA
      ; (= Nat
      ;   (+ k (+ n a))
      ;   b)
      ; Serve assoc+
      (trans (symm (<=-simplify-step (car n+a<=b) n a))
        (cdr n+a<=b)))))

;; Exercise 10.2.3
;;
;; Define a function called <=-trans that states and proves that <= is
;; transitive.

(claim <=-trans
  (Π ([a Nat]
      [b Nat]
      [c Nat])
    (-> (<= a b)
        (<= b c)
      (<= a c))))
(define <=-trans
  (λ (a b c a<=b b<=c)
    ; a + (car a<=b) = b ~ (cdr a<=b)
    ; b + (car b<=c) = c ~ (cdr b<=c)
    (<=-simplify a c (car a<=b) ; (<= (+ (car a<=b a) c)
      (replace (symm (cdr a<=b))
        (λ (b)
          (Σ ([k Nat])
            (= Nat (+ k b) c)))
        b<=c))))
    
;; Exercise 10.3
;;
;; Define a function called length-filter-list that states and proves that
;; filtering a list (in the sense of filter-list from Exercise 5.3) evaluates
;; to a a list no longer than the original list.

(claim <=+1
  (Π ([a Nat]
      [b Nat]
      [_ (<= a b)])
    (<= a (+ 1 b))))
(define <=+1
  (λ (a b a<=b)
    (cons (+ 1 (car a<=b))
      (cong (cdr a<=b) (+ 1)))))

(claim +1<=+1
  (Π ([a Nat]
      [b Nat]
      [_ (<= a b)])
    (<= (+ 1 a) (+ 1 b))))
(define +1<=+1
  (λ (a b a<=b)
    (cons (car a<=b)
      (replace (add1t (car a<=b) a)
        (λ (sum) (= Nat sum (add1 b)))
        (cong (cdr a<=b) (+ 1))))))
      

(claim motive
  (Π ([E U]
      [_ (-> E Nat)]
      [_ (List E)])
    U))
(define motive
  (λ (E p l)
    (<= (length E (filter-list E p l))
      (length E l))))
 
(claim length-filter-list
  (Π ([E U]
      [l (List E)]
      [p (-> E Nat)])
    (<= (length E (filter-list E p l))
        (length E l))))
(define length-filter-list
  (λ (E l p)
    (ind-List l
      (motive E p)
      (cons 0 (same 0))
      (λ (e es proof-1)
        (<=-trans (length E (filter-list E p (:: e es)))
          (length E (:: e (filter-list E p es)))
          (length E (:: e es))
          (if (motive E p (:: e (filter-list E p es))) (p e)
            TODO
            TODO)
          (+1<=+1 (length E (filter-list E p es))
            (length E es)
            proof-1))))))