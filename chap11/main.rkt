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

(claim vec-append
  (Π ([E U]
      [l Nat]
      [j Nat]
      [_ (Vec E l)]
      [_ (Vec E j)])
    (Vec E (+ l j))))
(define vec-append
  (λ (E l j vl vj)
    (ind-Vec l vl
      (λ (l vl)
        (Vec E (+ l j)))
      vj
      (λ (vl-1 v vls acc)
        (vec:: v acc)))))

(claim vec→list
  (Π ([E U]
      [l Nat]
      [_ (Vec E l)])
    (List E)))
(define vec→list
  (λ (E l es)
    (ind-Vec l es
      (λ (_ _)
        (List E))
      nil
      (λ (l e es acc)
        (:: e acc)))))

(claim list→vec→list
  (Π ([E U]
      [es (List E)])
    (= (List E)
       es
       (vec→list E (length E es) (list→vec E es)))))
(define list→vec→list
  (λ (E es)
    (ind-List es
      (λ (es)
        (= (List E)
          es
          (vec→list E (length E es) (list→vec E es))))
      (same nil)
      (λ (e es p-1)
        (cong p-1
          (the (→ (List E) (List E))
            (λ (r)
              (:: e r))))))))

;; Exercises on ind-Vec from Chapter 11 of The Little Typer

;; Exercise 11.1
;;
;; Use ind-Vec to define a function called unzip that takes unzips
;; a vector of pairs into a pair of vectors.

(claim unzip
  (Π ([A U]
      [B U]
      [n Nat])
    (-> (Vec (Pair A B) n)
      (Pair (Vec A n) (Vec B n)))))
(define unzip
  (λ (A B l xs)
    (ind-Vec l xs
      (λ (l xs) (Pair (Vec A l) (Vec B l)))
      (cons vecnil vecnil)
      (λ (_ x _ acc)
        (cons (vec:: (car x) (car acc))
          (vec:: (cdr x) (cdr acc)))))))