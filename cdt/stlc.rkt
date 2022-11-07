#lang racket

(struct Closure
  (env var body)
  #:transparent)

(define (extend ρ n v)
  (cons (cons n v) ρ))

(define (val ρ expr)
  (match expr
    [`(λ (,var) ,body)
     (Closure ρ var body)]
    [`(,clos ,arg)
     (do-ap (val ρ clos)
            (val ρ arg))]
    [x #:when (symbol? x)
       (let ((val (assv x ρ)))
         (if val
             (cdr val)
             (error 'val "Unknown name ~a" x)))]))

;(define (do-ap clos arg)
;  (match clos
;    [(Closure ρ arg-name body)
;     (val (extend ρ arg-name arg) body)]))

;(define (run-program ρ exprs)
;  (match exprs
;    ['() (void)]
;    [(cons `(define ,name ,body) rest)
;     (let ([value (val ρ body)])
;       (run-program (extend ρ name value) rest))]
;    [(cons e rest)
;     (displayln (val ρ e))
;     (run-program ρ rest)]))


(define (add-* x)
  (string->symbol
   (string-append (symbol->string x)
                  "*")))
(define (freshen used x)
  (if (memv x used)
      (freshen used (add-* x))
      x))

(struct Neutral-Variable
  (name))
(struct Neutral-Application
  (rator rand))

(define (do-ap clos arg)
  (match clos
    [(Closure ρ arg-name body)
     (val (extend ρ arg-name arg) body)]
    [x
     (Neutral-Application x arg)]))

(define (read-back used-names v)
  (match v
    [(Closure ρ var body)
     (let* ((var* (freshen used-names var))
            (neutral-var (Neutral-Variable var*)))
       `(λ (,var*)
          ,(read-back (cons var* used-names)
                      (val (extend ρ var neutral-var) body))))]
    [(Neutral-Variable x) x]
    [(Neutral-Application rator rand)
     `(,(read-back used-names rator) ,(read-back used-names rand))]))

(define (norm e)
  (read-back '() e))

(define (run-program ρ exprs)
  (match exprs
    ['() (void)]
    [(cons `(define ,name ,body) rest)
     (let ([value (val ρ body)])
       (run-program (extend ρ name value) rest))]
    [(cons e rest)
     (displayln (norm (val ρ e)))
     (run-program ρ rest)]))

(define (with-numerals e)
  `((define church-zero
      (λ (f)
        (λ (x)
          x)))
    (define church-add1
      (λ (n-1)
        (λ (f)
          (λ (x)
            (f ((n-1 f) x))))))
    ,e))

(define (to-church n)
  (cond [(zero? n) 'church-zero]
        [(positive? n)
         (let ([church-of-n-1 (to-church (sub1 n))])
           `(church-add1 ,church-of-n-1))]))

(define church-add
  `(λ (j)
     (λ (k)
       (λ (f)
         (λ (x)
           ((j f) ((k f) x)))))))


(struct go
  (result)
  #:transparent)
(struct stop
  (expr message)
  #:transparent)

(require (for-syntax syntax/parse))

(define-syntax (go-on stx)
  (syntax-parse stx
    [(go-on () result)
     (syntax/loc stx
       result)]
    [(go-on ([pat0 e0] [pat e] ...) result)
     (syntax/loc stx
       (match e0
         [(go pat0) (go-on ([pat e] ...) result)]
         [(go v)    (error 'go-on "Pattern did not mathc ~v" v)]
         [(stop expr msg) (stop expr msg)]))]))

(define (type=? t1 t2)
  (match* (t1 t2)
    [('Nat 'Nat)
     #t]
    [(`(→ ,A1 ,R1) `(→ ,A2 ,R2))
     (and (type=? A1 A2) (type=? R1 R2))]
    [(_ _)
     #f]))

(define (type? t)
  (type=? t t))

(define (synth Γ expr)
  (match expr
    ; Annotations are an explicit form of type checking
    [`(the ,t ,e)
     (if (not (type? t))
         (stop expr (format "~a is not a type" t))
         (go-on ([_ (check Γ e t)])
                (go t)))]
    [`(rec ,t ,target ,base ,step)
     (go-on ([target-type (synth Γ target)]
             [_           (if (type=? target-type 'Nat)
                              (go 'ok)
                              (stop target (format "Expected Nat but got ~v"
                                                   target-type)))]
             [_           (check Γ base t)]
             [_           (check Γ step `(→ Nat (→ ,t ,t)))])
            (go t))]
    [x #:when (and (symbol? x)
                   (not (memv x '(the rec λ zero add1))))
       (match (assv x Γ)
         [#f         (stop x "Variable not found")]
         [(cons _ t) (go t)])]
    (`(,rator ,rand)
     (go-on ([rator-type (synth Γ rator)])
            (match rator-type
              [`(→ ,rator-arg-type, rator-ret-type)
               (go-on ([_ (check Γ rand rator-arg-type)])
                      (go rator-ret-type))]
              [else (stop rator (format "~v is not a function type"
                                        rator-type))])))))

(define (check Γ expr t)
  (match expr
    ['zero
     (if (type=? t 'Nat)
         (go 'ok)
         (stop expr (format "zero is not a ~v" t)))]
    [`(add1 ,n)
     (if (type=? t 'Nat)
         (go-on ([_ (check Γ n 'Nat)])
                (go 'ok))
         (stop expr (format "add1 is not a contructor for ~v" t)))]
    [`(λ (,arg) ,body)
     (match t
       [`(→ ,arg-type ,ret-type)
        (go-on ([_ (check (extend Γ arg arg-type) body ret-type)])
               (go 'ok))]
       [x
        (stop expr (format "Expected an → but found ~a" x))])]
    [x
     (go-on ([x-type (synth Γ expr)])
            (if (type=? t x-type)
                (go 'ok)
                (stop expr
                      (format "Infered type ~v but expected ~v"
                              x-type x))))]))

(define (check-program Γ prog)
  (match prog
    ['()
     (go Γ)]
    [(cons `(define ,name ,expr) rest)
     (go-on ([t (synth Γ expr)])
            (check-program (extend Γ name t) rest))]
    [(cons expr rest)
     (go-on ([t (synth Γ expr)])
            (begin
              (printf "~a has type ~a\n" expr t)
              (check-program Γ rest)))]))

(struct Zero ()
  #:transparent)
(struct Add1 (predecessor)
  #:transparent)
(struct Neutral (type neutral-expr)
  #:transparent)
(struct Neutral-Recursion (type target base step)
  #:transparent)
(struct The (type value)
  #:transparent)

(define (norm? v)
  (THE? v))

(define (val ρ e)
  (match e
    [`(the ,type ,expr)
     (val ρ expr)]
    ['zero (ZERO)]
    [`(add1 ,n) (ADD1 (val ρ n))]
    [x #:when (and (symbol? x)
                   (not (memv x '(the zero add1 λ rec))))
     (cdr (assv x ρ))]
    [`(λ (,x) ,b)
     (CLOS ρ x b)]
    [`(rec ,type ,target ,base ,step)
     (do-rec type (val ρ target) (val ρ base) (val ρ step))]
    [`(,rator ,rand)
     (do-ap (val ρ rator) (val ρ rand))]))