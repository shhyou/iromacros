#lang racket/base

#|
A small-step semantics Redex model of a simple hygienic macro system.
The model is a slight modification of the macro model presented by
W. Clinger and J. Rees in the paper Macros That Work.

This Redex model is built on top of the binding forms, designed by Stansifer,
to emphasis the binding aspect of the environments and hide the mechanical
refreshening of variables behind the scenes.

Additionally, the metafunctions transcribe, match and rewrite* are called
T, matches and substitute* in this model. Their signature also differ from
the paper in that the environments are paired with the syntaxes to signify
that the syntaxes must be interpreted under some environment.

Side note. To expand the collapsed S-expressions ( '(...)' ), copy the
elided forms to the definition window or the prompt area of the REPL and
select "Expand S-expression" from the context menu.

    William Clinger and Jonathan Rees. Macros That Work. In POPL'91.
    https://doi.org/10.1145/99583.99607

    Paul Stansifer and Mitchell Wand. Romeo: A System for More Flexible
    Binding-Safe Programming. In ICFP'14.
    https://doi.org/10.1145/2628136.2628162

    Michael D. Adams. Towards the Essence of Hygiene. In POPL'15.
    https://dl.acm.org/doi/10.1145/2676726.2677013
    https://michaeldadams.org/papers/hygiene/

    Klein et al., Run Your Research: On the Effectiveness of Lightweight
    Mechanization. In POPL'12.
    https://doi.org/10.1145/2103656.2103691
    https://docs.racket-lang.org/redex/index.html

|#

(require racket/list
         racket/pretty
         racket/lazy-require
         redex/reduction-semantics
         "private/runtime-config.rkt"
         "private/collapse-pp.rkt")

(lazy-require
 [redex/gui (stepper traces)])

(define (traces-R t)
  (traces R t #:pp (λ (term out-port print-columns text)
                     (parameterize ([sexp-pp-write-special? #t])
                       (sexp-pp term out-port
                                #:print-columns print-columns)))))

#|
Examples: ex0, ex0.1, ex1, ex2, ex3, ex3.1, ex3.2, ex3.3, ex4 and ex5

   (traces-R ex0)
   (traces-R ex0.1)
   (traces-R ex3)
   (traces-R ex3.3)
   (apply-reduction-relation* R ex4)
   (apply-reduction-relation* R ex5)
   (term (ι ,example-bind-rho))
|#
(define-language L
  [pattern ::= x (pattern ...)]
  [template ::= integer variable (template ...)]
  [M ::= (syntax-rules (x ...) [(x pattern ...) template] ...)]

  [ρ ρ′ ::= (env [x_!_ ↦ d] ...)]
  [d ::= x λ let* let-syntax* if* (transformer ρ M)]
  [σ ::= (subst [x ↦ e] ...)]

  [x y x′ ::= variable-not-otherwise-mentioned]
  [e e′ ::= integer variable (e ...) (ρ ⊢ e-)]
  [e- ::= integer variable (e- ...)]

  [core ::=
        integer
        x
        (λ (x) core)
        (let* ([x core]) core)
        (if* core core core)
        (core core ...)]

  [E ::=
     hole
     (λ (x) E)
     (let* ([x E]) e)
     (let* ([x core]) E)
     (if* E e e)
     (if* core E e)
     (if* core core E)
     (core ... E e ...)]

  #:binding-forms
  (env [x ↦ any] ...) #:exports (shadow x ...)
  (transformer ρ M #:refers-to ρ)
  (ρ ⊢ e #:refers-to ρ))

(define-term ρ0
  (env [lambda ↦ λ] [let ↦ let*] [let-syntax ↦ let-syntax*] [if ↦ if*]))

(define example-bind-rho
  (term
   ((env [var ↦ λ]) ⊢ (var (x) (λ (y) (y x))))))

(define ex0
  (term (ρ0 ⊢ (let-syntax ([or (syntax-rules ()
                                 [(or e1 e2)
                                  (let ([temp e1])
                                    (if temp temp e2))])])
                (let ([temp (read-temperature)])
                  (if (or (< temp 65)
                          (< 105 temp))
                      1
                      0))))))

(define ex0.1
  (term (ρ0 ⊢ (let ([temp #xDEADBEEF])
                (let-syntax ([or (syntax-rules ()
                                   [(or e1 e2)
                                    (let ([temp e1])
                                      (if temp temp e2))])])
                  (let ([temp (read-temperature)])
                    (if (or (< temp 65)
                            (< 105 temp))
                        1
                        0)))))))

(define ex1
  (term (ρ0 ⊢ (lambda (x)
                (lambda (y)
                  x)))))

(define ex2
  (term (ρ0 ⊢ (lambda (x)
                (let ([x x])
                  (x x))))))

(define ex3
  (term (ρ0 ⊢ (lambda (x)
                (let-syntax ([m (syntax-rules ()
                                  [(m) x])])
                  (let ([x 1])
                    (m)))))))
(define ex3.1
  (term (ρ0 ⊢ (let ([x 0])
                (let-syntax ([mplus (syntax-rules ()
                                      [(mplus y)
                                       (let ([z 1])
                                         (list x y z))])])
                  (let ([w 2])

                    (mplus w)))))))

(define ex3.2
  (term (ρ0 ⊢ (let ([x 0])
                (let-syntax
                    ([mplusplus
                      (syntax-rules ()
                        [(mplusplus mplus z e)
                         (let-syntax ([mplus (syntax-rules ()
                                               [(mplus y)
                                                (let ([z 1])
                                                  (list x y z))])])
                           e)])])
                  (mplusplus mplus
                             x
                             (let ([x 2])
                               (mplus x))))))))

(define ex3.3
  (term (ρ0 ⊢ (let ([x 3])
                (let-syntax ([let-inc (syntax-rules ()
                                        [(let-inc z e)
                                         (let ([z (+ z 1)]) e)])])
                  (let-syntax ([m (syntax-rules ()
                                    [(m y) (let-inc x (* x y))])])
                    (m x)))))))

(define ex4
  (term (ρ0 ⊢ (let ([x 0])
                (let-syntax ([m1 (syntax-rules ()
                                   [(m1 m2 e)
                                    (let-syntax ([m2 (syntax-rules ()
                                                       [(m2) x])])
                                      e)])])
                  (let ([x 1])
                    (m1 m2
                        (let ([x 2])
                          (m2)))))))))

(define ex5
  (term (ρ0 ⊢ (let-syntax ([check-bv=? (syntax-rules ()
                                         [(check-bv=? x y)
                                          (list
                                           (let ([x 0]) (let ([y 1]) (cons x y)))
                                           (let ([y 1]) (let ([x 0]) (cons x y))))])])
                (list
                 (check-bv=? x x)
                 (let-syntax ([check-macro-x (syntax-rules ()
                                               [(check-macro-x a)
                                                (check-bv=? x a)])])
                   (check-macro-x x)))))))

(define R
  (reduction-relation
   L
   #:domain e
   (--> (in-hole E (ρ ⊢ integer))
        (in-hole E integer)
        "#%datum")

   (--> (in-hole E (ρ ⊢ x))
        (in-hole E y)

        (where y ,(or (term (env-ref-id/#f ρ x))
                      (term x)))
        "var")

   (--> (in-hole E (ρ ⊢ (x_lam (x) e)))
        (in-hole E (λ (x) (ρ′ ⊢ e)))

        (where λ (env-ref/#f ρ x_lam))
        (where ρ′ (env-set ρ x x))
        "lambda")

   (--> (in-hole E (ρ ⊢ (e_1 e_2 ...)))
        (in-hole E ((ρ ⊢ e_1) (ρ ⊢ e_2) ...))

        (judgment-holds (not-keyword-or-macro ρ e_1))
        (where #f ,(redex-match? L (ρ ⊢ e) (term (e_1 e_2 ...))))
        "#%app")

   (--> (in-hole E (ρ ⊢ (x_letstx ([x M]) e)))
        (in-hole E (ρ′ ⊢ e))

        (where let-syntax* (env-ref/#f ρ x_letstx))
        (where/error (x_fv ...) (list-difference (identifiers-in-template M) (dom ρ)))
        (where/error ρ_fv (env [x_fv ↦ x_fv] ...))
        (where/error ρ′ (env-set ρ x (transformer (← ρ ρ_fv) M)))
        "let-syntax")

   (--> (in-hole E (ρ ⊢ (x_m e ...)))
        (in-hole E (ρ′ ⊢ e′))

        (where (transformer ρ_m M) (env-ref/#f ρ x_m))
        (where (ρ′ ⊢ e′) (T (transformer ρ_m M) (ρ ⊢ (x_m e ...))))
        "transform")

   (--> (in-hole E (ρ ⊢ (x_let ([x e_1]) e_2)))
        (in-hole E (let* ([x (ρ ⊢ e_1)]) (ρ′ ⊢ e_2)))

        (where let* (env-ref/#f ρ x_let))
        (where/error ρ′ (env-set ρ x x))
        "let")

   (--> (in-hole E (ρ ⊢ (x_if e_1 e_2 e_3)))
        (in-hole E (if* (ρ ⊢ e_1) (ρ ⊢ e_2) (ρ ⊢ e_3)))

        (where if* (env-ref/#f ρ x_if))
        "if")))

(define-judgment-form L
  #:contract (matches [ρ (x ...)] [ρ e] pattern σ)
  #:mode     (matches I           I     I       O)

  [(where x_def (env-ref-id/#f ρ_m x_lit))
   (where x_def (env-ref-id/#f ρ_use y))
   ---------------------------------------------------------
   (matches [ρ_m (_ ... x_lit _ ...)] [ρ_use y] x_lit
            (subst))]

  [(not-member x_pat (x_lit ...))
   ---------------------------------------------------------
   (matches [ρ_m (x_lit ...)] [ρ_use e] x_pat
            (subst [x_pat ↦ e]))]

  [(matches [ρ_m (x_lit ...)] [ρ_use e_1] pattern_1
            (subst [x_pat ↦ e] ...))
   ...
   ---------------------------------------------------------
   (matches [ρ_m (x_lit ...)] [ρ_use (e_1 ..._len)] (pattern_1 ..._len)
            (subst [x_pat ↦ e] ... ...))])

(define-metafunction L
  T : (transformer ρ M) (ρ ⊢ (x_m e ...)) -> (ρ ⊢ e)
  [(T (transformer ρ_m (syntax-rules (x_lit ...) [(x_m pattern ...) template] _ ...))
      (ρ ⊢ (_ e ...)))
   ((← ρ ρ_m) ⊢ (substitute* template σ))
   (judgment-holds (matches [ρ_m (x_lit ...)] [ρ (e ...)] (pattern ...)
                            σ))
   (where (x_fv ...) (list-difference (identifiers template) (dom σ)))
   #;
   (where _ ,(begin
               (printf "expanding ~s\n" (term
                                         (syntax-rules (x_lit ...)
                                           [(x_m pattern ...) template] _ (... ...))))
               (printf "template FVs: ~a\n" (term (x_fv ...)))
               (printf "output:\n    ")
               (pretty-print (term (substitute* template σ)))
               (printf "macro env:\n    ")
               (pretty-print (term ρ_m))
               (printf "user env:\n    ")
               (pretty-print (term ρ))))]
  [(T (transformer ρ_m (syntax-rules (x_lit ...) _ [(x pattern ...) template] ...))
      (ρ ⊢ (x_m e ...)))
   (T (transformer ρ_m (syntax-rules (x_lit ...) [(x pattern ...) template] ...))
      (ρ ⊢ (x_m e ...)))])



(define-judgment-form L
  #:contract (not-keyword-or-macro ρ e)
  #:mode     (not-keyword-or-macro I I)

  [------------------------------
   (not-keyword-or-macro ρ (e ...))]

  [(where #f (env-ref/#f ρ x))
   ------------------------------
   (not-keyword-or-macro ρ x)]

  [(where d (env-ref/#f ρ x))
   (where #f ,(member (term d) '(λ let* let-syntax* if*)))
   (where #f ,(redex-match? L (transformer ρ M) (term d)))
   ------------------------------
   (not-keyword-or-macro ρ x)])



(define-metafunction L
  env-set : ρ x d -> ρ′
  [(env-set
    (env [x_1 ↦ d_1] ... [x ↦ _] [x_2 ↦ d_2] ...)
    x d)
   (env [x_1 ↦ d_1] ... [x ↦ d] [x_2 ↦ d_2] ...)]
  [(env-set (env [x_1 ↦ d_1] ...) x d)
   (env [x ↦ d] [x_1 ↦ d_1] ...)])

(define-metafunction L
  env-set* : ρ {[x d] ...} -> ρ′
  [(env-set* ρ {}) ρ]
  [(env-set* (env [x_1 ↦ d_1] ... [x ↦ _] [x_2 ↦ d_2] ...)
             {[x d] [x_r d_r] ...})
   (env-set* (env [x_1 ↦ d_1] ... [x ↦ d] [x_2 ↦ d_2] ...)
             {[x_r d_r] ...})]
  [(env-set* (env [x_1 ↦ d_1] ...)
             {[x d] [x_r d_r] ...})
   (env-set* (env [x ↦ d] [x_1 ↦ d_1] ...)
             {[x_r d_r] ...})])

(define-metafunction L
  ← : ρ ρ -> ρ
  [(← (env [x_1 ↦ d_1] ...) (env [x_2 ↦ d_2] ...))
   (env [x_1 ↦ d_1] ... [x_2 ↦ d_2] ...)])

(define-metafunction L
  env-ref/#f : ρ x -> d or #f
  [(env-ref/#f (env _ ... [x ↦ d] _ ...) x) d]
  [(env-ref/#f ρ x) #f])

(define-metafunction L
  env-ref-id/#f : ρ x -> x or #f
  [(env-ref-id/#f (env _ ... [x ↦ y] _ ...) x) y]
  [(env-ref-id/#f (env [x_1 ↦ d_1] ...) x)
   #f
   (where/error #f ,(member (term x) (term (x_1 ...))))])

(define-metafunction L
  ι : e -> e
  [(ι integer) integer]
  [(ι variable) variable]
  [(ι (e_1 ...))
   ((ι e_1) ...)]
  [(ι (ρ ⊢ e)) (ρ ⊢ (ι e))])

(define-judgment-form L
  #:contract (not-member variable (x ...))
  #:mode     (not-member I I)

  [(where #f ,(member (term variable) (term (x_lst ...))))
   ---------------------------------------------------------
   (not-member variable (x_lst ...))])

(define-metafunction L
  substitute* : template σ -> e
  [(substitute* (ρ ⊢ e) σ)
   (ρ ⊢ (substitute* e σ))]
  [(substitute* integer σ)
   integer]
  [(substitute* x (subst _ ... [x ↦ e] _ ...))
   e]
  [(substitute* variable (subst [x_1 ↦ e_1] ...))
   variable
   (judgment-holds (not-member variable (x_1 ...)))]
  [(substitute* (template_1 ...) σ)
   ((substitute* template_1 σ) ...)])

(define-metafunction L
  list-difference : (x ...) (x ...) -> (x ...)
  [(list-difference (x_1 ...) (x_2 ...))
   ,(remove* (term (x_2 ...)) (term (x_1 ...)))])

(define-metafunction L
  identifiers-in-template : M -> (x ...)
  [(identifiers-in-template (syntax-rules (x_lit ...) [pattern template] ...))
   (x_fv ...)
   (where ((x_template-fv ...) ...) ((list-difference (identifiers template)
                                                      (identifiers pattern))
                                     ...))
   (where (x_fv ...) ,(remove-duplicates (term (x_template-fv ... ...))))])

(define-metafunction L
  identifiers : template -> (x ...)
  [(identifiers template) ,(remove-duplicates
                            (filter (redex-match? L x)
                                    (flatten (term template))))])

(define-metafunction L
  dom : any -> (x ...)
  [(dom (any_tag [x ↦ any_val] ...)) (x ...)])
