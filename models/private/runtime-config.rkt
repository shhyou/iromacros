#lang racket/base

(require racket/match
         racket/string
         "collapse-pp.rkt")

(provide PRETTY-PRINT-WIDTH)

(port-count-lines! (current-output-port))

(define PRETTY-PRINT-WIDTH 60)

(define (prefix-match? prefix)
  (define prefix-str (format "~a«" prefix))
  (λ (v)
    (and (symbol? v)
         (string-prefix? (symbol->string v) prefix-str))))

(define (collapse?/size v display-mode?)
  (match v
    [`(env . ,_)
     1]
    [`(,(or (? (prefix-match? 'lambda))
            (? (prefix-match? 'let))
            (? (prefix-match? 'let-syntax))
            (? (prefix-match? 'if)))
       ↦ ,_)
     #:when (sexp-pp-write-special?)
     1]
    [_ #f]))

(sexp-pp-collapse?/size collapse?/size)

(current-print
 (λ args
   (apply sexp-pp args
          #:print-columns PRETTY-PRINT-WIDTH)))
