#lang racket/base


(require racket/snip
         racket/gui/base
         framework)

(provide get-string-snip%-class
         get-racket:sexp-snip%-class
         get-racket:text%-class
         open-output-text-editor)

(define (get-string-snip%-class)
  string-snip%)

(define (get-racket:sexp-snip%-class)
  racket:sexp-snip%)

(define (get-racket:text%-class)
  racket:text%)
