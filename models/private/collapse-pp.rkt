#lang racket/base

(require racket/class
         racket/pretty
         racket/lazy-require)

(lazy-require
 ["gui-utils.rkt"
  (get-string-snip%-class
   get-racket:sexp-snip%-class
   get-racket:text%-class
   open-output-text-editor)])

(provide sexp-pp
         sexp-pp-write-special?
         sexp-pp-collapse?/size)

(require racket/match racket/string)

(define (prefix-match? prefix)
  (define prefix-str (format "~a«" prefix))
  (λ (v)
    (and (symbol? v)
         (string-prefix? (symbol->string v) prefix-str))))

(define sexp-pp-write-special? (make-parameter #f))
(define sexp-pp-collapse?/size (make-parameter (λ (v display-mode?) #f)))
(define (sexp-pp v
                 #:print-columns [print-columns #f]
                 #:minimum-columns [minimum-columns 20]
                 . args)
  (unless (void? v)
    (define old-size-hook (pretty-print-size-hook))
    (define old-print-hook (pretty-print-print-hook))
    (parameterize ([pretty-print-columns (or print-columns (pretty-print-columns))]
                   [pretty-print-size-hook
                    (λ (v display-mode? out-port)
                      (cond
                        [(port-writes-special? out-port)
                         (or ((sexp-pp-collapse?/size) v display-mode?)
                             (old-size-hook v display-mode? out-port))]
                        [else (old-size-hook v display-mode? out-port)]))]
                   [pretty-print-print-hook
                    (λ (v display-mode? out-port)
                      (cond
                        [((sexp-pp-collapse?/size) v display-mode?)
                         (define-values (line col pos)
                           (port-next-location out-port))
                         (define remaining-width
                           (max minimum-columns
                                (- (pretty-print-columns) col)))
                         (define text
                           (new (get-racket:text%-class)))
                         (define latest-size-hook (pretty-print-size-hook))
                         (parameterize ([current-output-port (open-output-text-editor text)]
                                        [sexp-pp-write-special? #t]
                                        [pretty-print-size-hook
                                         (λ (new-v display-mode? out-port)
                                           (and (not (equal? v new-v))
                                                (latest-size-hook new-v
                                                                  display-mode?
                                                                  out-port)))])
                           (port-count-lines! (current-output-port))
                           (write-string (build-string col (λ (index) #\space)))
                           (pretty-write v #:newline? #f))
                         (send text split-snip col)
                         (define snips
                           (let loop ([snip (send text find-snip col 'after)])
                             (if snip
                                 (cons (send snip copy) (loop (send snip next)))
                                 '())))
                         (define s
                           (new (get-racket:sexp-snip%-class)
                                [left-bracket #\(]
                                [right-bracket #\)]
                                [saved-snips snips]))
                         (cond
                           [(sexp-pp-write-special?)
                            (write-special s out-port)]
                           [else
                            (old-print-hook s display-mode? out-port)])]
                        [else
                         (old-print-hook v display-mode? out-port)]))])
      (apply pretty-print v args))))
