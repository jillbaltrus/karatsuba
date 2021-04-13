; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);
(make-event
 (er-progn
  (set-deferred-ttag-notes t state)
  (value '(value-triple :invisible))))

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/base-theory" :dir :system :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/custom" :dir :system :ttags :all)

;; guard-checking-on is in *protected-system-state-globals* so any
;; changes are reverted back to what they were if you try setting this
;; with make-event. So, in order to avoid the use of progn! and trust
;; tags (which would not have been a big deal) in custom.lisp, I
;; decided to add this here.
;; 
;; How to check (f-get-global 'guard-checking-on state)
;; (acl2::set-guard-checking :nowarn)
(acl2::set-guard-checking :all)

;Settings common to all ACL2s modes
(acl2s-common-settings)
;(acl2::xdoc acl2s::defunc) ;; 3 seconds is too much time to spare -- commenting out [2015-02-01 Sun]

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/acl2s-sigs" :dir :system :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))

(acl2::xdoc acl2s::defunc) ; almost 3 seconds

; Non-events:
;(set-guard-checking :none)

(set-inhibit-warnings! "Invariant-risk" "theory")

(in-package "ACL2")
(redef+)
(defun print-ttag-note (val active-book-name include-bookp deferred-p state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp deferred-p))
  state)

(defun print-deferred-ttag-notes-summary (state)
  (declare (xargs :stobjs state))
  state)

(defun notify-on-defttag (val active-book-name include-bookp state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp))
  state)
(redef-)

(acl2::in-package "ACL2S")

; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s
(defdata nat-digit (oneof 0 1 2 3 4 5 6 7 8 9))
(defdata back-nat (listof nat-digit))

#|
(defdata pos-digit (oneof 1 2 3 4 5 6 7 8 9))
(defdata pos-nat (oneof (list pos-digit) (cons pos-digit pos-nat) (cons 0 pos-nat)))
(defdata back-nat (oneof (list 0) pos-nat))
|#

(set-defunc-termination-strictp nil)
(set-defunc-function-contract-strictp nil)
(set-defunc-body-contracts-strictp nil)

; converts backnat to regular old decimal representation
(definec backnat-to-nat (n1 :back-nat) :nat
  (cond
   ((endp n1) 0)
   (t (+ (car n1) (* 10 (backnat-to-nat (cdr n1)))))))

; classic len2 function, returns length of list
(definec len2 (x :tl) :nat
  (if (endp x)
      0
    (+ 1 (len2 (rest x)))))

; subtracts a - b (numbers represented as backnats)
(definec backnat-sub (a :back-nat b :back-nat acc :nat) :back-nat
  :ic (or (== 1 acc) (== 0 acc))
  :ic (>= (backnat-to-nat a) (+ acc (backnat-to-nat b)))
  ;:ic (>= (len2 a) (len2 b))
  (cond
   ((endp a) '())
   ((and (endp b) (not (endp a))) (backnat-sub a '(0) acc))
   ((and (== 1 acc) (> (car a) (car b))) (cons (- (- (car a) (car b)) 1) (backnat-sub (cdr a) (cdr b) 0)))
   ((and (== 1 acc) (<= (car a) (car b))) (cons (- (+ 10 (- (car a) (car b))) 1) (backnat-sub (cdr a) (cdr b) 1)))
   ((and (== 0 acc) (>= (car a) (car b))) (cons (- (car a) (car b)) (backnat-sub (cdr a) (cdr b) 0)))
   (t (cons (+ 10 (- (car a) (car b))) (backnat-sub (cdr a) (cdr b) 1))))) ; this would be when (and (== 0 acc) (< (car a) (car b)))

#|
(defthm max-nat
  (implies (and (natp n1) (natp n2)) (natp (max n1 n2))))

(defthm len-back-nat
  (implies (back-natp n1) (natp (length n1))))
|#

; given 2 lists, returns the size of the longer list
(definec size (n1 :tl n2 :tl) :nat
  (max (len2 n1) (len2 n2)))

#|
(defdata nil-or-backnat (oneof nil back-nat))
|#

; given 2 backnats, computes the midpoint index of the longer backnat
; (used in karatsuba algo for breaking numbers in half)
(definec my-n (n1 :back-nat n2 :back-nat) :nat
  (ceiling (/ (size n1 n2) 2) 1))

; sums 2 backnats
(definec add-back-nat-help (n1 :back-nat n2 :back-nat acc :nat) :back-nat
  :ic (or (== acc 0) (== acc 1))
  (cond
   ((endp n1) n2)
   ((endp n2) n1)
   (t (if (< (+ (car n1) (car n2) acc) 10)
        (cons (+ (car n1) (car n2) acc) (add-back-nat-help (cdr n1) (cdr n2) 0))
        (cons (- (+ (car n1) (car n2) acc) 10) (add-back-nat-help (cdr n1) (cdr n2) 1))))))

; should we have skip proofs?
; needed for getting acls to accept our backnat addition
(skip-proofs
(defthm add-back-nat-contract 
  (implies (and (back-natp n1) (back-natp n2))
           (back-natp (add-back-nat-help n1 n2 0)))))

; see above (non-accumulator version, calls accumulator version)
(definec add-back-nat (n1 :back-nat n2 :back-nat) :back-nat
  (add-back-nat-help n1 n2 0))

; multiplies 2 backnats. We will only ever need to call this function
; on backnats that are empty of have length 1. 
(definec mult-back-nat (n1 :back-nat n2 :back-nat) :back-nat
  :ic (and (<= (len2 n1) 1) (<= (len2 n2) 1))
  (cond
   ((or (endp n1) (endp n2)) '(0))
   ((== (floor (* (car n1) (car n2)) 10) 0) (cons (mod (* (car n1) (car n2)) 10) nil))
   (t (cons (mod (* (car n1) (car n2)) 10) (cons (floor (* (car n1) (car n2)) 10) nil)))))

#|
(definec nat-to-backnat (n :nat) :back-nat
  

(definec first-half (backnat :back-nat start :nat) :back-nat
  :ic (< start (len2 backnat))
  (if (== start 0)
    backnat
    (first-half (cdr backnat) (- start 1))))
|#

; used in algo for breaking numbers in half
(definec sub-list (backnat :back-nat start :nat end :int) :back-nat
  :ic (or (== -1 end) (natp end))
  (cond 
   ((or (> start end) (endp backnat)) (list 0))
   ((== end 0) (cons (car backnat) nil))
   ((== start 0) (cons (car backnat) (sub-list (cdr backnat) 0 (- end 1))))
   (t (sub-list (cdr backnat) (- start 1) (- end 1)))))

; multiplies backnat by 10 to the given power, used in karatsuba algo
(definec backnat-expt (backnat :back-nat nat :nat) :back-nat
  (if (== nat 0)
    backnat
    (cons 0 (backnat-expt backnat (- nat 1)))))#|ACL2s-ToDo-Line|#


; the algorithm itself
(definec karatsuba (n1 :back-nat n2 :back-nat) :back-nat
  (cond
   ((and (<= (len2 n1) 1) (<= (len2 n2) 1)) (mult-back-nat n1 n2))
   (t (add-back-nat
       (add-back-nat
        (backnat-expt (karatsuba (sub-list n1 (my-n n1 n2) (- (len2 n1) 1))
                                 (sub-list n2 (my-n n1 n2) (- (len2 n2) 1)))
                      (* 2 (my-n n1 n2)))
        (backnat-expt (backnat-sub
                       (backnat-sub
                        (karatsuba (add-back-nat (sub-list n1 (my-n n1 n2) (- (len2 n1) 1))
                                                 (sub-list n1 0 (- (my-n n1 n2) 1)))
                                   (add-back-nat (sub-list n2 (my-n n1 n2) (- (len2 n2) 1))
                                                 (sub-list n2 0 (- (my-n n1 n2) 1))))
                        (karatsuba (sub-list n1 (my-n n1 n2) (- (len2 n1) 1))
                                   (sub-list n2 (my-n n1 n2) (- (len2 n2) 1)))
                        0)
                       (karatsuba (sub-list n1 0 (- (my-n n1 n2) 1))
                                  (sub-list n2 0 (- (my-n n1 n2) 1)))
                       0)
                      (my-n n1 n2)))
       (karatsuba (sub-list n1 0 (- (my-n n1 n2) 1))
                  (sub-list n2 0 (- (my-n n1 n2) 1)))))))

