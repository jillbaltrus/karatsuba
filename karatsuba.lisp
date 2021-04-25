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
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Karatsuba;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(set-gag-mode nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Data: Back-Nat;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Below, we define the base for our back-nat data representations.
;; We choose to use base 10.
(defconst *base* 10)
;; Below, we define the necessary data types for representing a back-nat,
;; a backward list of digits to represent a natural number
(defdata pos-digit (range integer (0 < _ < *base*)))
(defdata digit (oneof 0 pos-digit))
(defdata singleton-pos-nat (list pos-digit))
(defdata back-pos-nat (oneof (cons digit back-pos-nat) singleton-pos-nat))
(defdata back-nat (oneof nil back-pos-nat))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Decimal/Back-Nat Conversion;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lemma. A back-nat is a true list
(defthm back-nats-are-tls
  (implies (back-natp x) (tlp x)))

;; converts back-pos-nat to regular old decimal representation
(definec back-pos-nat-to-pos (n1 :back-pos-nat) :pos
  (declare (xargs :measure-debug t :guard-debug t))
  (cond
   ((singleton-pos-natp n1) (car n1))
   (t (+ (car n1) (* (back-pos-nat-to-pos (cdr n1)) *base*)))))

;; converts back-nat to regular old decimal representation
(definec back-nat-to-nat (n1 :back-nat) :nat
  (declare (xargs :measure-debug t :guard-debug t))
  (cond
   ((lendp n1) 0)
   (t (back-pos-nat-to-pos n1))))

;; converts decimal representation to back-nat
(definec nat-to-back-nat (n :nat) :back-nat
  (cond 
   ((zp n) '())
   (t (cons (mod n *base*) (nat-to-back-nat (floor n *base*))))))

;; Theorem. Round-trip conversion between Back-Nat and Nat
(defthm round-trip
  (implies (natp n)
           (equal (back-nat-to-nat (nat-to-back-nat n)) n)))

;; Theorem. Reverse-round-trip conversion between Back-Nat and Nat
(defthm reverse-round-trip
  (implies (back-natp n)
           (equal (nat-to-back-nat (back-nat-to-nat n)) n)))

;; Theorem. Two equal natural numbers implies the back-nats represented by
;; these natural numbers are equal
(defthm one-to-one-pt2
  (implies (and (natp n1)
                (natp n2)
                (equal n1 n2))
           (equal (nat-to-back-nat n1) (nat-to-back-nat n2))))

;; Theorem. Two equal back-nats implies the natural numbers represented by
;; these back-nats are equal
(defthm one-to-one-pt4
  (implies (and (back-natp n1)
                (back-natp n2)
                (equal n1 n2))
           (equal (back-nat-to-nat n1) (back-nat-to-nat n2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Helper-Functions;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; classic len2 function, returns length of list
(definec len2 (x :tl) :nat
  (if (endp x)
      0
    (+ 1 (len2 (rest x)))))

;; given 2 lists, returns the size of the longer list
(definec size (n1 :tl n2 :tl) :nat
  (max (len2 n1) (len2 n2)))

;; given 2 backnats, computes the midpoint index of the longer backnat
;; (used in karatsuba algo for breaking numbers in half)
(definec my-n (n1 :back-nat n2 :back-nat) :nat
  (ceiling (/ (size n1 n2) 2) 1))

;; measure function of backnat-expt
(definec backnat-expt-measure (backnat :back-nat nat :nat) :nat
  (declare (ignorable backnat))
  nat)

;; Lemma. Not a back-nat implies not a back-pos-nat
(defthm not-back-nat-implies-not-back-pos-nat
  (implies (not (back-natp backnat))
           (not (back-pos-natp backnat))))

;; Lemma. Cons 0 on to a back-nat will return a back-nat
(defthm cons-0-on-backposnat-is-a-backnat
  (implies (and (back-pos-natp backnat)
                (natp nat)
                (< 0 nat))
           (back-natp (cons 0 backnat))))

;; Lemma. A positive nat sub1 is still a nat
(defthm not-zero-nat-sub1-is-still-nat
  (implies (and (natp nat)
                (not (== nat 0)))
           (natp (- nat 1))))

;; multiplies backnat by 10 to the given power, used in karatsuba algo
(PROGN
 (ENCAPSULATE
   NIL
   (ENCAPSULATE
        ((ACL2S-BACK-NAT-UNDEFINED (X Y)
                                   T
                                   :GUARD (AND (SYMBOLP X) (TRUE-LISTP Y))))
        (LOCAL (DEFUN ACL2S-BACK-NAT-UNDEFINED (X Y)
                      (DECLARE (IGNORABLE X Y))
                      'NIL))
        (DEFTHM ACL2S-BACK-NAT-UNDEFINED-BACK-NATP
                (BACK-NATP (ACL2S-BACK-NAT-UNDEFINED X Y))
                :RULE-CLASSES ((:TYPE-PRESCRIPTION) (:REWRITE))))
   (DEFUN ACL2S-BACK-NAT-UNDEFINED-ATTACHED (X Y)
          (DECLARE (XARGS :GUARD (AND (SYMBOLP X) (TRUE-LISTP Y))))
          (PROG2$ (CGEN::CW? (SHOW-CONTRACT-VIOLATIONS?)
                             "~|**Input contract  violation in ~x0**: ~x1 ~%"
                             'ACL2S-BACK-NAT-UNDEFINED-ATTACHED
                             (CONS X Y))
                  'NIL))
   (DEFATTACH ACL2S-BACK-NAT-UNDEFINED
              ACL2S-BACK-NAT-UNDEFINED-ATTACHED))
 (ENCAPSULATE
  NIL
  (WITH-OUTPUT
    :OFF :ALL :ON (ERROR)
    (DEFUN
         BACKNAT-EXPT (BACKNAT NAT)
         (DECLARE (XARGS :GUARD (AND (BACK-NATP BACKNAT) (NATP NAT))
                         :VERIFY-GUARDS NIL
                         :NORMALIZE NIL
                         :HINTS (("goal" :DO-NOT-INDUCT T))
                         :MEASURE (IF (AND (BACK-NATP BACKNAT) (NATP NAT))
                                      (BACKNAT-EXPT-MEASURE BACKNAT NAT)
                                      0)
                         :TIME-LIMIT 75/2))
         (MBE :LOGIC (IF (AND (BACK-NATP BACKNAT) (NATP NAT))
                         (COND ((ENDP BACKNAT) NIL)
                               ((ZEROP NAT) BACKNAT)
                               (T (CONS 0 (BACKNAT-EXPT BACKNAT (- NAT 1)))))
                         (ACL2S-BACK-NAT-UNDEFINED 'BACKNAT-EXPT
                                                   (LIST BACKNAT NAT)))
              :EXEC (COND ((ENDP BACKNAT) NIL)
                          ((ZEROP NAT) BACKNAT)
                          (T (CONS 0
                                   (BACKNAT-EXPT BACKNAT (- NAT 1)))))))))
 (DEFTHM BACKNAT-EXPT-CONTRACT
         (IMPLIES (AND (FORCE (BACK-NATP BACKNAT))
                       (FORCE (NATP NAT)))
                  (BACK-NATP (BACKNAT-EXPT BACKNAT NAT)))
         :HINTS (("Goal" :USE ((:INSTANCE NOT-ZERO-NAT-SUB1-IS-STILL-NAT)))
                 ("Goal'5'" :INDUCT T)))
 (ENCAPSULATE
    NIL
    (WITH-OUTPUT
         :OFF :ALL :ON (ERROR)
         (VERIFY-GUARDS BACKNAT-EXPT
                        :GUARD-DEBUG T
                        :HINTS (("Goal" :DO-NOT-INDUCT T
                                        :DO-NOT '(GENERALIZE FERTILIZE)))))))

#|
;; multiplies backnat by 10 to the given power, used in karatsuba algo
(definec backnat-expt (backnat :back-nat nat :nat) :back-nat
  :function-contract-hints (("Goal" :use ((:instance not-zero-nat-sub1-is-still-nat)))
                            ("Goal'5'" :induct t))
  (declare (xargs :measure (if (and (back-natp backnat)
                                    (natp nat))
                             (backnat-expt-measure backnat nat)
                             0)
                  :hints (("goal" :do-not-induct t))))
  (cond
   ((endp backnat) nil)
   ((zerop nat) backnat)
   (t (cons 0 (backnat-expt backnat (- nat 1))))))
|#

;; helper function of sub-list, used in algo for breaking numbers in half
(definec sub-list-helper (backnat :back-nat start :nat end :nat) :back-nat
  :ic (and (<= start end) 
           (not (== 0 start)) 
           (not (== 0 end))
           (<= end (len2 backnat)))
  (cond
   ((and (== start 1) (== end 1)) (if (== 0 (car backnat))
                                    nil
                                    (list (car backnat))))
   ((== start 1) 
    (let ((res (sub-list-helper (cdr backnat) 1 (- end 1))))
      (cond
       ((and (== (car backnat) 0) (endp res)) res)
       (t (cons (car backnat) res)))))
   (t (sub-list-helper (cdr backnat) (- start 1) (- end 1)))))

;; used in algo for breaking numbers in half
(definec sub-list (backnat :back-nat start :nat end :nat) :back-nat
  :ic (not (== 0 start))
  (cond
   ((== 0 end) nil)
   ((or (> start end) (> start (len2 backnat))) nil)
   ((> end (len2 backnat)) (sub-list-helper backnat start (len2 backnat)))
   (t (sub-list-helper backnat start end))))

;;Addition;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; add one to the given back-pos-nat
(definec back-pos-nat-add1 (a :back-pos-nat) :back-pos-nat
  (cond
   ((lendp (cdr a)) ;; base case
    (cond
     ((pos-digitp (+ 1 (car a))) (cons (+ 1 (car a)) (cdr a))) ;; when we hit carry
     (t (cons (- (+ 1 (car a)) *base*) (cons 1 (cdr a))))))
   (t
    (cond 
     ((pos-digitp (+ 1 (car a))) (cons (+ 1 (car a)) (cdr a))) ;; when we hit carry
     (t (cons (- (+ 1 (car a)) *base*) (back-pos-nat-add1 (cdr a))))))))

;; add one to the given back-nat
(definec back-nat-add1 (a :back-nat) :back-pos-nat
  (cond
    ((endp a) (list 1))
    (t (back-pos-nat-add1 a))))

;; check if the first given back-pos-nat is samller than the second one
(definec back-pos-nat-<-back-pos-nat (a :back-pos-nat b :back-pos-nat) :bool
  (or (and (lendp (cdr a))
       (back-pos-natp (cdr b)))
      (and (lendp (cdr a))
       (lendp (cdr b))
       (< (car a) (car b)))
      (and (back-pos-natp (cdr a))
       (back-pos-natp (cdr b))
       (or (back-pos-nat-<-back-pos-nat (cdr a) (cdr b))
           (and (< (car a) (car b))
            (equal (cdr a) (cdr b)))))))

;; check if the first given back-pos-nat is samller or equal to the second one
(definec back-pos-nat-<=-back-pos-nat (a :back-pos-nat b :back-pos-nat) :bool
  (or (back-pos-nat-<-back-pos-nat a b)
      (equal a b)))

;; check if the first given back-nat is samller than the given back-pos-nat
(definec back-nat-<-back-pos-nat (a :back-nat b :back-pos-nat) :bool
  (or (lendp a) (back-pos-nat-<-back-pos-nat a b)))

;; check if the first given back-nat is samller than the second one
(definec back-nat-< (a :back-nat b :back-nat) :bool
  (and (back-pos-natp b) (back-nat-<-back-pos-nat a b)))

;; check if the first given back-nat is samller or equal to the second one
(definec back-nat-<= (a :back-nat b :back-nat) :bool
  (or (back-nat-< a b) (equal a b)))

;; add two back-nat together to a new back-nat
(PROGN
 (ENCAPSULATE
   NIL
   (ENCAPSULATE
        ((ACL2S-BACK-NAT-UNDEFINED (X Y)
                                   T
                                   :GUARD (AND (SYMBOLP X) (TRUE-LISTP Y))))
        (LOCAL (DEFUN ACL2S-BACK-NAT-UNDEFINED (X Y)
                      (DECLARE (IGNORABLE X Y))
                      'NIL))
        (DEFTHM ACL2S-BACK-NAT-UNDEFINED-BACK-NATP
                (BACK-NATP (ACL2S-BACK-NAT-UNDEFINED X Y))
                :RULE-CLASSES ((:TYPE-PRESCRIPTION) (:REWRITE))))
   (DEFUN ACL2S-BACK-NAT-UNDEFINED-ATTACHED (X Y)
          (DECLARE (XARGS :GUARD (AND (SYMBOLP X) (TRUE-LISTP Y))))
          (PROG2$ (CGEN::CW? (SHOW-CONTRACT-VIOLATIONS?)
                             "~|**Input contract  violation in ~x0**: ~x1 ~%"
                             'ACL2S-BACK-NAT-UNDEFINED-ATTACHED
                             (CONS X Y))
                  'NIL))
   (DEFATTACH ACL2S-BACK-NAT-UNDEFINED
              ACL2S-BACK-NAT-UNDEFINED-ATTACHED))
 (ENCAPSULATE
  NIL
  (WITH-OUTPUT
   :OFF :ALL :ON (ERROR)
   (DEFUN
    ADD-BACK-NAT (N1 N2)
    (DECLARE (XARGS :GUARD (AND (BACK-NATP N1) (BACK-NATP N2))
                    :VERIFY-GUARDS NIL
                    :NORMALIZE NIL
                    :TIME-LIMIT 75/2))
    (MBE :LOGIC (IF (AND (BACK-NATP N1) (BACK-NATP N2))
                    (COND ((ENDP N1) N2)
                          ((ENDP N2) N1)
                          (T (IF (< (+ (CAR N1) (CAR N2)) *BASE*)
                                 (CONS (+ (CAR N1) (CAR N2))
                                       (ADD-BACK-NAT (CDR N1) (CDR N2)))
                                 (CONS (- (+ (CAR N1) (CAR N2)) *BASE*)
                                       (ADD-BACK-NAT (BACK-NAT-ADD1 (CDR N1))
                                                     (CDR N2))))))
                    (ACL2S-BACK-NAT-UNDEFINED 'ADD-BACK-NAT
                                              (LIST N1 N2)))
         :EXEC (COND ((ENDP N1) N2)
                     ((ENDP N2) N1)
                     (T (IF (< (+ (CAR N1) (CAR N2)) *BASE*)
                            (CONS (+ (CAR N1) (CAR N2))
                                  (ADD-BACK-NAT (CDR N1) (CDR N2)))
                            (CONS (- (+ (CAR N1) (CAR N2)) *BASE*)
                                  (ADD-BACK-NAT (BACK-NAT-ADD1 (CDR N1))
                                                (CDR N2))))))))))
 (DEFTHM ADD-BACK-NAT-CONTRACT
         (IMPLIES (AND (FORCE (BACK-NATP N1))
                       (FORCE (BACK-NATP N2)))
                  (BACK-NATP (ADD-BACK-NAT N1 N2))))
 (ENCAPSULATE
    NIL
    (WITH-OUTPUT
         :OFF :ALL :ON (ERROR)
         (VERIFY-GUARDS ADD-BACK-NAT
                        :GUARD-DEBUG T
                        :HINTS (("Goal" :DO-NOT-INDUCT T
                                        :DO-NOT '(GENERALIZE FERTILIZE)))))))

#|
;; add two back-nat together to a new back-nat
(definec add-back-nat (n1 :back-nat n2 :back-nat) :back-nat
  (cond
   ((endp n1) n2)
   ((endp n2) n1)
   (t (if (< (+ (car n1) (car n2)) *base*)
        (cons (+ (car n1) (car n2)) (add-back-nat (cdr n1) (cdr n2)))
        (cons (- (+ (car n1) (car n2)) *base*) (add-back-nat (back-nat-add1 (cdr n1)) (cdr n2)))))))
|#   

;; Lemma. A back-pos-nat is a back-nat
(defthm back-pos-nat-is-back-nat
  (implies (back-pos-natp n)
           (back-natp n)))

;; Lemma. add two back-pos-nat will return a cons
(defthm add-equiv-help
  (IMPLIES (AND (BACK-POS-NATP N1)
                (BACK-POS-NATP N2)
                (CONSP N1)
                (CONSP N2))
           (CONSP (ADD-BACK-NAT N1 N2))))

;; Theorem. add two back-nats is equiv to add two decimal natural numbers
(defthm add-equiv
  (implies (and (back-natp n1)
                (back-natp n2))
           (equal (+ (back-nat-to-nat n1) (back-nat-to-nat n2))
                  (back-nat-to-nat (add-back-nat n1 n2))))
  :hints (("Goal" :use ((:instance add-equiv-help)))))

;;Substraction;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; sub one to the given back-pos-nat
(definec back-nat-sub1 (a :back-pos-nat) :back-nat
  (cond
   ((lendp (cdr a))
    (cond
      ((zp (- (car a) 1)) '())
      (t (cons (- (car a) 1) '()))))
   (t
    (cond
     ((zp (car a)) (cons (- *base* 1) (back-nat-sub1 (cdr a))))
     (t (cons (- (car a) 1) (cdr a)))))))

;; Lemma. a back-nat is equal to a back-nat add one and then sub1
(defthm add1-sub1-annihil
  (implies (back-natp x)
    (equal (back-nat-sub1 (back-nat-add1 x)) x)))

;; Lemma. A non-empty back-nat is a back-pos-nat
(defthm unempty-backnat-is-backposnat
  (implies (and (back-natp x)
                (not (endp x)))
           (back-pos-natp x)))

;; Lemma. Two back-nat a and b, if a > b and b is empty,
;; then a is a back-pos-nat
(defthm backnat-a->-b-implies-a-is-backposnat
  (implies (and (back-natp a)
                (back-natp b)
                (back-nat-< b a)
                (endp b))
           (back-pos-natp a)))

;; Lemma. Two back-nat a and b, if a >= b and a is empty, 
;; then b is empty.
(defthm backnat-a->=-b-and-empty-a-implies-empty-b
  (implies (and (back-natp a)
                (back-natp b)
                (back-nat-<= b a)
                (endp a))
           (endp b)))

;; Lemma. Call back-nat-sub1 onto the cdr of non-empty back-nat x,
;; will return a back-nat
(defthm backnat-sub-help
  (implies (and (back-natp x)
                (not (endp x)))
           (back-natp (back-nat-sub1 (cdr x)))))

;; Lemma. Two back-nat a and b, if a >= b and b is non-empty,
;; then a is non-empty
(defthm backnat-a->=-b-and-unempty-b-implies-unempty-a
  (implies (and (back-natp a)
                (back-natp b)
                (back-nat-<= b a)
                (not (endp b)))
           (not (endp a))))

;; Lemma. Two back-nat a and b, if a >= b and b is non-empty,
;; then a is a back-pos-nat
(defthm backnat-a->=-b-and-unempty-b-implies-backposnat-a
  (implies (and (back-natp a)
                (back-natp b)
                (back-nat-<= b a)
                (not (endp b)))
           (back-pos-natp a)))

;; Lemma. The cdr of a back-nat is still a back-nat
(defthm cdr-of-backnat-is-backnat
  (implies (back-natp x)
           (back-natp (cdr x))))

#| NOT PASSING
;; subtracts a - b (numbers represented as back-nats)
(definec back-nat-sub (a :back-nat b :back-nat) :back-nat
  :ic (back-nat-<= b a)
  :body-contracts-hints (("Goal" :use ((:instance backnat-a->=-b-and-unempty-b-implies-backposnat-a)))
                         ("Goal" :use ((:instance cdr-of-backnat-is-backnat))))
  (cond
   ((endp b) a)
   ((< (car b) (car a)) (cons (- (car a) (car b)) (back-nat-sub (cdr a) (cdr b))))
   ((= (car b) (car a))
    (let ((res (back-nat-sub (cdr a) (cdr b))))
      (cond
       ((endp res) nil)
       (t (cons 0 res)))))
   (t (cons (- (+ *base* (car a)) (car b)) (back-nat-sub (back-nat-sub1 (cdr a)) (cdr b))))))
|#

;;Multiplication;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lemma. Two back-nat n1 and n2, if (car n1) * (car n2) >= 10,
;; then taking the floor of (car n1) * (car n2) / 10 will 
;; return a pos-digit
(defthm mult-back-natp-help
  (implies (and (back-natp n1)
                (back-natp n2)
                (not (< (* (car n1) (car n2)) *base*)))
           (pos-digitp (floor (* (car n1) (car n2)) *base*))))

;; Lemma. Taking the car of a non-empty back-nat returns
;; a pos-digit
(defthm car-of-len-1-unempty-backnat-is-posdigit
  (implies (and (back-natp x)
                (<= (len2 x) 1)
                (not (endp x)))
           (pos-digitp (car x))))

;; Lemma. Two pos-digit n1 and n2, if n1 * n2 >= 10,
;; then taking the floor of n1 * n2 / 10 will
;; return a pos-digit
(defthm floor-of-mult-two-posdigit-bigger-than-10-is-posdigit
  (implies (and (pos-digitp n1)
                (pos-digitp n2)
                (not (< (* n1 n2) *base*)))
           (pos-digitp (floor (* n1 n2) *base*))))

;; Lemma. Two back-pos-nat n1 and n2 implies 
;; (car n1) * (car n2) >= 1
(defthm mult-car-of-two-len-1-back-nat-is-greater-than-1
  (IMPLIES (AND (BACK-POS-NATP N1)
                (BACK-POS-NATP N2)
                (<= (LEN2 N1) 1)
                (<= (LEN2 N2) 1)
                (CONSP N1)
                (CONSP N2)
                (LIST (* (CAR N1) (CAR N2))))
           (<= 1 (* (CAR N1) (CAR N2)))))

; multiplies 2 backnats. We will only ever need to call this function
; on backnats that are empty or have length 1. 
(PROGN
 (ENCAPSULATE
   NIL
   (ENCAPSULATE
        ((ACL2S-BACK-NAT-UNDEFINED (X Y)
                                   T
                                   :GUARD (AND (SYMBOLP X) (TRUE-LISTP Y))))
        (LOCAL (DEFUN ACL2S-BACK-NAT-UNDEFINED (X Y)
                      (DECLARE (IGNORABLE X Y))
                      'NIL))
        (DEFTHM ACL2S-BACK-NAT-UNDEFINED-BACK-NATP
                (BACK-NATP (ACL2S-BACK-NAT-UNDEFINED X Y))
                :RULE-CLASSES ((:TYPE-PRESCRIPTION) (:REWRITE))))
   (DEFUN ACL2S-BACK-NAT-UNDEFINED-ATTACHED (X Y)
          (DECLARE (XARGS :GUARD (AND (SYMBOLP X) (TRUE-LISTP Y))))
          (PROG2$ (CGEN::CW? (SHOW-CONTRACT-VIOLATIONS?)
                             "~|**Input contract  violation in ~x0**: ~x1 ~%"
                             'ACL2S-BACK-NAT-UNDEFINED-ATTACHED
                             (CONS X Y))
                  'NIL))
   (DEFATTACH ACL2S-BACK-NAT-UNDEFINED
              ACL2S-BACK-NAT-UNDEFINED-ATTACHED))
 (ENCAPSULATE
  NIL
  (WITH-OUTPUT
   :OFF :ALL :ON (ERROR)
   (DEFUN
    MULT-BACK-NAT (N1 N2)
    (DECLARE (XARGS :GUARD (AND (BACK-NATP N1)
                                (BACK-NATP N2)
                                (<= (LEN2 N1) 1)
                                (<= (LEN2 N2) 1))
                    :VERIFY-GUARDS NIL
                    :NORMALIZE NIL
                    :TIME-LIMIT 75/2))
    (MBE :LOGIC (IF (AND (BACK-NATP N1)
                         (BACK-NATP N2)
                         (<= (LEN2 N1) 1)
                         (<= (LEN2 N2) 1))
                    (COND ((OR (ENDP N1) (ENDP N2)) 'NIL)
                          ((< (* (CAR N1) (CAR N2)) *BASE*)
                           (CONS (* (CAR N1) (CAR N2)) NIL))
                          (T (CONS (MOD (* (CAR N1) (CAR N2)) *BASE*)
                                   (CONS (FLOOR (* (CAR N1) (CAR N2)) *BASE*)
                                         NIL))))
                    (ACL2S-BACK-NAT-UNDEFINED 'MULT-BACK-NAT
                                              (LIST N1 N2)))
         :EXEC (COND ((OR (ENDP N1) (ENDP N2)) 'NIL)
                     ((< (* (CAR N1) (CAR N2)) *BASE*)
                      (CONS (* (CAR N1) (CAR N2)) NIL))
                     (T (CONS (MOD (* (CAR N1) (CAR N2)) *BASE*)
                              (CONS (FLOOR (* (CAR N1) (CAR N2)) *BASE*)
                                    NIL))))))))
 (DEFTHM
  MULT-BACK-NAT-CONTRACT
  (IMPLIES (AND (FORCE (BACK-NATP N1))
                (FORCE (BACK-NATP N2))
                (FORCE (<= (LEN2 N1) 1))
                (FORCE (<= (LEN2 N2) 1)))
           (BACK-NATP (MULT-BACK-NAT N1 N2)))
  :HINTS
  (("Goal"
       :USE
       ((:INSTANCE FLOOR-OF-MULT-TWO-POSDIGIT-BIGGER-THAN-10-IS-POSDIGIT)))))
 (ENCAPSULATE
    NIL
    (WITH-OUTPUT
         :OFF :ALL :ON (ERROR)
         (VERIFY-GUARDS MULT-BACK-NAT
                        :GUARD-DEBUG T
                        :HINTS (("Goal" :DO-NOT-INDUCT T
                                        :DO-NOT '(GENERALIZE FERTILIZE)))))))

#|
; multiplies 2 backnats. We will only ever need to call this function
; on backnats that are empty or have length 1. 
(definec mult-back-nat (n1 :back-nat n2 :back-nat) :back-nat
  :ic (and (<= (len2 n1) 1) (<= (len2 n2) 1))
  :function-contract-hints (("Goal" :use ((:instance floor-of-mult-two-posdigit-bigger-than-10-is-posdigit))))
  (cond
   ((or (endp n1) (endp n2)) '())
   ((< (* (car n1) (car n2)) *base*) (cons (* (car n1) (car n2)) nil))
   (t (cons (mod (* (car n1) (car n2)) *base*) (cons (floor (* (car n1) (car n2)) *base*) nil)))))
|#

;;Karatsuba;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(set-defunc-termination-strictp nil)
(set-defunc-function-contract-strictp nil)
(set-defunc-body-contracts-strictp nil)

;; subtracts a - b (numbers represented as back-nats)
(definec back-nat-sub (a :back-nat b :back-nat) :back-nat
  :ic (back-nat-<= b a)
  :body-contracts-hints (("Goal" :use ((:instance backnat-a->=-b-and-unempty-b-implies-backposnat-a)))
                         ("Goal" :use ((:instance cdr-of-backnat-is-backnat))))
  (cond
   ((endp b) a)
   ((< (car b) (car a)) (cons (- (car a) (car b)) (back-nat-sub (cdr a) (cdr b))))
   ((= (car b) (car a))
    (let ((res (back-nat-sub (cdr a) (cdr b))))
      (cond
       ((endp res) nil)
       (t (cons 0 res)))))
   (t (cons (- (+ *base* (car a)) (car b)) (back-nat-sub (back-nat-sub1 (cdr a)) (cdr b))))))

; the Karatusba algorithm itself
(definec karatsuba (n1 :back-nat n2 :back-nat) :back-nat
  (cond
   ((and (<= (len2 n1) 1) (<= (len2 n2) 1)) (mult-back-nat n1 n2))
   (t (add-back-nat
       (add-back-nat
        (backnat-expt (karatsuba (sub-list n1 (+ (my-n n1 n2) 1) (len2 n1))
                                 (sub-list n2 (+ (my-n n1 n2) 1) (len2 n2)))
                      (* 2 (my-n n1 n2)))
        (backnat-expt (back-nat-sub
                       (back-nat-sub
                        (karatsuba (add-back-nat (sub-list n1 (+ (my-n n1 n2) 1) (len2 n1))
                                                 (sub-list n1 1 (my-n n1 n2)))
                                   (add-back-nat (sub-list n2 (+ (my-n n1 n2) 1) (len2 n2))
                                                 (sub-list n2 1 (my-n n1 n2))))
                        (karatsuba (sub-list n1 (+ (my-n n1 n2) 1) (len2 n1))
                                   (sub-list n2 (+ (my-n n1 n2) 1) (len2 n2))))
                       (karatsuba (sub-list n1  1 (my-n n1 n2))
                                  (sub-list n2  1 (my-n n1 n2))))
                      (my-n n1 n2)))
       (karatsuba (sub-list n1 1 (my-n n1 n2))
                  (sub-list n2 1 (my-n n1 n2)))))))

;; Test the equivalence between the Karatsuba and standard multiplication
(test? (implies (and (back-natp x) 
                     (back-natp y))
                (equal (nat-to-back-nat (* (back-nat-to-nat x) (back-nat-to-nat y)))
                       (karatsuba x y))))#|ACL2s-ToDo-Line|#


