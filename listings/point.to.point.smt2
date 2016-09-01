; #####################################
; Base encoding structures
; In this encoding, a receive from endpoint 0 is considered wildcard
;   as is a receive with tag 0
; #####################################

(declare-datatypes
  ()
  ((Send
     (mk-send (src Int)
              (dest Int)
              (tag Int)
              (order Int)
              (wait Wait)
              (time Int)))
   (Recv
     (mk-recv (src Int)
              (dest Int)
              (tag Int)
              (order Int)
              (wait Wait)
              (time Int)))
   (Wait
     (mk-wait (src Int)
              (order Int)
              (time Int)))
   (Barrier
     (mk-barrier (src Int)
                 (count Int)
                 (order Int)
                 (time Int)))))

; #####################################
; Base ordering rules - independent of matching
; #####################################

; Operations must come before their witnessing wait
(assert (forall ((s Send))
          (< (time s) (time (wait s)))))
(assert (forall ((r Recv))
          (< (time r) (time (wait r)))))

; Enforce total order
(assert (forall ((s1 Send) (s2 Send))
          (=> (= (time s1) (time s2)
              (= s1 s2)))))
(assert (forall ((r1 Recv) (r2 Recv))
          (=> (= (time r1) (time r2)
              (= r1 r2)))))
(assert (forall ((w1 Wait) (w2 Wait))
          (=> (= (time w1) (time w2)
              (= w1 w2)))))
(assert (forall ((s Send) (r Recv))
          (not (= (time s) (time r)))))
(assert (forall ((s Send) (w Wait))
          (not (= (time s) (time w)))))
(assert (forall ((s Send) (b Barrier))
          (not (= (time s) (time b)))))
(assert (forall ((r Recv) (w Wait))
          (not (= (time r) (time w)))))
(assert (forall ((r Recv) (b Barrier))
          (not (= (time r) (time b)))))

; Barriers happen simultaneously on all processes
(assert (forall ((b1 barrier) (b2 Barrier))
          (=> (= (count b1) (count b2))
              (= (time b1) (time b2)))))

; No operation may be moved across a barrier
(assert (forall ((b Barrier) (s Send))
          (=> (and (= (src b) (src s))
                   (< (order b) (order s)))
              (< (time b) (time s)))))
(assert (forall ((b Barrier) (r Recv))
          (=> (and (= (src b) (dest r))
                      (< (order b) (order r)))
              (< (time b) (time r)))))
(assert (forall ((b Barrier) (w Wait))
          (=> (and (= (src b) (src w))
                   (< (order b) (order w)))
              (< (time b) (time w)))))
(assert (forall ((b Barrier) (b1 Barrier))
          (=> (< (count b) (count b1))
              (< (time b) (time b1)))))

; Receives stay ordered
; FIXME: Witnessing waits must stay ordered, but do the receives need to?
(assert (forall ((r1 Recv) (r2 Recv))
          (=> (and (= (dest r1) (dest r2))
                   (< (order r1) (order r2)))
              (< (time r1) (time r2)))
(assert (forall ((r1 Recv) (r2 Recv))
          (=> (and (= (dest r1) (dest r2))
                   (< (order (wait r1)) (order (wait r2))))
              (< (time (wait r1)) (time (wait r2))))

; Sends cannot move beyond recieves
; FIXME: How late can we move a sends wait? How early can we move the send?
(assert (forall ((s Send) (r Recv))
          (=> (and (= (src s) (dest r))
                   (< (order r) (order s))
              (< (time r) (time s))))))

; #####################################
; Matching rules
; #####################################

(declare-fun match (Send Recv) Bool)

(define-fun canmatch ((s Send) (r Recv)) Bool
  (and (or (= (src s) (src r))
           (= (src r) 0))
       (or (= (tag s) (tag r))
           (= (tag r) 0))
       (= (dest s) (dest r))))

; Match rules must hold
(assert (forall ((s Send) (r Recv))
          (=> (match s r)
              (canmatch s r))))

; Every receive must match a send
(assert (forall ((r Recv))
          (not (forall ((s Send))
                 (not (match s r))))))

; A send must occur before the enclosing wait of its receive
(assert (forall ((s Send) (r Recv))
          (=> (match s r)
              (< (time s) (time (wait r))))))

; Only one send per receive
(assert (forall ((s1 Send) (s2 Send) (r Recv))
          (=> (and (match s1 r) (match s2 r))
              (= s1 s2))))

; Only one receive per send
(assert (forall ((s Send) (r1 Recv) (r2 Recv))
          (=> (and (match s r1) (match s r2))
              (= r1 r2))))

; Non-overtaking sends
(assert (forall ((s1 Send) (s2 Send) (r2 Receive))
          (=> (and (= (src s1) (src s2))
                   (canmatch s1 r2)
                   (canmatch s2 r2)
                   (match s2 r2)
                   (< (order s1) (order s2)
                   (forall ((r1 Receive))
                     (=> (match s1 r1)
                         (< (time r1) (time r2)))))
              (< (time s1) (time s2))))))

; Sequential sends with common endpoints
; FIXME: This may be superfluous due to the non-overtaking rules
(assert (forall ((s1 Send) (s2 Send))
          (=> (and (= (src s1) (src s2))
                   (= (dest s1) (dest s2))
                   (< (order s1) (order s2)))
              (< (time s1) (time s2)))))

; Wait happens before the following send
; FIXME: The rule will need to change for tags, but we believe it is OK for the point-to-point we currently support.
;   The issue with tags relates to the separate run-time buffers for each destination.
;   Different tags go to different buffers on the destination, so that effectively makes it appear that sends are reordered, even around waits (assuming those waits are send waits).
;   This also assumes that we have send-waits (currently we do not).
;   We will need those for send-modes.
;   Bottom line: the rule is fine for the base point-to-point encoding where we only wait on receives and there are not tags.
;   It must change for send-modes and tags.
(assert (forall ((w Wait) (s Send))
          (=> (< (order w) (order s))
              (< (time w) (time s)))))
