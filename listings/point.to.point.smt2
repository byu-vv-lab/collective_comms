(declare-datatypes () ((Send (mk-send (src Int)
                                      (dest Int)
                                      (tag Int)
                                      (order Int)
                                      (wait Wait)
                                      (time Int)))
                       (Recv (mk-recv (src Int)
                                      (dest Int)
                                      (tag Int)
                                      (order Int)
                                      (wait Wait)
                                      (time Int)))
                       (Wait (mk-wait (recv Recv)
                                      (order Int)
                                      (time Int)))
                       (Barrier (mk-barrier (order Int)
                                            (time Int)))))

(declare-fun match (Send Recv) Bool)

(define-fun canmatch ((s Send) (r Recv)) Bool
  (and (or (= (src s) (src r))
           (= (src r) 0))
       (or (= (tag s) (tag r))
           (= (tag r) 0))
       (= (dest s) (dest r))))

; Every receive must match a send

; Match rules
(assert (forall ((s Send) (r Recv))
          (=> (match s r)
              (canmatch s r))))

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

; Sends cannot move beyond recieves
(assert (forall ((s Send) (r Recv))
          (=> (and (= (src s) (dest r))
                   (< (order r) (order s))
              (< (time r) (time s))))))

; Receives stay ordered
(assert (forall ((r1 Recv) (r2 Recv))
          (=> (and (= (dest r1) (dest r2))
                   (< (order r1) (order r2)))
              (< (time r1) (time r2)))

;sequential sends with common endpoints
(assert (forall ((s1 Send) (s2 Send))
          (=> (and (= (src s1) (src s2))
                   (= (dest s1) (dest s2))
                   (< (order s1) (order s2)))
              (< (time s1) (time s2)))))

;receive happens before its paired wait
(assert (forall ((r Recv) (w Wait))
          (=> (= r (recv w))
              (< (time r) (time w)))))


;wait happens before the following send
(assert (forall ((w Wait) (s Send))
          (=> (< (order w) (order s))
              (< (time w) (time s)))))
;The above rule will need to change for tags, but we believe it is OK for the point-to-point we currently support. The issue with tags relates to the separate run-time buffers for each destination. Different tags go to different buffers on the destination, so that effectively makes it appear that sends are reordered, even around waits (assuming those waits are send waits). This also assumes that we have send-waits (currently we do not). We will need those for send-modes. Bottom line: the rule is fine for the base point-to-point encoding where we only wait on receives and there are not tags.  It must change for send-modes and tags.

;receive has a nearest-enclosing barrier
(assert (forall ((w Wait) (r Recv) (b Barrier))
          (=> (and (= r (recv w))
                   (forall ((r1 Recv) (w1 Wait))
                      (and (not (= r r1))
                           (= r1 (recv w1))
                           (not (and (< (order w1) (order w)) (< (order b) (order w1)))))))
              (< (time w) (time b)))))
;Let’s come back to the above rule. It is a little hard to understand.

;barrier happens before any operation ordered after a member of the barrier
(assert (forall ((b Barrier) (s Send))
          (=> (< (order b) (order s))
              (< (time b) (time s)))))

(assert (forall ((b Barrier) (r Recv))
          (=> (< (order b) (order r))
              (< (time b) (time r)))))

(assert (forall ((b Barrier) (w Wait))
          (=> (< (order b) (order w))
              (< (time b) (time w)))))

(assert (forall ((b Barrier) (b1 Barrier))
          (=> (< (order b) (order b1))
              (< (time b) (time b1)))))
