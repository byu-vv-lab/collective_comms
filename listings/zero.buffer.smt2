;zero buffer semantics: sequential sends
(assert (forall ((s1 Send) (s2 Send))
          (=> (and (= (src s1) (src s2))
                   (< (order s1) (order s2)))
              (< (time s1) (time s2)))))

;zero buffer semantics: send happens before receive on a common process
(assert (forall ((s Send) (r Recv))
          (=> (and (= (src s) (dest r))
                   (< (order s) (order r)))
              (< (time s) (time r)))))


;zero buffer semantics: send happens before a member of barrier on a common process
(assert (forall ((s Send) (b Barrier))
          (=> (< (order s) (order b))
              (< (time s) (time b)))))
