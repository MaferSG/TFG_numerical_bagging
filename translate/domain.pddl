(define (domain gripper-strips)
 (:requirements :strips :typing) 
 (:types room ball robot gripper person color)
 (:predicates (at-robby ?r - robot ?x - room)
 	      (at ?o - ball ?x - room)
       	      (at-person ?p - person ?x - room)
	      (has-color ?o - ball ?c - color)
	      (has-gripper ?r - robot ?g - gripper)
	      (freegripper ?g - gripper)
              (served ?p - person ?c - color)
	      (carry ?o - ball ?g - gripper)
	      )

    
   (:action move
       :parameters  (?r - robot ?from ?to - room)
       :precondition (and  (at-robby ?r ?from))
       :effect (and  (at-robby ?r ?to)
		     (not (at-robby ?r ?from))))

   (:action pick
       :parameters (?r - robot ?obj - ball ?room - room ?g - gripper)
       :precondition  (and  (at ?obj ?room) (at-robby ?r ?room) (has-gripper ?r ?g)  (freegripper ?g))
       :effect (and (carry ?obj ?g)
		    (not (at ?obj ?room)) 
		    (not (freegripper ?g))))

   (:action drop
       :parameters (?r - robot ?obj - ball ?room - room ?g - gripper)
       :precondition  (and (carry ?obj ?g) (has-gripper ?r ?g) (at-robby ?r ?room))
       :effect (and (at ?obj ?room)
		    (freegripper ?g)
		    (not (carry ?obj ?g))))

(:action serve
	   :parameters (?p - person ?obj - ball ?r - room ?c - color)
	   :precondition (and 
			      (at ?obj ?r)
 			      (at-person ?p ?r)
                              (has-color ?obj ?c)
			      )
	   :effect (and
                        (not (at ?obj ?r))
		        (served ?p ?c)
			))
  )
			     