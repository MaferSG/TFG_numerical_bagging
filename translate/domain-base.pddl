(define (domain child-snack)
(:requirements :typing :equality)
(:types child bread-portion content-portion sandwich)

(:predicates (at_kitchen_bread ?b - bread-portion)
	     (at_kitchen_content ?c - content-portion)
     	     (at_kitchen_sandwich ?s - sandwich)
     	     (no_gluten_bread ?b - bread-portion)
       	     (no_gluten_content ?c - content-portion)
      	     (ontray ?s - sandwich)
       	     (no_gluten_sandwich ?s - sandwich)
	     (allergic_gluten ?c - child)
     	     (not_allergic_gluten ?c - child)
	     (served ?c - child)
	     ;; control predicate
	     ;; sería equivalente a tener not at_kitchen y not on_tray a la vez
	     (free ?s - sandwich)
	   )

(:action make_sandwich_no_gluten 
	 :parameters (?s - sandwich ?b - bread-portion ?c - content-portion)
	 :precondition (and (at_kitchen_bread ?b)
			    (at_kitchen_content ?c)
			    (no_gluten_bread ?b)
			    (no_gluten_content ?c)
			    (free ?s))
	 :effect (and
		   (not (at_kitchen_bread ?b))
		   (not (at_kitchen_content ?c))
		   (at_kitchen_sandwich ?s)
		   (no_gluten_sandwich ?s)
                   (not (free ?s))
		   ))


(:action make_sandwich
	 :parameters (?s - sandwich ?b - bread-portion ?c - content-portion)
	 :precondition (and (at_kitchen_bread ?b)
			    (at_kitchen_content ?c)
                            (free ?s)
			    )
	 :effect (and
		   (not (at_kitchen_bread ?b))
		   (not (at_kitchen_content ?c))
		   (at_kitchen_sandwich ?s)
                   (not (free ?s))
		   ))


(:action put_on_tray
	 :parameters (?s - sandwich)
	 :precondition (and  (at_kitchen_sandwich ?s))
	 :effect (and
		   (not (at_kitchen_sandwich ?s))
		   (ontray ?s)))


(:action serve_sandwich_no_gluten
 	:parameters (?s - sandwich ?c - child)
	:precondition (and
		       (allergic_gluten ?c)
		       (ontray ?s)
		       (no_gluten_sandwich ?s)
		       )
	:effect (and (not (ontray ?s))
		     (served ?c)))

(:action serve_sandwich
	:parameters (?s - sandwich ?c - child)
	:precondition (and (not_allergic_gluten ?c)
			   (ontray ?s))
	:effect (and (not (ontray ?s))
		     (served ?c)))
 	 
)