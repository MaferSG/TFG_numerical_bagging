(define (problem child-snack-0)
  (:domain  child-snack)
  (:objects bread1 bread2 bread3 bread4 bread5 - bread-portion
	    content1 content2 content3 content4 content5 - content-portion
	    s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 - sandwich
;;    	    s1 - sandwich
            child1 child2 child3 child4 child5 - child)
	     
  (:init
    (at_kitchen_bread bread1)
    (at_kitchen_bread bread2)
    (at_kitchen_bread bread3)
    (at_kitchen_bread bread4)
    (at_kitchen_bread bread5)

    (at_kitchen_content content1)
    (at_kitchen_content content2)
    (at_kitchen_content content3)
    (at_kitchen_content content4)
    (at_kitchen_content content5)


    (no_gluten_bread bread1)
    (no_gluten_bread bread2)

    (no_gluten_content content1)
    (no_gluten_content content2)

    (allergic_gluten child1)
    (allergic_gluten child2)
    (not_allergic_gluten child3)
    (not_allergic_gluten child4)
    (not_allergic_gluten child5)
		     
    (free s1)
    (free s2)
    (free s3)
    (free s4)
    (free s5)
    (free s6)
    (free s7)
    (free s8)
    (free s9)
    (free s10)
    )
(:goal (and (served child1) (served child2) (served child3) (served child4) (served child5)))

)

    
    