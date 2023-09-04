(define (problem gripper-2-2-4)
(:domain gripper-strips)
(:objects
robot1 robot2 - robot
rgripper1 lgripper1 rgripper2 lgripper2 - gripper
rojo verde azul amarillo - color
room1 room2 - room
ball1 ball2 ball3 ball4 - ball
person1 person2 person3 person4 - person
)
(:init
 
(at-robby robot1 room2)
(freegripper  rgripper1)
(freegripper  lgripper1)
(has-gripper robot1 rgripper1)
(has-gripper robot1 lgripper1)

(at-robby robot2 room1)
(freegripper rgripper2)
(freegripper lgripper2)
(has-gripper robot2 rgripper2)
(has-gripper robot2 lgripper2)


(at ball1 room1)
(at ball2 room1)
(at ball3 room1)
(at ball4 room1)

(has-color ball1 rojo)
(has-color ball2 verde)
(has-color ball3 azul)
(has-color ball4 azul)

(at-person person1 room2)
(at-person person2 room2)
(at-person person3 room1)
(at-person person4 room1)

; (carry ball1 lgripper1)   

)
(:goal
(and
(served person1 rojo)
(served person2 verde)
(served person3 azul)
(served person4 azul) 
;;(goal-gen)

)))


