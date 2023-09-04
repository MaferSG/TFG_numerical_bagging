# TFG_numerical_bagging
Reformulation of automated planning tasks into a more efficient representation

- Reformulación de la tarea:

python3 baggy.py --writeout_reformulated_pddl --writeout_reformulation_logic --direction=bck domain.pddl problem.pddl

(--direction=bck sirve para cuando el tipo embolsable está en las metas, porque de esta manera embolsa respecto a las metas, y
aseguramos que el plan del dominio traducido sea también un plan del dominio original
Cuando el tipo embolsable no está en las metas, se va a embolsar respecto al estado inicial, se ponga o no el flag de direction)

Este comando genera los ficheros reformulated-domain.pddl y reformulated-problem.pddl, con el dominio y el problema reformulados.
También genera un fichero mappings.txt, con los objetos que contiene cada bolsa creada.

- Solucionar la tarea con el dominio y el problema reformulado con Metric-FF:

metric-ff -s 0 -o reformulated-domain.pddl -f reformulated-problem.pddl 

- Traducir el plan al dominio original:

python3 baggy original-domain.pddl original-problem.pddl --solution plan.txt --mappings mappings.txt


