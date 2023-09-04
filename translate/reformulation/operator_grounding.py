

from collections import OrderedDict
import copy
import re
import pddl.conditions
from . import operator_splitter
from . import helper_functions

def ground_operators(task, baggable_types_list):
    
    # Ground less than atoms in all operators
    ground_operator_less_than_atoms(task, baggable_types_list)
    


             
def ground_operator_less_than_atoms(task, baggable_types_list):  
   
    
    # Add sum-lte predicates to initial state, predicate list and operator preconditions (if they are required by operators)
    for baggable_type in baggable_types_list:
        
        sum_lte_necessary = False
        count_max = [x.number_object for x in baggable_type.macropredicate.counts if x.number == baggable_type.get_max_bag_size()][0]
        sum_lte_args = [pddl.pddl_types.TypedObject("?sum1", baggable_type.macropredicate.num_type_name), pddl.pddl_types.TypedObject("?sum2", baggable_type.macropredicate.num_type_name), pddl.pddl_types.TypedObject("?lte", baggable_type.macropredicate.num_type_name)]
        sum_lte_pred = pddl.predicates.Predicate(helper_functions.create_unique_name(baggable_type.macropredicate.typ.name + "-lte-sum", [x.name for x in task.predicates]), sum_lte_args)
        bag_size_args = [pddl.pddl_types.TypedObject("?bag", baggable_type.macropredicate.typ.name), pddl.pddl_types.TypedObject("?size", baggable_type.macropredicate.num_type_name)]
        bag_size_pred = pddl.predicates.Predicate(helper_functions.create_unique_name(baggable_type.macropredicate.typ.name + "-bag-size", [x.name for x in task.predicates]), bag_size_args)
        
        # Add to operator preconditions
        for action in task.actions:
            #print("Action", action.name)
        
            bag_size_params = []
            vars_of_this_macropredicate_type = [x.name for x in action.parameters if x.type_name == baggable_type.macropredicate.typ.name] + [x.lstrip("%") for x in re.findall("%[a-zA-Z0-9\-]+", action.name) if x.lstrip("%") in [y.name for y in task.objects if y.type_name == baggable_type.macropredicate.typ.name]]
            #print("\tMacropredicate type:", baggable_type.macropredicate.typ)
           
            for bag_variable in vars_of_this_macropredicate_type:
                 #print("\t\tBaggable parameter:", bag_variable)
               
                 for macropred in [baggable_type.macropredicate] + baggable_type.goal_macropredicates:
                    #print("\t\t\tMacopredicate:", macropred.name)
            
                    # Find the 2 variables of this type which refer to the counts in the preconditions. If there are no variables in the effects then we do not need to add the preconditions
                    count_variables_of_this_type = [x.literal.args[-1] for x in action.effects if type(x.literal) is pddl.conditions.NegatedAtom and x.literal.predicate == macropred.name and x.literal.args[0] == bag_variable]
                    if not len(count_variables_of_this_type) == 2:
                        #print("No negated macropredicates")
                        bag_size_params.append(None)
                        continue
                    
                    # Grounding constraint preconditions necessary for this operator                 
                    sum_lte_necessary = True   
                    var_name_decr_upper = count_variables_of_this_type[0]  
                    var_name_incr_lower = count_variables_of_this_type[1]
                    
                    # Add the sum_lte and bag_size preconditions                            
                    parts = list(action.precondition.parts)
                    bag_size_param = pddl.pddl_types.TypedObject(helper_functions.create_unique_name("?" + bag_variable.lstrip("?") + "-size", [x.name for x in action.parameters]), macropred.num_type_name)
                    bag_size_params.append(bag_size_param)
                    action.parameters.append(bag_size_param)
                    parts.append(pddl.conditions.Atom(sum_lte_pred.name, [var_name_decr_upper, var_name_incr_lower, bag_size_param.name]))
                    parts.append(pddl.conditions.Atom(bag_size_pred.name, [bag_variable, bag_size_param.name]))
                    action.precondition.parts = tuple(parts)
            

                    
                
        # Add new predicates to task if needed  
        if not sum_lte_necessary:
            continue
        task.predicates.append(sum_lte_pred)
        task.predicates.append(bag_size_pred)
        
        
        # Ground bag size init predicates
        bag_sizes = []
        for bag in baggable_type.bags:
            bag_size = len(bag.objects)
            count_bag_size = [x.number_object for x in baggable_type.macropredicate.counts if x.number == bag_size][0]
            task.init.append(pddl.conditions.Atom(bag_size_pred.name, [bag.bagname, count_bag_size.name]))
            bag_sizes.append(bag_size)
        
        
        for bag_size in list(OrderedDict.fromkeys(bag_sizes)):
       
            bag_size_num_obj = [x.number_object for x in baggable_type.macropredicate.counts if x.number == bag_size][0]
            
            # Ground first parameter of sum-lte
            for i in range(0, bag_size + 1):
                count_i = [x.number_object for x in baggable_type.macropredicate.counts if x.number == i][0]
           
                # Ground second parameter
                for j in range(0, bag_size - i + 1):
                    count_j = [x.number_object for x in baggable_type.macropredicate.counts if x.number == j][0]
               
                    # Add to initial state
                    task.init.append(pddl.conditions.Atom(sum_lte_pred.name, [count_i.name, count_j.name, bag_size_num_obj.name]))
        
        

       
def sort_number_variables(variable_pair, less_than_predicates):
    relevant_less_than_predicate = [x for x in less_than_predicates if x.args[0] in variable_pair and x.args[1] in variable_pair][0]
    small_pos = [x for x in range(0,2) if variable_pair[x] == relevant_less_than_predicate.args[0]][0]
    large_pos = [x for x in range(0,2) if variable_pair[x] == relevant_less_than_predicate.args[1]][0]
    return [variable_pair[small_pos], variable_pair[large_pos]]
                                                                                                                                                                                        
                

                
                
                
                
                
                
                


    
    
    
    
    
    
    

    
