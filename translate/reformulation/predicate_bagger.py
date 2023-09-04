import copy
import random
import options
import pddl
import invariants as invariants_file
from pddl import functions
from reformulation import bag_classes
from . import single_valued_checker
from . import relation_mapping
from . import helper_functions
from collections import OrderedDict
import pprint

import reformulation



def bag_predicates(baggable_types_list, task, invariants, type_checker_list):
    


    create_bag_predicates_and_functions(baggable_types_list, task, invariants, type_checker_list) # Generate macropredicates
    desired_count_grounded_atoms = modify_goal_state(baggable_types_list, task, invariants, type_checker_list) # Ground macropredicates in goal
    modify_initial_state(baggable_types_list, task, invariants, type_checker_list, desired_count_grounded_atoms) # Ground macropredicates in initial state
    
    if options.writeout_reformulation_logic:
        print_types_and_objects(task)
    
        


def modify_initial_state(baggable_types_list, task, invariants, type_checker_list, desired_count_grounded_atoms):
    
    if options.writeout_reformulation_logic:
        print("Grounding macropredicates in initial state...")
    
    new_init = []
    init_bags = [[] for x in baggable_types_list]
    
        
    # Find all init atoms which baggable objects appear in, and add all other init atoms into the new init
    for init in [x for x in task.init if type(x) is pddl.conditions.Atom and not x.predicate == '=']:
        to_remove = False
        for b in range(0, len(baggable_types_list)):
            baggable_type = baggable_types_list[b]
            for bag in baggable_type.bags:
                if len([x for x in bag.objects if x.name in init.args]):
                    to_remove = True
                    init_bags[b].append(init)
        if not to_remove:
            new_init.append(init)

    new_init.extend([x for x in task.init if type(x) is pddl.f_expression.Assign])  



    #### MafeInicio ####
    functions_to_add = []
    bag_predicates_to_add = []

    unbagged_objects_of_each_baggable_type = dict.fromkeys(baggable_types_list, None)
    for baggable_type in baggable_types_list:
        unbagged_objects_of_each_baggable_type[baggable_type] = tuple(baggable_type.all_unbagged_objects)

    
    for b in range(0, len(baggable_types_list)):
        baggable_type = baggable_types_list[b]
        init_bag = init_bags[b]

        baggable_original_predicates = []

        task_objects_of_this_baggable_type = [obj for obj in task.objects if obj.type_name == baggable_type.object_type.name]

        
        
        ##################################################################
        ################ ADDING BAG PREDICATES ###########################  
        ##################################################################
        for bag_predicate in baggable_type.bag_predicates:
            bag_predicate_of_this_type = baggable_type.bag_predicates[0]

            atoms_with_baggable_arguments_of_the_same_bag = {}

            original_predicates_of_this_bag_predicate = bag_predicate_of_this_type.original_predicate
            functions_of_this_baggable_type = [function.predicate for function in baggable_type.functions]

            baggable_original_predicates.extend(original_predicates_of_this_bag_predicate)
            baggable_original_predicates.extend(functions_of_this_baggable_type)

            bag_predicates_to_add = add_bag_predicates_to_initial_state(task, baggable_type, init_bag, original_predicates_of_this_bag_predicate, task_objects_of_this_baggable_type,\
                                         atoms_with_baggable_arguments_of_the_same_bag, bag_predicate, bag_predicates_to_add, unbagged_objects_of_each_baggable_type)


    
        ##########################################################
        ################### ADDING FUNCTIONS #####################
        ##########################################################
        functions_to_add = add_functions_to_initial_state(baggable_type, baggable_types_list, init_bag, functions_to_add, task, unbagged_objects_of_each_baggable_type)


    task.init = new_init + bag_predicates_to_add + functions_to_add

    bag_objects(task, unbagged_objects_of_each_baggable_type, baggable_types_list)
    #### MafeFin ####	



def add_bag_predicates_to_initial_state(task, baggable_type, init_bag, original_predicates_of_this_bag_predicate, task_objects_of_this_baggable_type,\
                                         atoms_with_baggable_arguments_of_the_same_bag, bag_predicate, bag_predicates_to_add, unbagged_objects_of_each_baggable_type):
    
    for atom in init_bag:
        # if not len(original_predicates_of_this_bag_predicate), then the bag_predicate has no original predicates, 
        # so it is a bag with just id and we'll add them always
        if atom.predicate in original_predicates_of_this_bag_predicate or not len(original_predicates_of_this_bag_predicate):
            for atom_argument in atom.args:
                if atom_argument in [obj.name for obj in task_objects_of_this_baggable_type]:   
                    if atoms_with_baggable_arguments_of_the_same_bag.get(atom_argument) is None:
                        atoms_with_baggable_arguments_of_the_same_bag[atom_argument] = []
                    atoms_with_baggable_arguments_of_the_same_bag[atom_argument] = atoms_with_baggable_arguments_of_the_same_bag[atom_argument] + [atom]
        

    bags_used = []
    
    for key, value in atoms_with_baggable_arguments_of_the_same_bag.items():

        new_predicate_args = []
        args_of_each_atom = [atom.args for atom in value]

        for element in args_of_each_atom:
            for x in element:
                # If the bag has just the id, we do not need to add any argument
                if not len(original_predicates_of_this_bag_predicate):
                    pass
                # If the bag has more than one argument, we add as argument all the arguments except the baggable object
                else:
                    if x != key:
                        # We have to check if the argument is of a baggable type, because if it is, we have to substitute it for the id of the bag
                        if x in [obj.name for obj in baggable_type.all_unbagged_objects]:
                            for bag in baggable_type.bags:
                                if x in [obj.name for obj in bag.objects]:
                                    new_predicate_args.append(bag.bagname)
                        new_predicate_args.append(x)


        for bag in baggable_type.bags:
            if key in [obj.name for obj in bag.objects]:
                if bag.bagname not in bags_used:
                    bags_used.append(bag.bagname)
                    new_predicate_args = sort_bag_predicate_arguments(task, new_predicate_args, bag_predicate)
                    new_predicate_args = substitute_baggable_objects_for_bag_id_in_bag(new_predicate_args, baggable_type, unbagged_objects_of_each_baggable_type)
                    new_bag_predicate =  bag_predicate.ground_bag_predicate(new_predicate_args, [bag.bagname])
                    if new_bag_predicate not in bag_predicates_to_add:
                        bag_predicates_to_add.append(new_bag_predicate)  

    return bag_predicates_to_add





def sort_bag_predicate_arguments(task, new_predicate_args, bag_predicate):
    """ Sort the arguments of the bag predicate in the same order as the arguments of the original predicate """
    
    new_predicate_args_with_types = []

    # Order of the arguments of the bag predicate
    order_of_args_in_bag_predicate = bag_predicate.arguments
    order_of_args_in_bag_predicate = [x.type_name for x in order_of_args_in_bag_predicate if x != bag_predicate.id]
    # Since the arguments of the atoms are strings, we have to search in the objects which is their type
    for arg in new_predicate_args:
        new_predicate_args_with_types.extend([object for object in task.objects if object.name == arg])

    # Sort the arguments of the bag predicate in the same order as the arguments of the original predicate
    # We use the type of the objects to sort them
    new_predicate_args_ordered = sorted(new_predicate_args_with_types, key=lambda obj: order_of_args_in_bag_predicate.index(obj.type_name))
    # We just need the names of the objects for grounding the predicate
    new_predicate_args_ordered = [x.name for x in new_predicate_args_ordered]

    return new_predicate_args_ordered
    



def add_functions_to_initial_state(baggable_type, baggable_types_list, init_bag, functions_to_add, task, unbagged_objects_of_each_baggable_type):

    atom_to_add = []
    
    for function in baggable_type.functions:
        atoms_of_each_bag = dict.fromkeys([bag.bagname for bag in baggable_type.bags], [])
        for bag in baggable_type.bags:
            for atom in init_bag:
                if atom.predicate in function.predicate:
                    for argument in atom.args:
                        args_for_grounding_function = []
                        if argument in [object.name for object in bag.objects]:
                            atoms_of_each_bag[bag.bagname] = atoms_of_each_bag[bag.bagname] + [atom]

        #################################################################################################################
        ######################### When the baggable type is in the goals ################################################
        #################################################################################################################

        functions_to_add = add_functions_to_initial_state_when_baggable_type_is_in_goals(baggable_type, baggable_types_list, atoms_of_each_bag, function, functions_to_add, task, unbagged_objects_of_each_baggable_type)

        
        
        #################################################################################################################
        ######################### When the baggable type is not in the goals ############################################
        #################################################################################################################
        functions_to_add = add_functions_to_initial_state_when_baggable_type_is_not_in_goals(baggable_type, baggable_types_list, atoms_of_each_bag, function, functions_to_add, task, unbagged_objects_of_each_baggable_type)
        


        # For the functions tha do not appear in the initial state, we create a function with 0 objects in the bag
        args_of_this_function = []
        for arg in function.arguments:
            for bag in baggable_type.bags:
                bags_of_this_function = [bag.bagname for bag in baggable_type.bags if arg.type_name in [object.type_name for object in bag.objects]]
                args_of_this_function = [arg for arg in function.arguments if arg.type_name not in {object.type_name for object in bag.objects}]
                args_of_this_function = [object for object in task.objects if object.type_name in {arg.type_name for arg in args_of_this_function} or object.type_name in {typ.name for arg in args_of_this_function for typ in arg.get_child_types(task.types)}]

                
            if arg.type_name in [object.type_name for object in baggable_type.all_unbagged_objects]:

                for bag_of_this_function in bags_of_this_function:
                    for arg_of_this_function in args_of_this_function:
                        
                        # We'll do separated cases for functions with interacting baggable types and functions without interacting baggable types
                        
                        if function.has_interacting_baggable_types(baggable_types_list):
                            for key, value in unbagged_objects_of_each_baggable_type.items():
                                if key.object_type.name != baggable_type.object_type.name:
                                    if arg_of_this_function in value:
                                        bag_type = [key for key in unbagged_objects_of_each_baggable_type.keys() if unbagged_objects_of_each_baggable_type[key] == value][0]
                                        arg_to_ground_function = bag_type.get_bag_name_of_object(arg_of_this_function)
                                    else:
                                        arg_to_ground_function = arg_of_this_function.name
                                    
                                    new_function = function.ground_function([arg_to_ground_function], [bag_of_this_function], 0)
                                    if new_function not in functions_to_add:
                                        functions_to_add.append(new_function)

                        else: # Not interacting baggable types
                            for key, value in unbagged_objects_of_each_baggable_type.items():
                                if key.object_type.name == baggable_type.object_type.name:
                                    if arg_of_this_function in value:
                                        bag_type = [key for key in unbagged_objects_of_each_baggable_type.keys() if unbagged_objects_of_each_baggable_type[key] == value][0]
                                        arg_to_ground_function = bag_type.get_bag_name_of_object(arg_of_this_function)
                                    else:
                                        arg_to_ground_function = arg_of_this_function.name

                                    new_function = function.ground_function([arg_to_ground_function], [bag_of_this_function], 0)
                    
                                    if new_function not in functions_to_add:
                                        functions_to_add.append(new_function)


                        # new_function = function.ground_function([arg_to_ground_function], [bag_of_this_function], 0)
                        # if new_function.predicate not in [f.predicate for f in functions_to_add]:
                            # functions_to_add.append(new_function)

                    # If not len(args_of_this_function), it's because the functions only has the id of the bag
                    # so we create a function without any argument except for the bag  
                    if not len(args_of_this_function):
                        new_function = function.ground_function([], [bag_of_this_function], 0)
                        if new_function not in functions_to_add:
                            functions_to_add.append(new_function)

    return functions_to_add



def add_functions_to_initial_state_when_baggable_type_is_in_goals(baggable_type, baggable_types_list, atoms_of_each_bag, function, functions_to_add, task, unbagged_objects_of_each_baggable_type):
    for bag in baggable_type.bags:
        # First, we create the functions for the predicates that are in the original initial state
        equal_arguments = {}
        for atom in atoms_of_each_bag[bag.bagname]:
            if atom.predicate in function.predicate:
                # Pass to the function just the arguments that are not a of a baggable type
                baggable_objects = [arg for arg in atom.args if arg in [object.name for object in baggable_type.all_unbagged_objects]]
                args_to_ground_function = [arg for arg in atom.args if arg not in baggable_objects] 

                
                
                # If the object is of a baggable type, we substitute it for the id of the bag
                # if [pddl.pddl_types.TypedObject.is_baggable(arg, baggable_types_list) for arg in args_to_ground_function]:
                args_to_ground_function = substitute_baggable_objects_for_bag_id(args_to_ground_function, function, baggable_type, unbagged_objects_of_each_baggable_type, task)

                
                for arg in args_to_ground_function:
                    if equal_arguments.get(arg) is None:
                        equal_arguments[arg] = 0
                    equal_arguments[arg] = equal_arguments[arg] + 1


        for key, value in equal_arguments.items():

            new_function = function.ground_function([key], [bag.bagname], value)
            # I'm not sure if this is the best way to assure that the function is not repeated
            # The idea is that we should create just one function for each bag
            if new_function not in functions_to_add:
                functions_to_add.append(new_function)

        for atom in atoms_of_each_bag[bag.bagname]:
            # For the rest of objects of the same type of the argument of the function, 
            # we create a new function with 0 objecs in the bag
            non_baggable_objects_in_function = [arg for arg in task.objects if arg.name in atom.args and arg not in baggable_type.all_unbagged_objects]
            non_baggable_objects_type = [x.type_name for x in non_baggable_objects_in_function]
            rest_of_objects_of_the_other_types = [obj for obj in task.objects if obj.type_name in non_baggable_objects_type and obj not in non_baggable_objects_in_function]
            # 
            rest_of_objects_of_the_other_types = substitute_baggable_objects_for_bag_id([obj.name for obj in rest_of_objects_of_the_other_types], function, baggable_type, unbagged_objects_of_each_baggable_type, task)
            for obj_not_in_function in rest_of_objects_of_the_other_types:
                new_function = function.ground_function([obj_not_in_function], [bag.bagname], 0)
                if new_function not in functions_to_add:
                    functions_to_add.append(new_function)

    return functions_to_add



def add_functions_to_initial_state_when_baggable_type_is_not_in_goals(baggable_type, baggable_types_list, atoms_of_each_bag, function, functions_to_add, task, unbagged_objects_of_each_baggable_type):
    for bag in baggable_type.bags:
        # First, we create the functions for the predicates that are in the original initial state
        for atom in atoms_of_each_bag[bag.bagname]:
            if atom.predicate in function.predicate:
                # Just pass to the function the arguments that are not a of a baggable type
                baggable_objects = [arg for arg in atom.args if arg in [object.name for object in baggable_type.all_unbagged_objects]]
                args_to_ground_function = [arg for arg in atom.args if arg not in baggable_objects] 

                # If the object is of a baggable type, we substitute it for the id of the bag
                # if [pddl.pddl_types.TypedObject.is_baggable(arg, baggable_types_list) for arg in args_to_ground_function]:
                args_to_ground_function = substitute_baggable_objects_for_bag_id(args_to_ground_function, function, baggable_type, unbagged_objects_of_each_baggable_type, task)


                new_function = function.ground_function(args_to_ground_function, [bag.bagname], len(atoms_of_each_bag[bag.bagname]))

                # I'm not sure if this is the best way to assure that the function is not repeated
                # The idea is that we should create just one function for each bag
                if new_function not in functions_to_add:
                    functions_to_add.append(new_function)

                # For the rest of objects of the same type of the argument of the function, 
                # we create a new function with 0 objecs in the bag
                non_baggable_objects_in_function = [arg for arg in task.objects if arg.name in atom.args and arg not in baggable_type.all_unbagged_objects]
                non_baggable_objects_type = [x.type_name for x in non_baggable_objects_in_function]
                rest_of_objects_of_the_other_types = [obj for obj in task.objects if obj.type_name in non_baggable_objects_type and obj not in non_baggable_objects_in_function]
                
                rest_of_objects_of_the_other_types = substitute_baggable_objects_for_bag_id([obj.name for obj in rest_of_objects_of_the_other_types], function, baggable_type, unbagged_objects_of_each_baggable_type, task)
                for obj_not_in_function in rest_of_objects_of_the_other_types:
                    new_function = function.ground_function([obj_not_in_function], [bag.bagname], 0)
                    if new_function not in functions_to_add:
                        functions_to_add.append(new_function)

    return functions_to_add








def substitute_baggable_objects_for_bag_id_in_bag(bag_arguments, baggable_type, unbagged_objects_of_each_baggable_type):
    """ Substitute the objects of a baggable type for the id of the bag in the arguments of a bag predicate """
    for arg in bag_arguments:
        for key, value in unbagged_objects_of_each_baggable_type.items():
            if key.object_type.name != baggable_type.object_type.name:
                for elem in value:
                    if arg == elem.name:
                        bag_arguments[bag_arguments.index(arg)] = key.get_bag_name_of_object(elem)

    return bag_arguments


def substitute_baggable_objects_for_bag_id(args_to_ground_function, function, baggable_type, unbagged_objects_of_each_baggable_type, task):
    """ Substitute the objects of a baggable type for the id of the bag in the arguments of a function """
    for arg in function.arguments:
        for bag in baggable_type.bags:
            bags_of_this_function = [bag.bagname for bag in baggable_type.bags if arg.type_name in [object.type_name for object in bag.objects]]
            # args_of_this_function = [arg for arg in function.arguments if arg.type_name not in [object.type_name for object in bag.objects] and arg.name in args_to_ground_function]
            args_of_this_function = [arg for arg in function.arguments if arg.type_name not in [object.type_name for object in bag.objects]]
            args_of_this_function = [object for object in task.objects if object.type_name in [arg.type_name for arg in args_of_this_function]]

        
        # If the argument is of the baggable type
        if arg.type_name in [object.type_name for object in baggable_type.all_unbagged_objects]:
            # for bag_of_this_function in bags_of_this_function:
            for arg_of_this_function in args_of_this_function:

                # key=bag_type, value=unbagged_objects_of_this_baggable_type
                for key, value in unbagged_objects_of_each_baggable_type.items():
                    # For the baggable types that are not the same as the baggable type of the function
                    if key.object_type.name != baggable_type.object_type.name:
                        # If the object is of one of this baggable types
                        if arg_of_this_function in value:
                            # Substitute the object for the id of the bag
                            bag_type = [key for key in unbagged_objects_of_each_baggable_type.keys() if unbagged_objects_of_each_baggable_type[key] == value][0]
                            args_to_ground_function = [bag_type.get_bag_name_of_object(arg_of_this_function)]
                        # else: # If it is not baggable, args_to_ground_function remains the same

    return args_to_ground_function


def bag_objects(task, unbagged_objects_of_each_baggable_type, baggable_types_list):
    #TODO: Hacer esto mejor. Ver la funcion bag_objects del fichero object_bagger.py

    for baggable_type in baggable_types_list:
        task.objects = [x for x in task.objects if not x.type_name == baggable_type.object_type.name]
        task.objects.extend(baggable_type.all_bagged_objects)


    # new_objects = []
    # original_objects = task.objects

    # for obj in task.objects:

    #     for elem in unbagged_objects_of_each_baggable_type.values():
    #         if obj in elem:
    #             bag_type = [key for key in unbagged_objects_of_each_baggable_type.keys() if unbagged_objects_of_each_baggable_type[key] == elem][0]
    #             obj.name = bag_type.get_bag_name_of_object(obj)
    #             if obj.name not in [x.name for x in new_objects]:     
    #                 new_objects.append(obj)
    #         else:
    #             if obj.name not in [x.name for x in new_objects]:
    #                 new_objects.append(obj)

    # task.objects = new_objects


    


def modify_goal_state(baggable_types_list, task, invariants, type_checker_list):
    if options.writeout_reformulation_logic:
        print("Grounding macropredicates in goal state...")
    
    new_goal = []
    goal_bags = [[] for x in baggable_types_list]
    desired_count_grounded_atoms = []
    
    
    
    # Find all goal atoms which baggable objects appear in, and add all other goal atoms into the new goal
    for goal in [x for x in task.goal.parts if type(x) is pddl.conditions.Atom]:
        to_remove = False
        for b in range(0, len(baggable_types_list)):
            baggable_type = baggable_types_list[b]
            for bag in baggable_type.bags:
                if len([x for x in bag.objects if x.name in goal.args]):
                    to_remove = True
                    goal_bags[b].append(goal)
        if not to_remove:
            new_goal.append(goal)
    new_goal.extend([x for x in task.goal.parts if type(x) is pddl.f_expression.Assign])
        
    ########## MafeInicio ##########
    # ungrounded_bag_predicates_to_add = []
    grounded_bag_predicates_to_add = []
    # ungrounded_functions_to_add = []
    grounded_functions_to_add = []

    unbagged_objects_of_each_baggable_type = dict.fromkeys(baggable_types_list, None)
    for baggable_type in baggable_types_list:
        unbagged_objects_of_each_baggable_type[baggable_type] = tuple(baggable_type.all_unbagged_objects)


    for b in range(0, len(baggable_types_list)):

        baggable_type = baggable_types_list[b]
        goal_bag = goal_bags[b]
        baggable_original_predicates = []

        # ungrounded_bag_predicates_to_add.append(baggable_type.bag_predicates)
        # ungrounded_functions_to_add.append(baggable_type.functions)

        task_objects_of_this_baggable_type = [obj for obj in task.objects if obj.type_name == baggable_type.object_type.name]

        ##################################################################
        ################ ADDING BAG PREDICATES ###########################  
        ##################################################################
        for bag_predicate in baggable_type.bag_predicates:

            bag_predicate_of_this_type = baggable_type.bag_predicates[0]

            atoms_with_baggable_arguments_of_the_same_bag = {}

            original_predicates_of_this_bag_predicate = bag_predicate_of_this_type.original_predicate
            functions_of_this_baggable_type = [function.predicate for function in baggable_type.functions]

            baggable_original_predicates.extend(original_predicates_of_this_bag_predicate)
            baggable_original_predicates.extend(functions_of_this_baggable_type)            

            grounded_bag_predicates_to_add = add_bag_predicates_to_goal_state(\
                baggable_type, goal_bag, original_predicates_of_this_bag_predicate, task_objects_of_this_baggable_type,\
                atoms_with_baggable_arguments_of_the_same_bag, bag_predicate, grounded_bag_predicates_to_add)
 

        ##########################################################
        ################### ADDING FUNCTIONS #####################
        ##########################################################
        grounded_functions_to_add = add_functions_to_goal_state(baggable_type, goal_bag, grounded_functions_to_add)
  
    
    # Add the new goal bag_predicates and functionsto the goal and return the list of 'desired-count' atoms which will later be added to the initial state (only if a GTE system is needed)
    task.goal.parts = new_goal + grounded_bag_predicates_to_add + grounded_functions_to_add
    return desired_count_grounded_atoms



def add_bag_predicates_to_goal_state(baggable_type, goal_bag, original_predicates_of_this_bag_predicate, task_objects_of_this_baggable_type,\
                                    atoms_with_baggable_arguments_of_the_same_bag, bag_predicate, grounded_bag_predicates_to_add):
    for atom in goal_bag:
        # if not len(original_predicates_of_this_bag_predicate), then the bag_predicate has no original predicates, 
        # so it is a bag with just id and we'll add them always
        if atom.predicate in original_predicates_of_this_bag_predicate or not len(original_predicates_of_this_bag_predicate):
            for atom_argument in atom.args:
                if atom_argument in [obj.name for obj in task_objects_of_this_baggable_type]:   
                    if atoms_with_baggable_arguments_of_the_same_bag.get(atom_argument) is None:
                        atoms_with_baggable_arguments_of_the_same_bag[atom_argument] = []
                    atoms_with_baggable_arguments_of_the_same_bag[atom_argument] = atoms_with_baggable_arguments_of_the_same_bag[atom_argument] + [atom]

    bags_used = []
    for key, value in atoms_with_baggable_arguments_of_the_same_bag.items():
        new_predicate_args = []
        args_of_each_atom = [atom.args for atom in value]
        for element in args_of_each_atom:
            for x in element:
                # If the bag has just the id, we do not need to add any argument
                if not len(original_predicates_of_this_bag_predicate):
                    pass
                # If the bag has more than one argument, we add as argument all the arguments except the baggable object
                else:
                    if x != key:
                        new_predicate_args.append(x)
        for bag in baggable_type.bags:
            if bag.bagname not in bags_used:
                if key in [obj.name for obj in bag.objects]:
                    bags_used.append(bag.bagname)

                    new_bag_predicate =  bag_predicate.ground_bag_predicate(new_predicate_args, [bag.bagname])
                    if new_bag_predicate not in grounded_bag_predicates_to_add:
                        grounded_bag_predicates_to_add.append(new_bag_predicate) 

    return grounded_bag_predicates_to_add



def add_functions_to_goal_state(baggable_type, goal_bag, grounded_functions_to_add):
    for function in baggable_type.functions:
        atoms_of_each_bag = dict.fromkeys([bag.bagname for bag in baggable_type.bags], [])
        for bag in baggable_type.bags:
            for atom in goal_bag:
                if atom.predicate in function.predicate:
                    for argument in atom.args:
                        args_for_grounding_function = []
                        if argument in [object.name for object in bag.objects]:
                            atoms_of_each_bag[bag.bagname] = atoms_of_each_bag[bag.bagname] + [atom]

        # for bag in baggable_type.bags:
            for atom in atoms_of_each_bag[bag.bagname]:
                if atom.predicate in function.predicate:
                    # Just pass to the funciton the arguments that are not a of a baggable type
                    baggable_objects = [arg for arg in atom.args if arg in [object.name for object in baggable_type.all_unbagged_objects]]
                    args_for_grounding_function = [arg for arg in atom.args if arg not in baggable_objects]
            
                    new_function = function.ground_function(args_for_grounding_function, [bag.bagname], len(atoms_of_each_bag[bag.bagname]))
                    # I'm not sure if this is the best way to assure that the function is not repeated
                    # The idea is that we should create just one function for each bag
                    if new_function not in grounded_functions_to_add:
                        grounded_functions_to_add.append(new_function)

    return grounded_functions_to_add

        
        

def create_bag_predicates_and_functions(baggable_types_list, task, invariants, type_checker_list):
    
    if options.writeout_reformulation_logic:
        print("Generating BagPredicates and functions...")
    
    task = reformulation.task_modifier.modify_task(task)[1]
    predicates_that_remain_the_same = [predicate for predicate in task.predicates if predicate.remains_the_same]
    # print("predicates_that_remain_the_same: ", [p.name for p in predicates_that_remain_the_same])

    
    new_predicates = []
    new_functions = []
    new_functions = task.functions

    # Get rid of all '=' predicates (we don't need them in Baggy) and get rid of all predicates which have an argument of a baggable type
    types_to_bag = [x.object_type for x in baggable_types_list]
    new_predicates = [x for x in task.predicates if not x.name == '=' and not len([y for y in types_to_bag if y.name in [z.type_name for z in x.arguments]])]
    # For each baggable type
    for baggable_type in baggable_types_list:
        # print(bag_classes.BaggableType.is_in_goal_state(baggable_type, task))

        invariants_of_type_b = baggable_type.type_checker.invariants_of_this_type
        print("invariants_of_type ", baggable_type.object_type.name, " : ", invariants_of_type_b)
        macropredicate = relation_mapping.Macropredicate(task, baggable_type.object_type, baggable_type.type_checker.supertypes, type_checker_list)
        macropredicate.baggable_type = baggable_type


        ################## Creation predicates ##################

        new_invariants_of_type_b = invariants_of_type_b.copy()
        for invariant in invariants_of_type_b:
            part_with_creation_predicate = []
            part_without_creation_predicate = []
            if ("freee" or "notexist") in [part.predicate for part in invariant.parts]:
                # substitute the invariant for two invariants, onre with the creation predicate and one with the other predicates
                part_with_creation_predicate = [part for part in invariant.parts if part.predicate == ("free" or "notexist")]
                part_without_creation_predicate = [part for part in invariant.parts if part.predicate != ("free" or "notexist")]
                invariant_with_creation_predicate = invariants_file.Invariant(part_with_creation_predicate)
                invariant_without_creation_predicate = invariants_file.Invariant(part_without_creation_predicate)

                task.creation_predicates.append(part_with_creation_predicate[0])

                print("BEFORE: ", new_invariants_of_type_b)
                new_invariants_of_type_b.remove(invariant)
                new_invariants_of_type_b.append(invariant_with_creation_predicate) if invariant_with_creation_predicate not in new_invariants_of_type_b else None
                new_invariants_of_type_b.append(invariant_without_creation_predicate)
                # baggable_type.type_checker.invariants_of_this_type.remove(invariant)

                print("AFTER: ", new_invariants_of_type_b)

        invariants_of_type_b =  new_invariants_of_type_b.copy()
        # baggable_type.type_checker.invariants_of_this_type = new_invariants_of_type_b

        ################## End creation predicates ##################


        
        # Invariants
        #### MafeInicio: ####
        # Aquí necesito saber cómo determinar cuál es la propiedad que caracteriza a la bolsa,
        # porque ellos meten todas en el macropredicate, pero yo necesito separarlas en el predicate
        # que tenga solamente la propiedad de la bolsa, y en el contador para las otras.
        # Creo que eso se sabe con los invariants que contienen un solo predicado
        exist_invariant_groups_with_various_predicates = False
        exist_invariant_groups_with_1_predicate = False
        invariant_groups_with_1_predicate = []
        for invariant_group in invariants_of_type_b:

            # If the invariant has only one predicate, it is the property that will characterize the bag
            # except when that predicate is a creation predicate

            # If it has only one predicate that is not a creation predicate
            
            if len(invariant_group.predicates) == 1 and True not in [part.is_a_creation_predicate(task) for part in invariant_group.parts]:
                exist_invariant_groups_with_1_predicate = True
                invariant_groups_with_1_predicate.append(invariant_group)
                # print("invariant_groups_with_1_predicate: ", invariant_groups_with_1_predicate)

            # #### Esto es asumiendo que la bolsa tiene una sola propiedad. Descomentar si lo otro da problemas #####
            #     for predicate in invariant_group.predicates:
            #         new_bag_predicate = create_bag_predicate(task, predicate, baggable_type)
            #         new_predicate = pddl.predicates.Predicate(new_bag_predicate.name, new_bag_predicate.arguments)
            #         new_predicates.append(new_predicate)
            # #### Esto es asumiendo que la bolsa tiene una sola propiedad. Descomentar si lo otro da problemas #####
                
                # macropredicate.add_invariant_argument(invariant_group) 
            # If the invariant has more that one predicate, we will create a function that counts
            # the objects of the bag that have the property described in those predicates
            # Also, we will include here the invariants with just one argument if they have a creation predicate
            elif len(invariant_group.predicates) > 1 or True in [part.is_a_creation_predicate(task) for part in invariant_group.parts]:
                exist_invariant_groups_with_various_predicates = True
                for predicate in invariant_group.predicates:                    
                    # Esto debería hacerlo con lo de la biyección, pero no entiendo cómo
                    # TODO: No agregar una nueva función si ya existe una con el mismo predicado puede ser la solución?
                    if predicate not in [x.predicate for x in new_functions]:
                        new_function = create_functions(task, predicate, baggable_type)
                        print("HOLA",predicate, new_function.name)
                        new_functions.append(new_function)

        
        # De lo que está dentro de este if no estoy segura
        # If there is no invariant group with more than one predicate, we will create a function that counts
        # the objects of the bag, having as only argument the id of the bag
        if not exist_invariant_groups_with_various_predicates:
            for invariant_group in invariant_groups_with_1_predicate:
                for predicate in invariant_group.predicates:

                    # Esto debería hacerlo con lo de la biyección, pero no entiendo cómo
                    # TODO: No agregar una nueva función si ya existe una con el mismo predicado puede ser la solución?
                    # if predicate not in [x.predicate for x in new_functions]:
                    new_function = create_functions(task, predicate, baggable_type)
                    new_functions.append(new_function)
                    for arg in new_function.arguments:
                        if arg.type_name == baggable_type.object_type.name:
                            if not len(baggable_type.bag_predicates):
                                new_bag_predicate = create_bag_predicate_just_with_id(task, arg, baggable_type)
                                new_predicates.append(new_bag_predicate)
                # new_bag_predicate = create_bag_predicate_just_with_id(task, arg, baggable_type)
                # new_functions.append(new_function)

            # If there is more than one invariant group with only one predicate for a baggable type, 
        # we will create a bag predicate that contains the arguments of all of the predicates
        if exist_invariant_groups_with_1_predicate and exist_invariant_groups_with_various_predicates:
            predicates_to_bag = []
            for invariant_group in invariant_groups_with_1_predicate:
                for predicate in invariant_group.predicates:
                    predicates_to_bag.append(predicate)
                    print("invariant_group: ", [x.name for x in predicates_that_remain_the_same])

            for predicate in predicates_to_bag:
                #TODO: Organize this better
                if predicate not in [p.name for p in predicates_that_remain_the_same] and predicate not in [p.predicate for p in new_functions]:

                    new_function = create_functions(task, predicate, baggable_type)
                    print("HOLA",predicate, new_function.name)
                    new_functions.append(new_function)
                    for arg in new_function.arguments:
                        if arg.type_name == baggable_type.object_type.name:
                            if not len(baggable_type.bag_predicates):
                                new_bag_predicate = create_bag_predicate_just_with_id(task, arg, baggable_type)
                                new_predicates.append(new_bag_predicate)
                else:
                    if not len(baggable_type.bag_predicates):
                        new_bag_predicate = create_bag_predicate(task, predicates_to_bag, baggable_type)
                        new_predicates.append(new_bag_predicate)


        # If there is no invariant group with just one predicate, that means theres no property
        # of the baggable type that remains always the same.
        # We will create a bag just with the id of the bag, and count the objects of the bag
        # in the functions
        if not exist_invariant_groups_with_1_predicate:
            # We use any function of the baggable type to get the bag for the bag predicate
            any_function_of_this_baggable_type = baggable_type.functions[0]
            for arg in any_function_of_this_baggable_type.arguments:
    
                if arg.type_name == baggable_type.object_type.name:
                    # TODO: Buscar una mejor forma de asegurarme de que no se cree más de un bag_predicate para el mismo baggable_type
                    if not len(baggable_type.bag_predicates):
                        new_bag_predicate = create_bag_predicate_just_with_id(task, arg, baggable_type)
                        new_predicates.append(new_bag_predicate)

                elif arg.type_name in [typ.basetype_name for typ in arg.get_child_types(task.types)]:
                    for object in task.objects:
                        if baggable_type.object_type.name == object.type_name:
                            for function in task.functions:
                                for arg in function.arguments:
                                    if arg.type_name == baggable_type.object_type.name:
                                        if arg.is_baggable(baggable_types_list):
                                            bag_id = arg
                                        # if bag_id.name[0] != "?":
                                            # bag_id.name = "?" + bag_id.name

                    if not len(baggable_type.bag_predicates):
                        new_bag_predicate = create_bag_predicate_just_with_id(task, bag_id , baggable_type)
                        new_predicates.append(new_bag_predicate)

        # Final argument is the counter
        # less_than_predicate = macropredicate.add_count() # Mafe: Esto no sería necesario en numérico
        # new_predicates.append(less_than_predicate) 
        
        
        # See if macropredicate needs GTE system
        # macropredicate.see_if_type_needs_GTE_system() # Esto tampoco sería necesario 
 
        
        # Create macropredicate
        macropred = pddl.predicates.Predicate(macropredicate.name, macropredicate.args)
        # new_predicates.append(macropred) # Mafe: descomentar esto para volver a agregar su macropredicate
        baggable_type.macropredicate = macropredicate
        for bag in baggable_type.bags:
            bag.goal_macropredicate = macropredicate
        
        if options.writeout_reformulation_logic:
            print("BagPredicate added for ", baggable_type.object_type.name, "is", new_bag_predicate, end = "\n")



    task.predicates = list(OrderedDict.fromkeys(new_predicates))
    task.functions = list(OrderedDict.fromkeys(new_functions))




def create_functions(task, predicate, baggable_type):
    
    new_functions = []

    baggable_type_name = baggable_type.object_type.name

    function_arguments = []

    for pred in task.predicates:
        if pred.name == predicate:
            for arg in pred.arguments:
                if arg.type_name == baggable_type_name:
                    function_arguments.insert(0, arg)
                else:
                    function_arguments.append(arg)


    new_function = functions.MyFunction(task, function_arguments, baggable_type_name, predicate)

    # new_functions.append(new_function)

    baggable_type.functions.append(new_function)

    return new_function


def create_functions_just_with_id(task, predicate, bag_id, baggable_type):
    if options.writeout_reformulation_logic:
        print("Generating functions...")
    
    new_functions = []

    baggable_type_name = baggable_type.object_type.name

    function_arguments = [bag_id]
    # function_arguments = [baggable_type.object_type.name]

    new_function = functions.MyFunction(task, function_arguments, baggable_type_name, predicate)

    # new_functions.append(new_function)

    baggable_type.functions.append(new_function)

    return new_function



def create_bag_predicate(task, original_predicate, baggable_type):

    new_predicates = []

    baggable_type_name = baggable_type.object_type.name

    predicate_arguments = []

    if isinstance(original_predicate, pddl.predicates.Predicate):
        for pred in task.predicates:
            if pred.name == original_predicate:
                for arg in pred.arguments:
                    argument = arg.name + " - " + arg.type_name
                    # if arg.type_name == baggable_type_name:
                    predicate_arguments.append(argument)

    # Mafe: Esto es para cuando se agrega más de un predicado a la bolsa
    elif isinstance(original_predicate, list):
        for pred in task.predicates:
            for predi in original_predicate:
                if pred.name == predi:
                    for arg in pred.arguments:
                        # argument = arg.name + " - " + arg.type_name
                        argument = arg
                        # if arg.type_name == baggable_type_name:
                        if argument not in predicate_arguments:
                            if argument.type_name == baggable_type_name:
                                predicate_arguments.insert(0,argument)
                            else:
                                predicate_arguments.append(argument)


    new_predicate = pddl.predicates.Bag_Predicate(task, predicate_arguments, baggable_type, original_predicate)

    baggable_type.bag_predicates.append(new_predicate)
    new_predicates.append(new_predicate)

    # baggable_type.predicates.append(new_predicate)

    return new_predicate

def create_bag_predicate_just_with_id(task, bag_id, baggable_type):

    baggable_type_name = baggable_type.object_type.name

    predicate_arguments = [bag_id]
    # predicate_arguments = [baggable_type.object_type]

    new_predicate = pddl.predicates.Bag_Predicate(task, predicate_arguments, baggable_type)
    baggable_type.bag_predicates.append(new_predicate)

    # baggable_type.predicates.append(new_predicate)

    return new_predicate



    


def print_types_and_objects(task):
    for typ in task.types:
        print("Type", typ.name, "has the following objects: ", end = "")
        print(', '.join([x.name for x in task.objects if x.type_name == typ.name]))


def print_grounded_macropredicates(preds, terminus):
    for pred in preds:
        print("Grounded macropredicate added to", terminus, "state:", pred)
    print()



