import re
import copy
import pddl
from . import single_valued_checker
from . import mapping_printer
from . import bag_classes
import options



# Find objects of the same type which can be bagged 
def bag_objects(task, invariants, conditionalEffectGroups):
    
    types = []
    baggable_types_list = [] 
    goal_state_equivalences = []
    type_checker_list = single_valued_checker.Type_checker_list(task, invariants)
    if options.writeout_reformulation_logic:
        print("Fast Downward invariant groups: ", invariants)
        print()
	
    # For each type
    for object_type in task.types:
        # print("######################################holi#######################################################################")
        # print(object_type)
        # print([baggable_type.object_type for baggable_type in baggable_types_list])
        # print("#############################################################################################################")
        # Declare forward and/or backwards singleton sets for this type. Singletons are unprocessed objects, objects are in a grouped list when it has been processed
        singleton = [ [],[] ]
        grouped = [ [],[] ]

        
        # Ensure type is single-valued, indexable and all its objects are action equivalent
        if not type_checker_list.type_is_baggable(object_type, conditionalEffectGroups, [x.object_type.name for x in baggable_types_list]):
            if options.writeout_reformulation_logic:
                print()
            continue
        




        # Select objects of this object_type (objects which do not appear in the goal appear at the end) (because of the non-transitive property of initial state equivalence)
        objects_of_type = [x for x in task.objects if x.type_name == object_type.name]
        objects_of_type_in_goal = [x for x in objects_of_type if len([y for y in task.goal.parts if x.name in [z for z in y.args]])]
        singleton[0] = [x for x in objects_of_type if x in objects_of_type_in_goal] + [x for x in objects_of_type if not x in objects_of_type_in_goal]
        singleton[1] = copy.deepcopy(singleton[0])
        num_obj = len(singleton[0])
        if num_obj == 0:
            if options.writeout_reformulation_logic:
                print()
            continue
        
        type_checker = type_checker_list.get(object_type)
        object_checker_list = single_valued_checker.Object_checker_list(task, type_checker, invariants)
        
        
        # For each direction (fwd and bck)
        for direction in range(0, 2):
                
            # If we are enforcing backwards bagging then we don't need to waste time on forwards bagging    
            # Backwards bagging is necessary either way as we need to store GSE bags for solution translation
            if options.direction == 'bck' and direction == 0:
                continue
                
            if options.writeout_reformulation_logic:
                d = 'forward' if direction == 0 else 'backward'
                print('Comparing', object_type.name + "s", 'in', d, 'direction.')
            
            # Determine objects which can be merged in this direction
            for i in range(0, num_obj):
                
                
    	        # If element is null then it has already been grouped
                obj1 = copy.deepcopy(singleton[direction][i])
                if obj1 is None :
                    continue
                    
                
                # Remove this item from the singleton list and add to grouped list 
                singleton[direction][i] = None
                grouped[direction].append([obj1])
                
                
                # Can this object be merged with any of the other singletons?
                for j in range(i+1, num_obj):
                    obj2 = copy.deepcopy(singleton[direction][j])
                    if obj2 is not None and are_indistinguishable(obj1, obj2, direction, task, object_checker_list):
                        
                        # If so then remove from singleton list and add to grouped sublist
                        singleton[direction][j] = None
                        grouped[direction][-1].append(obj2)
                        
            
            
            if options.writeout_reformulation_logic and len(grouped[direction]) < num_obj:
                print('Type', object_type, 'in', d, 'direction has the following', len(grouped[direction]), 'equivalence classes:', grouped[direction])
            
        
        goal_state_equivalences = copy.deepcopy(grouped[1])
        # Mafe
        # If the type is baggable, we change its name to indicate that it is a bag
        # object_type.name += '_bag'
        bag_merged = find_best_partition(grouped[0], grouped[1], object_type, task, num_obj)
        if bag_merged is not None:
            
            bag_merged.goal_state_equivalences = goal_state_equivalences
            bag_merged.type_checker = type_checker
            baggable_types_list.append(bag_merged)

            types.append(object_type)
            if options.writeout_reformulation_logic:
                print('After partitioning, type', object_type, 'has', len(bag_merged.bags), 'bags')
        if options.writeout_reformulation_logic:
            print()
    

    
    # Remove the statics we just added from the goal                
    type_checker_list.remove_statics_from_goal()
    
    # Check that there are no bags which interact with each other
    # Mafe: I don't think this is necessary, bags can interact with each other if their arguments are not of the same type
    # baggable_types_list = remove_interacting_baggable_types(baggable_types_list, task)
    
    
    if options.writeout_reformulation_logic:    
        print('FINAL EQUIVALENCE CLASSES:')
        for entry in baggable_types_list:
            print(entry)
          
    # Return the list of bags and the type_checker_list object which contains invariant information
    task.solution_mapper.baggable_types_list = baggable_types_list
    return baggable_types_list, type_checker_list
                                                                                                                                                                                                                                                                                                                                                                                                                                       
                                                                                                                                                                                                                                                     
# obj1, obj2 of class pddl_types.TypedObject, fwd indicates direction of bagging                                                                 
def are_indistinguishable(obj1, obj2, bck, task, object_checker_list):
    

    # Terminus equivalence 
    if bck and not terminal_equivalent(obj1, obj2, task, True, object_checker_list):
        if options.writeout_reformulation_logic:
            print('Objects', obj1.name, 'and', obj2.name, 'are not goal-state equivalent.')
        return False
    if not bck and not terminal_equivalent(obj1, obj2, task, False, object_checker_list):
        #if options.writeout_reformulation_logic:
        #    print('Objects', obj1.name, 'and', obj2.name, 'are not initial-state equivalent.')
        return False
    
    if options.writeout_reformulation_logic:
        print('Objects', obj1.name, 'and', obj2.name, 'are being merged.')
    return True
    
    

    
# Initial state / goal equivalence 
def terminal_equivalent(obj1, obj2, task, bck, object_checker_list):
    #print('terminal_equivalent', obj1, obj2, bck)
    
    # Find terminus predicates with object 1 or object 2
    if(bck):
        terminal = task.goal.parts
    else:
        terminal = task.init

    obj1_preds = []
    obj2_preds = []
    for fact in [x for x in terminal if type(x) is pddl.conditions.Atom and not x.predicate == '=']:
    
        for i in range(0, len(fact.args)):
            arg = fact.args[i]
            if(arg == obj1.name):
                obj1_preds.append(get_ungrounded_predicate(fact, i))
            if(arg == obj2.name):
                obj2_preds.append(get_ungrounded_predicate(fact, i))

                                        
    # Goal equivalent if the two lists are equivalent
    obj1_preds.sort()
    obj2_preds.sort()
    if bck:
        return obj1_preds == obj2_preds
    
    
    # Initial state equivalent only if they are heading to goals from the same invariant groups 
    # (eg. if in goal shot1 has cocktail and shot2 is on table, then they cannot be described by the same goal macropredicate so we do not bag them)
    obj1_preds_goal = []
    obj2_preds_goal = []       
    for fact in [x for x in task.goal.parts if type(x) is pddl.conditions.Atom and not x.predicate == '=']:
    
        for i in range(0, len(fact.args)):
            arg = fact.args[i]
            if(arg == obj1.name):
                obj1_preds_goal.append(get_ungrounded_predicate(fact, i))
            if(arg == obj2.name):
                obj2_preds_goal.append(get_ungrounded_predicate(fact, i))
        
                                                  
    # Find all invariant groups which each of the objects goal predicates belong to
    obj1_invariant_groups = []
    obj2_invariant_groups = []
    for obj_pred in obj1_preds_goal:
        obj1_invariant_groups.append([x for x in object_checker_list.invariants if obj_pred[0] in x.predicates])
    for obj_pred in obj2_preds_goal:
        obj2_invariant_groups.append([x for x in object_checker_list.invariants if obj_pred[0] in x.predicates])
    obj1_invariant_groups.sort()
    obj2_invariant_groups.sort()
    
    
    
    # The two objects only initial state equivalent if their occurrences in the initial state are identical and they will later require the same goal macropredicate 
    #print(obj1, "invariants", obj1_invariant_groups, ";", obj2, "invariants", obj2_invariant_groups)
    if not(not len(obj1_invariant_groups) or not len(obj2_invariant_groups) or obj1_invariant_groups == obj2_invariant_groups):
        if options.writeout_reformulation_logic:
            print('Objects', obj1.name, 'and', obj2.name, 'do not share the same attributes in the goal state. These objects cannot be bagged.')
        return False

    if not(obj1_preds == obj2_preds):
        if options.writeout_reformulation_logic:
            print('Objects', obj1.name, 'and', obj2.name, 'are not initial-state equivalent.')
        return False
           
                    
    return True


        
        

# Greedy algorithm to merge forward and and backward bags. Iteratively selects largest bag until there are no objects left in either direction
def find_best_partition(fwd_bag, bck_bag, object_type, task, num_obj):
    #print('partition-bags', fwd_bag, bck_bag)
    
    
    
    # If user specified a direction then return bags from that direction
    if options.direction == 'bck':
        if len(bck_bag) == num_obj:
            return None
        bags = bag_classes.BaggableType(object_type)
        for objs in bck_bag:
            bags.add_bag(objs, task)
        return bags
        
    if options.direction == 'fwd':
        if len(fwd_bag) == num_obj:
            return None
        bags = bag_classes.BaggableType(object_type)
        for objs in fwd_bag:
            bags.add_bag(objs, task)
        return bags



    # Otherwise perform greedy algorithm on forward and backwards bags
    merged_bag = []
    bag1 = bck_bag
    bag2 = fwd_bag
    while bag1 and bag2:
    
        # Find largest equivalence class
        largest_class = bag1[0]
        largest_from = 1
        for e_class in bag1:
            if len(e_class) > len(largest_class):
                largest_class = e_class
        for e_class in bag2:
            if len(e_class) > len(largest_class):
                largest_class = e_class
                largest_from = 2
                
        # Move the class to the merged bag and remove objects of this class from other bag
        merged_bag.append(largest_class)
        if largest_from == 1:
            bag1.remove(largest_class)
            for e_class in bag2:
                to_remove = []
                for obj in e_class:
                    if any(obj_large.name == obj.name for obj_large in largest_class):
                        to_remove.append(obj)
                for rem in to_remove:
                   e_class.remove(rem)
            bag2 = [x for x in bag2 if x]
        else:
            bag2.remove(largest_class)
            for e_class in bag1:
                to_remove = []
                for obj in e_class:
                    if any(obj_large.name == obj.name for obj_large in largest_class):
                        to_remove.append(obj)
                for rem in to_remove:
                   e_class.remove(rem)
            bag1 = [x for x in bag1 if x]
    
                
    if len(merged_bag) == num_obj:
        return None
    bags = bag_classes.BaggableType(object_type)
    for objs in merged_bag:
        bags.add_bag(objs, task)
    return bags

                                            
# If there are 2 baggable types which interact with each other, and they each have 2 or more attributes, then remove the one with fewer objects
# from the baggable type list
def remove_interacting_baggable_types(baggable_types_list, task):
    # Mafe: Esto podría modificarlo para usarlo cuando hay varias bolsas para un tipo de objeto (por ejemplo, lo de color y size)
    cannot_bag_pairs = []
    for baggable_type_1 in baggable_types_list:
        invariants_of_type_1 = baggable_type_1.type_checker.invariants_of_this_type
        for baggable_type_2 in [x for x in baggable_types_list if x.object_type != baggable_type_1.object_type]:
            invariants_of_type_2 = baggable_type_2.type_checker.invariants_of_this_type
            
            
            for invariant_group in invariants_of_type_1:
                for part in invariant_group.parts:
                    rel_pred = [x for x in task.predicates if x.name == part.predicate][0]
                    
                    # If this is a binary predicate then look at the other argument
                    if len(rel_pred.arguments) == 2:
                        other_arg = rel_pred.arguments[[x for x in range(0,2) if not x in part.order][0]]
                        
                        # If the other argument's type is one of the supertypes of type_2, and each bag has > 1 attribute, then type_1 and type_2 cannot both be bagged
                        if other_arg.type_name in baggable_type_2.type_checker.supertypes and len(invariants_of_type_1) > 1 and len(invariants_of_type_2) > 1:
                            cannot_bag_pairs.append(tuple([baggable_type_1, baggable_type_2]))
                            


    # Remove from the list
    removed = []
    for pair in cannot_bag_pairs:
        candidate_to_remove_1 = pair[0]
        candidate_to_remove_2 = pair[1]
        
        if candidate_to_remove_1.object_type in removed or candidate_to_remove_2.object_type in removed:
            continue
        

        
        # Choose which one to remove
        remove_1 = len(candidate_to_remove_1.all_unbagged_objects) < len(candidate_to_remove_2.all_unbagged_objects)
        
        if remove_1:
            baggable_types_list = [x for x in baggable_types_list if not x.object_type == candidate_to_remove_1.object_type]
            removed.append(candidate_to_remove_1.object_type)
            if options.writeout_reformulation_logic:
                print("Cannot bag both", candidate_to_remove_1.object_type, "and", candidate_to_remove_2.object_type, "-> will not bag ", candidate_to_remove_1.object_type)
        else:
            baggable_types_list = [x for x in baggable_types_list if not x.object_type == candidate_to_remove_2.object_type]
            removed.append(candidate_to_remove_2.object_type)
            if options.writeout_reformulation_logic:
                print("Cannot bag both", candidate_to_remove_1.object_type, "and", candidate_to_remove_2.object_type, "-> will not bag ", candidate_to_remove_2.object_type)
        
        
    # Now modify the task so that the old objects have been removed and the new ones have been added
    for baggable_type in baggable_types_list:
        task.objects = [x for x in task.objects if not x.type_name == baggable_type.object_type.name]
        task.objects.extend(baggable_type.all_bagged_objects)
            
    
    return baggable_types_list
                                                                                        
                                                                                                                                                                                

# Creates a tuple (predicate, arg1, arg2, ... , arg_i-1, *X*, arg_i+1, ... , argn)
def get_ungrounded_predicate(fact, i):
    new_atom = [fact.predicate]
    for j in range(0, i):
        new_atom.append(fact.args[j])
    new_atom.append('*X*')
    for j in range(i+1, len(fact.args)):
        new_atom.append(fact.args[j])
    
    return tuple(new_atom)
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
       


    