import copy
import options
import pddl
import re
import sys
from collections import OrderedDict

from pddl import functions
from pddl import pddl_types
from . import single_valued_checker
from . import relation_mapping
from . import operator_splitter
from . import mapping_printer
from . import helper_functions
from . import bagged_operator


def bag_operators(baggable_types_list, task, type_checker_list, conditionalEffectGroups):
    

    # Take any baggable types which occur in conditional effects and transfer their preconditions, effects and parameters to the main action body 
    conditionalEffectClasses = move_baggable_conditional_effects_into_main(task, baggable_types_list, conditionalEffectGroups)


    # Convert operators into bagged format
    split_operators_into_subtypes(task, baggable_types_list, type_checker_list)
    variables_to_ground_mapping_list = transform_operators(task, baggable_types_list, type_checker_list, conditionalEffectClasses)
    task.solution_mapper.variables_to_ground_mapping_list = variables_to_ground_mapping_list
    
    # Split operators into cases of equality between parameters that could be grounded to the same object
    equality_mapper = split_operators_into_equality_classes(task, baggable_types_list)
    task.solution_mapper.equality_mapper = equality_mapper
    
    # Add GTE system to operators # MafeComentado
    # add_GTE_system(task, variables_to_ground_mapping_list, baggable_types_list)


    # Split operators into conditional effect cases
    split_operators_by_conditional_effects(task, conditionalEffectClasses, baggable_types_list)
    
    
    

def transform_operators(task, baggable_types_list, type_checker_list, conditionalEffectClasses):
    
    
    variables_to_ground_mapping_list_all = []
    baggable_ops = []
    for action in task.actions:
        
        #print("ACTION:", action.name)
        action_precond = tuple([action.precondition]) if not len(action.precondition.parts) else action.precondition.parts

        
        baggable_op = bagged_operator.BaggableOperator(action, task)
        
        action_names = [x.name for x in task.actions]
        goal_macropredicate_infomation = []
        for baggable_type in baggable_types_list:
        
            objects_of_type_in_action = [x for x in action.parameters if x.type_name == baggable_type.object_type.name]
            
            # Do we need to keep the old version of this action? eg. grasp action in barman needs one for shot and one for shaker
            for obj in objects_of_type_in_action:
                

                conditionalEffectClassesForActionAndParameter = [x for x in conditionalEffectClasses if x.action.name == action.name and x.param.name == obj.name]

                # Add preconditions/effects only for the complete macropredicate (not the partial ones yet)
                baggable_param = bagged_operator.BaggableParameter(obj, baggable_type, baggable_op, action, task, conditionalEffectClassesForActionAndParameter)
                param_needs_macropredicate = baggable_param.initialise_macropredicate_for_parameter()
                if not param_needs_macropredicate:
                    continue
                baggable_param.add_macropredicates_for_parameter()
                baggable_op.baggable_parameters.append(baggable_param)
              
 
        
        # Create goal macropredicates
        bagged_ops_to_add, variables_to_ground_mapping_list_new = add_goal_macropredicates(baggable_op, task, action_names)
        # for pos in range(len(bagged_ops_to_add)):
        #     print("\n\n\n\n bagged_ops_to_add", bagged_ops_to_add[pos].name,  "\n")
        # If this action needs to be reformulated then add to the list of operators to add
        baggable_ops.extend(bagged_ops_to_add)
        variables_to_ground_mapping_list_all.extend(variables_to_ground_mapping_list_new)
        
        # if len(baggable_ops):
        #     for pos in range(len(baggable_ops)):
        #         print("\n\n\n\n bagged_ops_to_add", baggable_ops[pos].name, "\n")
    
    
    # Remove the original space operators and replace them with the reformulated ones
    for reform_action in baggable_ops:
    # for i in range(len(baggable_ops)):
        # reform_action = baggable_ops[i]
        # print("\n\n\n\n task.actions", task.actions[i].name, reform_action.original_action_name, "\n")
        task.actions = [x for x in task.actions if x.name != reform_action.original_action_name]
        task.actions.append(reform_action.convert_to_pddl_action())
        # print("\n\n\n\n task.actions", len(task.actions), "\n")
    # for pos in range(len(task.actions)):
    #     print("\n\n\n\n task.actions", pddl.conditions.Conjunction.pddl_str(task.actions[pos].precondition), "\n")
    
    return variables_to_ground_mapping_list_all
        
  



    
def add_goal_macropredicates(baggable_op, task, action_names):
    
    #print('\n\nAction being modified', baggable_op.name)
    
    all_new_actions = [baggable_op]
    variables_to_ground_mapping_list_all = []
    
    
    # For each baggable parameter in the action
    for baggable_param in baggable_op.baggable_parameters:
        #print("\n\nThis param", baggable_param.parameter)
    
        # For each newly created grounding of the action
        new_actions = []
        for action in all_new_actions:
            #print("\tAdding goal macropredicates to action", action.name)
            
            # Create the goal macropredicates
            action_baggable_param = [x for x in action.baggable_parameters if x.parameter == baggable_param.parameter][0]
            new_actions_for_split, variables_to_ground_mapping_list = add_goal_macropredicates_for_parameter(action, action_baggable_param, task, action_names)
            #print("\tNew actions generated:", [x.name for x in new_actions_for_split])
            new_actions.extend(new_actions_for_split)
            variables_to_ground_mapping_list_all.extend(variables_to_ground_mapping_list)
            
        all_new_actions = new_actions
        #print("Current actions:", [x.name for x in all_new_actions])
        
     
    return all_new_actions, variables_to_ground_mapping_list_all
   
 
def add_goal_macropredicates_for_parameter(baggable_op, baggable_param, task, action_names):


    #print("Action:", baggable_op.name)

    all_new_actions = []
    variables_to_ground_mapping_list_all = []
    variables_to_ground_mapping_list_bag_groundings = []

    # If there is more than 1 type of goal macropredicate then we ground each goal-macropredicate-containing operator to the bag 
    ground_ops_to_bag = len(baggable_param.baggable_type.goal_macropredicates) > 1
    needs_splitting = False # Do we definitely require this operator to be split into different groundings. We don't need to if all splits are equivalent. Won't know until later
    
    
    # For each goal-macropredicate of this type
    original_actions_to_keep = []
    new_actions_for_this_goal_macropredicate = []
    for goal_macropredicate in [baggable_param.baggable_type.macropredicate] + baggable_param.baggable_type.goal_macropredicates:
        
        
        
        # If there is a GTE system then the goal is described using desired-count predicates in the initial state
        # If not then the goal is described in the goal state
        relevant_goal_macropredicates = [x for x in task.goal.parts if type(x) is pddl.conditions.Atom and x.predicate == goal_macropredicate.name] if (not goal_macropredicate.needs_GTE) else [x for x in task.init if type(x) is pddl.conditions.Atom and x.predicate == goal_macropredicate.desired_count_goal_macropredicate_name and not x.args[-1] == [x for x in goal_macropredicate.counts if x.number == 0][0].number_object.name]
        #print("This macropredicate:", goal_macropredicate.name, relevant_goal_macropredicates)
        
        
        # Find variables in this macropredicate which need to be grounded in order to generate goal macropredicates
        variables_to_ground_mapping_list = baggable_param.get_variables_to_ground_for_goal_macropredicates(relevant_goal_macropredicates, goal_macropredicate)
        
        # Generate the goal-macropredicate preconditions and effects by grounding these variables
        goal_preconditions, count_mapping, params_to_add = baggable_param.add_precondition_for_goal_macopredicate(goal_macropredicate, variables_to_ground_mapping_list)

        if not len(goal_preconditions):
        
            # If no goal-macropredicate preconditions/effects are required then we may still need to ground the operator to each bag with this macropredicate in the goal to make the operator applicable
            if ground_ops_to_bag:
                #print("Non goal macropredicate, grounding bags", [x.bagname for x in baggable_param.baggable_type.bags if x.goal_macropredicate is not None and x.goal_macropredicate.name == goal_macropredicate.name], "for", baggable_op.name)
                all_new_actions.extend(baggable_op.ground_to_bags(baggable_param.parameter, [x.bagname for x in baggable_param.baggable_type.bags if x.goal_macropredicate is not None and x.goal_macropredicate.name == goal_macropredicate.name], variables_to_ground_mapping_list_bag_groundings, action_names))
            continue
            
            
        needs_splitting = True  
        goal_effects = baggable_param.add_effects_for_goal_macopredicate(goal_macropredicate, count_mapping, variables_to_ground_mapping_list)
        param_to_ground = variables_to_ground_mapping_list[0].variable
        variables_to_ground_mapping_list_all = variables_to_ground_mapping_list_all + variables_to_ground_mapping_list
        
        
        print("Yes", baggable_op.name, "does need goal macropredicates", goal_preconditions, "Effects", goal_effects)
        
        
        # For each parameter in this action we are to ground in the goal-macropredicates
        new_actions_for_this_parameter = []
        ungrounded_op = copy.deepcopy(baggable_op)
        maps_with_this_param = [x for x in variables_to_ground_mapping_list if x.variable.name == param_to_ground.name]
        
        #print("Parameter of interest is", param_to_ground.name)
        
        
        
        # Add the preconditions and effects now if the target is not a variable
        if str(param_to_ground.name)[0] != "?":
            #print("Not variable")
            new_actions_for_this_parameter = [] if ground_ops_to_bag else [baggable_op]
            if params_to_add[0].name in [x.name for x in baggable_op.parameters]:
                break
            baggable_op.parameters = baggable_op.parameters + params_to_add
            parts = list(baggable_op.precondition.parts)
            parts = parts + copy.deepcopy(goal_preconditions)
            baggable_op.precondition.parts = tuple(parts)
            baggable_op.effects = baggable_op.effects + [pddl.effects.Effect([], pddl.conditions.Truth(), copy.deepcopy(x)) for x in goal_effects if not x is None]
            
            if ground_ops_to_bag:
                #print("Constant objects, grounding bags", [x.bagname for x in baggable_param.baggable_type.bags if x.goal_macropredicate is not None and x.goal_macropredicate.name == goal_macropredicate.name], "for", baggable_op.name)
                new_actions_for_this_parameter.extend(baggable_op.ground_to_bags(baggable_param.parameter, [x.bagname for x in baggable_param.baggable_type.bags if x.goal_macropredicate is not None and x.goal_macropredicate.name == goal_macropredicate.name], variables_to_ground_mapping_list_bag_groundings, action_names))
        
        
        
        # Otherwise modify the original action by grounding the attribute parameter
        #print("Current action split:", baggable_op.name)
    
        # If one action is grounded for every object of that type, remove ungrounded action
        else:
            keep_ungrounded_action = True
            neq_preconds = []
            if len(variables_to_ground_mapping_list) == maps_with_this_param[0].num_objects or baggable_op.name in [x.name for x in original_actions_to_keep]:
                keep_ungrounded_action = False
    
    
            # For each object in the goal state this parameter can be grounded to
            for variable_to_ground_map in maps_with_this_param:
        
                #print("Variable to ground:", variable_to_ground_map.ground_to)
            
                # If there is a neq precondition between this variable and this grounding, then skip
                neq_precond = [x for x in baggable_op.precondition.parts if type(x) is pddl.conditions.NegatedAtom and x.predicate == "=" and variable_to_ground_map.ground_to in x.args and param_to_ground.name in x.args]
                if len(neq_precond):
                    #print("neq", neq_precond)
                    continue
    
                # Create grounded action
                new_action = copy.deepcopy(baggable_op)
            
                #print("Grounded to", new_action.name, new_action.parameters , ';', variable_to_ground_map.ground_to, "\n\n\n")
            
            
                # Add preconditions, effects and parameters
                new_action.parameters = new_action.parameters + params_to_add
                if not len(new_action.precondition.parts) and len(goal_preconditions):
                    new_action.precondition.parts = [new_action.precondition] + copy.deepcopy(goal_preconditions)
                else:
                    new_action.precondition = pddl.conditions.Conjunction(list(new_action.precondition.parts) + copy.deepcopy(goal_preconditions))
                new_action.effects = new_action.effects + [pddl.effects.Effect([], pddl.conditions.Truth(), copy.deepcopy(x)) for x in goal_effects if not x is None]
                new_actions_for_this_parameter.append(new_action)
            
                # Ground the action
                new_action.ground_atoms_for_goal(variable_to_ground_map, action_names)
            
               # print("GROUNDED", new_action.name)
            
                # Add neq preconditions to ungrounded action (if there is one)
                if keep_ungrounded_action:
                    neq_preconds.append(pddl.NegatedAtom('=', [variable_to_ground_map.variable.name, variable_to_ground_map.ground_to]))
               
            
            # Create ungrounded action if appropriate   
            if keep_ungrounded_action:   
                if not len(baggable_op.precondition.parts) and len(neq_preconds):
                    ungrounded_op.precondition.parts = [ungrounded_op.precondition] + neq_preconds
                else:
                    ungrounded_op.precondition = pddl.conditions.Conjunction(list(ungrounded_op.precondition.parts) + neq_preconds)
                new_actions_for_this_parameter.append(ungrounded_op)
        
        
        # Ground bag if necessary
        new_ops = [] if ground_ops_to_bag else new_actions_for_this_parameter
        for split_action in [x for x in new_actions_for_this_parameter]:
            
            # Ground the operator to each bag
            if ground_ops_to_bag:
               # print("Variable objects, grounding bags", [x.bagname for x in baggable_param.baggable_type.bags if x.goal_macropredicate is not None and x.goal_macropredicate.name == goal_macropredicate.name], "for", split_action.name)
                new_ops.extend(split_action.ground_to_bags(baggable_param.parameter, [x.bagname for x in baggable_param.baggable_type.bags if x.goal_macropredicate is not None and x.goal_macropredicate.name == goal_macropredicate.name], variables_to_ground_mapping_list_bag_groundings, action_names))
        new_actions_for_this_parameter = new_ops
        
        # Update list of new actions
        new_actions_for_this_goal_macropredicate.extend(new_actions_for_this_parameter)
    
    if needs_splitting:
        #print("Adding new actions", [x.name for x in new_actions_for_this_goal_macropredicate])
        all_new_actions.extend(new_actions_for_this_goal_macropredicate)     
    
    all_new_actions = all_new_actions if len(all_new_actions) else [baggable_op]
    
    
    
    return all_new_actions, variables_to_ground_mapping_list_all + variables_to_ground_mapping_list_bag_groundings
    

    
    
# ASSUMPTION: !=(constant, constant) happens sometimes  
# ASSUMPTION: goal may be satisfied if one of the goal attributes is satisfied but not the rest. Need to ground the ?dc in some operators (or something like that)
# Maybe ground remaining desired counts to zero in initial state
# Mafe: Esta función no la necesito
def add_GTE_system(task, variables_to_ground_mapping_list, baggable_types_list):
    
    
    if options.writeout_reformulation_logic:
        print('Adding GTE system to types:', ', '.join([x.macropredicate.typ.name for x in baggable_types_list if x.macropredicate.needs_GTE]))
    
    new_actions = []
    for action in task.actions:
        
        #print("ACTION:", action.name)
        
        split_actions = [action]
        action_has_been_split = False


		# For each baggable type
        for baggable_type in baggable_types_list:
            #print("i=", i)

            objects_of_type_in_action = [x for x in action.parameters if x.type_name == baggable_type.object_type.name] + get_grounded_bags_from_operator(action, task, baggable_type.object_type.name)
            
            # Find which macropredicate style (if any) is used and generate its GTE actions
            GTE_actions = None
                
            # For each style of macropredicate of this type (full or partial)
            for macropredicate_style in [baggable_type.macropredicate] + baggable_type.goal_macropredicates:
                #print("macropredicate_style", macropredicate_style.name)
                
                # Find each precondition macropredicate (of this type) in this action that could be grounded with a desired count macropredicate (whose count > 0)
                preconds_indices_to_split_over = get_GTE_action_preconditions_to_factor_over(task, action, macropredicate_style)
                for index in preconds_indices_to_split_over:
                    new_splits = []
                    for split_action in split_actions:
                        #print("Current split action", split_action, "from pool of", [x.name for x in split_actions])
                         
                        GTE_actions = macropredicate_style.add_gte_macropredicates_to_action(split_action, index, task, [x.name for x in new_actions])
                        if not GTE_actions is None:
                            #print("GTE actions added:", [x.name for x in GTE_actions])
                            new_splits = new_splits + GTE_actions
                            action_has_been_split = True
                        #else:
                            #print("NOT NEEDED")
            
            
                #if not GTE_actions is None:
                   # print("GTE actions added:", [x.name for x in GTE_actions])
                   # new_splits = new_splits + GTE_actions
                    #action_has_been_split = True
        
            
                    if len(new_splits):
                        #print("New splits are",  new_splits)   
                        split_actions = new_splits
            
        
        if action_has_been_split:
            #print("action has been split", split_actions)
            new_actions = new_actions + split_actions
        else:
            #print("action has NOT been split", split_actions)
            new_actions.append(action)
    
    task.actions = new_actions        
                    

# Mafe: Esta función no la necesito             
def get_GTE_action_preconditions_to_factor_over(task, action, macropredicate):    
    

    # We need to split GTE operators over this factor
    action_macropred_preconds = [x for x in action.precondition.parts if x.predicate is macropredicate.name]
    nonzero_desired_inits = [x for x in task.init if type(x) is pddl.conditions.Atom and x.predicate is macropredicate.desired_count_goal_macropredicate_name and not x.args[-1] == [x.number_object.name for x in macropredicate.counts if x.number == 0][0]]
    preconds_indices_to_split_over = []
    for j in range(0, len(action_macropred_preconds)):
    
        #print("Precond = ", action_macropred_preconds[j])
        for des in nonzero_desired_inits:
        
            #print("Desired = ", des)
        
            can_ground_to = True
            
            # The desired predicate can be grounded to the action's macropredicate iff all precond arguments belong to the respective des arg supertype or objects are equal
            for arg_index in range(1, len(action_macropred_preconds[j].args)-1):
            

                j_arg = action_macropred_preconds[j].args[arg_index]
                des_arg = des.args[arg_index]
                #print("J arg = ", j_arg, " Des arg = ", des_arg)
                j_type = [x.type_name for x in action.parameters if x.name == j_arg]
                
                if not len(j_type): # If the precond is already grounded then see if des arg equals it
                    
                    if des_arg != j_arg:
                        can_ground_to = False
                        #print("1 THIS ACTION DOES NOT NEED ANY GTE FOR", action_macropred_preconds[j], " WRT ", des)
                        break
                
                else: # If precond arg is not grounded then see if its arg type belongs to des args supertype
                
                    
                    des_type = [x.type_name for x in task.objects if x.name == des_arg][0]
                    des_supertype = helper_functions.get_supertypes([x for x in task.types if x.name == des_type][0], task)
                    #print("Des args supertype: ", des_supertype, " j arg type ", j_type[0])
                    if not j_type[0] in des_supertype:
                        can_ground_to = False
                        #print("2 THIS ACTION DOES NOT NEED ANY GTE FOR", action_macropred_preconds[j], " WRT ", des)
                        break
            
            
            if can_ground_to:
                #print("XXX Precondition ", action_macropred_preconds[j], " need to be split over. Adding index ", j)
                preconds_indices_to_split_over.append(j)
                break
                
    #print("For action ", action.name, " returning ", preconds_indices_to_split_over, "\n")
    return preconds_indices_to_split_over
                    
                    
                                                                                
                    
def get_grounded_bags_from_operator(action, task, bag_type):

    bags_to_return = []
    bag_objects = [x for x in task.objects if x.type_name == bag_type]
    for prec in action.precondition.parts:
        for bag_object in bag_objects:
            if bag_object.name in prec.args:
                bags_to_return.append(bag_object)
    
    return list(OrderedDict.fromkeys(bags_to_return))
                            
                                                
                                                                    
                                                                                                            
def split_operators_into_equality_classes(task, baggable_types_list):

    equality_mapper = []
    for action in [x for x in task.actions if x.precondition.parts is not None]:
    
        action_splitter = operator_splitter.splitter(action, task)
        
        # 1) Build equivalence pairs of parameters
        equivalence_pairs = action_splitter.build_parameter_equivalence_pairs(baggable_types_list)
                                                           
                
        # 2) Split over each equivalence class
        split_actions = [action]
        task.actions = [x for x in task.actions if not x is action]
        action_names = [x.name for x in task.actions]
        for pair in equivalence_pairs:
        
        
            
            new_splits = []
            for split_action in split_actions:
            
            
                # Confirm that the splits are sitll needed for this pair (one of the previous pairs may have affected it)
                need_split = pair.validate_pair(split_action)
                if not need_split:
                    new_splits.append(split_action)
                    continue
                
                # We have one operator where the two macropreds have the same attributes (we increment/decrement the count by 2).
                #print("Creating eq operator")
                new_splits.append(pair.create_eq_operator(copy.deepcopy(split_action), action_names))
            
                # We may also have one operator where the two macropreds have different attributes (increment/decrement by 1)
                #print("Creating neq operator")
                new_splits.extend(pair.create_neq_operator(copy.deepcopy(split_action), action_names))
                
            
            split_actions = new_splits
        
        
        # Tidy the operators
        for split_action in split_actions:
            
            if len(split_action.precondition.parts):
            
            
                # Remove duplicate preconditions
                split_action.precondition.parts = list(OrderedDict.fromkeys(split_action.precondition.parts))
                
                
                # Remove neq (=) preconds which apply to bags
                for bag_variable in list(OrderedDict.fromkeys([x.args[0] for x in split_action.precondition.parts if x.predicate in [y.macropredicate.name for y in baggable_types_list]])):
                    neq_precond = [x for x in split_action.precondition.parts if type(x) is pddl.conditions.NegatedAtom and x.predicate == "=" and bag_variable in x.args and bag_variable in x.args]
                    split_action.precondition.parts = [x for x in split_action.precondition.parts if not x in neq_precond]
            
            
                # Replace all new not equals (=%) preconds with the normal not equals (=) 
                new_neq = [x for x in split_action.precondition.parts if type(x) is pddl.conditions.NegatedAtom and x.predicate == "=%"]
                for atom in new_neq:
                    atom.predicate = "="
                
                
                # Remove all new equals preconds and replace all instances of the second argument with the first one
                new_equals = [x for x in split_action.precondition.parts if type(x) is pddl.conditions.Atom and x.predicate == "=%"]
                split_action.precondition.parts = [x for x in split_action.precondition.parts if not x in new_equals]
                for equal in new_equals:
                    operator_splitter.splitter.replace_argument_with(equal.args[1], equal.args[0], split_action.precondition.parts)
                    operator_splitter.splitter.replace_argument_with(equal.args[1], equal.args[0], [x.literal for x in split_action.effects if type(x) is not pddl.f_expression.Assign])
                    
            
            
            
                # Remove redundant baggable parameter names from the parameter list
                for macropred in [x.macropredicate for x in baggable_types_list]:
                    for param_name in [x.name for x in split_action.parameters if x.type_name == macropred.typ.name]:
                    
                                        
                        # If parameter not used then remove it. If it has been merged with another parameter (through equality) then we must record this for solution transformation
                        if not param_name in [y.args[0] for y in split_action.precondition.parts if y.predicate == macropred.name] and not param_name in [y.literal.args[0] for y in split_action.effects if type(y) is not pddl.f_expression.Assign and y.literal.predicate == macropred.name]:
                            split_action.parameters = [x for x in split_action.parameters if not x.name == param_name]
                            equality_args_with_param = [x.args for x in split_action.precondition.parts if type(x) is pddl.conditions.Atom and x.predicate == "=%" and param_name in x.args]
                            if len(equality_args_with_param):
                                equal_to = [z for z in equality_args_with_param[0] if z != param_name]
                                if len(equal_to):
                                    equality_mapper.append(mapping_printer.BagEqualityMapper(split_action.name, equal_to[0], param_name))
            
                
                
                    
               
            task.actions.append(split_action)
            
    return equality_mapper
        
        

          
            
# If an operator parameter is a supertype of a baggable type, then split the operator so that there is one operator for each child subtype of the original parameter type         
def split_operators_into_subtypes(task, baggable_types_list, type_checker_list):
    
    # Split each operator based off parameter types
    new_task_actions = copy.deepcopy(task.actions)
    baggable_types = [x.object_type for x in baggable_types_list]
    for action in task.actions:
    
        actions_to_check = [action]
        actions_to_add = [action]
        param_index = 0
        for action_to_check in actions_to_check:
            new_task_actions = [x for x in new_task_actions if not x.name == action_to_check.name]
            
            for p in range(param_index, len(action_to_check.parameters)):
                
                param = action_to_check.parameters[p]
                new_actions = split_tree(task, baggable_types, type_checker_list, param.type_name, action_to_check, p, [], action_to_check.name, new_task_actions)
                
                # If there is still only 1 action, move onto next parameter
                if len(new_actions) < 2:
                    continue

                # Otherwise we repeat this process for all the other parameters
                actions_to_add = [x for x in actions_to_add if x.name != action_to_check.name] + new_actions
                for a in new_actions:
                    actions_to_check.append(a)
                
                param_index = p
                break
            
        
        new_task_actions = new_task_actions + actions_to_add    
    task.actions = new_task_actions
            
                    

# Keep splitting until this type is not in some baggable objects supertype list
def split_tree(task, baggable_types, type_checker_list, current_type, action, p, accumulative_names, original_name, list_of_actions):
    
    
    children = [x.name for x in task.types if x.basetype_name == current_type]
    if len(children) and len([x for x in baggable_types if current_type in type_checker_list.get([y for y in task.types if y.name == x.name][0]).supertypes]):
        to_return = []
        for child in children:
            child_action = copy.deepcopy(action)
            child_action.name = helper_functions.create_unique_name(original_name + '#' + child, [x.name for x in list_of_actions if not x is None] + accumulative_names)
            child_action.parameters[p].type_name = child
            accumulative_names = accumulative_names + [child_action.name]
            if options.writeout_reformulation_logic:
                print('Adding new action', re.sub("[#]", "-", child_action.name), 'for', original_name) 
            to_return = to_return + split_tree(task, baggable_types, type_checker_list, child, child_action, p, accumulative_names, original_name, list_of_actions)
        
        return to_return
    
    return [action]
        

# conditionalEffectGroups has information on which conditional effects belonged to the same group in the original pddl domain 
# (since FD splits them up so each conditional effect has 1 effect)
# Creates and object 'conditionalEffectClasses' which informs the operator bagger what to name the count variables
def move_baggable_conditional_effects_into_main(task, baggable_types_list, conditionalEffectGroups):


    if conditionalEffectGroups is None:
        return []
    

    baggable_types = [x.object_type for x in baggable_types_list]
    conditionalEffectClasses = []
    if conditionalEffectGroups is not None:
        for condEffGroupObj in conditionalEffectGroups:

            action = [x for x in task.actions if x.name == condEffGroupObj[0]][0]
            conditionalEffectGroups = condEffGroupObj[1]


            # Remove all conditional effects with baggable types from the action
            for baggable_typ in baggable_types:
                action.effects = [x for x in action.effects if (not len(x.parameters)) or (len(x.parameters) and not baggable_typ.name in [y.type_name for y in x.parameters])]

        

            # Move any preconditions, effects and parameters from the conditional effect groups to the main body of the action
            if conditionalEffectGroups is not None:
                for condEffGroup in conditionalEffectGroups:


                    # Parameters
                    for param in condEffGroup.parameters:
                        action.parameters.append(param)
                        conditionalEffectClasses.append(operator_splitter.conditionalEffectSplitter(action, param))


                    # Preconditions
                    precond_atoms = condEffGroup.condition.parts if len(condEffGroup.condition.parts) else [condEffGroup.condition]
                    newPreconds = list(action.precondition.parts) if len(action.precondition.parts) else [action.precondition]
                    for precond in precond_atoms:
                        newPreconds.append(precond)
                    action.precondition  = pddl.conditions.Conjunction(newPreconds)


                    # Effects
                    for effect in condEffGroup.literal:
            
                        effect = pddl.effects.Effect([], pddl.conditions.Truth(), effect)
                        action.effects.append(effect)



    return conditionalEffectClasses


# TODO: what there is forall precondition but no effect 
def split_operators_by_conditional_effects(task, conditionalEffectClasses, baggable_types_list):

    if conditionalEffectClasses is None:
        return


  
    for conditionalEffectClass in conditionalEffectClasses:

        baggableType = [x for x in baggable_types_list if x.object_type.name == conditionalEffectClass.param.type_name]
        if not len(baggableType):
            continue
        baggableType = baggableType[0]

        actions = [x for x in task.actions if re.sub("([#]|[%]|[$]|[&]|[+]).+", "", x.name) == conditionalEffectClass.action.name]

        for action in actions:

       	    
            # Remove the count variables from action parameters
            action.parameters = [x for x in action.parameters 	if x.name != conditionalEffectClass.num_object_variable_name_precond 
                                and x.name != conditionalEffectClass.less_number_variable_name_precond
                                and x.name != conditionalEffectClass.num_object_variable_name_effect
                                and x.name != conditionalEffectClass.more_number_variable_name_effect]
            

            # Remove less-than predicates
            precond_atoms = list(action.precondition.parts) if len(action.precondition.parts) else [action.precondition]
            precond_atoms = [x for x in precond_atoms if x.predicate != conditionalEffectClass.less_than_pred_name]
            
            action.precondition.parts = tuple(precond_atoms)
            
            """Enumerate all combinations of count changes for each change size (the change size is the number of times the forall cycled)

                     Change in effects, change in preconds
                c = 1:
                       0->1; 1->0
                       0->1; 2->2
                       ...
                       N-1->N; 1->0
                c = 2:
                       0->2; 2->0
                       ...
                       ...
                c = N:
                       ...
                       0->N; N->0
            """


            action_clones = []
            N = baggableType.get_max_bag_size()
            for c in range(1, N+1):
                for lowerEffNum in range(0, N-c+1):
                    lowerEffNum_num_obj_name = [x.number_object.name for x in baggableType.macropredicate.counts if x.number == lowerEffNum][0]
                    upperEffNum_num_obj_name = [x.number_object.name for x in baggableType.macropredicate.counts if x.number == lowerEffNum+c][0]
                    for upperPrecondNum in range(c, N+1-lowerEffNum):
                        upperPrecondNum_num_obj_name = [x.number_object.name for x in baggableType.macropredicate.counts if x.number == upperPrecondNum][0]
                        lowerPrecondNum_num_obj_name = [x.number_object.name for x in baggableType.macropredicate.counts if x.number == upperPrecondNum-c][0]
                        #print("c =", c, ":", str(lowerEffNum), "->", str(lowerEffNum+c), ";", str(upperPrecondNum), "->", str(upperPrecondNum-c))

                        # Create a new action object
                        split_action = copy.deepcopy(action)
                        action_clones.append(split_action)



                        # Set the name of the new action
                        split_action.name = helper_functions.create_unique_name(action.name + "+CE+c+" + str(c) + "+" + str(lowerEffNum) + "+" + str(upperPrecondNum), [x.name for x in task.actions] + [x.name for x in action_clones])


                        # Change all references to number variables into the grounded number
                        precond_atoms = list(split_action.precondition.parts) if len(split_action.precondition.parts) else [split_action.precondition]
                        helper_functions.replace_argument_with(conditionalEffectClass.num_object_variable_name_effect, lowerEffNum_num_obj_name, precond_atoms)
                        helper_functions.replace_argument_with(conditionalEffectClass.more_number_variable_name_effect, upperEffNum_num_obj_name, precond_atoms)
                        helper_functions.replace_argument_with(conditionalEffectClass.num_object_variable_name_precond, upperPrecondNum_num_obj_name, precond_atoms)
                        helper_functions.replace_argument_with(conditionalEffectClass.less_number_variable_name_precond, lowerPrecondNum_num_obj_name, precond_atoms)
                        split_action.precondition.parts = tuple(precond_atoms)


                        helper_functions.replace_argument_with(conditionalEffectClass.num_object_variable_name_effect, lowerEffNum_num_obj_name, [x.literal for x in split_action.effects if not len(x.parameters)])
                        helper_functions.replace_argument_with(conditionalEffectClass.more_number_variable_name_effect, upperEffNum_num_obj_name, [x.literal for x in split_action.effects if not len(x.parameters)])
                        helper_functions.replace_argument_with(conditionalEffectClass.num_object_variable_name_precond, upperPrecondNum_num_obj_name, [x.literal for x in split_action.effects if not len(x.parameters)])
                        helper_functions.replace_argument_with(conditionalEffectClass.less_number_variable_name_precond, lowerPrecondNum_num_obj_name, [x.literal for x in split_action.effects if not len(x.parameters)])


      
            # Remove the original action and add the new ones to task
            task.actions = [x for x in task.actions if x.name != action.name]
            task.actions = task.actions + action_clones
            

def bag_actions(baggable_types_list, task, type_checker_list, conditionalEffectGroups):
    """" For each action, checks every predicate at its precondition and effect, and if it has
    an object of a baggable type, it replaces it with a bag-predicate or a function, depending
    if it this the predicate from which the bag-predicate or the function was created"""

    
    # For each action
    for action in task.actions:
        # Store the original effects as a list of each effect
        original_effects = [effect for effect in action.effects]
        # Store the original precondition as a list of its parts
        if len(action.precondition.parts):
            original_precondition_parts = action.precondition.parts
        else:
            original_precondition_parts = [action.precondition]

        # To store the predicates that have arguments of the baggable type and are used to
        # create the bag predicates and the functions
        baggable_original_predicates = [] 
        new_precondition_parts = []
        new_effects = []

        for baggable_type in baggable_types_list:
            # Each baggable type has only one bag predicate
            try:
                bag_predicate_of_this_type = baggable_type.bag_predicates[0]
            except:
                print("The type ", baggable_type.object_type.name, " has no bag predicate")

            
            original_predicates_of_this_bag_predicate = bag_predicate_of_this_type.original_predicate
            functions_of_this_baggable_type = [function.predicate for function in baggable_type.functions]

            baggable_original_predicates.extend(original_predicates_of_this_bag_predicate)
            baggable_original_predicates.extend(functions_of_this_baggable_type)


            ############################################
            #### Reformulation of the precondition: ####
            ############################################
            new_precondition_parts = precondition_reformulation(task, action, baggable_type, original_precondition_parts, original_predicates_of_this_bag_predicate,\
                                        functions_of_this_baggable_type, bag_predicate_of_this_type, new_precondition_parts, baggable_types_list)
       

            ############################################
            ####### Reformulation of the effects: ######
            ############################################
            new_effects = effects_reformulation(task, action, baggable_type, original_effects, original_predicates_of_this_bag_predicate,\
                            functions_of_this_baggable_type, bag_predicate_of_this_type, new_effects)
            
        # Dictionary to store the type of each argument, because the arguments are strings instead of TypedObjects
        type_of_atoms_argumets = {} 
        # else: # If the predicate is not baggable, we add it just at it is
        # print("baggable_original_predicates: ", baggable_original_predicates)
        for precondition_part in original_precondition_parts:

            # Storing the types of the arguments of the atoms
            for atom_argument in precondition_part.args:
                for action_parameter in action.parameters:
                    if atom_argument == action_parameter.name:
                        # if the atom has an argument of the baggable type
                        type_of_atoms_argumets[atom_argument] = action_parameter

            if precondition_part.predicate not in baggable_original_predicates:

                # Hack for domains that compare baggable types of the same bag
                # If the precondition compares objects of a baggable type, we'll delete that precondition

                if not len(precondition_part.args):
                    if precondition_part not in new_precondition_parts:
                        new_precondition_parts.append(precondition_part)
                for arg in precondition_part.args:
                    if arg in type_of_atoms_argumets:
                        if pddl_types.TypedObject.is_baggable(type_of_atoms_argumets[arg], baggable_types_list) and precondition_part.predicate == "=":
                            pass
                        else:
                            if precondition_part not in new_precondition_parts:
                                new_precondition_parts.append(precondition_part)




            
        # else: # If the predicate is not baggable, we add it just at it is
        for effect in original_effects:
            if effect.literal.predicate not in baggable_original_predicates: 
                new_effects.append(effect)

        
        # Change effect for the reformulated effect
        action.effects = new_effects

        # Change precondition for the reformulated precondition
        if len(action.precondition.parts):
            action.precondition.parts =  new_precondition_parts
        else:
            if len(new_precondition_parts) > 1:
                action.precondition = pddl.conditions.Conjunction(new_precondition_parts)
            elif len(new_precondition_parts) == 1:
                action.precondition = new_precondition_parts[0]

    

def precondition_reformulation(task, action, baggable_type, original_precondition_parts, original_predicates_of_this_bag_predicate,\
                                functions_of_this_baggable_type, bag_predicate_of_this_type, new_precondition_parts, baggable_types_list):
    """"Given the preconditions of an action, it reformulates them to add the bag-predicates and the functions"""
    # print(action.name)
    
    # To store the atoms that are in the same bag. It has the form: {bag_object: [atom1, atom2, ...]}
    atoms_with_baggable_arguments_of_the_same_bag = {}
    # Since the atoms' arguments do not have a type associated, we match each argument 
    # with the parameters of the action and store here the type of each argument of the atoms 
    type_of_atoms_argumets = {} 

    for precondition_part in original_precondition_parts:
        ####################################
        ############ PREDICATES ############
        ####################################



        for atom_argument in precondition_part.args:
            for action_parameter in action.parameters:
                if atom_argument == action_parameter.name:
                    # if the atom has an argument of the baggable type
                    type_of_atoms_argumets[atom_argument] = action_parameter.type_name

        if precondition_part.predicate in original_predicates_of_this_bag_predicate:
            for atom_argument in precondition_part.args:
                for action_parameter in action.parameters:
                    # if the atom has an argument of the baggable type
                    # type_of_atoms_argumets[atom_argument] = action_parameter.type_name
                    if atom_argument == action_parameter.name: 
                        if action_parameter.type_name == baggable_type.object_type.name:
                            if atoms_with_baggable_arguments_of_the_same_bag.get(atom_argument) is None:
                                atoms_with_baggable_arguments_of_the_same_bag[atom_argument] = []
                            atoms_with_baggable_arguments_of_the_same_bag[atom_argument] = atoms_with_baggable_arguments_of_the_same_bag[atom_argument] + [precondition_part]
            
        
        ####################################
        ############ FUNCTIONS #############
        ####################################
        if precondition_part.predicate in functions_of_this_baggable_type: 
            # print("\n\n functions_of_this_baggable_type: ", functions_of_this_baggable_type, "\n")
            for function in task.functions:
                if function.predicate == precondition_part.predicate:

                    function_args = []
                    # If the argument is the bag, we add it at the beginning of the list
                    # else, we add it at the end
                    for arg in precondition_part.args:

                        if type_of_atoms_argumets[arg] == baggable_type.object_type.name:
                            function_args.insert(0, arg)
                        else:
                            function_args.append(arg)

                    # if function.has_interactiong_baggable_types(baggable_types_list):
                    #         # If the function has interacting baggable types, the argument could be in a different order

                    
                    # print("\n\n--------- function_args: ", function_args, "\n")
                    # function_args = []
                    # for i in range(len(function.arguments)):
                    #     for key, value in type_of_atoms_argumets.items():

                    #         if function.arguments[i].type_name == value:
                    #             function_args.insert(i, key)
                    #             print("function_args: ", function_args)


                    new_function = pddl.conditions.Atom(predicate = function.name, args = function_args, type = 'greater')
                    # new_function = add_function_to_precondition(function, precondition_part)
                    new_precondition_parts.append(new_function)
                    # print(new_precondition_parts)

    for key, value in atoms_with_baggable_arguments_of_the_same_bag.items():

        new_predicate_args = []
        args_of_each_atom = [atom.args for atom in value]
        

        for element in args_of_each_atom:
            for x in element:
                if x == key:
                    if x not in new_predicate_args:
                        new_predicate_args.insert(0, x)
                else:
                    new_predicate_args.append(x)


        new_bag_predicate = pddl.conditions.Atom(predicate = bag_predicate_of_this_type.name, args = new_predicate_args)
        new_precondition_parts.append(new_bag_predicate)  

    # When the action has predicates of the baggable type, and the bag of this baggable type
    # does not have original predicates (just ID) we have to add the bag here
    for param in action.parameters:
        if param.type_name == baggable_type.object_type.name and not len(bag_predicate_of_this_type.original_predicate): 
            new_bag_predicate = pddl.conditions.Atom(predicate = bag_predicate_of_this_type.name, args = [param.name])
            new_precondition_parts.append(new_bag_predicate)
    
    # print("\n#######################\n")
    # print("atoms_with_baggable_arguments_of_the_same_bag: ", atoms_with_baggable_arguments_of_the_same_bag)
    # print("\n#######################\n")


    return new_precondition_parts




def effects_reformulation(task, action, baggable_type, original_effects, original_predicates_of_this_bag_predicate,\
                            functions_of_this_baggable_type, bag_predicate_of_this_type, new_effects):
    """"Given the effects of an action, it reformulates them to add the bag-predicates and the functions"""
    # To store the atoms that are in the same bag. It has the form: {bag_object: [atom1, atom2, ...]}
    atoms_with_baggable_arguments_of_the_same_bag = {}
    type_of_atoms_argumets = {} 

    for effect in original_effects:
        # I do not need to add bag predicates to the effects
        # if effect.literal.predicate in original_predicates_of_this_bag_predicate:
        #     # Add bag-predicate
        #     for atom_argument in effect.literal.args:
        #         for action_parameter in action.parameters:
        #             if atom_argument == action_parameter.name and action_parameter.type_name == baggable_type.object_type.name:
        #                 if atoms_with_baggable_arguments_of_the_same_bag.get(atom_argument) is None:
        #                     atoms_with_baggable_arguments_of_the_same_bag[atom_argument] = []
        #                 atoms_with_baggable_arguments_of_the_same_bag[atom_argument] = atoms_with_baggable_arguments_of_the_same_bag[atom_argument] + [effect.literal]


        
        ####################################
        ############ FUNCTIONS #############
        ####################################
        # elif effect.literal.predicate in functions_of_this_baggable_type: 
        if effect.literal.predicate in functions_of_this_baggable_type: 
                        
            # Store the type of each atom of the effects
            for action_parameter in action.parameters:
                for atom_argument in effect.literal.args:
                    if atom_argument == action_parameter.name:
                        # if the atom has an argument of the baggable type
                        type_of_atoms_argumets[atom_argument] = action_parameter.type_name

        
            for function in task.functions:
                if function.predicate == effect.literal.predicate:

                    function_args = []
                    # If the argument is the bag, we add it at the beginning of the list
                    # else, we add it at the end
                    for arg in effect.literal.args:
                        if type_of_atoms_argumets[arg] == baggable_type.object_type.name:
                            function_args.insert(0, arg)
                        else:
                            function_args.append(arg)
                    new_effect = add_function_to_effect(original_effect = effect, predicate = function.name, args = function_args)
                    new_effects.append(new_effect)
                    # print("new_effects: ", new_effects, "\n")

    # I do not need to add bag predicates to the effects

    # for key, value in atoms_with_baggable_arguments_of_the_same_bag.items():
        
    #     new_predicate_args = []
    #     args_of_each_atom = [atom.args for atom in value]
    #     for element in args_of_each_atom:
    #         for x in element:
    #             if x == key:
    #                 if x not in new_predicate_args:
    #                     new_predicate_args.insert(0, x)
    #             else:
    #                 new_predicate_args.append(x)


    #     new_bag_predicate = pddl.conditions.Atom(predicate = bag_predicate_of_this_type.name, args = new_predicate_args)
    #     new_effects.append(new_bag_predicate)  

    # When the action has predicates of the baggable type, and the bag of this baggable type
    # does not have original predicates (just ID) we have to add the bag here
    # for param in action.parameters:
        # if param.type_name == baggable_type.object_type.name and not len(bag_predicate_of_this_type.original_predicate): 
            # new_bag_predicate = pddl.conditions.Atom(predicate = bag_predicate_of_this_type.name, args = [param.name])
            # new_effects.append(new_bag_predicate)

    return new_effects


def add_function_to_precondition(function, precondition_part):
    
    
    precondition_part.predicate = function.name
    precondition_part.type = 'greater'

    return precondition_part


# def add_function_to_effect(effect, task):

#     if isinstance(effect.literal, pddl.conditions.NegatedAtom):
#         effect.literal.type = 'decrease'
#     elif isinstance(effect.literal, pddl.conditions.Atom):
#         effect.literal.type = 'increase'
#     # print("\n\n action_effect_predicates \n\n", type(effect.literal))
#     for function in task.functions:                            
#         if function.predicate == effect.literal.predicate:
#             effect.literal.predicate = function.name

#     return effect

def add_function_to_effect(original_effect, predicate, args):
    if isinstance(original_effect.literal, pddl.conditions.NegatedAtom):
        # print("decrease")
        new_effect = pddl.conditions.Atom(predicate = predicate, args = args, type = 'decrease')
    elif isinstance(original_effect.literal, pddl.conditions.Atom):
        # print("increase")
        new_effect = pddl.conditions.Atom(predicate = predicate, args = args, type = 'increase')

    return new_effect



def add_predicates_to_actions(precondition_part, task):
    precondition_predicate = precondition_part.predicate
    precondition_args = precondition_part.args
    result = []
    arguments = []
    predicates_of_this_type_to_substitute_for_bag_predicate = []
    for predicate in task.predicates:
        if isinstance(predicate, pddl.predicates.Bag_Predicate):
            if precondition_predicate in [original_pred for original_pred in predicate.original_predicate]:
                # print("\n\n iguales \n")
                result = [predicate.name, precondition_args, predicate]
                predicates_of_this_type_to_substitute_for_bag_predicate.append(precondition_predicate)

            # for original_pred in predicate.original_predicate:
            #     if precondition_predicate == original_pred:
            #         print("\n\n iguales \n")
            #         result = [predicate.name, precondition_args, predicate]
            #         predicates_of_this_type_to_substitute_for_bag_predicate.append(precondition_predicate)
                    # print(precondition_predicate.arguments)

    return result
    # return predicates_of_this_type_to_substitute_for_bag_predicate
