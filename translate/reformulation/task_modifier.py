from . import type_tree
from . import helper_functions
import copy
import options
import pddl
import re
import random
import string



def modify_task(task):    
    

    
    
    # Make the goal a conjunction
    task.goal = pddl.conditions.Conjunction([task.goal]) if not len(task.goal.parts) else task.goal

    
    # Remove unused predicates from the task
    change = remove_unused_predicates(task)



    # Ensure the type hierarchy is a tree not a forest
    new_types = []
    for typ in [x for x in task.types if not x.basetype_name is None]:
        parent_type = [x for x in task.types if typ.basetype_name == x.name]
        if not len(parent_type) and typ.basetype_name not in [x.name for x in new_types]:
            new_types.append(pddl.Type(typ.basetype_name, "object"))
            print("Setting parent of type", typ.basetype_name, "as object")
            change = True
    task.types.extend(new_types)
    
	
    # For each predicate with type t but no action parameters are of type t, create one new predicate for each occurrence of a subtype of t
    typ = [x for x in task.types if x.name == 'object' and x.basetype_name == None][0]
    root = type_tree.type_tree_node(typ, False, task)
    x = fix_type(root, task)
    change = x[0] or change
    task = x[1]
    
    
    # Create a type hierarchy if the domain is untyped
    if ":typing" not in task.requirements.requirements:
        create_type_hierarchy(task)
        change = True
    
    
    return change, task
    




# Move conditional effects into the body to help us calculate invariants. These changes are only temporary
def move_conditional_effects_into_body(task):
	


    changesMade = False
    taskCopy = copy.deepcopy(task);
    conditionalEffectGroupForAllActions = []
    for action in taskCopy.actions:

        conditionalEffects = [x for x in action.effects if len(x.parameters)]
        if not len(conditionalEffects):
            continue

        changesMade = True
         
        # Group together any loops into one variable if the two loops share:
        #		1) Parameters of the same type in same positions (but different names)
        #		2) Identical preconditions
        conditionalEffectGroups = []
        for condEff in conditionalEffects:
            if not len(conditionalEffectGroups):
                condEff.literal = [condEff.literal]
                conditionalEffectGroups.append(condEff)

            # Try to merge with one of the other conditional effects
            else:
                successfulMatch = False
                for condEffGroup in conditionalEffectGroups:

                    parametersHaveSameType = len(condEff.parameters) == len(condEffGroup.parameters)
                    eff_to_effGroup_param_mapping = []
                    if parametersHaveSameType:
                        for i in range(0, len(condEff.parameters)):
                            if condEff.parameters[i].type_name != condEffGroup.parameters[i].type_name:
                                parametersHaveSameType = False
                                break
                            else:
                                eff_to_effGroup_param_mapping.append([condEff.parameters[i].name, condEffGroup.parameters[i].name])


                    # If they have different parameter types then cannot group them
                    if not parametersHaveSameType:
                        continue


                    # Use the parameter mapping to see if the two have the same preconditions
                    precondsAreSame = True
                    precond_atoms = condEff.condition.parts if len(condEff.condition.parts) else [condEff.condition]
                    precond_atoms_group = condEffGroup.condition.parts if len(condEffGroup.condition.parts) else [condEffGroup.condition]
                    for precond in precond_atoms:

                        pddlStr = precond.pddl_str()
                        for mapping in eff_to_effGroup_param_mapping:
                            pddlStr = str.replace(pddlStr, mapping[0], mapping[1])

                        if not pddlStr in [x.pddl_str() for x in precond_atoms_group]:
                            precondsAreSame = False
                            break


                    if not precondsAreSame:
                        continue


                    # If the preconds can be matched then these two loops are the same (except for possibly the effect)
                    # Need to apply the parameter mapping to the effect
                    else:
                        condEff.literal.args = list(condEff.literal.args)
                        for mapping in eff_to_effGroup_param_mapping:
                            for i in range(0, len(condEff.literal.args)):
                                if condEff.literal.args[i] == mapping[0]:
                                    condEff.literal.args[i] = mapping[1]
                        condEff.literal.args = tuple(condEff.literal.args)

                        condEffGroup.literal.append(condEff.literal)
                        successfulMatch = True
                        break


                if not successfulMatch:
                    condEff.literal = [condEff.literal]
                    conditionalEffectGroups.append(condEff)
                    continue

        print("conditionalEffectGroups")
        # Move any preconditions, effects and parameters from the conditional effect groups to the main body of the action
        for condEffGroup in conditionalEffectGroups:

            # Parameters
            for param in condEffGroup.parameters:
                action.parameters.append(param)


            # Preconditions
            precond_atoms = condEffGroup.condition.parts if len(condEffGroup.condition.parts) else [condEffGroup.condition]
            newPreconds = list(action.precondition.parts) if len(action.precondition.parts) else [action.precondition]
            for precond in precond_atoms:
                newPreconds.append(precond)
            action.precondition = pddl.conditions.Conjunction(newPreconds)


            # Effects
            for effect in condEffGroup.literal:
                
                effect = pddl.effects.Effect([], pddl.conditions.Truth(), effect)
                action.effects.append(effect)


        # Delete the conditional effects from the action
        action.effects = [x for x in action.effects if not len(x.parameters)]
        conditionalEffectGroupForAllActions.append([action.name, conditionalEffectGroups]);
     
    if changesMade:
        print("Contents of conditional effects were moved into the main body to calculate invariants")
        return taskCopy, conditionalEffectGroupForAllActions
    return task, None


def fix_type(typ_node, task):
    

    changes = False
    sub_types = typ_node.get_descendants()
    super_types = typ_node.get_ancestors()
    sub_types.pop(0)
    
    
    typ_lineage = sub_types + super_types
    
    preds_of_typ = [p for p in task.predicates if len([a for a in p.arguments if a.type_name == typ_node.node.name]) and len([a for a in p.arguments if a.type_name in [x.node.name for x in typ_lineage]]) == 1] # Not self affiliated
    
    
    for pred in preds_of_typ:
        S = []
        type_at_index = [x.type_name for x in pred.arguments].index(typ_node.node.name)
        s = get_uses_of_predicate_of_type(pred, typ_node, task, type_at_index)
        task = s[4]
        if s:
            continue
        
        for typ_n in sub_types:
            s = get_uses_of_predicate_of_type(pred, typ_n, task, type_at_index)
            task = s[4]
            if s:
                S.append(s)
        
        # Modify pddl
        if len(S) > 1:
            create_new_predicate(S, task, typ_node)
            changes = True
        

    # Repeat for children
    for typ_n in sub_types:
        changes = changes or fix_type(typ_n, task)[0]
    

    return changes, task


# Return a list: [predicate, type_node, type index, [pred1, ... ] ] iff the predicate's argument is of this type in the parameters 
def get_uses_of_predicate_of_type(pred, typ_node, task, type_at_index):
    

    to_return = []
   
    for action in task.actions:
        action_parameters = action.parameters + task.objects
        preconds = [[action.precondition] if action.precondition.parts == [] else list(action.precondition.parts)][0]
        effects = [x.literal for x in action.effects]
        conditional_effects_preconditions = []

        for param_list in [x.parameters for x in action.effects]:
            action_parameters = action_parameters + param_list


        for precond_effect in [x for x in action.effects if not isinstance(x.condition, pddl.conditions.Literal)]:
            #print("precond", precond_effect)
            conditional_effects_preconditions = conditional_effects_preconditions + [[precond_effect.condition.precondition] if precond_effect.condition.parts == [] else list(precond_effect.condition.parts)][0]
            #action_parameters = action_parameters + precond_effect.parameters


        #print("action_parameters", action_parameters)
        
        for p in [x for x in (preconds + effects + conditional_effects_preconditions) if pred.name == x.predicate]:
            variable_name = p.args[type_at_index]
            type_of_variable_in_action = [x.type_name for x in action_parameters if x.name == variable_name]

            if not len(type_of_variable_in_action):
                continue
            if type_of_variable_in_action[0] == typ_node.node.name:
                to_return.append(p)
    


    if len(to_return):
        # print("to_return", to_return)
        exist_negated_atom = False
        exist_non_negated_atom = False
        for atom in to_return:
            # If exist both negated and non-negated atoms, then the predicate does not remain the same
            if isinstance(atom, pddl.conditions.NegatedAtom):
                exist_negated_atom = True
            if isinstance(atom, pddl.conditions.Atom):
                exist_non_negated_atom = True

        if not(exist_negated_atom and exist_non_negated_atom):
            for predicate in task.predicates:
                if predicate.name == pred.name:
                    predicate.remains_the_same = True

        return [pred, typ_node, type_at_index, to_return, task]
    else:
        return [False, False, False, False, task]
        # return False
    
    
def create_new_predicate(S, task, typ_node):
    
    # If the original type has been referred to, then keep this predicate, else remove it
    if not S[0][1].node.name == typ_node.node.name:
        task.predicates = [pred for pred in task.predicates if not pred.name == S[0][0].name]
    else:
        S.pop(0)
    
    for s in S:
        
        # Create the new predicate
        pred = s[0]
        sub_typ_node = s[1]
        index_in_args = s[2]
        new_predicate_name = helper_functions.create_unique_name(pred.name + '-' + sub_typ_node.node.name, [x.name for x in task.predicates])
        new_argument_name = helper_functions.create_unique_name('?' + sub_typ_node.node.name[0], [x.name for x in pred.arguments])
        new_argument = pddl.pddl_types.TypedObject(new_argument_name, sub_typ_node.node.name)
        new_arguments = copy.deepcopy(pred.arguments)
        new_arguments[index_in_args] = new_argument
        new_predicate = pddl.predicates.Predicate(new_predicate_name, new_arguments)
        
        task.predicates.append(new_predicate)
        print("For pred", pred, "of type", sub_typ_node.node.name, "new predicate created is", new_predicate)
        
        # Replace occurrences of this predicate in each action
        for pred_in_action in s[3]:

            #if len(pred_in_action.parameters):
            #print("conditional", pred_in_action)
            pred_in_action.predicate = new_predicate_name
            
        # Replace occurrences in initial and goal state
        objects_of_this_type = [x.name for x in task.objects if x.type_name == sub_typ_node.node.name]
        for init in [x for x in task.init if type(x) is pddl.conditions.Atom and x.predicate == pred.name and len([y for y in x.args if y in objects_of_this_type])]:
            init.predicate = new_predicate_name
        for goal in [x for x in task.goal.parts if type(x) is pddl.conditions.Atom and x.predicate == pred.name and len([y for y in x.args if y in objects_of_this_type])]:
            goal.predicate = new_predicate_name
            
            
            

# Remove any predicates which are not in any operators or in the goal
def remove_unused_predicates(task):

    changes = False
    for pred in task.predicates:
    
        keep_pred = False
        if pred.name == "=" or pred in [x.predicate for x in task.goal.parts if type(x) is pddl.conditions.Atom]:
            continue
        
        
        for action in task.actions:


            # Shortcut: if there is a disjunction do not look at the atoms inside it just move on
            if len([y for y in (action.precondition.parts if len(action.precondition.parts) else [action.precondition]) if type(y) is pddl.conditions.Disjunction]):
                keep_pred = True
                break

            #print("action", action.name, pred.name)
            precond_names = [y.predicate for y in (action.precondition.parts if len(action.precondition.parts) else [action.precondition]) if not type(y) is pddl.conditions.Disjunction]
            effect_names = [y.predicate for y in [x.literal for x in action.effects if type(x) is not pddl.f_expression.Assign]]

            #conditional_effect_conditions = [y.predicate for y in [x.condition for x in action.effects if len(x.parameters)]]

            if pred.name in precond_names or pred.name in effect_names or pred.name:# in conditional_effect_conditions:
                keep_pred = True
                break
        
        
        if not keep_pred:
            changes = True
            if options.writeout_reformulation_logic:
                print("Removing unnecessary predicate", pred.name)
            task.predicates = [x for x in task.predicates if not x == pred]
            task.init = [x for x in task.init if type(x) is pddl.f_expression.Assign or not x.predicate == pred.name]
    
    return changes

            


                                                                                                                                                                                                                             
  
def create_type_hierarchy(task):
    
    print ("Creating a type hierarchy")
    
    # Assign each object a type. The type name is one of the static unary predicates the object belongs to
    new_types = []
    for obj in task.objects:
        type_name, parent_name = find_type_for_object(obj, task, new_types)
        obj.type_name = type_name
        if type_name != "object" and type_name not in [x.name for x in new_types]:
            new_types.append(pddl.pddl_types.Type(type_name, parent_name))

    
    # Remove the predicates from the domain and add the types to the operators
    for typ in new_types:
        task.predicates = [x for x in task.predicates if not x.name == typ.name]
        task.init = [x for x in task.init if (type(x) is pddl.conditions.Atom and not x.predicate == typ.name) or type(x) is not pddl.conditions.Atom]

        task.types.append(pddl.pddl_types.Type(typ.name, typ.basetype_name))
        print("Creating type", typ.name, "of type", typ.basetype_name)

        for action in task.actions:
            preconds = tuple([action.precondition]) if not len(action.precondition.parts) else action.precondition.parts
            for precondition_type in [x for x in preconds if type(x) is pddl.conditions.Atom and x.predicate == typ.name]:
            
                # Remove the precondition
                action.precondition.parts = [x for x in action.precondition.parts if x != precondition_type]
                
                # Change the object type in the parameter list
                param = [x for x in action.parameters if x.name == precondition_type.args[0]][0]
                param.type_name = typ.name
                
                
                
    # Add types to the predicate list by going through the operators and the initial state
    for pred in task.predicates:
        if (pred.name == "="):
            continue
    
        for arg_num in range(0, len(pred.arguments)):
            arg_types = [] # If there is more than 1 valid type then we split the predicate into one for each type
            
            for action in task.actions:
                #preconds = tuple([action.precondition]) if not len(action.precondition.parts) else action.precondition.parts
                preconds = [[action.precondition] if action.precondition.parts == [] else list(action.precondition.parts)][0]
                effects = [x.literal for x in action.effects if type(x) is not pddl.f_expression.Assign]
                for atom in [x for x in preconds + effects if x.predicate == pred.name]:
                    
                    # Find the object type for the parameter matching this argument
                    matching_param = [x for x in action.parameters if x.name == atom.args[arg_num]]
                    if len(matching_param) and matching_param[0].type_name not in arg_types:
                        arg_types.append(matching_param[0].type_name)
            
            
            
            for atom in [x for x in task.init if x.predicate == pred.name]:
                object_type = [x.type_name for x in task.objects if x.name == atom.args[arg_num]][0]
                if object_type not in arg_types:
                    arg_types.append(object_type)


            
            
            if "object" in arg_types:
                pred.arguments[arg_num].type_name = "object"
                continue

            # If there is only 1 possible object type then use that one, otherwise create one predicate for each type (eg. at becomes at-truck, at-plane)
            if len(arg_types) == 1:
                pred.arguments[arg_num].type_name = arg_types[0]
                #print("Setting object type of", pred.pddl_str(), "arg", arg_num, "to", arg_types[0])
            else:

            	# If one type is a subtype of the other then just use the upper type
                if len(arg_types) == 2:


                    A_is_subtype_of_B = len([x for x in task.types if x.name == arg_types[0] and x.basetype_name == arg_types[1]]) > 0
                    if A_is_subtype_of_B:
                        pred.arguments[arg_num].type_name = arg_types[1]
                        #print("Setting object type of", pred.pddl_str(), "arg", arg_num, "to", arg_types[1])
                        continue 

                    B_is_subtype_of_A = len([x for x in task.types if x.name == arg_types[1] and x.basetype_name == arg_types[0]]) > 0
                    if B_is_subtype_of_A:
                        pred.arguments[arg_num].type_name = arg_types[0]
                        #print("Setting object type of", pred.pddl_str(), "arg", arg_num, "to", arg_types[0])
                        continue 

            
                # Will only give one predicate for each type for one of the arguments, not both (eg. will not have at-truck-city, at-truck-airport etc.)          
                for typ in arg_types:
                    unique_pred_name = helper_functions.create_unique_name(pred.name + "-" + typ, [x.name for x in task.predicates if not x is None])
                    new_pred = pddl.predicates.Predicate(unique_pred_name, copy.deepcopy(pred.arguments))
                    new_pred.arguments[arg_num].type_name = typ
                    task.predicates.append(new_pred)
                    print("Creating", new_pred.pddl_str(), "removing", pred.pddl_str())
                    
                    
                    # Replace all occurrences in actions
                    for action in task.actions:
                        preconds = tuple([action.precondition]) if not len(action.precondition.parts) else action.precondition.parts
                        effects = [x.literal for x in action.effects if type(x) is not pddl.f_expression.Assign]
                        for atom in [x for x in preconds + effects if x.predicate == pred.name]:
                            matching_param = [x for x in action.parameters if x.name == atom.args[arg_num]][0]
                            if matching_param.type_name == typ:
                                atom.predicate = unique_pred_name
             
            
                    # Replace all occurrences in the initial state and goal
                    for atom in [x for x in task.init if x.predicate == pred.name]:
                        object_type = [x.type_name for x in task.objects if x.name == atom.args[arg_num]][0]
                        if object_type == typ:
                            atom.predicate = unique_pred_name
                            
                    for atom in [x for x in task.goal.parts if x.predicate == pred.name]:
                        object_type = [x.type_name for x in task.objects if x.name == atom.args[arg_num]][0]
                        if object_type == typ:
                            atom.predicate = unique_pred_name
                    
                 
                # Remove the original predicate 
                to_remove = [x for x in range(0, len(task.predicates)) if task.predicates[x] is not None and task.predicates[x] == pred]
                for index in to_remove:
                    task.predicates[index] = None
                        
                        
                        
                        
        
        
    task.predicates = [x for x in task.predicates if not x is None]    
    task.requirements.requirements.append(":typing")
    
    
    
    
    
def find_type_for_object(obj, task, new_types):    
    
    unary_preds_of_object = [x for x in task.init if len(x.args) == 1 and x.args[0] == obj.name]
        
    # Filter out non-static predicates
    static_unary_preds_of_object = []
    for pred in unary_preds_of_object:
        static = True
        for action in task.actions:
            if pred.predicate in [x.literal.predicate for x in [y for y in action.effects if type(y) is not pddl.f_expression.Assign]]:
                 static = False
                 break
        if static:
            static_unary_preds_of_object.append(pred)


    # If this object has 2 possible unary predicates, then we will try to make a hierarchy between the 2
    if len(static_unary_preds_of_object) == 2:


        objs_with_predA_in_init = [x.args[0] for x in task.init if x.predicate == static_unary_preds_of_object[0].predicate]
        objs_with_predB_in_init = [x.args[0] for x in task.init if x.predicate == static_unary_preds_of_object[1].predicate]

        # If all objects of typeA are also of typeB, then make typeA a subtype of typeB
        if set(objs_with_predA_in_init) < set(objs_with_predB_in_init):
            return static_unary_preds_of_object[0].predicate, static_unary_preds_of_object[1].predicate

        # Else if all objects of typeB are also of typeA, then make typeB a subtype of typeA
        if set(objs_with_predB_in_init) < set(objs_with_predA_in_init):
            return static_unary_preds_of_object[1].predicate, static_unary_preds_of_object[0].predicate

        # Otherwise proceed as normal


                                                    
    # If there are any static unary predicates with this object, then create a new type
	# But first check the type does not already exist
    for pred in static_unary_preds_of_object:
        if pred.predicate in [x.name for x in new_types]:
            return pred.predicate, "object"
        
        
    if len(static_unary_preds_of_object):
        return static_unary_preds_of_object[random.randint(0, len(static_unary_preds_of_object) - 1)].predicate, "object"
    
    
    return "object", None


    
    



# Splits all operators which have disjunctions into two or more operators                                                                 
def split_disjunction_operators(task):

    new_actions = []
    for action in task.actions:

        # If there are no disjunctions then the original domain will be used
        new_actions = new_actions + split_disjunction_for_operator(action, [x.name for x in new_actions])


    task.actions = new_actions



# Recursively splits the current action into actions without disjunctions
def split_disjunction_for_operator(action, actionNames):

    preconds = [y for y in (list(action.precondition.parts) if len(action.precondition.parts) else [action.precondition])]
    for precondIndex in range(0, len(preconds)):
        precond = preconds[precondIndex]
        if type(precond) is pddl.conditions.Disjunction:
            #print("Operator", action.name, "contains disjunctions and must be split")
            new_actions = []
            for disjunction_part in precond.parts:


                new_action = copy.deepcopy(action)

                # Replace the disjunction precondition with an Atom/NegatedAtom
                action.name = helper_functions.create_unique_name(action.name + "$" + "d", actionNames)
                actionNames.append(action.name)
                new_preconds = [y for y in (list(new_action.precondition.parts) if len(new_action.precondition.parts) else [new_action.precondition])]
                new_preconds[precondIndex] = copy.deepcopy(disjunction_part)
                new_action.precondition.parts = tuple(new_preconds)

                # Recurse down to the next disjunction
                new_actions = new_actions + split_disjunction_for_operator(new_action, actionNames)



            # Return the actions now. Don't continue looping because the other disjunctions in this operator (if there are any) are handled recursively
            return new_actions


    # If this part of the function has been reached then there are no (more) disjunctions so just return the current action
    return [action]

  
