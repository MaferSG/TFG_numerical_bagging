import pddl
import copy
import re
import options
from . import helper_functions
from collections import OrderedDict

def repair_domain(task):
    changes1 = delete_unused_preconditions(task)
    changes2 = add_removed_precondition(task)

    return changes1 or changes2
    
    
      
            

# If   there exists an action with predicate precondition X(?a, ?b, ...), where X is not used in any other action preconditions 
#      such that action has identical positive effects and all positive effects are 0 or 1-ary only
#      and there exist unary positive effects Y1(?a), Y2(?b), ... where Yi is not removed in any other actions
# Then add X(?a, ?b, ...) to the negative effects
def delete_unused_preconditions(task):
    
    changes = False
    newactions = copy.deepcopy(task.actions)
    
    for action in task.actions:
        
        
        # Find precondition(s) X
        preconds_to_delete = []
        action_precond = tuple([action.precondition]) if not len(action.precondition.parts) else action.precondition.parts
        
        # Do not continue if there are any m-ary positive effects for m > 1 or functions
        positive_effects_of_action = [x.literal for x in action.effects if type(x.literal) is pddl.conditions.Atom]
        if len([x for x in positive_effects_of_action if len(x.args) > 1] + [x for x in action.effects if type(x.literal) is pddl.f_expression.Assign]):
            continue

        negative_effects_of_action = [x.literal for x in action.effects if type(x.literal) is pddl.conditions.NegatedAtom]
        for precond in [x for x in action_precond]:
        
                    
            # Do not continue if the precondition is already a negative effect
            if precond.pddl_str() in [x.negate().pddl_str() for x in negative_effects_of_action]:
                continue
            
            found_in_other_illegal_preconditions = False
            for other_action in [x for x in task.actions]:
                
                other_action_precond = tuple([other_action.precondition]) if not len(other_action.precondition.parts) else other_action.precondition.parts
                positive_effects_of_other_action = [x.literal.predicate for x in other_action.effects if type(x.literal) is pddl.conditions.Atom and not x.literal.negated]
                if precond.predicate in [x.predicate for x in other_action_precond] and len([x for x in positive_effects_of_action if x.predicate in positive_effects_of_other_action]) < len(positive_effects_of_action):
                    found_in_other_illegal_preconditions = True
                    break
            
            if not found_in_other_illegal_preconditions:
                preconds_to_delete.append(precond)
        
        
        # Find unary positive effect(s) Y
        for precond in preconds_to_delete:
            
            removed_in_other_actions = False
            effects_to_mutex = []
            for variable_name in precond.args:
                           
                for pos_effect in [x.literal for x in action.effects if type(x.literal) is pddl.conditions.Atom and not x.literal.negated and len(x.literal.args) == 1 and x.literal.args[0] == variable_name]:
                    
                    for other_action in [x for x in task.actions if not x.name == action.name]:
                     
                        
                        if pos_effect.pddl_str() in [x.literal.negate().pddl_str() for x in other_action.effects if type(x.literal) is pddl.conditions.NegatedAtom]:
                            removed_in_other_actions = True
                            break
                    effects_to_mutex.append(pos_effect)          
                if removed_in_other_actions:
                    break
                    
                                    
            if not removed_in_other_actions:
             
                # Add precond object to negative effects
                for pos_effect in list(OrderedDict.fromkeys(effects_to_mutex)):

                    atom = pddl.conditions.NegatedAtom(precond.predicate, copy.deepcopy(precond.args))
                    negeffect = pddl.effects.Effect([], pddl.conditions.Truth(), atom)
                    
                    new_action = [x for x in newactions if x.name == action.name][0]
                    new_action.effects.append(negeffect)
                    changes = True
                    
            
    
    task.actions = newactions
    return changes
    
    



# For all actions with unary positive effect Y(?a), where Y(?a) is not removed in any other actions
#         and all other positive effects in this action satisfy this property
#         and there are no negative effects in this action using this object
#         Add a new precondition X(?a) which is true in the initial state for all ?a, and is a negative effect in each of these actions 
def add_removed_precondition(task):
    
    
    changes = False
    notserved = []
    typs = []
    notservedmutexwith = []
    newactions = copy.deepcopy(task.actions)
    
    for action in task.actions:
        
        # If there are any m-ary positive effects with m > 1 or any functions, skip to next action
        positive_effects_of_action = [x.literal for x in action.effects if type(x.literal) is pddl.conditions.Atom]
        unary_positive_effects_of_action = [x for x in positive_effects_of_action if len(x.args) == 1]
        if len([x for x in positive_effects_of_action if len(x.args) > 1] + [x for x in action.effects if type(x.literal) is pddl.f_expression.Assign]):
            #print('Cannot rewire', action.name, 'because of m-ary positive effects m>1')
            continue
        
        
        # Update list of supertypes
        objs = list(OrderedDict.fromkeys([x.args[0] for x in unary_positive_effects_of_action]))
        
        
        # Ensure that there are no negative effects wrt this object in this action (this is to prevent pddl repair protocol 1 and 2 acting on same action to yield 2 'notserved' preconditions
        negative_effects_of_action_with_obj = [x.literal for x in action.effects if type(x.literal) is pddl.conditions.NegatedAtom and len([y for y in objs if y in x.literal.args])]
        if len(negative_effects_of_action_with_obj):
            #print('Cannot rewire', action.name, 'because there are negative effects of type', objs)
            continue
        
        
        # Check that every unary positive in this action is not removed in any other action
        removed = False
        for effect in unary_positive_effects_of_action:
            for other_action in [x for x in task.actions]: 
                if effect.predicate in [x.literal.predicate for x in other_action.effects if type(x.literal) is pddl.conditions.NegatedAtom and len(x.literal.args) == 1]:
                    removed = True
                    #print('Cannot repair', action.name, 'because action', other_action.name, 'removes predicate', effect.predicate)
                    break
            if removed:
                break
        if removed:
            continue
        
        
        # At this point, we can add a 'notserved(?obj)' precondition and negative effect where ?obj is of type typ
        typs = list(OrderedDict.fromkeys(typs + [w for w in task.types if w.name in [x.type_name for x in action.parameters if x.name in objs]]))
        changes = True
        for typ in typs:
            matching_notserved = [x for x in notserved if x.arguments[0].type_name == typ.name]
            new_pred = None
            if not len(matching_notserved):
                new_pred = pddl.predicates.Predicate(helper_functions.create_unique_name('notserved', [x.name for x in task.predicates]), [pddl.pddl_types.TypedObject('?o', typ.name)])
                task.predicates.append(new_pred)
                notserved.append(new_pred)
                #print("Creating predicate", new_pred, "for action", action.name)
            else:
                new_pred = matching_notserved[0]
        
        
            new_action = [x for x in newactions if x.name == action.name][0]
            for obj in [x for x in objs if [y for y in action.parameters if y.name == x][0].type_name == typ.name]:
                new_precond = pddl.conditions.Atom(new_pred.name, [obj])
                if not len(action.precondition.parts):
                    new_action.precondition = pddl.conditions.Conjunction([new_action.precondition, new_precond])
                else:
                    new_action.precondition = pddl.conditions.Conjunction(list(new_action.precondition.parts) + [new_precond])
                new_action.effects.append(pddl.effects.Effect([], pddl.conditions.Truth(), pddl.conditions.NegatedAtom(new_pred.name, [obj])))
        
        
            notservedmutexwith = notservedmutexwith + [x.predicate for x in unary_positive_effects_of_action]
        
           #print('Adding notserved to action', action.name, new_action.effects)
            
            
    # Add initial state 'notserved' atoms to every object with an appropriate type
    init_atoms_to_add = []
    for o in [x for x in task.objects if x.type_name in [y.name for y in typs]]:
        init_atoms_with_o = [x.predicate for x in task.init if o.name in x.args]
        
        # Only add notserved(?o) to initial state if one of the mutexed predicates is not already there
        if not len([x for x in init_atoms_with_o if x in notservedmutexwith]) and len([x for x in notserved if x.arguments[0].type_name == o.type_name]):
            print(action.name, [x for x in notserved if x.arguments[0].type_name == o.type_name][0].name, o, "mutexed with", notservedmutexwith)
            init_atoms_to_add.append(pddl.conditions.Atom([x for x in notserved if x.arguments[0].type_name == o.type_name][0].name, [o.name]))
        
    
    task.actions = newactions    
    task.init = list(task.init) + init_atoms_to_add
    return changes
        
        
        
        
        
        
            
            
            











