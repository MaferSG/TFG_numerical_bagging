import re
import copy
import options
import pddl
import sys
from . import pddl_repair
from . import mapping_printer
from collections import OrderedDict



def translate_solution(task, solution_file, mapping_file):


    # For reading the plans that metric-ff returns
    with open(solution_file) as f:
        contents = f.read()


    match = re.findall("[0-9]+:.*\n", contents)
    if match:
        # with open(solution_file, "a") as f: # Without deleting what was in the file
        with open(solution_file, "w") as f: # Deleting what was in the file
            for line in match:
                f.write("({})\n".format(line.strip().split(' ', 1)[1]).lower())

    
    
    soln = open(solution_file, 'r')


    orig_reform_mapping = mapping_printer.SolutionMappings(task, mapping_file)
    
    state = [x for x in task.init if type(x) is pddl.conditions.Atom]
    step = soln.readline().strip()
    
    original_solution = ''
    
    while not step == '':

        if step[0] == ";":
            step = soln.readline().strip()
            continue
        
        print('\n\nstate', [x for x in state if not x.predicate =="="], '\n')
        
        step_parameters = re.sub("([(]|[)]|\n)", "", step).split()
        step_action = step_parameters.pop(0).lower()
        print("Action:", step_action, step_parameters)
        #print("AA", [x.grounded_action.lower() for x in orig_reform_mapping.variables_to_ground_mapping_list] )
        
        
        # Ground action
        #print("JJJ", [x.variable + "," + x.ground_to + "," + x.grounded_action for x in orig_reform_mapping.variables_to_ground_mapping_list])
        grounded_action_mapping = [x for x in orig_reform_mapping.variables_to_ground_mapping_list if x.grounded_action.lower() == step_action]
        action_mapping = [x for x in orig_reform_mapping.action_mappings if x.reformulated_action.lower() == step_action][0]
        grounded_action, bags_in_action = ground_action_parameters_with_bags(action_mapping, step_parameters, orig_reform_mapping, task, grounded_action_mapping)
        
        
        # Find bagged objects that satisfy preconditions
        action_dc_parameter_mapping = [x for x in orig_reform_mapping.parameter_property_mapping if x.action_name.lower() == step_action]
        #print("?dc", [x.parameter_number for x in action_dc_parameter_mapping], [x.action_name for x in orig_reform_mapping.parameter_property_mapping], action_mapping.original_action.name)
        if not len(bags_in_action):
            bagged_objects = bags_in_action
            fully_grounded_action = grounded_action
        else:
            bagged_objects, fully_grounded_action = satisfy_preconditions(bags_in_action, grounded_action, state, orig_reform_mapping, action_dc_parameter_mapping, step_parameters, step_action) 
        if bagged_objects == False:    
            raise ValueError("ERROR: unable to satisfy an action's preconditions!")

        #print("Grounded action", grounded_action.name, [x for x in fully_grounded_action.parameters], [x for x in fully_grounded_action.precondition.parts], [x.literal for x in fully_grounded_action.effects])
        #print("\n")
        
        # Update state
        update_state(state, fully_grounded_action)
        
        # Add original step to solution
        original_solution = original_solution + '(' + ' '.join([fully_grounded_action.name] + ['$' + x + '$' for x in fully_grounded_action.parameters]) + ')\n'
        #print(original_solution)
        
        step = soln.readline().strip()
        #print('\nstate', state, '\n\n')

    
# Finally, account for initial-state equivalence by swapping objects
    #print('\n\nstate', state, '\n')
    if options.writeout_reformulation_logic:
        print("REFORMULATED INITIAL SOLUTION:")
        print(re.sub('[$]', '', original_solution))
    

    original_space_solution = tidy_solution(original_solution, tuple([task.goal]) if not len(task.goal.parts) else task.goal.parts, state, orig_reform_mapping)
    
    # Write solution to file
    bits = re.split('/', ' %s' %solution_file)
    outputfile = bits.pop().lstrip(' ')
    outputfile = ('/'.join(bits) + '/translated-' + outputfile).lstrip(' ') if len(bits) else ('translated-' + outputfile)
    translated_soln_writer = open(outputfile, 'w+')
    translated_soln_writer.write(original_space_solution)
    translated_soln_writer.close()
    
    print ("Transformed solution written to", outputfile)




# Recursively find bagged objects to satisfy preconditions
def satisfy_preconditions(bags_in_action, grounded_action, state, orig_reform_mapping, action_dc_parameter_mapping, step_parameters, step_action):
    
    #print("\nstarting", grounded_action.name, [x for x in grounded_action.precondition.parts])
    
    if not len(bags_in_action):
        
        
        # Check all action preconditions are satisfied by this state
        preconds = tuple([grounded_action.precondition]) if not len(grounded_action.precondition.parts) else grounded_action.precondition.parts
        for precond in [x for x in preconds if type(x) is pddl.conditions.Atom]:
            #print("precondition:", precond)
            if not str(precond) in [str(x) for x in state]:
                #print("State not satisfied by preconditions because of", str(precond), "in action", grounded_action.name)
                return False, False
                
        for precond in [x for x in preconds if type(x) is pddl.conditions.NegatedAtom]:
            #print("negated precondition", precond)
            if str(precond.negate()) in [str(x) for x in state]:
                #print("State not satisfied by preconditions because of", str(precond), "in action", grounded_action.name)
                return False, False
        
        #print("State is satisfied by preconditions of", grounded_action.name)

        return [], grounded_action
        
    
    bag = bags_in_action.pop(0)
    # print("Bag:", bag, "Bags in action:", bags_in_action)
    bagname = bag.split()[0]
    varname = bag.split()[1]
    
    for obj in [x.original_object for x in orig_reform_mapping.bag_mappings if x.bagged_object == bagname]:
        
        #print("Obj:", obj,"Bag:", bags_in_action, "Bagname:", bagname, "Varname:", varname)
        #print("Attemping to ground", varname, "as", obj.name)
        
        # Check that ?dc parameters are satisfied by this object in current state
        if not object_satisfies_dc_parameters(step_action, obj.name, action_dc_parameter_mapping, step_parameters, orig_reform_mapping, orig_reform_mapping.bag_mappings, state):
            #print("DC not satisfied")
            continue
        
        # Replace precondition occurrences of this bag with this object
        action_grounded_with_this_object = copy.deepcopy(grounded_action) 
        preconds = tuple([action_grounded_with_this_object.precondition]) if not len(action_grounded_with_this_object.precondition.parts) else action_grounded_with_this_object.precondition.parts
        for precond in preconds:
            #print("ungrounded precond;", precond)
            for a in range(0, len(precond.args)):
                new_args = list(precond.args)
                new_args[a] = obj.name if new_args[a].split()[-1] == varname else new_args[a]
                precond.args = tuple(new_args)
            
        
        next_bag_objects, fully_grounded_action = satisfy_preconditions(copy.deepcopy(bags_in_action), action_grounded_with_this_object, state, orig_reform_mapping, action_dc_parameter_mapping, step_parameters, step_action)
        if not next_bag_objects == False:
            
            #print("returning...")
            
            # Now we know that we have a valid grounding, we can ground the effects
            for effect in [x.literal for x in fully_grounded_action.effects]:
                for a in range(0, len(effect.args)):
                    new_args = [x.split()[-1] for x in effect.args]
                    new_args[a] = obj.name if new_args[a] == varname else new_args[a]
                    effect.args = tuple(new_args)
                    
           # for p in range(0, len(fully_grounded_action.parameters)):
           #     fully_grounded_action.parameters[p] = obj.name if fully_grounded_action.parameters[p] == varname else fully_grounded_action.parameters[p]
                
            param_index = [i for i in range(len(fully_grounded_action.parameters)) if fully_grounded_action.parameters[i] == varname]
            for i in param_index:
                fully_grounded_action.parameters[i] = obj.name
                
            #print("preconditions...", fully_grounded_action.parameters)
            #print("effects...", [x.args for x in fully_grounded_action.effects])
            return [obj] + next_bag_objects, fully_grounded_action
        
    
    
    #print("STATE CANNOT EVER BE SATISFIED BY ACTION", grounded_action.name)
    return False, False


    


def object_satisfies_dc_parameters(step_action, obj_name, action_dc_parameter_mapping, step_parameters, orig_reform_mapping, bag_mappings, state):
    
    
    #orig_reform_mapping.parameter_property_mapping
    obj_typ = [x.typ for x in bag_mappings if x.original_object.name == obj_name][0]
    #print("Satisfying ?dc parameters for",  obj_name)

    # For each ?dc parameter in the action:
    for dc in [x for x in action_dc_parameter_mapping if x.typ == obj_typ]:
        print("\t", dc.action_name, dc.typ, dc.parameter_number, dc.property_number)
        
        # The parameter number in the grounded operator is the parameter number mapped minus the number of parameters in this operator which have been grounded or merged (implicitally equal)
        instance_value_of_dc = step_parameters[dc.parameter_number-1]
        property_map = [x for x in orig_reform_mapping.property_predicate_mapping if x.property_number == dc.property_number and x.typ == dc.typ and x.value == instance_value_of_dc]
        
        #print("dc grounded to:", instance_value_of_dc, "property value", property_map[0].value, "property predicate", property_map[0].predicate)
        
        # 1) If predicate is None -> satisfy action with an object which has NONE of the other properties satisfied.
        if len(property_map) == 1 and property_map[0].predicate is None:
            #print('None object', obj_name)
            
            # Find all values of this property and check that none are satisfied by this object
            other_values = [x for x in orig_reform_mapping.property_predicate_mapping if x.property_number == dc.property_number and x.typ == dc.typ and not x.predicate is None]
            for val in other_values:
                
                
                # Unary predicate
                if not val.value is None:
                    matching_instance_in_state = [x for x in state if x.predicate == val.predicate.name and x.args[0] == obj_name]
                    if len(matching_instance_in_state):
                        return False
                
                
                # Binary predicate
                else:
                    matching_instance_in_state = [x for x in state if x.predicate == val.predicate.name and obj_name in x.args and instance_value_of_dc in x.args]
                    if len(matching_instance_in_state):
                        return False
        
        
        # 2) If predicate is unary -> satisfy action with an object which has this predicate true.
        elif len(property_map) == 1:
            #print('Unary object')
            #print("Action", dc.action_name, "has ?dc parameter id", dc.property_number, property_map[0].predicate, "for argument number", dc.parameter_number, "w/ value", instance_value_of_dc)
            
            
            #print("Matches", [x for x in state if x.predicate == property_map[0].predicate.name], "\n\n")
            matching_instance_in_state = [x for x in state if x.predicate == property_map[0].predicate.name and x.args[0] == obj_name]
            if not len(matching_instance_in_state):
                return False
           
            
        # 3) If predicate is binary -> satisfy action with an object which has this object in its predicate. 
        elif not len(property_map):
            #print('Binary object')
            binary_property_map = [x for x in orig_reform_mapping.property_predicate_mapping if x.property_number == dc.property_number and x.typ == dc.typ and x.value is None][0]
            print(instance_value_of_dc, binary_property_map.predicate, binary_property_map.value, obj_name)
            matching_instance_in_state = [x for x in state if x.predicate == binary_property_map.predicate.name and obj_name in x.args]
            if not len(matching_instance_in_state):
                return False


            # If the dc is a bag then turn into all values in the bag
            dc_is_a_bag = len([x for x in bag_mappings if x.bagged_object == instance_value_of_dc]) > 0
            unbagged_instance_value_of_dc = [instance_value_of_dc]
            if dc_is_a_bag:
                unbagged_instance_value_of_dc = [x.original_object.name for x in bag_mappings if x.bagged_object == instance_value_of_dc]
            #print("unbagged_instance_value_of_dc", unbagged_instance_value_of_dc)


            # Check if one element (in the bag?) satisfies this
            dc_instantiates_action = False
            for dc_instance in unbagged_instance_value_of_dc:


                # Check for unbagged objects
                if len([x for x in matching_instance_in_state if dc_instance in x.args]):
                    dc_instantiates_action = True
                    break

            
            if not dc_instantiates_action:
                return False
        
        #else: 
            #raise ValueError("ERROR: more than one property satisfies object!")
    
    return True
        
def ground_action_parameters_with_bags(action_mapping, step_parameters, orig_reform_mapping, task, grounded_action_mapping):
   
    #print("Grounding action", action_mapping.original_action.name)
    grounded_action = copy.deepcopy(action_mapping.original_action) 
    #print("Preconditions", grounded_action.precondition.parts)
    grounded_parameters = []
    bagged_objects_in_action = []
    preconds = [grounded_action.precondition] if not len(grounded_action.precondition.parts) else list(grounded_action.precondition.parts)
    
    #print("Grounded Params", grounded_action.parameters, " Step params", step_parameters)
        
    # Pre-grounded actions for goal macropredicates
    pregrounded_paramater_indices = []
    current_pregrounded_paramater_index = 0
    for var_mapping in grounded_action_mapping:
        parameter_index = [x.name for x in action_mapping.original_action.parameters].index(var_mapping.variable)
        pregrounded_paramater_indices.append(parameter_index)
    
    original_action_index = 0
    #print("num", action_mapping.num_params_to_ground + len(grounded_action_mapping)-1)
    for p in range(0, action_mapping.num_params_to_ground + len(grounded_action_mapping)):
    
        
        grounded_solution_param = step_parameters[original_action_index]
        original_variable_name = grounded_action.parameters[p].name
        #print("p = ", p, grounded_solution_param, original_variable_name)
        
        
        # Variable has been removed from operator but it should be equal to another parameter
        equal_to_param = [x for x in orig_reform_mapping.equality_mapper if x.action_name == action_mapping.reformulated_action and x.param_name_removed == original_variable_name]
        if len(equal_to_param):
            grounded_parameters.append(equal_to_param[0].param_name_removed)
            bagged_objects_in_action.append(copy.deepcopy(equal_to_param[0]))
            grounded_solution_param = "$$$" +  equal_to_param[0].param_name_removed # Temporary name
            
           
        # Parameter maps to pre-grounded object (ie. a modified action with the grounded object in the name)
        elif p in pregrounded_paramater_indices:
            
            grounded_solution_param = grounded_action_mapping[current_pregrounded_paramater_index].ground_to
            grounded_parameters.append(grounded_solution_param)
            current_pregrounded_paramater_index = current_pregrounded_paramater_index + 1
            #print("P is in pregrounded_paramater_indices", grounded_solution_param)
            
            # Is the pre-grounded a bag?
            if grounded_solution_param in [x.bagged_object for x in orig_reform_mapping.bag_mappings]: 
                grounded_solution_param = grounded_solution_param + " " + original_variable_name
                bagged_objects_in_action.append(grounded_solution_param)
                grounded_parameters[-1] = original_variable_name
           
           
        # Parameter maps to bagged object    
        elif grounded_solution_param in [x.bagged_object for x in orig_reform_mapping.bag_mappings]:
            #print("Grounded_solution_param is in [x.bagged_object for x in bag_mappings]", grounded_solution_param)
            grounded_solution_param = grounded_solution_param + " " + original_variable_name
            bagged_objects_in_action.append(grounded_solution_param)
            grounded_parameters.append(original_variable_name)
            original_action_index = original_action_index + 1
       
       
        # Parameter maps to pre-grounded object (ie. a standard object that is not baggable and not in the action name)
        else:
            #print("Parameter maps to pre-grounded object")
            grounded_parameters.append(grounded_solution_param)
            original_action_index = original_action_index + 1
       
               
        #print(p, "Parameter", step_parameters[p], "set to", grounded_parameters[-1])
        
           
           
        # Ground parameter in preconditions and effects
        for atom in preconds + [x.literal for x in grounded_action.effects]:
            param_index = [i for i in range(len(atom.args)) if atom.args[i] == original_variable_name]
            atom.args = list(atom.args)
            for i in param_index:
                atom.args[i] = grounded_solution_param
            atom.args = tuple(atom.args)    
           
    
    
    # Any baggable parameters which were added because they were removed from reformulated action 
    # but are equal to another baggable parameter - need to be added to the list of baggable objects
    for to_bag in [x for x in bagged_objects_in_action if type(x) is mapping_printer.BagEqualityMapper]:
        equal_object = [x for x in  bagged_objects_in_action if type(x) is str and x.split()[1] == to_bag.param_name_included][0]
        bagged = str(equal_object.split()[0]) + " " + str(to_bag.param_name_removed)
        bagged_objects_in_action.remove(to_bag)
        bagged_objects_in_action.append(bagged)
        
        
        # Now we can ground the parameter in preconditions and effects
        for atom in preconds + [x.literal for x in grounded_action.effects]:
            param_index = [i for i in range(len(atom.args)) if atom.args[i] == "$$$" +  to_bag.param_name_removed]
            atom.args = list(atom.args)
            for i in param_index:
                atom.args[i] = bagged
            atom.args = tuple(atom.args)  
        
    

    grounded_action.parameters = grounded_parameters
    # print("Grounded action", grounded_action.name, [x for x in grounded_action.parameters], [x for x in grounded_action.precondition.parts], [x.literal for x in grounded_action.effects])
    return grounded_action, bagged_objects_in_action
       



# Update state and move to next action. ASSUMPTION: assign objects are ignored    
def update_state(state, grounded_action):
    
    
    # Positive effects
    for effect in [x.literal for x in grounded_action.effects if not x.literal.negated]:
        state.append(effect)
    
    # Negative effects
    for effect in [x.literal for x in grounded_action.effects if x.literal.negated]:
        #print("YYY", type(effect), type(effect.negate()), type(effect.negate().pddl_str()), state[0].pddl_str(), type(state), type(state[0]))
        #print([x for x in state if str(x.pddl_str()) != str(effect.negate().pddl_str())])
        matching_atom = [x for x in state if x.pddl_str() == effect.negate().pddl_str()]
        if len(matching_atom) == 1:
            state.remove(matching_atom[0])
        #if len(matching_atom) > 1:
            #raise ValueError('ERROR: duplicate atom in state!')
        
        
    
    
# Account for initial-state equivalence by swapping bagged objects around until goal is satisfied 
def tidy_solution(original_solution, real_goal_state, this_goal_state, orig_reform_mapping):
    
    this_goal_state = [x for x in this_goal_state if type(x) is pddl.conditions.Atom and not x.predicate == '=']
    
    valid_mappings = []
    ISE_classes = []
    
    # Find GSE bags - we do not need to adjust these
    for e_class in list(OrderedDict.fromkeys([x.bagged_object for x in orig_reform_mapping.bag_mappings])):
        members_of_class = [x.original_object for x in orig_reform_mapping.bag_mappings if x.bagged_object == e_class]
        matching_GSE = orig_reform_mapping.goal_state_equivalence_classes.get_class(members_of_class[0].name)[0]
        gse_class = True
        for obj in members_of_class:
            if not obj.name in matching_GSE:
                gse_class = False
                break
        
        if not gse_class:
            ISE_classes.append(e_class)
            if options.writeout_reformulation_logic:
                print('Equivalence class {' + ', '.join([x.name for x in members_of_class]) + '} is NOT goal state equivalent -> proceed with repainting.')
        if gse_class and options.writeout_reformulation_logic:
            print('Equivalence class {' + ', '.join([x.name for x in members_of_class]) + '} is goal state equivalent -> no repainting is necessary.')


    # Find a valid mapping between reformulated goal baggable objects and original goal baggable objects for ISE non-GSE bags
    # One class is done at a time, goal-predicate arguments from classes not yet resolved are ignored 
    future_classes = copy.deepcopy(ISE_classes)
    for e_class in ISE_classes:
        future_classes.remove(e_class)
        bag = [x.original_object for x in orig_reform_mapping.bag_mappings if x.bagged_object == e_class]
        future_class_objects = [x.original_object.name for x in orig_reform_mapping.bag_mappings if x.bagged_object in future_classes] 
        valid_mappings = valid_mappings + resolve_bag(bag, copy.deepcopy(real_goal_state), copy.deepcopy(this_goal_state), future_class_objects)
    
    
    # Use the mapping regime to string replace objects in the solution
    for mapping in valid_mappings:
        original_solution = re.sub('[$]' + mapping.bagged_object_with_wrong_goal.name + '[$]', mapping.bagged_object_with_correct_goal.name, original_solution)
    original_solution = re.sub('[$]', '', original_solution)
    if options.writeout_reformulation_logic:
        print("\nREFORMULATED FINAL SOLUTION:")
        print(original_solution)
        
    
    return original_solution


    
def resolve_bag(bag, original_goal, reformulated_goal, future_class_objects):
    
    # We must ignore any predicates that have arguments from classes we haven't resolved yet
    original_goal = [x for x in original_goal if len([y for y in x.args if y in future_class_objects]) == 0]
    #reformulated_goal = [x for x in reformulated_goal if len([y for y in x.args if y in future_class_objects]) == 0]
    
    satisfying_mappings = []
    
    
    for obj in bag:
        #print("Attempting to map", obj)

        for mapping_candidates in bag:
            #print("Candidate:", mapping_candidates)
            
            mapping_satisfies_goal = True
            
            # Map object to reformulated goal
            reformulated_goal_copy = copy.deepcopy(reformulated_goal)
            reformulated_goal_atoms_with_candidate = [x for x in reformulated_goal_copy if obj.name in x.args]
            for goal_atom in reformulated_goal_atoms_with_candidate:
                for a in range(0, len(goal_atom.args)):
                    new_args = list(goal_atom.args)
                    new_args[a] = mapping_candidates.name if new_args[a] == obj.name else new_args[a]
                    goal_atom.args = tuple(new_args)
            
            
            # Does this mapping satisfy the new goal
            original_goal_atoms_with_candidate = [x for x in original_goal if mapping_candidates.name in x.args]
            for original_goal_atom in original_goal_atoms_with_candidate:
            #for reformulated_goal_atom in reformulated_goal_atoms_with_candidate:
                #print('Checking for satisfaction', original_goal_atom.pddl_str(), [x.pddl_str() for x in reformulated_goal_atoms_with_candidate])
                if not original_goal_atom.pddl_str() in [x.pddl_str() for x in reformulated_goal_atoms_with_candidate]:
                    mapping_satisfies_goal = False
                    break
                #print(original_goal_atom.pddl_str(), 'is satisfied by', [x.pddl_str() for x in reformulated_goal_atoms_with_candidate])
            
            if mapping_satisfies_goal:
                satisfying_mappings.append(mapping_printer.BaggedObjectMap(obj, mapping_candidates))
            
    
    # Due to partial matches, not all mappings are valid
    # Prune the list of mappings so that each object appears is mapped to and from precisely one object
    unmapped_objs = copy.deepcopy(bag)
    valid_mappings = []
    time_since_last_validation = 0
    while len(unmapped_objs):
    
        X = unmapped_objs.pop(0)

        
        # Does this mapping (X -> X') only have one possible value of X'?
        X_map = [x for x in satisfying_mappings if x.bagged_object_with_wrong_goal == X]
        if not len(X_map):
            raise ValueError("ERROR: unable to satisfy object", X, "in goal state!")
        
        # If there is only one valid options or if we have been round a complete cycle, then force this object to assume a mapping
        if len(X_map) == 1 or time_since_last_validation == len(unmapped_objs):
            satisfying_mappings = [x for x in satisfying_mappings if not x.bagged_object_with_correct_goal == X_map[0].bagged_object_with_correct_goal]
            valid_mappings.append(X_map[0])
            time_since_last_validation = 0
            if options.writeout_reformulation_logic:
                print('Object', X_map[0].bagged_object_with_wrong_goal.name, 'in the reformulated solution is being mapped to', X_map[0].bagged_object_with_correct_goal.name)
        
        else:
            unmapped_objs.append(X)
            time_since_last_validation = time_since_last_validation + 1
    
    return valid_mappings
    
           
    
    
    
    
    
