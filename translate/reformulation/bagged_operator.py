from collections import OrderedDict
from . import helper_functions
from . import mapping_printer
from . import relation_mapping
import pddl
import copy
import sys

class BaggableOperator():
    def __init__(self, original_space_action, task):
        self.name = original_space_action.name
        self.original_action_name = original_space_action.name
        self.precondition = copy.deepcopy(original_space_action.precondition)
        self.effects = copy.deepcopy(original_space_action.effects)
        self.parameters = copy.deepcopy(original_space_action.parameters)
        self.num_external_parameters = original_space_action.num_external_parameters
        self.cost = original_space_action.cost
        self.task = task
        self.baggable_parameters = []
        self.grounded_to_bagname = False
    
    def convert_to_pddl_action(self):
        return pddl.actions.Action(self.name, self.parameters, self.num_external_parameters, self.precondition, self.effects, self.cost)    
    
    
    # Ground the specified parameter to each specified bag       
    def ground_to_bags(self, param, bagnames, variables_to_ground_mapping_list, action_names):
        new_actions = []
        
        for bagname in bagnames:
        
            op_copy = copy.deepcopy(self)
        
            # Remove the parameter and replace its occurrences
            op_copy.name = helper_functions.create_unique_name(op_copy.name + "%" + bagname, action_names)
            action_names.append(op_copy.name)
            op_copy.parameters = [x for x in op_copy.parameters if x.name != param.name]
            helper_functions.ground_atoms(list(op_copy.precondition.parts) + [x.literal for x in op_copy.effects if type(x) is not pddl.f_expression.Assign], param.name, bagname)
            op_copy.grounded_to_bagname = bagname
        
            # Create the new mapping
            num_objs_of_param_supertype =  len([x for x in self.task.objects if x.type_name in helper_functions.get_supertypes(param.type_name, self.task)])
            variable_mapper = mapping_printer.VariablesToGroundMapping(param, bagname, num_objs_of_param_supertype, "")
            variable_mapper.grounded_action = op_copy.name
            variables_to_ground_mapping_list.append(variable_mapper)
            
            new_actions.append(op_copy)
            
            print("Created new operator", op_copy.name)
        
        return new_actions
        
        
        
    def ground_atoms_for_goal(self, variable_to_ground_map, action_names):    
        
        #print("Grounding atoms for goal for", self.name, self.parameters, variable_to_ground_map.variable, "\n") 
        
        if len([x for x in self.parameters if x == variable_to_ground_map.variable]):
            self.parameters.remove(variable_to_ground_map.variable)
        self.name = helper_functions.create_unique_name(self.name + "%" + variable_to_ground_map.ground_to, action_names)
        action_names.append(self.name)
        variable_to_ground_map.grounded_action = self.name

        
        new_action_preconds = [self.precondition] if not len(self.precondition.parts) else list(self.precondition.parts)
        for atom in new_action_preconds + [x.literal for x in self.effects]:
            param_index = [i for i in range(len(atom.args)) if atom.args[i] == variable_to_ground_map.variable.name]
            atom.args = list(atom.args)
            for i in param_index:
                atom.args[i] = variable_to_ground_map.ground_to
            atom.args = tuple(atom.args)
               
        


class BaggableParameter():
    def __init__(self, parameter, baggable_type, reformulated_operator, original_space_operator, task, conditionalEffectClassesForActionAndParameter):
    
        self.parameter = parameter
        self.task = task
        self.baggable_type = baggable_type
        self.reformulated_operator = reformulated_operator
        self.original_space_operator = original_space_operator
        self.conditionalEffectClasses = conditionalEffectClassesForActionAndParameter
        
        self.precondition_atom_to_increment = None # The two macropredicates which describe the bag before the operator has been applied.
        self.precondition_atom_to_decrement = None #      If there are no macropredicate effects then only precondition_atom_to_decrement is used
        self.precondition_less_than_atom = None
        
        self.effect_atom_to_increment = None # The two macropredicates which describe the bag
        self.effect_atom_to_decrement = None #      after the operator has been applied
        self.effect_less_than_atom = None
        
    
    # Will this operator change the bagState of this parameter?       
    def does_action_modify_bagged_parameter(self):
        pass
        # return effect_atom_to_increment is not None # MafeComentado
    
    
    # Create and then ground the initial macropredicate precondition for the operator
    def initialise_macropredicate_for_parameter(self):
        
        action_precond = tuple([self.original_space_operator.precondition]) if not len(self.original_space_operator.precondition.parts) else self.original_space_operator.precondition.parts
        
        preconditions_of_this_obj = [x for x in action_precond if self.parameter.name in x.args and not x.predicate == "="]
        effects_of_this_obj = [x.literal for x in self.original_space_operator.effects if type(x) is not pddl.f_expression.Assign and self.parameter.name in x.literal.args and not x.literal.predicate == "="]
        if not len(preconditions_of_this_obj) and not len(effects_of_this_obj):
            return False
            
        
        
        precond_args = self.build_macropredicate_in_action(preconditions_of_this_obj)
        macropredicate = self.baggable_type.macropredicate
        
        # Add counter - only positive preconditions for now
        num_object_variable_name = helper_functions.create_unique_name('?n1', [x.name for x in self.reformulated_operator.parameters], True)
        # self.reformulated_operator.parameters.append(pddl.pddl_types.TypedObject(num_object_variable_name, macropredicate.num_object.type_name)) # MafeComentado
        precond_args.append(num_object_variable_name)
        new_precondition = pddl.conditions.Atom(macropredicate.name, precond_args)

        
        # Add less predicate so that we know that there exists a number less than the current one (or there are zero occurrences)
        less_number_variable_name = helper_functions.create_unique_name('?n0', [x.name for x in self.reformulated_operator.parameters], True)
        # less_than_precondition = pddl.conditions.Atom(macropredicate.less_than_pred.name, [less_number_variable_name, num_object_variable_name])  # MafeComentado
        # self.reformulated_operator.parameters.append(pddl.pddl_types.TypedObject(less_number_variable_name, macropredicate.num_object.type_name)) # MafeComentado
        
        
        # self.precondition_less_than_atom = less_than_precondition # MafeComentado
        self.precondition_atom_to_decrement = new_precondition
        
        
        # Remove the original space preconditions from the reformulated action and add the bagged space preconditions
        self.reformulated_operator.precondition = pddl.conditions.Conjunction([self.reformulated_operator.precondition]) if not len(self.reformulated_operator.precondition.parts) else self.reformulated_operator.precondition
        self.reformulated_operator.precondition.parts = [y for y in self.reformulated_operator.precondition.parts if not y in preconditions_of_this_obj]
        self.reformulated_operator.precondition.parts.append(new_precondition)
        # self.reformulated_operator.precondition.parts.append(less_than_precondition) # MafeComentado


        # If this variable was part of a conditional effect, then cache the count names selected
        for conditionalEffectClass in self.conditionalEffectClasses:
            conditionalEffectClass.num_object_variable_name_precond = num_object_variable_name
            conditionalEffectClass.less_number_variable_name_precond = less_number_variable_name
            conditionalEffectClass.less_than_pred_name = macropredicate.less_than_pred.name

        
        return True
    
    
    
    # Create the initial macropredicate precondition for the operator. This requires finding the variables or constants for each attribute. ?dc parameters may be required
    def build_macropredicate_in_action(self, preconditions_of_this_obj):
    
        args_to_return = [self.parameter.name]
        dc_mappings = []
        macropredicate = self.baggable_type.macropredicate
        for a in range(1, len(macropredicate.args)-1):
            arg = macropredicate.args[a]
            arg_mapper = macropredicate.mappings[a-1]
            
            if arg_mapper[0].arg_points_to_arg_index != -1:
                continue
            
            matching_with_preds = [x for x in arg_mapper if not x.predicate is None and x.predicate.name in [y.predicate for y in preconditions_of_this_obj]]
            
            
            # If more than one match, then it is not single-valued, throw error
            if len(matching_with_preds) > 1:
                raise ValueError('ERROR: Some action is not single-valued!')
            
            
            # If there is no match, then we don't care -> can be any value
            elif not len(matching_with_preds):
                #print("Using don't care object...", [x.value for x in arg_mapper])
                dont_care_variable_name = helper_functions.create_unique_name('?dc', [x.name for x in self.reformulated_operator.parameters])
                dont_care_object_type = arg.type_name
                self.reformulated_operator.parameters.append(pddl.pddl_types.TypedObject(dont_care_variable_name, dont_care_object_type))
                args_to_return.append(dont_care_variable_name)
                
                # Map the ?dc arg for later use
                dc_mappings.append(mapping_printer.ParameterPropertyMap(self.reformulated_operator.name, self.baggable_type.object_type.name, len(self.reformulated_operator.parameters), a)) # Action name, bag type, parameter number, property number (count 1,...,n)
            
            
                # We may need the next argument to define the predicate this argument refers to
                if arg_mapper[0].arg_pointed_to_by_arg_index != -1:
                    dont_care_variable_name_pointer = helper_functions.create_unique_name('?dc', [x.name for x in self.reformulated_operator.parameters])
                    # dont_care_object_type_pointer = macropredicate.args[Map[0].arg_pointed_to_by_arg_index].type_name # MafeComentado
                    # self.reformulated_operator.parameters.append(pddl.pddl_types.TypedObject(dont_care_variable_name_pointer, dont_care_object_type_pointer)) # MafeComentado
                    args_to_return.append(dont_care_variable_name_pointer)
            
            
            # If the value of the match is none, then it is a binary predicate -> use value of object in matching precondition
            elif matching_with_preds[0].value is None:
                #print("Using preexisting object...", matching_with_preds[0].predicate)
                matching_pred = [x for x in preconditions_of_this_obj if x.predicate == matching_with_preds[0].predicate.name][0]
                other_arg_in_pred = [x for x in matching_pred.args if not x == self.parameter.name][0]
                args_to_return.append(other_arg_in_pred)
                
                # We may need the next argument to define the binary predicate this argument refers to
                if arg_mapper[0].arg_pointed_to_by_arg_index != -1:
                    index_map = macropredicate.mappings[arg_mapper[0].arg_pointed_to_by_arg_index - 1]
                    pointer_pred = [x for x in index_map if x.predicate is not None and x.predicate.name == matching_pred.predicate][0]
                    args_to_return.append(pointer_pred.value.name)
                
                
            # If there is a value, it is a unary predicate -> use argument mapper's constant value
            else:
                #print("Using constant...", matching_with_preds[0].value, matching_with_preds[0].predicate)
                args_to_return.append(matching_with_preds[0].value.name)
                
                # We may need the next argument to state that this argument refers to a unary predicate
                if arg_mapper[0].arg_pointed_to_by_arg_index != -1:
                    none_object_name = [x.value.name for x in macropredicate.mappings[arg_mapper[0].arg_pointed_to_by_arg_index - 1] if x.predicate is None][0]
                    args_to_return.append(none_object_name)
         
        
        # Add the dc mappings to the solution mapper for later use                
        self.task.solution_mapper.parameter_property_mapping.append(dc_mappings)
        return args_to_return
        
        
        
    # Add all the effects for this parameter. If effects are necessary then action will also require additional precondition    
    def add_macropredicates_for_parameter(self):
        
        peffects_with_this_object = [x.literal for x in self.original_space_operator.effects if not x.literal.negated and self.parameter.name in x.literal.args]
        neffects_with_this_object = [x.literal for x in self.original_space_operator.effects if x.literal.negated and self.parameter.name in x.literal.args]
        
        if not len(neffects_with_this_object):
            return False
            
        
        
        # For each argument in precondition
        macropredicate = self.baggable_type.macropredicate
        args_to_return = [self.parameter.name]
        for a in range(1, len(self.precondition_atom_to_decrement.args)-1):
            precond_arg = self.precondition_atom_to_decrement.args[a]
            arg_mapping = macropredicate.mappings[a-1]
            
            if arg_mapping[0].arg_points_to_arg_index != -1:
                continue
            
            # By definition of single-valued, no positive effect will be added if there is not a negative effect in the same slot
            negeffect =  [x for x in arg_mapping if not x.predicate is None and x.predicate.name in [y.predicate for y in neffects_with_this_object]]
            if len(negeffect) > 1:
                raise ValueError('ERROR: Some action is not single-valued for a negative effect!')
            
            if not len(negeffect):
                args_to_return.append(precond_arg)
                
                # Use the same pointer argument
                if arg_mapping[0].arg_pointed_to_by_arg_index != -1:
                   args_to_return.append(self.precondition_atom_to_decrement.args[arg_mapping[0].arg_pointed_to_by_arg_index])
                continue
            
            # Is the value replaced by a positive effect or taken to null object?
            poseffect = [y for y in peffects_with_this_object if y.predicate in [x.predicate.name for x in arg_mapping if not x.predicate is None]]
            if len(poseffect) > 1:
                raise ValueError('ERROR: Some action is not single-valued for a positive effect!')
            
            # The argument becomes null # MafeComentado
            #### MafeInicio: ####
            # Esto lo comento porque es para hacer los property-none que yo cambiaría por un 0 en la función
            # if not len(poseffect):
                # args_to_return.append([x.value.name for x in arg_mapping if x.predicate is None][0])
                # 
                # Use the null object as the pointer argument
                # if arg_mapping[0].arg_pointed_to_by_arg_index != -1:
                    # none_object_name = [x.value.name for x in macropredicate.mappings[arg_mapping[0].arg_pointed_to_by_arg_index - 1] if x.predicate is None][0]
                    # args_to_return.append(none_object_name)
                # continue
            # MafeFin
            
            # The argument becomes a unary predicate
            # if len(poseffect[0].args) == 1:
                # args_to_return.append([x.value.name for x in arg_mapping if not x.predicate is None and x.predicate.name == poseffect[0].predicate][0])
                # 
                # Use the null object as the pointer argument
                # if arg_mapping[0].arg_pointed_to_by_arg_index != -1:
                    # none_object_name = [x.value.name for x in macropredicate.mappings[arg_mapping[0].arg_pointed_to_by_arg_index - 1] if x.predicate is None][0]
                    # args_to_return.append(none_object_name)
            
            
            # The argument becomes a binary predicate's value
            # else:
                # other_arg_in_pred = [x for x in poseffect[0].args if not x == self.parameter.name][0]
                # args_to_return.append(other_arg_in_pred)
                # 
                # Use the name of the predicate as the pointer argument
                # if arg_mapping[0].arg_pointed_to_by_arg_index != -1:
                    # index_map = macropredicate.mappings[arg_mapping[0].arg_pointed_to_by_arg_index - 1]
                    # pointer_pred = [x for x in index_map if x.predicate is not None and x.predicate.name == poseffect[0].predicate][0]
                    # args_to_return.append(pointer_pred.value.name)
            #### MafeFin ####
        
        
        
        # Create a precondition with the lower count
        num_object_variable_name = helper_functions.create_unique_name('?n1', [x.name for x in self.reformulated_operator.parameters], True)
        # self.reformulated_operator.parameters.append(pddl.pddl_types.TypedObject(num_object_variable_name, macropredicate.num_object.type_name)) # MafeComentado
        new_precondition = pddl.conditions.Atom(macropredicate.name, args_to_return + [num_object_variable_name])  

                
        # Create a positive effect with the higher count
        more_number_variable_name = helper_functions.create_unique_name('?n2', [x.name for x in self.reformulated_operator.parameters], True)
        # less_than_precondition = pddl.conditions.Atom(macropredicate.less_than_pred.name, [num_object_variable_name, more_number_variable_name])  # MafeComentado
        # self.reformulated_operator.parameters.append(pddl.pddl_types.TypedObject(more_number_variable_name, macropredicate.num_object.type_name)) # MafeComentado
        new_effect = pddl.conditions.Atom(macropredicate.name, args_to_return + [more_number_variable_name])
        
        # Add old preconditions to negative effects 
        original_precond_remove = pddl.conditions.NegatedAtom(macropredicate.name, self.precondition_atom_to_decrement.args)
        # original_precond_add = pddl.conditions.Atom(macropredicate.name, list(self.precondition_atom_to_decrement.args[:-1]) + [self.precondition_less_than_atom.args[0]]) # MafeComentado
        new_precond_neffect = pddl.conditions.NegatedAtom(macropredicate.name, new_precondition.args)
        
        
        # Store the atoms in this BaggableParameter object # MafeComentado
        self.precondition_atom_to_increment = new_precondition
        self.effect_atom_to_increment = new_effect
        self.effect_atom_to_decrement = new_precond_neffect.negate()
        # self.effect_less_than_atom = less_than_precondition # MafeComentado
        
        
        # Remove the original space effects from the reformulated action and add the new bagged preconditions/effects
        self.reformulated_operator.effects = [y for y in self.reformulated_operator.effects if not y.literal in peffects_with_this_object + neffects_with_this_object]
        # self.reformulated_operator.effects.append(pddl.effects.Effect([], pddl.conditions.Truth(), original_precond_add)) # MafeComentado
        self.reformulated_operator.effects.append(pddl.effects.Effect([], pddl.conditions.Truth(), original_precond_remove))
        self.reformulated_operator.effects.append(pddl.effects.Effect([], pddl.conditions.Truth(), new_effect))
        self.reformulated_operator.effects.append(pddl.effects.Effect([], pddl.conditions.Truth(), new_precond_neffect))
        self.reformulated_operator.precondition.parts.append(new_precondition)
        # self.reformulated_operator.precondition.parts.append(less_than_precondition) # MafeComentado
        


        # If this variable was part of a conditional effect, then cache the count names selected
        for conditionalEffectClass in self.conditionalEffectClasses:
            conditionalEffectClass.num_object_variable_name_effect = num_object_variable_name
            conditionalEffectClass.more_number_variable_name_effect = more_number_variable_name



        return True
                    

    # Returns a list of variables which appear in one of these macropredicates which needs to be grounded to an object which appears in the goal
    # If an empty list is returned then this baggable parameter does not require any goal macropredicates
    def get_variables_to_ground_for_goal_macropredicates(self, relevant_goal_macropredicates, goal_macropredicate):
        
        
        if not goal_macropredicate.is_goal_macro:
            return []
            
        #print("Attempting to ground for", self.reformulated_operator.name, relevant_goal_macropredicates)
        variables_to_ground_mapping_list = []

        for pred in relevant_goal_macropredicates:

            objects_in_goal = []
            #print("\tGoal predicate of interest:", pred)
            for i in range(1, len(pred.args)-1):
                
                attr = pred.args[i]
                attr_mappings = goal_macropredicate.mappings[i-1]
                
                
                if attr_mappings[0].arg_points_to_arg_index != -1:
                    continue
                
                #print("\t\tAttribute", attr)
                
                if attr in objects_in_goal:
                    continue
                objects_in_goal.append(attr)
                
                # Find supertype of this object
                attr_reform_type = [x for x in attr_mappings if not x.value is None and x.value.name == attr]
                if not len(attr_reform_type): # Mapped back to original object eg. cocktail1, and not predicate object eg. empty-true 
                    attr_reform_type = [y for y in self.task.types if y.name == [x.type_name for x in self.task.objects if x.name == attr][0]][0]
                else: # Mapped back to predicate object
                    attr_reform_type = [y for y in self.task.types if y.name == attr_reform_type[0].value.type_name][0]
                attr_supertype = helper_functions.get_supertypes(attr_reform_type, self.task)
                
                #print("Attribute of interest", attr, "with supertype", attr_supertype, "and type", attr_reform_type)

                
                action_preconds = tuple([self.reformulated_operator.precondition]) if not len(self.reformulated_operator.precondition.parts) else self.reformulated_operator.precondition.parts
                preconds_with_this_macropredicate = [x for x in action_preconds if x.predicate == goal_macropredicate.parent_name]
                
                # Find the parameters which are used in this argument
                params = [x for x in self.reformulated_operator.parameters if x.name in [y.args[goal_macropredicate.parent_arguments_to_include[i-1]] for y in preconds_with_this_macropredicate] and x.type_name in attr_supertype] + [x for x in self.task.objects if x.name in [y.args[i] for y in relevant_goal_macropredicates]]
                #print("\t\tAction parameters", params)
                
                #print("XXX", [x for x in action.parameters], self.parent_arguments_to_include[i-1], [y.args[self.parent_arguments_to_include[i-1]] for y in preconds_with_this_macropredicate])				
                # Find corresponding parameters of this supertype # ASSUMPTION: is this overkill??
                #params = [x for x in action.parameters if x.type_name in attr_supertype]
                for param in params:
                    
                    #print("\t\t\tParameter of interest:", param)
                    # Does this parameter appear as an attribute for a macropredicate
                    #print("Preconds", [x.predicate for x in action_preconds], self.parent_name, self.name)
                    macropredicate_with_attr = [x for x in preconds_with_this_macropredicate if param.name in x.args]
                    
                    
                    # See if the next attribute points to this one, differs between the two macropredicates and is in the goal
                    pointer_value_in_goal = ""
                    if attr_mappings[0].arg_pointed_to_by_arg_index != -1:
                        macropredicate_with_attr = [x for x in preconds_with_this_macropredicate if param.name in x.args and pred.args[attr_mappings[0].arg_pointed_to_by_arg_index] in x.args]
                        pointer_value_in_goal = pred.args[attr_mappings[0].arg_pointed_to_by_arg_index]
                        
                        
                    
                    if not len(macropredicate_with_attr) or len(list(OrderedDict.fromkeys([x.args[0] for x in macropredicate_with_attr]))) != len(macropredicate_with_attr):
                        #print(param.name, "does not change in", self.reformulated_operator.name, "--> will not add goal macropredicates.")
                        continue
                    
                    # No more than 2 macropredicates of this type will use this bagged object
                    bag_name_of_macropredicate = macropredicate_with_attr[0].args[0]
                    otherprecond_with_bag = [x for x in preconds_with_this_macropredicate if x.args[0] == bag_name_of_macropredicate and x != macropredicate_with_attr[0]]
                    
                    

                    # If there exists a second macropredicate precondition with the same bag but a different value for this attribute, then this action can change the value of the attribute
                    if len(otherprecond_with_bag):
                        print("Adding new", self.reformulated_operator.name, "for", attr, "in", pred.predicate, "for param", param)
                        num_objs_of_param_supertype =  len([x for x in self.task.objects if x.type_name in helper_functions.get_supertypes(param.type_name, self.task)])
                        variables_to_ground_mapping_list.append(mapping_printer.VariablesToGroundMapping(param, attr, num_objs_of_param_supertype, pointer_value_in_goal))
        
        
        if len(list(OrderedDict.fromkeys([x.variable.name for x in variables_to_ground_mapping_list]))) > 1:
            print("Unable to add goal-macropredicates to action", self.reformulated_operator.name, "because more than 1 parameter is in the goal:", list(OrderedDict.fromkeys([x.variable.name for x in variables_to_ground_mapping_list])))
            sys.exit()      
                                          
        return variables_to_ground_mapping_list     
        
        
        

    
    # Add preconditions for the goal macropredicate using the variable grounding mappings generated earlier
    def add_precondition_for_goal_macopredicate(self, goal_macropredicate, variables_to_ground_mapping_list): 
        
        
        if not len(variables_to_ground_mapping_list):
            return [], None, []            
        
        
        preconds_to_return = []
        count_mapping = []  
        params_to_add = []
          
        # Less than preconditions
        for precond in [x for x in [self.precondition_less_than_atom, self.effect_less_than_atom] if not x is None]:
            
            # Create goal-number version of this number
            goal_macro_num_small = helper_functions.create_unique_name(precond.args[0] + "_1", [x.name for x in self.reformulated_operator.parameters + params_to_add], True)
            # params_to_add.append(pddl.pddl_types.TypedObject(goal_macro_num_small, goal_macropredicate.num_object.type_name)) # MafeComentado
            count_mapping.append(relation_mapping.count_mapper(precond.args[0], goal_macro_num_small))   
            
            goal_macro_num_large = helper_functions.create_unique_name(precond.args[1] + "_1", [x.name for x in self.reformulated_operator.parameters + params_to_add], True)
            # params_to_add.append(pddl.pddl_types.TypedObject(goal_macro_num_large, goal_macropredicate.num_object.type_name)) # MafeComentado
            count_mapping.append(relation_mapping.count_mapper(precond.args[1], goal_macro_num_large)) 
            
            
            # Create new less than precondition with these new numbers
            new_less_than_precondition = pddl.conditions.Atom(goal_macropredicate.less_than_pred.name, [goal_macro_num_small, goal_macro_num_large])
            preconds_to_return.append(new_less_than_precondition)
            


        # Macropredicate preconditions for this object
        macro_preconds_in_action = []
        macropredicate_preconds_with_parameter = [x for x in self.reformulated_operator.precondition.parts if type(x) is pddl.conditions.Atom and x.predicate == goal_macropredicate.parent_name and x.args[0] == self.parameter.name]
        for precond in macropredicate_preconds_with_parameter:
            precond_args = [precond.args[0]]
            for val in goal_macropredicate.parent_arguments_to_include:
                precond_args.append(precond.args[val])
            
            
            # Set the final argument to the mapped version of this number
            mapped_num = [x.goal for x in count_mapping if x.orig == precond.args[-1]][0]
            precond_args.append(mapped_num)
            macro_preconds_in_action.append(pddl.conditions.Atom(goal_macropredicate.name, precond_args))

      
        # If all of the arguments (except count) are identical in the two preconditions, then nothing changes wrt. this goal macropredicate -> no goal macropredicate needed in this action (for this object)
        if len(macropredicate_preconds_with_parameter) == 2 and macro_preconds_in_action[0].args[:-1] == macro_preconds_in_action[1].args[:-1]:
            return [], None, []
        
        # If there is only one precondition macropredicate, nothing changes -> no goal macropredicate needed
        if len(macropredicate_preconds_with_parameter) == 1:
            return [], None, []
            
        
        
        # Remove any preconditions whose objects are not featured in the goal state
        for i in range(0, 2):
            to_remove = not len([y for y in macro_preconds_in_action[i].args if y in [z.variable.name for z in variables_to_ground_mapping_list]])
            if variables_to_ground_mapping_list[0].pointer_value != "":
                to_remove = not len([y for y in macro_preconds_in_action[i].args if y in [z.pointer_value for z in variables_to_ground_mapping_list]]) 
            if to_remove:
                macro_preconds_in_action[i] = None
                preconds_to_return[i] = None
                params_to_add[2 * i] = None
                params_to_add[2 * i + 1] = None
        
        preconds_to_return = [x for x in preconds_to_return if not x is None] + [x for x in macro_preconds_in_action if not x is None]
        return preconds_to_return, count_mapping, [x for x in params_to_add if not x is None]
                                

       
    # Add effects for the goal macropredicate using the variable grounding mappings generated earlier
    def add_effects_for_goal_macopredicate(self, goal_macropredicate, count_mapping, variables_to_ground_mapping_list):
        
        
        effects_to_return = []
        macropredicate_effects_with_parameter = [x.literal for x in self.reformulated_operator.effects if not type(x) is pddl.f_expression.Assign and x.literal.predicate == goal_macropredicate.parent_name and x.literal.args[0] == self.parameter.name]
        effects_with_args_in_goal = [x for x in macropredicate_effects_with_parameter if len([y for y in x.args if y in [z.variable.name for z in variables_to_ground_mapping_list]])]
        
        if variables_to_ground_mapping_list[0].pointer_value != "":
            effects_with_args_in_goal = [x for x in macropredicate_effects_with_parameter if len([y for y in x.args if y in [z.pointer_value for z in variables_to_ground_mapping_list]])]
        
        
        #print("effects_with_args_in_goal", effects_with_args_in_goal)
        
        for effect in effects_with_args_in_goal:
            effect_args = [effect.args[0]]
            for val in goal_macropredicate.parent_arguments_to_include:
                effect_args.append(effect.args[val])
            
            mapped_num = [x.goal for x in count_mapping if x.orig == effect.args[-1]][0]
            effect_args.append(mapped_num)
            if effect.negated:
                effects_to_return.append(pddl.conditions.NegatedAtom(goal_macropredicate.name, effect_args))
            else:
                effects_to_return.append(pddl.conditions.Atom(goal_macropredicate.name, effect_args))
        
        return effects_to_return
        
        
        
    
        
        