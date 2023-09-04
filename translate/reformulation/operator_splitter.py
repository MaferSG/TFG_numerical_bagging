import pddl
import re
import options
import copy
import sys
from . import helper_functions
from collections import OrderedDict


class splitter():
    def __init__(self, action, task):
        self.action = action
        self.task = task

    
    def build_parameter_equivalence_pairs(self, baggable_types_list):
    
        # Find pairs of baggable parameters in the operator. For each pair there is a possibility that the two may be instantiated to the same grounded macropredicate 
        # We are stopping at pairs (not triplets etc) for simplicity in coding
        # In the case of overlapping pairs, Baggy is aborted.
    
        if self.action.precondition.parts == None:
            return []
        #print("Action", self.action.name)
        equivalence_classes = []
        for baggable_type in baggable_types_list:
        
            for macropred in [baggable_type.macropredicate] + baggable_type.goal_macropredicates:
            
            
                # We build equivalence pairs for preconditions and for effects
                for precondOrEffect in range(0,2):
            
            
                    # Find all preconditions/effects of this macropredicate. (We search for these in the preconditions. The effect macropredicate refers to the attributes of the bag after the action has been applied) 
                    precondOrEffects_with_macropred = []
                    precond_is_in_pair = []
                    #for param_name in [x.name for x in self.action.parameters if x.type_name == baggable_type.object_type.name]:
                    for param_name in list(OrderedDict.fromkeys([x.args[0] for x in self.action.precondition.parts if x.predicate == macropred.name])):
                        macro = [x for x in self.action.precondition.parts if x.predicate == macropred.name and x.args[0] == param_name]
                    
                        # Add precond / effect to list
                        if len(macro) > precondOrEffect:
                            precondOrEffects_with_macropred.append(macro[precondOrEffect])
                            precond_is_in_pair.append(False)
                    
                    
                        # Does the parameter form an equivalence pair with itself? Can the precondition and effect be instantiated to the same predicate?
                        if precondOrEffect == 0 and len(macro) == 2:
                            can_be_paired, variable_args_that_can_be_instantiated = self.check_if_pair_can_be_instantiated(macro[0], macro[1], self.action)
                            can_be_paired = can_be_paired and macro[0].args[0] != macro[1].args[0]
                            if can_be_paired:
                                if options.writeout_reformulation_logic:
                                    print("Action ", self.action.name, " requires splitting {", macro[0].args[0], ", ", macro[1].args[0], "} as an equivalence pair.", sep = "")
                                equivalence_classes.append(self.parameter_equivalence_class(macro, macropred, variable_args_that_can_be_instantiated, 2))
                                precond_is_in_pair[-1] = True
                    
                
                
                    if len(precondOrEffects_with_macropred) < 2:
                        continue
                    
            
                    # Iterate through each pair of macro preconds
                    for i in range(0, len(precondOrEffects_with_macropred)):
                        macro_precond_i = precondOrEffects_with_macropred[i]
                        for j in range(i+1, len(precondOrEffects_with_macropred)):
                            macro_precond_j = precondOrEffects_with_macropred[j]
                    
                            can_be_paired, variable_args_that_can_be_instantiated = self.check_if_pair_can_be_instantiated(macro_precond_i, macro_precond_j, self.action)
                    
                            # Update pairing
                            if can_be_paired:
                    
                                # Ensure that there is a neq precond which refers to the old unbagged parameters. If not then we don't bag
                                neq_precond = [x for x in self.action.precondition.parts if type(x) is pddl.conditions.NegatedAtom and x.predicate == "=" and macro_precond_i.args[0] in x.args and macro_precond_j.args[0] in x.args]
                                if not len(neq_precond) and macro_precond_i.args[0] != macro_precond_j.args[0]:
                                    print("Action", self.action.name, "can instantiate the macropredicates of", macro_precond_i.args[0], "and", macro_precond_j.args[0] ,"the same but there is no neq precondition -> Baggy cannot treat objects from the same bag as the same object. There will be no reformulation.")
                                    sys.exit()
                            
                                # Now remove the neq precondition from the operator
                                #self.action.precondition.parts = [x for x in self.action.precondition.parts if not x in neq_precond]
                    
                                if options.writeout_reformulation_logic:
                                    print("Action ", self.action.name, " requires splitting {", macro_precond_i.args[0], ", ", macro_precond_j.args[0], "} as an equivalence pair.", sep = "")
                    
                                # Ensure that neither of the macropreds are already paired
                                if precond_is_in_pair[i] or precond_is_in_pair[j]:
                                    print("Action", self.action.name, "has a parameter class of size 3 or more -> Baggy cannot do that yet. There will be no reformulation.")
                                    sys.exit()
                                
                                
                                # Are there corresponding goal macropredicates? If both have goal macropredicates then we need to increment/decrement them by 2
                                #goal_macropredicate_preconditions = [x for x in self.action.precondition.parts if x.predicate in [y.name for y in baggable_type.goal_macropredicates] and (x.args[0] == macro_precond_i.args[0] or x.args[0] == macro_precond_j.args[0])]
                                #print("Goalmacros", [x for x in self.action.precondition.parts if x.predicate in [y.name for y in baggable_type.goal_macropredicates]])
                            
                                #goal_macropredicate_preconditions = goal_macropredicate_preconditions if len(goal_macropredicate_preconditions) == 2 else False
                    
                    
                                equivalence_classes.append(self.parameter_equivalence_class([macro_precond_i, macro_precond_j], macropred, variable_args_that_can_be_instantiated, precondOrEffect))
                                precond_is_in_pair[i] = True
                                precond_is_in_pair[j] = True
        
        return equivalence_classes
                    
    
    # Can the pair of macropredicate atoms be grounded into the same atom?
    def check_if_pair_can_be_instantiated(self, macro_i, macro_j, action):
    
    
        # If bag variables have already been grounded and are different then the two cannot be grounded together
        if macro_i.args[0][0] != "?" and macro_j.args[0][0] != "?" and macro_i.args[0] != macro_j.args[0]:
            return False, []
            

        # Iterate through each arg of these preconditions. The two preconds form an equivalence pair if every attribute can be instantiated to the same value
        variable_args_that_can_be_instantiated = [0]
        for arg_num in range(1, len(macro_i.args)-1):
        
            arg_i = macro_i.args[arg_num]
            arg_j = macro_j.args[arg_num]
        
            # Can the two args be instantiated to the same value?
        
                # 1) If they are the same constant/variable then yes
            if arg_i == arg_j:
                continue 
        
              	# 2) If they are different constants then no
            if arg_i[0] != "?" and arg_j[0] != "?":
                return False, []
        
        		# 3) Two different variables can be instantiated together if they are in the same type hierarchy and there is no neq precond
        		#    A variable can be instantiated to the same value as a constant if the variable's type can be instantiated to the constant's type
        
            arg_i_type = self.get_attribute_type(arg_i)
            arg_j_type = self.get_attribute_type(arg_j)
            
            
            neq_precond = [x for x in action.precondition.parts if type(x) is pddl.conditions.NegatedAtom and x.predicate == "=" and arg_i in x.args and arg_j in x.args]
            
            
            if len(neq_precond) == 0 and (arg_i_type[0] in arg_j_type or arg_j_type[0] in arg_i_type):
                variable_args_that_can_be_instantiated.append(arg_num)
            else:
                return False, []
        
        
        return True, variable_args_that_can_be_instantiated
        
    
                        
		
    def get_attribute_type(self, arg_name):
        
        # If argument is a constant then return its type from task
        if arg_name[0] != "?":
            param_type = [x.type_name for x in self.task.objects if x.name == arg_name][0]
            return helper_functions.get_supertypes(param_type, self.task)
            #return [x.type_name for x in self.task.objects if x.name == arg_name]
        
        # If argument is a variable, then find its type and return the type hierarchy
        param = [x for x in self.action.parameters if x.name == arg_name][0]
        param_type = [x for x in self.task.types if x.name == param.type_name][0]
        return helper_functions.get_supertypes(param_type, self.task)
        
        
    def replace_argument_with(old, new, atoms):
        for atom in atoms:
            args = list(atom.args)
            args = [(new if x == old else x) for x in args]
            atom.args = tuple(args)
        
    
    
    class parameter_equivalence_class():
        def __init__(self, atoms, macropred, variable_args_that_can_be_instantiated, precondOrEffect):
            self.params = [atoms[0].args[0], atoms[1].args[0]]
            self.macropred = macropred
            self.atoms = atoms
            self.variable_args_that_can_be_instantiated = variable_args_that_can_be_instantiated
            self.atomsArePreconds = [True,True] if precondOrEffect == 0 else [False,False] if precondOrEffect == 1 else [True,False]
            #self.goal_macropredicate_preconditions = goal_macropredicate_preconditions
            
        def __repr__(self):
            return ("<Precond: " if self.atomsArePreconds[0] else "<Effect: ") + str(self.atoms[0]) + " / " + ("Precond: " if self.atomsArePreconds[1] else "Effect: ") + str(self.atoms[1]) + ">" 


  		### Assumption: the two variable arguments are equivalent. It doesn't matter which we choose. This is incorrect if they have differing preconditions
        def create_eq_operator(self, action, action_names):
            
            action.name = helper_functions.create_unique_name(action.name + "&eq", action_names)
            action_names.append(action.name)
            action.precondition.parts = list(action.precondition.parts)
            
            print("Creating", action.name, "removing", [x for x in action.precondition.parts if x in self.atoms])
            
            # Remove the old macropredicates from the operator (preconds and effects)
            action.precondition.parts = [x for x in action.precondition.parts if not x in self.atoms]
            action.effects = [x for x in action.effects if type(x) is pddl.f_expression.Assign or not x.literal.args[:-1] in [y.args[:-1] for y in self.atoms]]
            
            
            #print("New preconds", [x for x in action.precondition.parts if not x in self.atoms], "\n")
            
            # Merge the two parameters into one
            param_name = self.params[0]
            splitter.replace_argument_with(self.params[1], param_name, [x for x in action.precondition.parts if x in self.atoms])
            splitter.replace_argument_with(self.params[1], param_name, [x.literal for x in action.effects if type(x) is not pddl.f_expression.Assign and x in self.atoms])
            
            # Create new combined macropredicate and remove the old parameters from the parameter list
            new_macropred_args = [param_name]
            for arg_num in range(1, len(self.atoms[0].args)-1):
                
            
                # If the two attributes are the same (same variable or same constant) then use this value
                if self.atoms[0].args[arg_num] == self.atoms[1].args[arg_num]:
                    new_macropred_args.append(self.atoms[0].args[arg_num])
                    continue
                    
                    
                # Else if one is a constant then use that value and remove the other from the parameters
                if self.atoms[0].args[arg_num][0] != "?":
                    splitter.replace_argument_with(self.atoms[1].args[arg_num], self.atoms[0].args[arg_num], action.precondition.parts)
                    splitter.replace_argument_with(self.atoms[1].args[arg_num], self.atoms[0].args[arg_num], [x.literal for x in action.effects if type(x) is not pddl.f_expression.Assign])
                    new_macropred_args.append(self.atoms[0].args[arg_num])
                    action.parameters = [x for x in action.parameters if x.name != self.atoms[1].args[arg_num]]
                    continue
                if self.atoms[1].args[arg_num][0] != "?":
                    splitter.replace_argument_with(self.atoms[0].args[arg_num], self.atoms[1].args[arg_num], action.precondition.parts)
                    splitter.replace_argument_with(self.atoms[0].args[arg_num], self.atoms[1].args[arg_num], [x.literal for x in action.effects if type(x) is not pddl.f_expression.Assign])
                    new_macropred_args.append(self.atoms[1].args[arg_num])
                    action.parameters = [x for x in action.parameters if x.name != self.atoms[0].args[arg_num]]
                    continue
                    
                
                # Else if both are variables then use the first variable name and remove the other from the parameters
                splitter.replace_argument_with(self.atoms[1].args[arg_num], self.atoms[0].args[arg_num], [x for x in action.precondition.parts if x in self.atoms])
                splitter.replace_argument_with(self.atoms[1].args[arg_num], self.atoms[0].args[arg_num], [x.literal for x in action.effects if type(x) is not pddl.f_expression.Assign and x in self.atoms])
                new_macropred_args.append(self.atoms[0].args[arg_num])
                action.parameters = [x for x in action.parameters if x.name != self.atoms[1].args[arg_num]]
                
                # Add a temporary eq precondition which states that the two parameters must be the same
                if not len([x for x in action.precondition.parts if x.predicate == "=%" and self.atoms[0].args[arg_num] in x.args and self.atoms[1].args[arg_num] in x.args]):
                    action.precondition.parts.append(pddl.conditions.Atom("=%", [self.atoms[0].args[arg_num], self.atoms[1].args[arg_num]]))
            
            
            

            new_macropred_args.append(self.atoms[0].args[-1])
            action.precondition.parts.append(pddl.conditions.Atom(self.macropred.name, new_macropred_args))
            
            # Goal macropredicates?
            #if self.goal_macropredicate_preconditions:
                #print("Need goal macropredicates", self.goal_macropredicate_preconditions)
                #goal_macropred = [x for x in self.baggable_type.goal_macropredicates if x.name == self.goal_macropredicate_preconditions[0].predicate][0]
                #goal_macropred_args = [param_name]
                #for goal_macropred
                #goal_macropred_args = new_macropred_args[goal_macropred.parent_arguments_to_include]
            
            
            
            # If the pair refers to the same parameter whose precond/effect may be instantiated to the same value, then we have an action with macropred as precondition but not effect 
            # Otherwise we add a second intermediate less than precondition so that count is incremented/decremented by 2 not 1
            # If there are goal macropredicates that need to be incremented/decremented by 2 then add additional less-than precondition and parameter now
            if self.atomsArePreconds[0] == self.atomsArePreconds[1]:
            
                # Create new count num and less-than-predicates
                new_num_intermediate = pddl.pddl_types.TypedObject(helper_functions.create_unique_name("?n_int", [x.name for x in action.parameters]), self.macropred.num_type_name)
                action.parameters.append(new_num_intermediate)
                first_less_than_precond = [x for x in action.precondition.parts if x.predicate == self.macropred.less_than_pred.name and self.atoms[0].args[-1] in x.args][0]
                second_less_than_precond = copy.deepcopy(first_less_than_precond)
                terminal_num = None
                if self.atomsArePreconds[0]:
                    first_args = list(first_less_than_precond.args)
                    first_args[0] = new_num_intermediate.name
                    first_less_than_precond.args = tuple(first_args)
                    second_args = list(second_less_than_precond.args)
                    second_args[1] = new_num_intermediate.name
                    second_less_than_precond.args = tuple(second_args)
                    terminal_num = second_args[0] if not self.macropred.is_goal_macro else first_args[1]
                else:
                    first_args = list(first_less_than_precond.args)
                    first_args[1] = new_num_intermediate.name
                    first_less_than_precond.args = tuple(first_args)
                    second_args = list(second_less_than_precond.args)
                    second_args[0] = new_num_intermediate.name
                    second_less_than_precond.args = tuple(second_args)
                    terminal_num = second_args[1]
                    
                # Add new less-than-predicates to oeprator
                action.precondition.parts.remove(first_less_than_precond)
                action.precondition.parts.append(first_less_than_precond)
                action.precondition.parts.append(second_less_than_precond)
                
                # Add new effects to operator
                action.effects.append(pddl.effects.Effect([], pddl.conditions.Truth(), pddl.conditions.Atom(self.macropred.name, new_macropred_args[:-1] + [terminal_num])))
                action.effects.append(pddl.effects.Effect([], pddl.conditions.Truth(), pddl.conditions.NegatedAtom(self.macropred.name, copy.deepcopy(new_macropred_args))))

                #print('new effects', pddl.conditions.Atom(self.macropred.name, new_macropred_args[:-1] + [terminal_num]), pddl.conditions.NegatedAtom(self.macropred.name, copy.deepcopy(new_macropred_args)))


                # Merge the two bag-name parameters into one
                #param_name = self.params[0]
                #action.parameters = [x for x in action.parameters if x.name != self.params[1]]
            
            
            # Remove the redundant less-than precondition and its counts from the operator  
            redundant_less_than_precond = [x for x in action.precondition.parts if x.predicate == self.macropred.less_than_pred.name and self.atoms[1].args[-1] in x.args][0]
            action.precondition.parts = [x for x in action.precondition.parts if not x == redundant_less_than_precond]
            action.parameters = [x for x in action.parameters if not x.name in redundant_less_than_precond.args]
            
            
            # Add a temporary eq precondition which states that the two baggable parameters must be the same
            action.precondition.parts.append(pddl.conditions.Atom("=%", [self.atoms[0].args[0], self.atoms[1].args[0]]))
            action.precondition.parts = tuple(action.precondition.parts)
            
            
            
            
            return action
            
            
            
        # We need one operator for each argument that can be instantiated together
        def create_neq_operator(self, action, action_names):    
        
            
            # If there is only one bag of this type in this problem then we do not need these operators
            #if len(self.macropred.baggable_type.all_bagged_objects) == 1:
                #return []
            
            # Otherwise create one bag for each attribute which can be instantiated to another in the same position
            actions = []
            for arg_num in self.variable_args_that_can_be_instantiated:
                new_action = copy.deepcopy(action)
                new_action.precondition.parts = list(new_action.precondition.parts)
                if not len([x for x in new_action.precondition.parts if x.predicate == "=%" and self.atoms[0].args[arg_num] in x.args and self.atoms[1].args[arg_num] in x.args]):
                    new_action.name = helper_functions.create_unique_name(action.name + "&neq" + str(arg_num), action_names)
                    action_names.append(new_action.name)
                    new_action.precondition.parts.append(pddl.conditions.NegatedAtom("=%", [self.atoms[0].args[arg_num], self.atoms[1].args[arg_num]]))
                    actions.append(new_action)
                    new_action.precondition.parts = tuple(new_action.precondition.parts)
                
                
            #print("neq actions needed", [x.name for x in actions])
            return actions
            
            
            

            
                    
        def validate_pair(self, new_action):
            self.can_be_equal(new_action)
            return not self.can_be_not_equal(new_action)
                
         
        def can_be_equal(self, new_action):
        
            # If there is another equivalence pair which enforces two parameters to be equal then we no longer need the neq precondition
            for arg_num in range(0, len(self.atoms[0].args)-1):
                eq_precond = [x for x in new_action.precondition.parts if type(x) is pddl.conditions.Atom and x.predicate == "=%" and self.atoms[0].args[arg_num] in x.args and self.atoms[1].args[arg_num] in x.args]
                if len(eq_precond) and arg_num in self.variable_args_that_can_be_instantiated:
                    self.variable_args_that_can_be_instantiated.remove(arg_num)
            
        
        
        def can_be_not_equal(self, new_action):
        
            # If there is another equivalence pair which enforces two parameters to be not-equal then we no longer need the eq/neq operators
            for arg_num in range(0, len(self.atoms[0].args)-1):
                #print("arg_num", arg_num, "attr1", self.atoms[0].args[arg_num], "attr2", self.atoms[1].args[arg_num], "args", [x for x in new_action.precondition.parts if type(x) is pddl.conditions.NegatedAtom and x.predicate == "="])
                neq_precond = [x for x in new_action.precondition.parts if type(x) is pddl.conditions.NegatedAtom and x.predicate == "=%" and self.atoms[0].args[arg_num] in x.args and self.atoms[1].args[arg_num] in x.args and self.atoms[0].args[arg_num] != self.atoms[1].args[arg_num]]
                if len(neq_precond):
                    print("Pair can be neq because of", neq_precond)
                    return True
            return False
        


                
        

        
    




class conditionalEffectSplitter():
    def __init__(self, action, baggableParam):
        self.action = action
        self.param = baggableParam

        self.num_object_variable_name_precond = ""
        self.less_number_variable_name_precond = ""
        self.num_object_variable_name_effect = ""
        self.more_number_variable_name_effect = ""
        self.less_than_pred_name = ""

