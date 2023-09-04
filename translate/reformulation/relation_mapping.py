import copy
import options
import pddl
import re
from collections import OrderedDict
from . import single_valued_checker
from . import mapping_printer
from . import helper_functions

class Macropredicate():
    def __init__(self, task, typ, supertypes, type_checker_list):
        self.task = task
        self.type_checker_list = type_checker_list
        self.typ = typ
        self.st = supertypes
        self.is_goal_macro = False
        self.args = []
        self.name = ""
        self.mappings = []
        self.counts = []
        self.baggable_type = None
        self.less_than_pred = None
        self.parent_arguments_to_include = None
        self.parent_name = ""
        self.num_type_name = ""
        self.satisfied_goal_macropredicate_name = None
        self.desired_count_goal_macropredicate_name = None
        self.needs_GTE = False
        self.init_macropredicate()
        
        
    def init_macropredicate(self):
        seed = ("bag-" + self.typ.name if not self.is_goal_macro else "count-" + self.typ.name + "-goal")
        self.name = helper_functions.create_unique_name(seed, [x.name for x in self.task.predicates])
        init_argument_name = helper_functions.create_unique_name("?" + self.typ.name, [x.name for x in self.args]) # Set first argument as the bagged type
        self.args = [pddl.pddl_types.TypedObject(init_argument_name, self.typ.name)]
        
    
    def add_invariant_argument(self, invariant_group):
        
        new_type_name = helper_functions.create_unique_name(self.typ.name + '-property1', [x.name for x in self.task.types], True)
        new_type = pddl.pddl_types.Type(new_type_name, 'object')
        self.task.types.append(new_type)
        mappings = []
        nein_obj = None
        number_binary_predicates = 0
        binary_predicate_types = [] # What types is this binary predicate mapped to?
        index_arg_mappings = [] # We may need a second arg which follows this one to indicate what predicate this arg refers to (if number_binary_predicates > 0)
        
        if options.writeout_reformulation_logic:
            print('Adding mutexed argument', new_type_name, end = ": ")
        
        # Add none property if applicable
        if invariant_group.nein:
            nein_obj_name = new_type_name + "-none"
            nein_obj = pddl.pddl_types.TypedObject(nein_obj_name, new_type_name)
            self.task.objects.append(nein_obj)
            mappings.append(argument_mapping(None, nein_obj))
            if options.writeout_reformulation_logic:
                print(nein_obj_name, 'is null object', end = "; ")
        
        for part in invariant_group.parts:
            invar_pred = part.predicate
            rel_pred = [x for x in self.task.predicates if x.name == invar_pred][0]
            rel_args = [a for a in rel_pred.arguments if not a.type_name in self.st]

            # If unary predicate, then add value t of a new type
            if not len(rel_args):
                true_object_name = helper_functions.create_unique_name(invar_pred + '-true', [x.name for x in self.task.objects])
                true_object = pddl.pddl_types.TypedObject(true_object_name, new_type_name)
                self.task.objects.append(true_object)
                mappings.append(argument_mapping(rel_pred, true_object))
                if options.writeout_reformulation_logic:
                    print(true_object_name, 'is true when', rel_pred, 'is true', end = "; ")
                    
            else: # Binary predicate so use object name
                other_arg = rel_pred.arguments[[x for x in range(0,2) if not x in part.order][0]]
                binary_predicate_types.append(other_arg.type_name)
                number_binary_predicates = number_binary_predicates + 1
                mappings.append(argument_mapping(rel_pred, None))
                if options.writeout_reformulation_logic:
                    print('takes on value of', rel_pred, end = "; ")
                    
        
        need_pointer = len(list(OrderedDict.fromkeys(binary_predicate_types))) < len(binary_predicate_types) # Assumption: not accounting for subtypes
        self.mappings.append(mappings)
        new_argument_name = helper_functions.create_unique_name("?" + new_type_name, [x.name for x in self.args])
        new_argument = pddl.pddl_types.TypedObject(new_argument_name, new_type_name if number_binary_predicates == 0 else 'object')
        self.args.append(new_argument)
        if options.writeout_reformulation_logic:
            print()
                     
                                       
        # If more than one object type maps to this binary argument then we must add a new argument specifying the predicate name
        if need_pointer:
                    
            if options.writeout_reformulation_logic:
                print('Adding pointer argument', new_type_name, end = ": ")
                
            # Create the None object if it does not already exist
            if nein_obj is None:
                nein_obj_name = new_type_name + "-none"
                nein_obj = pddl.pddl_types.TypedObject(nein_obj_name, new_type_name)
                self.task.objects.append(nein_obj)
            if options.writeout_reformulation_logic:
                print(nein_obj_name, 'is null object', end = "; ")
            index_arg_mappings.append(argument_mapping(None, nein_obj, index = len(self.mappings) + 1))
                
                
            # Add one value in the pointer argument for every binary predicate
            for part in invariant_group.parts:
                invar_pred = part.predicate
                rel_pred = [x for x in self.task.predicates if x.name == invar_pred][0]
                rel_args = [a for a in rel_pred.arguments if not a.type_name in self.st]

                if not len(rel_args):
                    continue
                
                true_object_name = helper_functions.create_unique_name(invar_pred + '-true', [x.name for x in self.task.objects])
                true_object = pddl.pddl_types.TypedObject(true_object_name, new_type_name)
                self.task.objects.append(true_object)
                index_arg_mappings.append(argument_mapping(rel_pred, true_object, index = len(self.mappings) + 1))
                if options.writeout_reformulation_logic:
                    print(true_object_name, 'is true when', rel_pred, 'takes on a value in the previous argument', end = "; ")
                

            
            
            # Point the new argument to argument with the object
            for mapping in mappings:
                mapping.pointed_at_by(len(self.mappings) + 1)
            
            
            # Update object lists
            self.mappings.append(index_arg_mappings)
            new_argument_name = helper_functions.create_unique_name("?" + new_type_name + "-pointer", [x.name for x in self.args])
            new_argument = pddl.pddl_types.TypedObject(new_argument_name, new_type_name)
            self.args.append(new_argument)
            if options.writeout_reformulation_logic:
                print()
                
    
    
    
    # Type needs GTE system if there exists a bag of this type such that there are more elements in the bag than there are in the goal
    def see_if_type_needs_GTE_system(self):
        
        #return
        
        # GTE system enforced by user?
        if options.enforce_GTE:
            self.needs_GTE = True
            if options.writeout_reformulation_logic:
                print("Type", self.typ.name, "will have a GTE system because --enforce_GTE has been enabled.")
            return
            
        for bag in self.baggable_type.bags:
            num_bag_elements_in_goal = 0
            for ele in bag.objects:
                goal_atoms_with_ele = [x for x in self.task.goal.parts if ele.name in x.args]
                if len(goal_atoms_with_ele):
                    num_bag_elements_in_goal = num_bag_elements_in_goal + 1
                    
            if num_bag_elements_in_goal > 0 and num_bag_elements_in_goal < len(bag.objects):
                self.needs_GTE = True
                if options.writeout_reformulation_logic:
                    print("Type", self.typ.name, "needs a GTE system because bag {", ', '.join([x.name for x in bag.objects]), "} has", len(bag.objects), "elements but only", num_bag_elements_in_goal, "in the goal.")
                return
                
        if options.writeout_reformulation_logic:
                print("Type", self.typ.name, "does not need a GTE system.")
    
    
    
    def add_count(self):

        
        num_type_name = helper_functions.create_unique_name(self.typ.name + "-num", [x.name for x in self.task.types] + [x.name for x in self.task.objects])
        self.num_type_name = num_type_name
        num_type = pddl.pddl_types.Type(num_type_name, 'object')
        self.task.types.append(num_type)
        num_objects = []
        inequality_arguments = [pddl.pddl_types.TypedObject("?l", num_type_name), pddl.pddl_types.TypedObject("?m", num_type_name)]
        
        less_than_pred_name = helper_functions.create_unique_name(self.typ.name + '-less', [x.name for x in self.task.predicates])
        less_than_pred = pddl.predicates.Predicate(less_than_pred_name, inequality_arguments)
        self.less_than_pred = less_than_pred
        
        ##for i in range(0, len([x for x in self.task.objects if x.type_name == self.typ.name])):
        for i in range(0, self.baggable_type.get_max_bag_size()):
        
            num_object_name = helper_functions.create_unique_name(num_type_name + str(i+1), [x.name for x in self.task.objects])
            num_object = pddl.pddl_types.TypedObject(num_object_name, num_type_name)
            self.num_object = num_object
            num_objects.append(num_object)
            self.counts.append(count_mappings(i+1, num_object))
            
            self.task.objects.append(num_object)
            
            if i > 0:
                
                less_than_atom = pddl.conditions.Atom(less_than_pred_name, [num_objects[i-1].name, num_objects[i].name])
                self.task.init.append(less_than_atom)
        
        num_argument_name = helper_functions.create_unique_name("?" + num_type_name, [x.name for x in self.args])
        num_argument = pddl.pddl_types.TypedObject(num_argument_name, num_type_name)
        self.args.append(num_argument)
        self.less_than_pred_name = less_than_pred_name
        
        return less_than_pred
        
    
    
    
    def ground_macropredicate(self, obj, predicates_to_ground, init = True):
        
        grounded_args = [self.baggable_type.get_bag_name_of_object(obj)]
        predicates_to_ground_for_this_obj = [x for x in predicates_to_ground if obj.name in x.args]
        for Map in [x for x in self.mappings if x[0].arg_points_to_arg_index == -1]:
            matching_init_pred = [x for x in Map if not x.predicate is None and x.predicate.name in [y.predicate for y in predicates_to_ground_for_this_obj]]
            if len(matching_init_pred) > 1:
                raise ValueError('ERROR: Some object is not single-valued!')
                
            # Null object    
            if not len(matching_init_pred):
                nein_object = [x.value.name for x in Map if x.predicate is None][0]
                grounded_args.append(nein_object)
                
                # We may need the next argument to define that this argument refers to the none object (by using the none object here too)
                if Map[0].arg_pointed_to_by_arg_index != -1:
                    none_object_name = [x.value.name for x in self.mappings[Map[0].arg_pointed_to_by_arg_index - 1] if x.predicate is None][0]
                    grounded_args.append(none_object_name)
                
            else:
                if matching_init_pred[0].value is None: # Binary predicate
                
                    init_pred = [x for x in predicates_to_ground_for_this_obj if x.predicate == matching_init_pred[0].predicate.name][0]
                    other_arg_in_pred = [x for x in init_pred.args if not x == obj.name][0]
                    
					# Will not bag object at this point
                    grounded_args.append(other_arg_in_pred)
                    
                    # We may need the next argument to define the binary predicate this argument refers to
                    if Map[0].arg_pointed_to_by_arg_index != -1:
                        index_map = self.mappings[Map[0].arg_pointed_to_by_arg_index - 1]
                        init_pred = [x for x in index_map if x.predicate is not None and x.predicate.name in [y.predicate for y in predicates_to_ground_for_this_obj]][0]
                        grounded_args.append(init_pred.value.name)
                    
                else: # Unary predicate
                    grounded_args.append(matching_init_pred[0].value.name)
                    
                    # We may need the next argument to define that this argument refers to a unary predicate (by using the none object)
                    if Map[0].arg_pointed_to_by_arg_index != -1:
                        none_object_name = [x.value.name for x in self.mappings[Map[0].arg_pointed_to_by_arg_index - 1] if x.predicate is None][0]
                        grounded_args.append(none_object_name)
                        
        
        # count_obj = [x.number_object for x in self.counts if x.number == 1][0] #MafeComentado
        # grounded_args.append(count_obj.name)
        
        
        # Ground goal-satisfied predicate in goal state - return grounded [goal-satisfied, goal-desire (grounded to desired count)]
        if not init:
            return [pddl.conditions.Atom(self.satisfied_goal_macropredicate_name, grounded_args[:-1]), pddl.conditions.Atom(self.desired_count_goal_macropredicate_name, copy.deepcopy(grounded_args))]
        
        
        # Ground goal-macropredicate in the initial state
        #if init and not self.satisfied_goal_macropredicate_name is None: # MafeComentado
            #return [pddl.conditions.Atom(self.name, grounded_args)]
        
        
        # Normal initial state macropredicate
        return pddl.conditions.Atom(self.name, grounded_args)
                
                    
        
    
    def increment(self, atom):
        current_number = [x.number for x in self.counts if x.number_object.name == atom.args[-1]][0]
        new_number_object = [x.number_object.name for x in self.counts if x.number == (current_number + 1)]
        new_args = list(atom.args[:-1]) + new_number_object
        atom.args = tuple(new_args)
        
    

    # Create goal macropredicates for this baggable type
    # If GTE system enforced to this type, also create desired and satisfied macropredicates 
    def create_goal_macropredicates(self, goal_atoms, obj):
    
        goal_atoms_of_this_obj =  [x.predicate for x in goal_atoms if obj.name in x.args]
        if not len(goal_atoms_of_this_obj):# or not self.satisfied_goal_macropredicate_name is None:
            return False, False, False
        
        
        sub_macropredicate = copy.deepcopy(self)
        sub_macropredicate.is_goal_macro = True
        sub_macropredicate.parent_name = self.name
        sub_macropredicate.init_macropredicate()
        args_to_include = []
        arg_mappers_to_include = []
        parent_arguments_to_include = []
        for a in range(1, len(self.args)-1):
            arg = self.args[a]
            arg_mapper = self.mappings[a-1]
            
            if arg_mapper[0].arg_points_to_arg_index != -1:
                continue
        
            goal_match = [x for x in arg_mapper if not x.predicate is None and x.predicate.name in goal_atoms_of_this_obj]
            if len(goal_match):
                parent_arguments_to_include.append(a)
                args_to_include.append(arg)
                new_arg_mapper = copy.deepcopy(arg_mapper)
                arg_mappers_to_include.append(new_arg_mapper)
                
                # If the next arg points to this arg then copy that over too
                if arg_mapper[0].arg_pointed_to_by_arg_index != -1:
                    parent_arguments_to_include.append(a+1)
                
                    for mapper in new_arg_mapper:
                        mapper.pointed_at_by(len(arg_mappers_to_include) + 1)
                        
                    args_to_include.append(self.args[arg_mapper[0].arg_pointed_to_by_arg_index])
                    new_pointer_arg_mapper = self.mappings[arg_mapper[0].arg_pointed_to_by_arg_index - 1]
                    for mapper in new_pointer_arg_mapper:
                        mapper.point_to(len(arg_mappers_to_include))
                    arg_mappers_to_include.append(new_pointer_arg_mapper)
                
    
        # Count argument
        args_to_include.append(self.args[-1])
    
        sub_macropredicate.args = sub_macropredicate.args + args_to_include
        sub_macropredicate.mappings = arg_mappers_to_include
        sub_macropredicate.parent_arguments_to_include = parent_arguments_to_include
    
    
        # Do not create a new goal predicate if it is the same as the original macropredicate
        if len(sub_macropredicate.args) == len(self.args):
            sub_macropredicate = self
        
        
        if not self.needs_GTE:
            return sub_macropredicate, False, False
        
        
        # Satisfied goal-macropredicate
        satisfied_goal_macropredicate_name = helper_functions.create_unique_name(sub_macropredicate.name + '-satisfied', [x.name for x in sub_macropredicate.task.predicates])
        satisfied_predicate = pddl.predicates.Predicate(satisfied_goal_macropredicate_name, copy.deepcopy(sub_macropredicate.args[:-1]))
        
        
        # Desired-count goal macropredicate
        desired_count_goal_macropredicate_name = helper_functions.create_unique_name(sub_macropredicate.name + '-desired-count', [x.name for x in sub_macropredicate.task.predicates])
        desired_predicate = pddl.predicates.Predicate(desired_count_goal_macropredicate_name, copy.deepcopy(sub_macropredicate.args))
        
        return sub_macropredicate, satisfied_predicate, desired_predicate
    
    
    def ground_all_at_zero(self, obj, keep_num_ungrounded = False):
        
        product_space = [[] for x in self.mappings]
        for p in range(0, len(self.mappings)):
            Map = self.mappings[p]
            unit = []
            for item in Map:
                
                # Binary predicate
                if item.value is None:


                    # If this attribute is static, then we do not need any instances of this attribute except the one in the initial state
                    if False and item.predicate.name in [x.name for x in self.type_checker_list.statics]:
                        other_args_pos = int(item.predicate.arguments[1].type_name not in self.st)
                        init_preds_match = [x for x in self.task.init if x.predicate == item.predicate.name and len([y for y in self.bag_mapping if y.original_object.name in x.args])]
                        init_other_object_match = list(OrderedDict.fromkeys([x.args[other_args_pos] for x in init_preds_match]))
                        unit = unit + init_other_object_match
                        #print("AAA",item.predicate.name, other_args_pos, init_preds_match, init_other_object_match, [x for x in self.task.init])
                    
                    else:
                        other_type_in_pred = [x.type_name for x in item.predicate.arguments if not x.type_name in self.type_checker_list.get([y for y in self.task.types if y.name == obj.type_name][0]).supertypes][0]
                        objects_of_other_type = [x.name for x in self.task.objects if other_type_in_pred in self.type_checker_list.get([y for y in self.task.types if y.name == x.type_name][0]).supertypes]
                        unit = unit + objects_of_other_type
                        #print("BBB", other_type_in_pred, objects_of_other_type)
                    
                # Unary predicate
                else:
                    unit = unit + [item.value.name]
                
            # Need as many copies of previous units as the number of objects in this unit
            if p == 0:
                product_space[p] = unit
            if p > 0:
                for q in range(0, p):
                    prev_col = product_space[q]
                    prev_unit = []
                    for i in range(0, len(unit)):
                        if i % 2 == 0:
                            prev_unit = prev_unit + prev_col
                        else:
                            prev_unit = prev_unit + prev_col[::-1]
                    
                    product_space[q] = prev_unit
                
                for i in range(0, len(unit)):    
                    for q in range(0, int(len(product_space[p-1])/len(unit))):
                        product_space[p] = product_space[p] + [unit[i]]
        
        # Print
        #print("product space", product_space)
        nrow = len(product_space[0])
        ncol = len(product_space)
        
        # Create zero object if it does not exist
        zero_object = [x for x in self.counts if x.number == 0]
        if not len(zero_object):
            num_type_name = [x.number_object.type_name for x in self.counts][0]
            num_object_name = helper_functions.create_unique_name(num_type_name + '0', [x.name for x in self.task.objects])
            zero_object = pddl.pddl_types.TypedObject(num_object_name, num_type_name)
            self.counts.append(count_mappings(0, zero_object))
            self.task.objects.append(zero_object)
            less_than_atom = pddl.conditions.Atom(self.less_than_pred_name, [num_object_name, [x.number_object.name for x in self.counts if x.number == 1][0]])
            self.task.init.append(less_than_atom)
        else:
            zero_object = zero_object[0].number_object
        
        init_atoms = []
        for row in range(0, nrow):
            grounded_args = [obj.name]
            for col in range(0, ncol):
                grounded_args.append(product_space[col][row])
            
            if keep_num_ungrounded:
                grounded_args.append("?num")
            else:
                grounded_args.append(zero_object.name)
            new_atom = pddl.conditions.Atom(self.name, grounded_args)
            init_atoms.append(new_atom)
        
        return init_atoms
    
    
    
        


    
    def add_gte_macropredicates_to_action(self, action, precond_factor_index, task, new_action_names):
        
        
        
        
        # 1) Find goal state atoms which have this macropredicate's 'satisfied' requirement
        satisfied_atoms_in_goal = [x for x in task.goal.parts if x.predicate == self.satisfied_goal_macropredicate_name]
        if not len(satisfied_atoms_in_goal):
            return None
        
        #print("GTEs are needed for", action.name, "because of goal atoms", satisfied_atoms_in_goal)
        
        
        
        
        # 2) Determine whether the count is being incremented, decremented or not affected by this action
        obj = [x for x in action.precondition.parts if x.predicate == self.name][precond_factor_index].args[0]
        positive_macropredicate_in_effects = [x.literal for x in action.effects if type(x.literal) is pddl.conditions.Atom and x.literal.predicate == self.name and x.literal.args[0] == obj]
        if not len(positive_macropredicate_in_effects):
            #print(self.name, "(", obj.name, ",...) is not affected by this action")
            return None
        
        
        
        positive_macropredicate_in_effects = positive_macropredicate_in_effects[precond_factor_index]
        negative_macropredicate_in_effects = [x.literal for x in action.effects if type(x.literal) is pddl.conditions.NegatedAtom and x.literal.predicate == self.name and x.literal.args[0] == obj][precond_factor_index]
        less_than_precondition = [x for x in action.precondition.parts if x.predicate == self.less_than_pred.name and positive_macropredicate_in_effects.args[-1] in x.args][0]
        #print("Less than precondition ", less_than_precondition, positive_macropredicate_in_effects.args[-1] == less_than_precondition.args[1])
        macropredicate_incremented = positive_macropredicate_in_effects.args[-1] == less_than_precondition.args[1]
        
     
     
        # 3) Find the count which will switch between the goal being satisfied and unsatisfied
        #exisiting_precondition_macropredicate = [x for x in action.precondition.parts if x.predicate == self.name and type(x) is pddl.conditions.Atom][0] #Jordan: bug is in this line. It is finding the first precondition of this type irrespective of the goal. If there were more than 2 possible precon macros then we would require an additional split eg. action which CHANGES the cocktail of a shot
        exisiting_precondition_macropredicate = [x for x in action.precondition.parts if x.predicate == self.name][precond_factor_index]
        desired_number_variable_name = helper_functions.create_unique_name("?des", [x.name for x in action.parameters])
        #print("exisiting_precondition_macropredicate", exisiting_precondition_macropredicate)
        
        
        # 4) If the action is incrementing, then we compare the desired number with the positive effect macropredicate count, otherwise the negative one
        macropredicate_effect_number_to_compare = positive_macropredicate_in_effects.args[-1] if macropredicate_incremented else negative_macropredicate_in_effects.args[-1]
     
          
        
        # 5) Add unaffected action (ie. this action will not immediately effect satisfaction of the goal)
        not_equal_desirednumber_precondition = pddl.conditions.NegatedAtom('=', [macropredicate_effect_number_to_compare, desired_number_variable_name])
        unaffected_action = copy.deepcopy(action)
        unaffected_desired_number_precondition = pddl.conditions.Atom(self.desired_count_goal_macropredicate_name, list(exisiting_precondition_macropredicate.args[:-1]) + [desired_number_variable_name])
        unaffected_action.precondition.parts = tuple(list(unaffected_action.precondition.parts) + [not_equal_desirednumber_precondition, unaffected_desired_number_precondition])
        unaffected_action.name = helper_functions.create_unique_name(action.name + '&N', [x.name for x in task.actions] + new_action_names) 
        unaffected_action.parameters.append(pddl.pddl_types.TypedObject(desired_number_variable_name, self.num_object.type_name))
      
        # 6) Add affected action (ie. this action will immediately effect satisfaction of the goal)
        affected_action = copy.deepcopy(action)
        affected_desired_number_precondition = pddl.conditions.Atom(self.desired_count_goal_macropredicate_name, list(exisiting_precondition_macropredicate.args[:-1]) + [macropredicate_effect_number_to_compare])
        affected_action.precondition.parts = tuple(list(affected_action.precondition.parts) + [affected_desired_number_precondition]) 
        affected_action.name = helper_functions.create_unique_name(action.name + ('&U' if macropredicate_incremented else '&D'), [x.name for x in task.actions] + new_action_names) 
        if macropredicate_incremented:
            satisfied_effect_atom = pddl.conditions.Atom(self.satisfied_goal_macropredicate_name, positive_macropredicate_in_effects.args[:-1])
            affected_action.effects.append(pddl.effects.Effect([], pddl.conditions.Truth(), satisfied_effect_atom))
        else:
            satisfied_effect_atom = pddl.conditions.NegatedAtom(self.satisfied_goal_macropredicate_name, negative_macropredicate_in_effects.args[:-1])
            affected_action.effects.append(pddl.effects.Effect([], pddl.conditions.Truth(), satisfied_effect_atom))

        
        #print("Performed GTE transformation of", action.name, "for style", self.name, "returning", unaffected_action.name)
        return [unaffected_action, affected_action]
    


    
    

    
class count_mappings():
    def __init__(self, number, number_object):
        self.number = number
        self.number_object = number_object


class argument_mapping():
    def __init__(self, predicate, value, index = -1):
        self.predicate = predicate
        self.value = value
        self.arg_points_to_arg_index = index
        self.arg_pointed_to_by_arg_index = -1
    
    def pointed_at_by(self, index):
        self.arg_pointed_to_by_arg_index = index
        
    def point_to(self, index):
        self.arg_points_to_arg_index = index
        
    def __eq__(self, other):
        return self.predicate == other.predicate and self.value.name == other.value.name


class bag_mappings():
    def __init__(self, bagged_object, original_object):
        self.bagged_object = bagged_object
        self.original_object = original_object
    
    
class count_mapper():
    def __init__(self, orig, goal):
        self.orig = orig
        self.goal = goal

                                                                                                                    
                                                                                                                                                                                                                                                                
    
    
    
    
    