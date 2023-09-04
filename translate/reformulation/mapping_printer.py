import re
import options
from . import pddl_repair
from collections import OrderedDict

def print_mappings(baggable_types_list, new_task, old_task):
    
    
    
    f1 = open('mappings.txt', 'w+')
    
    if options.enable_pddl_repair:
        f1.write('enable_pddl_repair\n\n')
    
    
    f1.write('#INVARIANTS\n')
    for baggable_type in baggable_types_list:
        for macro in [baggable_type.macropredicate] + baggable_type.goal_macropredicates:
            f1.write(macro.name + '\t' + str([x for x in range(0, len(macro.args)-1)]) + '\t' + str(len(macro.args)-1) + '\n')
    
    
    f1.write('\n#BAGS (type, bagname, member)\n')
    for baggable_type in baggable_types_list:
        for bag in baggable_type.bags:
            for obj in bag.objects:
                f1.write(baggable_type.object_type.name + '\t' + bag.bagname + '\t' + obj.name + '\n')
    
    
    f1.write('\n#ACTIONS (reformulated action name, original action name, number of parameters in original action)\n')
    for action in new_task.actions:
        action_match = [x for x in old_task.actions if x.name == re.sub("([$]|[+]).+", "", action.name)]
        if len(action_match):
            f1.write(re.sub("([#]|[%]|[$]|[&]|[+])", "-", action.name) + '\t' + action_match[0].name + '\t' + str(len(action_match[0].parameters)) + '\n')
        else:
            action_match_ungrounded = [x for x in old_task.actions if x.name == action.name[:action.name.find('#')]]
            if len(action_match_ungrounded):
                f1.write(re.sub("([#]|[%]|[$]|[&]|[+])", "-", action.name) + '\t' + action_match_ungrounded[0].name + '\t' + str(len(action_match_ungrounded[0].parameters) - action.name.count('%')) + '\n')
            action_match_grounded = [x for x in old_task.actions if x.name == action.name[:action.name.find('%')]] + [x for x in old_task.actions if x.name == action.name[:action.name.find('&')]]
            for match in action_match_grounded:
                f1.write(re.sub("([#]|[%]|[$]|[&]|[+])", "-", action.name) + '\t' + match.name + '\t' + str(len(match.parameters) - action.name.count('%')) + '\n')
    
    
    f1.write('\n#ATTRIBUTES (macropredicate type, attribute number, original predicate name, mapped value)\n')
    for baggable_type in baggable_types_list: 
        for a in range(0, len(baggable_type.macropredicate.mappings)):
            prop = baggable_type.macropredicate.mappings[a]
            for val in prop:
                f1.write(str(baggable_type.object_type.name) + '\t' + str(a+1) + '\t' + ('None' if val.predicate is None else re.sub("([#]|[%]|[$]|[&]|[+])", "-", val.predicate.name)) + '\t' + ('None' if val.value is None else val.value.name) + '\n')
    
    
    
    f1.write('\n#DC_PARAMETERS (action name, object type, parameter number in the action, property identifier number)\n')
    for act in new_task.solution_mapper.parameter_property_mapping:
        for param in act:
            for expanded_operator_name in [x.name for x in new_task.actions if re.sub("([$]|[%]|[&]).*", "", x.name) == param.action_name]:
            
                #print("Full name", expanded_operator_name, "small name", param.action_name, "for param", param.parameter_number)
                #print("Matches", expanded_operator_name.split("%"))
               
                # Update the parameter index to the parameter index mapped minus the number of parameters in this operator 
                # which have been grounded or merged 
                updated_parameter_number = param.parameter_number - (len(expanded_operator_name.split("%")) - 1) - len([x for x in new_task.solution_mapper.equality_mapper if re.sub("([#]|[%]|[$]|[&]|[+])", "-", x.action_name) == re.sub("([#]|[%]|[$]|[&]|[+])", "-", expanded_operator_name)])
                f1.write(re.sub("([#]|[%]|[$]|[&]|[+])", "-", expanded_operator_name) + '\t' + param.typ + '\t' + str(updated_parameter_number) +'\t' + str(param.property_number) + '\n')
            
    #for var in new_task.solution_mapper.variables_to_ground_mapping_list:
        #print(var.ground_to, "GGGG", re.sub("([$]|[&]|[#]|[%]).*", "", var.grounded_action))
        #for match in [x.name for x in new_task.actions if re.sub("([$]|[&]).*", "", x.name) == re.sub("([$]|[&]).*", "", var.grounded_action)]:
            #f1.write(var.variable.name + '\t' + var.ground_to + '\t' + re.sub("([#]|[%]|[$]|[&]|[+])", "-", match) + '\n')
        #f1.write(var.variable.name + '\t' + var.ground_to + '\t' + re.sub("([#]|[%]|[$])", "-", var.grounded_action) + '\n')
        
    f1.write('\n#GROUNDED_ACTIONS (variable, object, grounded action)\n')
    for action in new_task.actions:
        action_groundings = action.name.split("%")
        for i in range(1, len(action_groundings)):
            ground_to = re.sub("([$]|[&]|[%]).*", "", action_groundings[i])
            groundings = [x for x in new_task.solution_mapper.variables_to_ground_mapping_list if re.sub("([$]|[&]|[%]).*", "", x.grounded_action) == re.sub("([$]|[&]|[%]).*", "", action.name) and x.ground_to == ground_to]
            for grounding in list(OrderedDict.fromkeys([(x.variable.name + '\t' + x.ground_to + '\t') for x in groundings])):
                f1.write(grounding + re.sub("([#]|[%]|[$]|[&]|[+])", "-", action.name) + '\n')
            
        
    
    
    
    f1.write('\n#GSE (bagged object classes which are goal state equivalent)\n')
    #print(goal_state_equivalences)
    for baggable_type in baggable_types_list:
        for e_class in baggable_type.goal_state_equivalences:
            f1.write(' '.join([x.name for x in e_class]) + '\n')


    f1.write('\n#BAGGABLE_PARAMETERS_EQUALITY (action, parameter which is still in action, parameter which has been removed from action but is equal to the other one)\n')
    for eq in new_task.solution_mapper.equality_mapper:
        f1.write(re.sub("([#]|[%]|[$]|[&]|[+])", "-", eq.action_name) + '\t' + eq.param_name_included + '\t' + eq.param_name_removed + '\n')
                                
    for action in new_task.actions:
        action.name = re.sub("([#]|[%]|[$]|[&]|[+])", "-", action.name)
    
    f1.write('\n#END')
    f1.close()
    

class SolutionMappings:

    def __init__(self, task, mapping_file_name = None):
        self.task = task
        self.baggable_types_list = None
        self.bag_mappings = []
        self.action_mappings = []
        self.property_predicate_mapping = [] # Records which predicate goes to which object
        self.parameter_property_mapping = [] # Records which ?dc argument in the action goes to which property (number) 
        self.variables_to_ground_mapping_list = [] # Records which variables in the grounded actions map to which parameters in the ungrounded actions 
        self.equality_mapper = [] # Records any parameters which have been removed from an operator but are implicitly equal to another
        self.populate_mappings(mapping_file_name)


    
    
    def populate_mappings(self, mapping_file_name):
        
        if mapping_file_name is None:
            return
        
        maps = open(mapping_file_name, 'r')
        next_line = maps.readline().rstrip('\n')
        
        # PDDL repair enabled? If so then we need to repair the original domain
        if next_line == "enable_pddl_repair":
            pddl_repair.repair_domain(self.task)
        
        
        # Bags
        while not next_line.split() or next_line.split()[0] != '#BAGS':
            next_line = maps.readline().rstrip('\n')
        next_line = maps.readline().rstrip('\n')
        while not next_line == '':
            split_line = next_line.split()
            
            # if len([x for x in self.task.objects if x.name == split_line[2]]):
            #     self.bag_mappings.append(BagMap(split_line[1], [x for x in self.task.objects if x.name == split_line[2]][0], split_line[0])) # Mafe: esta línea da problemas no sé por qué
            # next_line = maps.readline().rstrip('\n')
            if len(split_line) == 3:
                if len([x for x in self.task.objects if x.name == split_line[2]]):
                    self.bag_mappings.append(BagMap(split_line[1], [x for x in self.task.objects if x.name == split_line[2]][0], split_line[0])) # Mafe: esta línea da problemas no sé por qué
            next_line = maps.readline().rstrip('\n')
            # elif len(split_line) == 2:
            #     self.bag_mappings.append(BagMap(split_line[1], [0][0], split_line[0]))
            #     next_line = maps.readline().rstrip('\n')
        

        # Actions
        next_line = maps.readline().rstrip('\n')
        while not next_line.split() or next_line.split()[0] != '#ACTIONS':
            next_line = maps.readline().rstrip('\n')
        next_line = maps.readline().rstrip('\n')
        while not next_line == '':
            split_line = next_line.split()
            self.action_mappings.append(ActionMap(split_line[0], [x for x in self.task.actions if x.name == split_line[1]][0], split_line[2]))
            next_line = maps.readline().rstrip('\n')
        
        # Attributes
        next_line = maps.readline().rstrip('\n')
        while not next_line.split() or next_line.split()[0] != '#ATTRIBUTES':
            next_line = maps.readline().rstrip('\n')
        next_line = maps.readline().rstrip('\n')
        while not next_line == '':
            split_line = next_line.split()
            self.property_predicate_mapping.append(PropertyMap(split_line[0], int(split_line[1]), split_line[2], split_line[3], self.task))
            next_line = maps.readline().rstrip('\n')
        
        # Parameters
        next_line = maps.readline().rstrip('\n')
        while not next_line.split() or next_line.split()[0] != '#DC_PARAMETERS':
            next_line = maps.readline().rstrip('\n')
        next_line = maps.readline().rstrip('\n')
        while not next_line == '':
            split_line = next_line.split()
            self.parameter_property_mapping.append(ParameterPropertyMap(split_line[0], split_line[1], int(split_line[2]), int(split_line[3])))
            next_line = maps.readline().rstrip('\n')
        
        # Grounded actions
        next_line = maps.readline().rstrip('\n')
        while not next_line.split() or next_line.split()[0] != '#GROUNDED_ACTIONS':
            next_line = maps.readline().rstrip('\n')
        next_line = maps.readline().rstrip('\n')
        while not next_line == '':
            split_line = next_line.split()
            self.variables_to_ground_mapping_list.append(VariablesToGroundMapping(split_line[0], split_line[1], None))
            self.variables_to_ground_mapping_list[-1].grounded_action = split_line[2]
            next_line = maps.readline().rstrip('\n')
        
        
        # Goal state equivalences
        splits = []
        next_line = maps.readline().rstrip('\n')
        while not next_line.split() or next_line.split()[0] != '#GSE' :
            next_line = maps.readline().rstrip('\n')
        next_line = maps.readline().rstrip('\n')
        while not next_line == '':
            splits.append(next_line.split())
            next_line = maps.readline().rstrip('\n')
        self.goal_state_equivalence_classes = GSE(splits)
        
        
        # Baggable parameter equality 
        next_line = maps.readline().rstrip('\n')
        while not next_line.split() or next_line.split()[0] != '#BAGGABLE_PARAMETERS_EQUALITY':
            next_line = maps.readline().rstrip('\n')
        next_line = maps.readline().rstrip('\n')
        while not next_line == '':
            split_line = next_line.split()
            self.equality_mapper.append(BagEqualityMapper(split_line[0], split_line[1], split_line[2]))
            next_line = maps.readline().rstrip('\n')
        self.goal_state_equivalence_classes = GSE(splits)
        
        
        
        maps.close()
        

class BagMap():
    def __init__(self, bagged_object, original_object, typ):
        self.bagged_object = bagged_object
        self.original_object = original_object
        self.typ = typ

class ActionMap():
    def __init__(self, reformulated_action, original_action, num_params_to_ground):
        self.reformulated_action = reformulated_action
        self.original_action = original_action
        self.num_params_to_ground = int(num_params_to_ground)
        
class VariablesToGroundMapping():
    def __init__(self, variable, ground_to, num_objects, pointer_value = ""):
        self.variable = variable
        self.ground_to = ground_to
        self.num_objects = num_objects
        self.grounded_action = ""
        self.pointer_value = pointer_value # If this variable has a pointer then what is it grounded to in the goal

        
    def __eq__(self, other):
        return self.variable.name == other.variable.name and self.ground_to == other.ground_to and self.grounded_action == other.grounded_action      
        


class BaggedObjectMap():
    def __init__(self, bagged_object_with_wrong_goal, bagged_object_with_correct_goal):
        self.bagged_object_with_wrong_goal = bagged_object_with_wrong_goal
        self.bagged_object_with_correct_goal = bagged_object_with_correct_goal

class GSE():
    def __init__(self, members):
        self.members = members
    def get_class(self, obj_name):
        return [x for x in self.members if obj_name in x]

class PropertyMap():
    def __init__(self, typ, property_number, predicate, value, task):
        self.typ = typ
        self.property_number = property_number
        self.value = None if value == 'None' else value
        self.predicate = self.set_predicate(predicate, task)
        
    def set_predicate(self, predicate, task):
        if predicate == 'None':
            return None
        
        pred = [x for x in task.predicates if x.name == predicate]
        
        if len(pred) == 1:
            return pred[0]
        
        # Strip off the -typ or -typ1 etc to get the true predicate name
        predicate = re.sub(r'[-]' + self.typ + '[0-9]*$', '', predicate)
        return [x for x in task.predicates if x.name == predicate][0]
            
        
       

class ParameterPropertyMap():
    def __init__(self, action_name, typ, parameter_number, property_number):
        self.action_name = action_name
        self.typ = typ
        self.parameter_number = parameter_number
        self.property_number = property_number
        
        
class BagEqualityMapper():
    def __init__(self, action_name, param_name_included, param_name_removed):
        self.action_name = action_name
        self.param_name_included = param_name_included # The parameter which is still in the reformulated operator
        self.param_name_removed = param_name_removed # The parameter which has been removed but equals 'param_name_included' 
        
        

        

