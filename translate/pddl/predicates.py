from . import pddl_types
from . import conditions

class Predicate(object):
    def __init__(self, name, arguments):
        self.name = name
        self.arguments = arguments
        self.remains_the_same = False # To know if for an object, the predicate remains the same throughout the problem or it can be changed by an action

    def __str__(self):
        return "%s(%s)" % (self.name, ", ".join(map(str, self.arguments)))

    def get_arity(self):
        return len(self.arguments)

    def pddl_str(self):
        try:
            return '(%s %s)' % (self.name, ' '.join([arg.pddl_str() for arg in self.arguments]))
        except:
            return '(%s %s)' % (self.name, ' '.join([arg for arg in self.arguments]))

import re
from reformulation import helper_functions


class Bag_Predicate(Predicate):
    def __init__(self, task, arguments, baggable_type, original_predicate = []):
        self.baggable_type_name = baggable_type.object_type.name
        self.name = self.baggable_type_name + "-bag" 

        self.arguments = arguments
        self.baggable_type =  baggable_type
        self.original_predicate = original_predicate
        for arg in self.arguments:
            if arg.type_name == self.baggable_type_name:
                self.id = arg

    # def __str__(self):
    #     result = "%s(%s)" % (self.name, ", ".join(map(str, self.arguments)))
    #     if self.type_name:
    #         result += ": %s" % self.type_name
    #     return result
    def pddl_str(self):
        try:
            return '(%s %s)' % (self.name, ' '.join([arg.pddl_str() for arg in self.arguments]))
        except:
            return '(%s %s)' % (self.name, ' '.join([arg for arg in self.arguments]))

    def ground_bag_predicate(self, args, bagname, init = True):
        # Put the arguments in the right order
        # print("grounding bag predicate", [type(arg) for arg in args])
        atom_args = bagname + args
        # grounded_args = [self.baggable_type.get_bag_name_of_object(obj)]
        # predicates_to_ground_for_this_obj = [x for x in predicates_to_ground if obj.name in x.args]

        return conditions.Atom(self.name, atom_args)
    
