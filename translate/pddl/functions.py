import re
from pddl import pddl_types
from reformulation import helper_functions
from . import conditions


class Function(object):
    def __init__(self, name, arguments, type_name=None, predicate=""):
        self.name = name
        self.arguments = arguments
        self.type_name = type_name
        self.predicate = predicate

    def pddl_str(self):
        try:
            return '(%s %s)\n' % (self.name, ' '.join([arg.pddl_str() for arg in self.arguments]))
        except:
            return '(%s %s)\n' % (self.name, ' '.join([arg for arg in self.arguments]))

    
    def ground_function(self, args, bagname, number_objects, type = "assignation", init = True):
        atom_args = bagname + args

        return conditions.Atom(self.name, atom_args, type, number_objects=number_objects)
    
        

class MyFunction(object):
    def __init__(self, task, arguments, baggable_type_name, predicate=""):

        self.name = "count-" + baggable_type_name + "-" + predicate

        # if name != "":
        #     self.name = name
        # else:
        #     self.name = "count-" + baggable_type_name + "-" + predicate
        self.task = task
        # seed = ("count-" + baggable_type_name)
        # self.name = helper_functions.create_unique_name(seed, [x.name for x in self.task.predicates])
        # self.name = seed + "-" + predicate
        self.arguments = arguments
        self.baggable_type_name = baggable_type_name
        self.predicate = predicate

    # def __str__(self):
    #     result = "%s(%s)" % (self.name, ", ".join(map(str, self.arguments)))
    #     if self.type_name:
    #         result += ": %s" % self.type_name
    #     return result
    def pddl_str(self):
        try:
            return '(%s %s)\n' % (self.name, ' '.join([arg.pddl_str() for arg in self.arguments]))
        except:
            return '(%s %s)\n' % (self.name, ' '.join([arg for arg in self.arguments]))
            # return '(%s %s)\n' % (self.name, " ".join([str(arg) for arg in self.arguments]))

        if hasattr(self, 'type_name'):
            result += " - %s" % self.type_name
        return result
        # return '(%s %s)' % (self.name, ' '.join([arg.pddl_str() for arg in self.arguments]))
    
    def ground_function(self, args, bagname, number_objects, type = "assignation", init = True):
        atom_args = bagname + args
        # atom_args = []
        # for atom in atoms_of_bag:
        #     for arg in atom.args:
        #         if arg not in baggable_type.all_unbagged_objects:
        #             atom_args.append(arg)
        # # atom_args = [atom.args for atom in atoms_of_bag]
        # arguments = bagname + atom_args

        return conditions.Atom(self.name, atom_args, type, number_objects=number_objects)
    
    def has_interacting_baggable_types(self, baggable_types_list):
        """Returns true if the function has more than one argument of a baggable type"""
        args_of_baggable_type = 0
        for arg in self.arguments:
            if pddl_types.TypedObject.is_baggable(arg, baggable_types_list):
                args_of_baggable_type += 1

        
        # For barman when shot is baggable
        # args_of_baggable_type = 0
        # args_to_check = []
        # # We have to check the arguments and the argumentsmof the function, and also the child types of the arguments
        # for arg in self.arguments:

        #     args_to_check.append(arg)
        #     args_to_check.extend([a for a in arg.get_child_types(self.task.types)])
        #     for x in args_to_check:
        #         if x.is_baggable(baggable_types_list):
        #             args_of_baggable_type += 1

        if args_of_baggable_type > 1:
            return True
        else:
            return False
        


    