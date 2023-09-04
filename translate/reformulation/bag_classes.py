from . import helper_functions
import pddl

class BaggableType():
    def __init__(self, object_type):
        self.object_type = object_type
        #self.task.objects = [x for x in self.task.objects if not x.type_name == object_type.name]
        self.bags = []
        self.goal_state_equivalences = None # The list of objects which are GSE (needed later for transforming the solution into original space)
        self.type_checker = None
        self.macropredicate = None
        self.goal_macropredicates = []
        self.all_unbagged_objects = []
        self.all_bagged_objects = []
        self.functions = [] # Mafe
        self.bag_predicates = []
        # self.original_type_name = original_type_name
    
    def add_bag(self, objects, task):
        
        # Create a valid bag name and add it to task
        bag_name = helper_functions.create_unique_name(self.object_type.name + "-bag1", [x.name for x in task.objects] + [x.name for x in self.all_bagged_objects], True)
        bagged_object = pddl.pddl_types.TypedObject(bag_name, self.object_type.name)
        #self.task.objects.append(bagged_object)
        self.bags.append(Bag(objects, bag_name))
        self.all_unbagged_objects.extend(objects)
        self.all_bagged_objects.append(bagged_object)
        
    def get_max_bag_size(self):
        return max([0] + [len(x.objects) for x in self.bags])
        
    def get_objects_in_bag(self, bag_name):
        return [x for x in self.bags if x.bagname == bag_name]
        
    def get_bag_name_of_object(self, obj):
        return [x.bagname for x in self.bags if obj.name in [y.name for y in x.objects]][0]
    
    def is_in_goal_state(self, task):
        args_of_the_goal_state = []
        for atom in task.goal.parts:
            for arg in atom.args:
                args_of_the_goal_state.extend([object for object in task.objects if object.name == arg])
        
        if self.object_type.name in [x.type_name for x in args_of_the_goal_state]:
            return True
        else:
            return False
        
        
    def __str__(self):
        intro = 'Type ' + self.object_type.name + ' has ' + str(len(self.bags)) + (' bag' if len(self.bags) == 1 else ' bags')
        return intro + ': ' + ', '.join([str(x) for x in self.bags])
    


class Bag():
    def __init__(self, objects, bagname):
        self.bagname = bagname
        self.objects = objects
        self.goal_macropredicate = None
        
    def __str__(self):
        return '{' + ', '.join([x.name for x in self.objects]) + '}'
    
    def __eq__(self, other: object) -> bool:
        return self.bagname == other.bagname and self.objects == other.objects
    
    
    