
import sys
import pddl

def import_counts(task, from_to_count_filename):
        
    maps = open(from_to_count_filename, 'r')
    next_line = maps.readline().rstrip('\n')

    typ = ""
    print("\n\n\n\n Typ: ", typ, "\n\n\n\n")
    preds_of_type = []
    obj_counter = 1
    while next_line != "":
        if next_line.split()[0] == "type:":
            typ = next_line.split()[1]
            supertypes = get_supertype([x for x in task.types if x.name == typ][0], task.types)
            task.objects = [x for x in task.objects if x.type_name != typ]
            preds_of_type = [x for x in task.predicates if len([y for y in x.arguments if y.type_name in supertypes]) and x.name != "="]
            print("ZZZ", [x.name for x in preds_of_type])
            task.init = [x for x in task.init if type(x) is pddl.f_expression.Assign or not x.predicate in [y.name for y in preds_of_type]]
            task.goal.parts = [x for x in task.goal.parts if type(x) is pddl.f_expression.Assign or not x.predicate in [y.name for y in preds_of_type]]
            obj_counter = 1
    
        elif len(next_line.split()) == 6:
            _init_pred = [x for x in task.predicates if x.name == next_line.split()[0][:-1].lower()][0]
            _from = next_line.split()[1].lower()
            _goal_pred = [x for x in task.predicates if x.name == next_line.split()[2][:-1].lower()][0]
            _to = next_line.split()[3].lower()
            _count = int(next_line.split()[5])
            
            
            for i in range(0, _count):
                new_name = typ + str(obj_counter)
                task.objects.append(pddl.pddl_types.TypedObject(new_name, typ))

                grounded_init_args = [_from, new_name] if _init_pred.arguments[1].type_name == typ else [new_name, _from]
                task.init.append(pddl.conditions.Atom(_init_pred.name, grounded_init_args))
                grounded_goal_args = [_to, new_name] if _goal_pred.arguments[1].type_name == typ else [new_name, _to]
                task.goal.parts.append(pddl.conditions.Atom(_goal_pred.name, grounded_goal_args))
            
        
                obj_counter = obj_counter + 1
            
            if not len([x for x in task.objects if x.name == _from]):
               raise ValueError("ERROR: cannot find object", _from)
            if not len([x for x in task.objects if x.name == _to]):
               raise ValueError("ERROR: cannot find object", _to)
          
        
        next_line = maps.readline().rstrip('\n')
            

def get_supertype(this_type, types):
    
    # For each type
    supertypes = []
    while True:
        supertypes.append(this_type.name)
        this_type = [x for x in types if x.name == this_type.basetype_name]
        if not len(this_type):
            break
        this_type = this_type[0]
    return supertypes
    
    
