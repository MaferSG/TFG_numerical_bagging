import options
import re



def create_unique_name(seed, search, bag_name = False):
    if not re.sub("([#]|[%]|[$]|[&]|[+])", "-", seed) in [re.sub("([#]|[%]|[$]|[&]|[+])", "-", x) for x in search]:
        return seed
    i = 2
    seed = seed + str(i) if not bag_name else seed[:-1] + str(i)
    while re.sub("([#]|[%]|[$]|[&]|[+])", "-", seed) in [re.sub("([#]|[%]|[$]|[&]|[+])", "-", x) for x in search]:
        digits = len(str(i))
        i = i + 1
        seed = seed[:-digits] + str(i)
    return seed 
    

# Parse list of pddl.conditions.Condition objects and arguments names to ground from to        
def ground_atoms(atoms, ground_from, ground_to):
    
    for atom in atoms:
        ground_to_index = [j for j in range(len(atom.args)) if atom.args[j] == ground_from]
        atom.args = list(atom.args)
        if len(ground_to_index):
            atom.args[ground_to_index[0]] = ground_to
            atom.args = tuple(atom.args)
    


# Get all supertypes of the specified object type (inclusive)
def get_supertypes(this_type, task):
    
    supertypes = []
    if type(this_type) is str:
        this_type = [x for x in task.types if x.name == x.name == this_type][0]
    while True:
        supertypes.append(this_type.name)
        this_type = [x for x in task.types if x.name == this_type.basetype_name]
        if not len(this_type):
            break
        this_type = this_type[0]
    return supertypes



def replace_argument_with(old, new, atoms):
    for atom in atoms:
        args = list(atom.args)
        args = [(new if x == old else x) for x in args]
        atom.args = tuple(args)
    
    
    
def dprint(text):
     if options.writeout_reformulation_logic:
         print(text)    
    
    
    