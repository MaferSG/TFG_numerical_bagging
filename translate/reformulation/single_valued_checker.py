import pddl
import options
import re
import invariants
from collections import OrderedDict
from . import helper_functions

class Type_checker_list():
    def __init__(self, task, invariants):
        self.task = task
        self.type_checkers = []
        self.invariants = invariants
        self.statics = []
        self.get_statics()
        self.statics_added_to_goal = []
        self.add_statics_to_goal()
    
    def add(self, type_checker):
        self.type_checkers.append(type_checker)
    
    # Find the type checker of this type. Create it if it does not exist
    def get(self, typ):
    
        type_checker = [x for x in self.type_checkers if x.typ.name == typ.name]
        if len(type_checker):
            return type_checker[0]
            
        type_checker = Type_checker(typ, self.task, self.invariants, self.statics)
        self.add(type_checker)
        return type_checker
    

    def type_is_baggable(self, typ, conditionalEffectGroups, baggable_type_names):
        
        if typ.name in options.dont_bag.split(','):
            if options.writeout_reformulation_logic:
                print(typ.name, "will not be bagged because you have requested using --dont_bag")
            return False
        
        
        # If parent type is non-indexable, then this type cannot be bagged
        parent = [x for x in self.task.types if x.name == typ.basetype_name]
        if len(parent) > 0 and self.get(parent[0]).is_non_indexable_type:
            return False


        


        # If type appears as the subject of a forall loop, this is allowed
        # 		Unless the type also appears in the main parameter list of the same action
        #		Or if the type appears within a forall but not as a subject
        #		Or if there are multiple subjects of a forall and this is one of them
        #		Or if it appears in a nested forall (but FD will not parse a file with nested foralls anyway)
        #		Or if there is more than 1 conditional effect group 
        #		Or if a single action has a foralls for multiple baggable types
        for action in self.task.actions:


        	

            variables_of_this_type_in_action = [x.name for x in action.parameters if x.type_name == typ.name]
            conditional_effects = [x for x in action.effects if len(x.parameters)]
            variables_of_this_type_in_conditional_effect = [y[0] for y in [x.parameters for x in action.effects if len(x.parameters)] if y[0].type_name == typ.name]


            # If user has not requested to bag conditional effects, then return if a baggable object appears in the parameters of a conditional effect
            if not options.bag_conditional_effects and len(variables_of_this_type_in_conditional_effect):
                if options.writeout_reformulation_logic:
                    print(typ.name, "will not be bagged because it is the subject of a conditional effect in action", action.name, "-> enable --bag_conditional_effects to attempt to bag this type")
                return False


            # If in conditional effect parameters AND in main parameters parameters, can not bag
            if len(variables_of_this_type_in_conditional_effect) and len(variables_of_this_type_in_action):
                if options.writeout_reformulation_logic:
                    print(typ.name, "will not be bagged because it is the subject of a conditional effect AND an action parameter in action", action.name)
                return False


            # If there are multiple forall subjects including this type then cannot bag. FD has bug where it adds a , onto the param name if there is a subsequent argument
            conditional_effects_multiple_params = [item.type_name for sublist in [y for y in [x.parameters for x in action.effects if len(x.parameters)] if len(y) > 1]  for item in sublist]
            if len([x for x in conditional_effects_multiple_params if re.sub(r"[,]", "", x) == typ.name]):
                if options.writeout_reformulation_logic:
                    print(typ.name, "will not be bagged because there are too many subjects in a conditional effect of", action.name)
                return False


            # If there are multiple foralls with the same type in this operator then do not bag (unless the foralls are linked)
            if conditionalEffectGroups is not None:
                for conditionalEffectGroup in conditionalEffectGroups:
                    n_conditional_effects_groups_of_type = len([y for y in [x.parameters for x in conditionalEffectGroup[1]] if y[0].type_name == typ.name])
                    if n_conditional_effects_groups_of_type > 1:
                        if options.writeout_reformulation_logic:
                            print(typ.name, "will not be bagged because it is the subject of more than one forall loop in", action.name)
                        return False



            # If there exists a forall in this action of another baggable type, then do no bag this object
            for conditional_effect in conditional_effects:
                if len([x for x in baggable_type_names if x == conditional_effect.parameters[0].type_name]):
                    if options.writeout_reformulation_logic:
                        print(typ.name, "will not be bagged because", action.name, "already has a bagged forall loop of a different type")
                    return False
            

            # If type is a conditional effect parameter but not a main action parameter then it satisfies this action (unless type appears in goal)
            if len(variables_of_this_type_in_conditional_effect) and not len(variables_of_this_type_in_action):
                self.remove_statics_from_goal()
                goal_state_predicates_of_this_obj = [i.predicate for i in self.task.goal.parts if type(i) is pddl.conditions.Atom and i.predicate != '=' and len([a for a in i.args if a in [obj.name for obj in self.task.objects if obj.type_name == typ.name]]) > 0]
                self.add_statics_to_goal()
                if len(goal_state_predicates_of_this_obj):
                    if options.writeout_reformulation_logic:
                        print(typ.name, "will not be bagged because it appears in both a conditional effect and the goal")
                    return False

                continue


            # See if type is an argument of preconds/effects of a conditional effect
            for condEff in conditional_effects:

                precond_atoms = list(condEff.condition.parts) if len(condEff.condition.parts) else [condEff.condition]
                atoms = precond_atoms + [condEff.literal]
                for precond in precond_atoms:
                    if len([x for x in precond.args if x in variables_of_this_type_in_action]):
                        if options.writeout_reformulation_logic:
                            print(typ.name, "will not be bagged because it appears in a conditional effect in action", action.name)
                        return False
                






        # If type is not action equivalent then it cannot be bagged
        if not self.get(typ).is_action_equivalent:
            return False
            
            
        # Check if type has already been evaluated
        for type_checker in self.type_checkers:
            if type_checker.typ.name == typ.name:
                return not type_checker.is_non_indexable_type and type_checker.get_is_single_valued() and type_checker.is_less_than_ternary()
            
            
        # If not, evaluate it
        type_checker = Type_checker(typ, self.task, self.invariants, self.statics)
        self.add(type_checker)
        return not type_checker.is_non_indexable_type and type_checker.get_is_single_valued() and type_checker.is_less_than_ternary()
    
    

    
    # Get the list of static predicates with arguments of any type
    def get_statics(self):
    
        for pred in [x for x in self.task.predicates if not x.name == '=']:
            is_static = True
            for action in self.task.actions:
                add_effects = [eff.literal.predicate for eff in action.effects if not eff.literal.negated]
                del_effects = [eff.literal.predicate for eff in action.effects if eff.literal.negated]
                if pred.name in add_effects or pred.name in del_effects:
                    is_static = False
                    break
            if is_static:
                self.statics.append(pred)
                
                # Add static to list of invariants
                for i in range(0, len(pred.arguments)):
                    part = invariants.InvariantPart(pred.name, [i], -1)
                    invar = invariants.Invariant([part])
                    self.invariants.append(invar)
                
                
        if len(self.statics) and options.writeout_reformulation_logic:
            print()
	
	
    # Add the static predicates to the goal to help with defining goal-state equivalence classes. Cache these added predicates for later removal
    def add_statics_to_goal(self):
            
        static_atoms_in_init = [x for x in self.task.init if type(x) is pddl.conditions.Atom and x.predicate in [y.name for y in self.statics]]
        self.task.goal.parts = list( self.task.goal.parts)
        self.task.goal.parts.extend(static_atoms_in_init)
        self.task.goal.parts = tuple( self.task.goal.parts)
        self.statics_added_to_goal = static_atoms_in_init
	
	
    # Remove the statics which we just added to the goal    
    def remove_statics_from_goal(self):
	    
        self.task.goal.parts = list( self.task.goal.parts)
        self.task.goal.parts = [x for x in self.task.goal.parts if not x in self.statics_added_to_goal]
        self.task.goal.parts = tuple( self.task.goal.parts)
	    
	    
    
    
# Used to check if a type can be bagged. Also stores information on invariants and type hierarchy     
class Type_checker():
    def __init__(self, typ, task, invariants, statics):
        self.typ = typ
        self.task = task
        self.invariants = invariants
        self.supertypes = helper_functions.get_supertypes(typ, task)
        self.predicates_with_this_type = self.get_predicates_of_this_type()
        self.is_non_indexable_type = self.non_indexable_type()
        self.is_action_equivalent = self.action_equivalence_test()
        self.is_single_valued = None
        self.statics = statics
    

        
    def get_is_single_valued(self):
        if self.is_single_valued is None:
            self.is_single_valued = self.single_valued_type()
        return self.is_single_valued
    
    
    
    # Single-valued type test. Type is single-valued if all predicates of this supertype belong to an invariant group 
    # and the number of instances of each invariant group in the initial state, wrt each object of this type, is 0 or 1
    def single_valued_type(self):
        
        
        #self.predicates_of_this_type = [p for p in self.task.predicates if not p.name == '=' and len(p.arguments) > 1 and len([a for a in p.arguments if a.type_name in self.supertypes])]
        
        self.predicates_of_this_type = [p for p in self.task.predicates if not p.name == '=' and len([a for a in p.arguments if a.type_name in self.supertypes])]
        self.invariants_of_this_type = []
        invariant_predicates_of_this_type = set()
        
        # Do not merge if all predicates are statics
        statics_of_this_type = [y for y in self.statics if y in self.predicates_with_this_type]
        if len(statics_of_this_type) == len(list(OrderedDict.fromkeys([x.name for x in self.predicates_with_this_type]))):
            if options.writeout_reformulation_logic:
                print('All' , self.typ, 'predicates are static -> will not merge objects of this type')
            return False
            
            
        # Do not merge if supertype appears in a function
        functions_of_this_supertype = [x for x in self.task.functions if len([y for y in x.arguments if y.type_name in self.supertypes])]
        if len(functions_of_this_supertype):
            if options.writeout_reformulation_logic:
                print('Type' ,self.typ, 'is an argument in a function -> This type will NOT be merged.')
            return False
        
        
        # Find invariant groups of this supertype
        for invar in self.invariants:
        
        
        
            pred = [x for x in self.task.predicates if x.name == next(iter(invar.parts)).predicate][0]
            index = next(iter(invar.parts)).order
            if not index:
                continue
            index = index[0]
            typ = [x.name for x in self.task.types if x.name == pred.arguments[index].type_name]
            if not len(typ) or not typ[0] in self.supertypes:
                continue
            
            
            # Check that all objects of this supertype are single-valued in initial state
            objs_of_supertype = [x for x in self.task.objects if x.type_name in self.supertypes]
            single_valued_init = True
            for o in objs_of_supertype:
                if not self.single_valued_obj(o, invar):
                    single_valued_init = False
                    break
            if not single_valued_init:
                continue
            
            
            # Remove an invariant group if it is a subset of this one
            to_remove = []
            for mut in self.invariants_of_this_type:
                if len(mut.parts) <= len(invar.parts):
                    superset = True
                    for mp in mut.parts:
                        if mp.predicate not in [x.predicate for x in invar.parts]:
                            superset = False
                            break
                    if superset:
                        to_remove.append(mut)
                else:
                    subset = True
                    for mp in invar.parts:
                        if mp.predicate not in [x.predicate for x in mut.parts]:
                            subset = False
                            break
                    if subset:
                        to_remove.append(mut)
            for to_rem in to_remove:
                self.invariants_of_this_type.remove(to_rem)
            
            
            self.invariants_of_this_type.append(invar)
            invariant_predicates_of_this_type = set.union(invariant_predicates_of_this_type, set(invar.predicates))
        
        
        # For each non unary predicate of this supertype
        for pred in [x for x in self.predicates_of_this_type]:
        
            # Is every predicate of this supertype in some invariant group?
            if pred.name not in invariant_predicates_of_this_type:
                if options.writeout_reformulation_logic:
                    print('Predicate', pred.name, 'of type' ,self.typ, 'is not an invariant in some action -> This type is NOT single-valued.')
                return False
        
        if options.writeout_reformulation_logic:            
            print('Every non-unary predicate of type',  self.typ, 'is an invariant or static -> This type is single-valued.')
        
       
        
        
        return True
        
        
    # Indexable test
    def non_indexable_type(self):
        
        # Build list of all ancestors of this type
        supertypes = []
        this_type = self.typ
        
        while True:
            supertypes.append(this_type.name)
            this_type = [x for x in self.task.types if x.name == this_type.basetype_name]
            if not len(this_type):
                break
            this_type = this_type[0]
        
        # Ensure that no predicates have more than one argument of this type
        for pred in self.task.predicates:
            if pred.name == '=':
                continue
            args_of_this_type = 0
            for arg in pred.arguments:
                if arg.type_name in supertypes:
                    args_of_this_type = args_of_this_type + 1
                    if args_of_this_type == 1:
                        self.predicates_with_this_type.append(pred)
                if args_of_this_type > 1:
                    if options.writeout_reformulation_logic:
                        print('Predicate', pred.name, 'has more than one argument of type', self.typ, '-> Objects of this type will NOT be merged.')
                    return True
                    
        return False
    
    
    
    def is_less_than_ternary(self):
        ternary = [x for x in self.predicates_of_this_type if len(x.arguments) > 2]
        if len(ternary) and options.writeout_reformulation_logic:
            print('Type', self.typ, 'contains m-ary predicates for m > 2 -> Objects of this type will NOT be merged.')
        return not ternary
    
    
    def get_predicates_of_this_type(self):
        return [x for x in self.task.predicates if self.typ.name in [y.type_name for y in x.arguments]]
    
    
    def single_valued_obj(self, obj, invar_candidate):
        #print('single-valued-obj', obj)
        
        # Check that there is not an =(obj, ?x) predicate in the initial/goal wrt this object where ?x does not equal object
        init_equals_predicate = [i for i in self.task.init if type(i) is pddl.conditions.Atom and i.predicate == '=' and len([a for a in i.args if a == obj.name]) == 1]
        goal_equals_predicate = [i for i in self.task.goal.parts if type(i) is pddl.conditions.Atom and i.predicate == '=' and len([a for a in i.args if a == obj.name]) == 1]
        if len(init_equals_predicate) or len(goal_equals_predicate):
            if options.writeout_reformulation_logic:
                print('Object', obj.name, 'will not be bagged because of the following initial/goal atoms:', init_equals_predicate + goal_equals_predicate)
            return False
        
        
        # Check each invariant group of this type has 1 or fewer instances in the initial state
        initial_state_predicates_of_this_obj = [i.predicate for i in self.task.init if type(i) is pddl.conditions.Atom and i.predicate != '=' and len([a for a in i.args if a == obj.name]) > 0]
        goal_state_predicates_of_this_obj = [i.predicate for i in self.task.goal.parts if type(i) is pddl.conditions.Atom and i.predicate != '=' and len([a for a in i.args if a == obj.name]) > 0]
        #print("init:", initial_state_predicates_of_this_obj)
        occurrences = 0
        for pred in invar_candidate.predicates:
            occurrences = occurrences + len([x for x in initial_state_predicates_of_this_obj if x == pred])
            if occurrences > 1:
                if options.writeout_reformulation_logic and False:
                    print('Object', obj.name, 'has more than one instance of', pred, 'in the initial state -> This object is not single-valued..')
                return False
        if occurrences == 0:
            if options.writeout_reformulation_logic and False:
                print("Adding none-object for", pred, "because there exists an initial state atom with no occurrences of this invariant.")
            invar_candidate.nein = True
        occurrences = 0
        for pred in invar_candidate.predicates:
            occurrences = occurrences + len([x for x in goal_state_predicates_of_this_obj if x == pred])
            if occurrences > 1:
                if options.writeout_reformulation_logic and False:
                    print('Object', obj.name, 'has more than one instance of', pred, 'in the goal state -> This object is not single-valued..')
                return False
        if options.writeout_reformulation_logic and False:
            print('Object', obj, 'is single-valued.')
        return True
        
        
    def action_equivalence_test(self):
    
        for obj in [x for x in self.task.objects if x.type_name == self.typ.name]:
    
            for act in self.task.actions:
                precond_atoms = act.precondition.parts if len(act.precondition.parts) else [act.precondition]
                for fact in precond_atoms:
                    for arg in fact.args:
                        if arg == obj.name:
                            if options.writeout_reformulation_logic:
                                print('Type', self.typ.name, 'is not action-equivalent because object', obj.name, 'is referred to in action', act.name)
                            return False
                            
        return True




class Object_checker_list():
    def __init__(self, task, type_checker, invariants):
        self.checkers = []
        self.task = task
        self.type_checker = type_checker
        self.invariants = invariants
    
    def add(self, obj_checker):
        self.checkers.append(obj_checker)
    
    def is_single_valued(self, obj):
        
        # Check if obj has already been evaluated
        for obj_checker in self.checkers:
            if(obj_checker.obj.name == obj.name):
                return obj_checker.is_single_valued
        
        # If not, evaluate it
        obj_checker = Object_checker(obj, self.type_checker)
        self.add(obj_checker)
        return obj_checker.is_single_valued


class Object_checker():
    def __init__(self, obj, type_checker):
        self.obj = obj
        self.is_single_valued = self.single_valued_obj(type_checker)
    
    
    # Single-valued object test - for each invariant group, does this object appear 0/1 times in the intial state?
    def single_valued_obj(self, type_checker):
        #print('single-valued-obj', self.obj, self.obj.name)
        
        
        # Check each invariant group of this type has 1 or fewer instances in the initial state
        initial_state_predicates_of_this_obj = [i.predicate for i in type_checker.task.init if type(i) is pddl.conditions.Atom and i.predicate != '=' and len([a for a in i.args if a == self.obj.name]) > 0]
        goal_state_predicates_of_this_obj = [i.predicate for i in type_checker.task.goal.parts if type(i) is pddl.conditions.Atom and i.predicate != '=' and len([a for a in i.args if a == self.obj.name]) > 0]
        #print("init:", initial_state_predicates_of_this_obj)
        for invar in type_checker.invariants_of_this_type:
            occurrences = 0
            for pred in invar.predicates:
                occurrences = occurrences + len([x for x in initial_state_predicates_of_this_obj if x == pred])
                if occurrences > 1:
                    if options.writeout_reformulation_logic and False:
                        print('Object', self.obj.name, 'has more than one instance of', pred, 'in the initial state -> This object is not single-valued..')
                    return False
            if occurrences == 0 and not invar.nein:
                if options.writeout_reformulation_logic and False:
                    print("Adding none-object for", pred, "because there exists an initial state atom with no occurrences of this invariant.")
                invar.nein = True
            occurrences = 0
            for pred in invar.predicates:
                occurrences = occurrences + len([x for x in goal_state_predicates_of_this_obj if x == pred])
                if occurrences > 1:
                    if options.writeout_reformulation_logic:
                        print('Object', self.obj.name, 'has more than one instance of', pred, 'in the goal state -> This object is not single-valued..')
                    return False
        if options.writeout_reformulation_logic and False:
            print('Object', self.obj, 'is single-valued.')
        return True

                