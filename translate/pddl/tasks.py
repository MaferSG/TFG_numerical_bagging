from __future__ import print_function

from . import axioms
from . import predicates
from . import pddl_types
from . import conditions
from . import effects
import sys


class Task(object):
    def __init__(self, domain_name, task_name, requirements,
                 types, objects, predicates, functions, init, goal,
                 actions, axioms, use_metric):
        self.domain_name = domain_name
        self.task_name = task_name
        self.requirements = requirements
        self.types = types
        self.objects = objects
        self.predicates = predicates
        self.functions = functions
        self.init = init
        self.goal = goal
        self.actions = actions
        self.axioms = axioms
        self.axiom_counter = 0
        self.use_min_cost_metric = use_metric
        self.solution_mapper = None # Used by Baggy to produce the mappings file after reformulation
        self.creation_predicates = [] # From numerical_counters

    def add_axiom(self, parameters, condition):
        name = "new-axiom@%d" % self.axiom_counter
        self.axiom_counter += 1
        axiom = axioms.Axiom(name, parameters, len(parameters), condition)
        self.predicates.append(predicates.Predicate(name, parameters))
        self.axioms.append(axiom)
        return axiom

    def dump(self):
        print("Problem %s: %s [%s]" % (
            self.domain_name, self.task_name, self.requirements))
        print("Types:")
        for type in self.types:
            print("  %s" % type)
        print("Objects:")
        for obj in self.objects:
            print("  %s" % obj)
        print("Predicates:")
        for pred in self.predicates:
            print("  %s" % pred)
        print("Functions:")
        for func in self.functions:
            print("  %s" % func)
        print("Init:")
        for fact in self.init:
            print("  %s" % fact)
        print("Goal:")
        self.goal.dump()
        print("Actions:")
        for action in self.actions:
            action.dump()
        if self.axioms:
            print("Axioms:")
            for axiom in self.axioms:
                axiom.dump()

    def unparse_domain(self):
        result = ''

        result += '(define (domain ' + self.domain_name + ')\n'

        result += '(:requirements ' + ' '.join(self.requirements.requirements) + ')\n'

        if self.types:
            result += '(:types %s)\n' % pddl_types.typed_list_to_string(self.types)

        if self.predicates:
            result += '(:predicates '
            for pred in self.predicates:
                if pred.name != '=':
                    # print the non-trivial predicates, excluding the predicate
                    # (= ?x - object ?y - object) 
                    result += "  %s\n" % pred.pddl_str()
            result += ')\n'

        if self.functions:
            result += '(:functions '
            for f in self.functions:
                result += "  %s" % f.pddl_str()
            result += ')\n'

        if self.actions:
            for action in self.actions:
                result += action.pddl_str()
        result += ')\n\n'

        return result

    def unparse_task(self):
        result = ''

        result += '(define (problem ' + self.task_name + ')\n'

        result += '(:domain ' + self.domain_name + ')\n'

        if self.objects:
            result += '(:objects\n%s)\n' % pddl_types.typed_list_to_string(self.objects, '\n')

        result += '(:init '
        for ini in self.init:
            # do not print trivial init statements such as (= x x)
            if ini.__class__.__name__ != 'Atom' or ini.predicate != '=' or ini.args[0] != ini.args[1]:
                result += '%s\n' % ini.pddl_str()
        result += ')\n'

        result += '(:goal %s)\n' % self.goal.pddl_str()

        if self.use_min_cost_metric:
            result += '(:metric minimize (total-cost))\n'

        # length spec not implemented in fastdownward, so we don't bother here
        result += ')\n'

        return result




    def check_objects(self):
        result = True
        for obj in self.objects:
            for t in self.types:
                if obj.type_name == t.name:
                    break
            else:
                print('TypeError: object %s has invalid type' % obj)
                result = False
        if False == result:
            sys.exit('Failed the object type check')
        else:
            print('Passed the object type check')

    def get_basetype_name(self, curr_typename):
        for t in self.types:
            if t.name == curr_typename:
                return t.basetype_name
        return None

    def check_type(self):
        max_generations = 50
        for t in self.types:
            curr = t
            counter = 0
            while (counter < max_generations):
                counter += 1
                curr = self.get_basetype_name(curr)
                if None == curr:
                    break
            else:
                sys.exit('Cyclic loop detected on type %s' % t)

    # returns True if type1 is equal to or is a subtype of type 2
    def is_in_type(self, type1, type2):
        curr_type = type1
        while curr_type != type2:
            curr_type = self.get_basetype_name(curr_type)
            if None == curr_type:
                print('type of %s not match type of %s' % (type1, type2))
                return False
        return True

    # return True if all arguments in the list matches the type of the corresponding type list
    def predicate_in_type(self, args1, args2):
        if len(args1) != len(args2):
            return False
        for i in range(len(args1)):
            for obj in self.objects:
                if obj.name == args1[i]:
                    if False == self.is_in_type(obj.type_name, args2[i].type_name):
                        return False
                    break
            else:
                print('invalid object %s in predicate' % args1[i])
                return False

        return True

    def check_predicate(self, fact):
        for pred in self.predicates:
            if fact.predicate == pred.name and len(fact.args) == len(pred.arguments) and self.predicate_in_type(fact.args, pred.arguments):
                return True
        else:
            print('Invalid init predicate %s' % fact)
            return False

    def check_init(self):
        result = True
        for fact in self.init:
            if isinstance(fact, conditions.Atom):
                # print('in :init    testing %s' % fact)
                result = result and self.check_predicate(fact)

        if False == result:
            sys.exit('Failed the :init predicate check')
        else:
            print('Passed the :init predicate check')



    def check_goal_aux(self, curr):
        print('checking %s' % curr)
        if isinstance(curr, conditions.JunctorCondition):
            for part in curr.parts:
                if False == self.check_goal_aux(part):
                    return False
        elif isinstance(curr, conditions.Literal):
            if False == self.check_predicate(curr):
                return False
        return True


    def check_goal(self):
        if False == self.check_goal_aux(self.goal):
            sys.exit('Faled the :goal check')
        else:
            print('Passed the :goal check')

    def action_check_type(self, params, args1, args2):
        if len(args1) != len(args2):
            return False
        for i in range(len(args1)):
            # read type of each argument in predicate
            for param in params:
                if args1[i] == param.name:
                    if self.is_in_type(param.type_name, args2[i].type_name):
                        break
                    else:
                        print('invalid object %s in predicate' % args1[i])
                        return False
            else:
                print('invalid object %s in predicate' % args1[i])
                return False
        return True

    def check_action_predicate_aux(self, params, curr):
        for pred in self.predicates:
            if curr.predicate == pred.name and len(curr.args) == len(pred.arguments) and self.action_check_type(params, curr.args, pred.arguments):
                return True
        else:
            print('Invalid action predicate %s' % curr)
            return False

    def check_action_predicate(self, params, curr):
        if isinstance(curr, conditions.JunctorCondition):
            for part in curr.parts:
                if False == self.check_action_predicate(params, part):
                    return False
        elif isinstance(curr, conditions.Literal):
            if False == self.check_action_predicate_aux(params, curr):
                return False
        else:
            print('Not checked: %s' % curr)
        return True

    def check_action_effect(self, params, effect):
        if isinstance(effect, effects.ConjunctiveEffect):
            for eff in effect.effects:
                if False == self.check_action_effect(params, eff):
                    return False
        elif isinstance(effect, effects.UniversalEffect):
            for param in effect.parameters:
                # check validity of type of param
                for t in self.types:
                    if param.type_name == t.name:
                        break
                else:
                    print('TypeError: parameter %s in effect %s has invalid type' % (param, effect))
            if False == self.check_action_predicate(params + effect.parameters, effect.effect):
                return False
        elif isinstance(effect, effects.ConditionalEffect):
            if False == self.check_action_predicate(params, effect.condition):
                print('Effect %s has invalid preconditions' % effect)
                return False
            if False == self.check_action_predicate(params, effect.effect):
                return False
        elif isinstance(effect, effects.SimpleEffect):
            if False == self.check_action_predicate(params, effect.effect):
                return False
        elif isinstance(effect, effects.CostEffect):
            print('CostEffect not checked %s' % effect)
        elif isinstance(effect, effects.Effect):
            for param in effect.parameters:
                # check validity of type of param
                for t in self.types:
                    if param.type_name == t.name:
                        break
                else:
                    print('TypeError: parameter %s in effect %s has invalid type' % (param, effect))
            p = params + effect.parameters
            if False == self.check_action_predicate(p, effect.condition) or False == self.check_action_predicate(p, effect.literal):
                return False
        else:
            print('Non-effect not checked %s' % effect)
        return True

    def check_actions(self):
        for action in self.actions:
            for param in action.parameters:
                # check validity of type of param
                for t in self.types:
                    if param.type_name == t.name:
                        break
                else:
                    print('TypeError: parameter %s in action %s has invalid type' % (param, action))
                    sys.exit('Failed parameter check in action %s' % action)

            # check precondition predicates identity, arity, and look up parameters and check whether type match
            if False == self.check_action_predicate(action.parameters + self.objects, action.precondition):
                sys.exit('Action %s has invalid preconditions' % action)
            for effect in action.effects:
                if False == self.check_action_effect(action.parameters + self.objects, effect):
                    sys.exit('Action %s has invalid effects' % action)
        print('Passed the :action check')

    def syntax_check(self):
        self.check_type()
        self.check_objects()
        self.check_init()
        self.check_goal()
        self.check_actions()


class Requirements(object):
    def __init__(self, requirements):
        if ":fluents" not in requirements:
            requirements.append(":fluents")
        self.requirements = requirements
        for req in requirements:
            assert req in (
              ":strips", ":adl", ":typing", ":negation", ":equality",
              ":negative-preconditions", ":disjunctive-preconditions",
              ":existential-preconditions", ":universal-preconditions",
              ":quantified-preconditions", ":conditional-effects",
              ":derived-predicates", ":action-costs", ":fluents"), req
    def __str__(self):
        return ", ".join(self.requirements)