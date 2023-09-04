# Renamed from types.py to avoid clash with stdlib module.
# In the future, use explicitly relative imports or absolute
# imports as a better solution.

import itertools
import collections

def _get_type_predicate_name(type_name):
    # PDDL allows mixing types and predicates, but some PDDL files
    # have name collisions between types and predicates. We want to
    # support both the case where such name collisions occur and the
    # case where types are used as predicates.
    #
    # We internally give types predicate names that cannot be confused
    # with non-type predicates. When the input uses a PDDL type as a
    # predicate, we automatically map it to this internal name.
    return "type@%s" % type_name


class Type(object):
    def __init__(self, name, basetype_name=None):
        self.name = name
        self.basetype_name = basetype_name

    def __str__(self):
        return self.name

    def __repr__(self):
        return "Type(%s, %s)" % (self.name, self.basetype_name)

    def get_predicate_name(self):
        return _get_type_predicate_name(self.name)
    
    def get_child_types(self, types_list):
        child_types = []
        for t in types_list:
            if t.basetype_name == self.name:
                child_types.append(t)
        return child_types

    def is_baggable(self, baggable_types_list):
        return self.name in [baggable_type.object_type.name for baggable_type in baggable_types_list]
        


class TypedObject(object):
    def __init__(self, name, type_name):
        self.name = name
        self.type_name = type_name

    def __hash__(self):
        return hash((self.name, self.type_name))

    def __eq__(self, other):
        return self.name == other.name and self.type_name == other.type_name

    def __ne__(self, other):
        return not self == other

    def __str__(self):
        return "%s: %s" % (self.name, self.type_name)

    def pddl_str(self):
        return "%s - %s" % (self.name, self.type_name)

    def __repr__(self):
        return "<TypedObject %s: %s>" % (self.name, self.type_name)

    def uniquify_name(self, type_map, renamings):
        if self.name not in type_map:
            type_map[self.name] = self.type_name
            return self
        for counter in itertools.count(1):
            new_name = self.name + str(counter)
            if new_name not in type_map:
                renamings[self.name] = new_name
                type_map[new_name] = self.type_name
                return TypedObject(new_name, self.type_name)

    def get_atom(self):
        # TODO: Resolve cyclic import differently.
        from . import conditions
        predicate_name = _get_type_predicate_name(self.type_name)
        return conditions.Atom(predicate_name, [self.name])
    
    # Mafe
    def is_baggable(self, baggable_types_list):
        return self.type_name in [baggable_type.object_type.name for baggable_type in baggable_types_list]
    
    def get_basetype_name(self, types_list):
        matching_type = next((t for t in types_list if t.name == self.type_name), None)
        if matching_type:
            return matching_type.basetype_name
        else:
            return None
    
    def get_child_types(self, types_list):
        child_types = []
        for t in types_list:
            if t.basetype_name == self.type_name:
                child_types.append(t)
        return child_types


# convert a list of typed items to string and group items of same type together
def typed_list_to_string(typed_list, separator=' '):
    result = ''
    type_dict = collections.defaultdict(list)
    for t in typed_list:
        if hasattr(t, "basetype_name"):
            type_dict[t.basetype_name].append(t.name)
        else:
            type_dict[t.type_name].append(t.name)
    for types in type_dict:
        if types != None:
            # don't print the trivial object - None entry 
            for t in type_dict[types]:
                result += t + ' '
            result += ' - %s%s' % (types, separator)
    return result
