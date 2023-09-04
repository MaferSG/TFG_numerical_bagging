
class type_tree_node(object):
    def __init__(self, node, parent, task):
        self.node = node
        self.parent = parent
        self.task = task
        self.children = self.set_children()
        
    # Mafe: To avoid problems with  the recursion
    # Ensure that the recursive calls within the set_children method terminate properly.
    def set_children(self):
        child_types = [x for x in self.task.types if x.basetype_name == self.node.name]
        child_nodes = []
        for c in child_types:
            if c != self.node:  # check to skip creating a child node for itself
                child_nodes.append(type_tree_node(c, self, self.task))
        return child_nodes

    
    # def set_children(self):
    #     child_types = [x for x in self.task.types if x.basetype_name == self.node.name]
    #     child_nodes = []
    #     for c in child_types:
    #         child_nodes.append(type_tree_node(c, self, self.task))
    #     return child_nodes 
    
    def get_descendants(self):
        descendants = [self]
        for c in self.children:
            descendants = descendants + c.get_descendants()
        return descendants
    
    def get_ancestors(self):
        if not(self.parent):
            return [self]
        return [self] + self.parent.get_ancestors()
        
        
        
    