from lang import *
from functools import reduce
from abc import ABC, abstractmethod


class Edge():
    """
    This class implements the edge of the points-to graph that is used to
    solve Andersen-style alias analysis.
    """
    def __init__(self, dst, src):
        """
        An edge dst -> src indicates that every pointer in dst must be also
        within the alias set of src.
        """
        self.src = src
        self.dst = dst

    def eval(self, env):
        """
        Evaluating an edge such as dst -> src means copying every pointer in
        Alias(dst) into Alias(src). This function returns True if the
        points-to set of dst changes after the evaluation.

        Se Alias(src) >= Alias(dst): tudo o que dst aponta também deve ser apontado por src

        Example:
            >>> e = Edge('a', 'b')
            >>> env = {'a': {'ref_1'}, 'b': {'ref_0'}}
            >>> result = e.eval(env)
            >>> f"{result}: {sorted(env['a'])}"
            "True: ['ref_0', 'ref_1']"
        """
        # The points-to set of dst changes if the union of the points-to set of dst and src is different from the points-to set of dst.
        # If the points-to set of dst changes, then we update the points-to set of dst with the union of the points-to set of dst and src.
        # We return True if the points-to set of dst changes; otherwise, we return False.
        if not env[self.dst].issuperset(env[self.src]):
            env[self.dst] = env[self.src].union(env[self.dst])
            return True
        else:
            return False

    def __str__(self):
        """
        The string representation of an edge.

        Example:
            >>> e = Edge('a', 'b')
            >>> str(e)
            'Alias(a) >= Alias(b)'
        """
        return f"Alias({self.dst}) >= Alias({self.src})"

    def __repr__(self):
        """
        The string representation of an edge.

        Example:
            >>> e = Edge('a', 'b')
            >>> repr(e)
            'Alias(a) >= Alias(b)'
        """
        return str(self)

def init_env(insts):
    """
    Uses the basic constraints derived from alloca instructions to initialize
    the environment.

    Example:
        >>> Inst.next_index = 0
        >>> i0 = Alloca('v')
        >>> i1 = Alloca('v')
        >>> i2 = Alloca('w')
        >>> sorted(init_env([i0, i1, i2])['v'])
        ['ref_0', 'ref_1']
    """
    # TODO: Implement this method.
    # env is a dictionary that maps variable names to the names of the references that the variable points to.
    # we iterate over all the instructions in insts and, for each instruction of type Alloca, add a new reference to the points-to set of the variable.
    # i0 = Alloca('v') -> v = alloca -> env = {'v': {'ref_0'}}
    # i1 = Alloca('v') -> v = alloca -> env = {'v': {'ref_0', 'ref_1'}}
    # i2 = Alloca('w') -> w = alloca -> env = {'v': {'ref_0', 'ref_1'}, 'w': {'ref_2'}}
    env = {}
    for inst in insts:
        if isinstance(inst, Alloca):
            if inst.name not in env:
                env[inst.name] = set()
            env[inst.name].add(f"ref_{inst.ID}")
    return env


def propagate_alias_info(edges, env):
    """
    Propagates all the points-to information along the edges of the points-to
    graph once. If any points-to set changes, then this function returns true;
    otherwise, it returns false.

    Example:
        >>> e0 = Edge('b', 'a')
        >>> e1 = Edge('y', 'x')
        >>> env = {'a': {'v0'}, 'x': {'v2'}}
        >>> changed = propagate_alias_info([e0, e1], env)
        >>> f"{changed, env['y'], env['b']}"
        "(True, {'v2'}, {'v0'})"

        >>> e = Edge('b', 'a')
        >>> env = {'a': {'v0'}, 'b': {'v0'}}
        >>> changed = propagate_alias_info([e], env)
        >>> f"{changed, env['a'], env['b']}"
        "(False, {'v0'}, {'v0'})"
    """
    # TODO: Implement this method.
    # If we have Edge ('b', 'a') so we have to copy all the elements of 'a' to 'b'
    # After calling propagate_alias_info([e0, e1], env), the function propagates the aliasing information
    # from 'a' to 'b' and from 'x' to 'y'. So, 'b' becomes an alias of 'v0' and 'y' becomes an alias of 'v2'.
    # Cria uma edge (b -> v0) e uma edge (y -> v2)
    # The function returns True because the points-to set of 'b' and 'y' changes.
    changed = False
    for edge in edges:
        # edge.eval(env) returns True if the points-to set of dst changes after the evaluation.
        if edge.dst not in env:
            env[edge.dst] = set()

        if edge.eval(env):
            changed = True
    return changed


def evaluate_st_constraints(insts, env):
    """
    A store constraint is created by an instruction such as *ref = src. To
    evaluate a constraint like this, we do as follows: for each t in ref, we
    create a new edge src -> t. The result of evaluating this constraint is a
    new set of edges. This function returns all the edges Edge(src, t), such
    that t is in the points to set of ref.

    Example:
        >>> Inst.next_index = 0
        >>> i0 = Store('b', 'a') # *b = a
        >>> i1 = Store('y', 'x') # *y = x
        >>> env = {'b': {'r'}, 'y': {'x', 's'}} #inst.ref = b, ref = r
        >>> edges = evaluate_st_constraints([i0, i1], env)
        >>> sorted([str(edge) for edge in edges])
        ['Alias(r) >= Alias(a)', 'Alias(s) >= Alias(x)']
    """
    # TODO: Implement this method.
    # *v = w: Stores the contents of w into the memory location referenced by v.
    # *v = w: For each reference t in v, we create a new edge w -> t.
    # The result of evaluating this constraint is a new set of edges.
    # This function returns all the edges Edge(w, t), such that t is in the points-to set of v.
    # In the example: i0 = Store('b', 'a') -> *b = a -> env = {'b': {'r'}, 'a': {'ref_0'}}
    # We have to create a new edge a -> r. It means that all the references in 'a' must be also in 'r'.
    # So, the function returns [Edge('a', 'r')] -> ['Alias(r) >= Alias(a)'] (a now points to r)
    edges = []
    for inst in insts:
        #print("EVALUATING INST", inst)
        if isinstance(inst, Store):
            if inst.src not in env:
               # print("SRC NOT IN ENV, CREATING SET() FOR: ", inst.src)
                env[inst.src] = set()
            if inst.ref not in env:
                #print("REF NOT IN ENV, CREATING SET() FOR: ", inst.ref)
                env[inst.ref] = set()
            for ref in env[inst.ref]:
                if (inst.src != ref):
                    #print("ADDING EDGE: ", Edge(inst.src, ref))
                    edges.append(Edge(ref, inst.src))
    return edges


def evaluate_ld_constraints(insts, env):
    """
    A load constraint is created by an instruction such as dst = *ref. To
    evaluate a constraint like this, we do as follows: for each t in ref, we
    create a new edge t -> dst. The result of evaluating this constraint is a
    new set of edges. This function, like evaluate_st_constraints, returns
    the set of edges t -> dst, such that t is in th points-to set of ref.

    Example:
        >>> Inst.next_index = 0
        >>> i0 = Load('b', 'a') # b = *a
        >>> i1 = Load('y', 'x') # y = *x
        >>> env = {'a': {'r'}, 'x': {'y', 's'}}
        >>> edges = evaluate_ld_constraints([i0, i1], env)
        >>> sorted([str(edge) for edge in edges])
        ['Alias(b) >= Alias(r)', 'Alias(y) >= Alias(s)']
    """
    # TODO: Implement this method.
    # v = *w: Loads the contents of the memory location referenced by w into v.
    # v = *w: For each reference t in w, we create a new edge t -> v.
    # The result of evaluating this constraint is a new set of edges.
    # This function returns all the edges Edge(t, v), such that t is in the points-to set of w.
    # In the example: i0 = Load('b', 'a') -> b = *a -> env = {'a': {'ref_0'}, 'b': {'r'}}
    # We have to create a new edge ref_0 -> r. It means that all the references in 'a' must be also in 'r'.
    # So, the function returns [Edge('ref_0', 'r')] -> ['Alias(b) >= Alias(r)']
    edges = []
    for inst in insts:
        if isinstance(inst, Load):
            if inst.dst not in env:
                env[inst.dst] = set()
            if inst.ref not in env:
                env[inst.ref] = set()
            for ref in env[inst.ref]:
                if (inst.dst != ref):
                    edges.append(Edge(inst.dst, ref))
    return edges


def abstract_interp(insts):
    """
    This function solves points-to analysis in four steps:
    1. It creates an initial environment with the results of Allocas
    2. It creates an initial points-to graph G with the Move instructions
    3. It iterates the following three steps, while points-to data changes:
       3.a: evaluate all the store constraints, maybe adding new edges to G.
       3.b: evaluate all the load constraints, maybe adding new edges to G.
       3.c: propagate points-to information along the edges of G.

    Example:
        >>> Inst.next_index = 0
        >>> i0 = Alloca('p0')
        >>> i1 = Alloca('p1')
        >>> i2 = Store('p0', 'p1')
        >>> i3 = Load('p2', 'p0')
        >>> i4 = Store('p2', 'one')
        >>> i5 = Move('p3', 'p1')
        >>> i6 = Store('p3', 'two')
        >>> env = abstract_interp([i0, i1, i2, i3, i4, i5, i6])
        >>> env['p0'], env['p1'], env['p2'], env['p3'], env['ref_0']
        ({'ref_0'}, {'ref_1'}, {'ref_1'}, {'ref_1'}, {'ref_1'})
    """
    # TODO: Implement this method.

    # 1. Initializing the environment:
    env = {}
    env = init_env(insts)
    #print("initial env;  ", env)

    # 2. Build the initial graph of points-to relations:
    edges = []
    for inst in insts:
        if isinstance(inst, Move):
            edges.append(Edge(inst.dst, inst.src))
    #for edge in edges:
        #print("edges added after move:  ", edge)

    # 3. Run iterations until we stabilize:
    store_insts = []
    load_insts = []
    for inst in insts:
        if isinstance(inst, Store):
            store_insts.append(inst)
        if isinstance(inst, Load):
            load_insts.append(inst)


    changed = True
    while changed:
        # 3.a: Evaluate all the complex constraints:
        initial_edges = edges
        new_st_edges = evaluate_st_constraints(store_insts, env)
        for edge in new_st_edges:
            if edge not in edges:
                edges.append(edge)

        new_ld_edges = evaluate_ld_constraints(load_insts, env)
        for edge in new_ld_edges:
            if edge not in edges:
                edges.append(edge)

        if initial_edges == edges:
            changed = False


        # 3.b: Propagate the points-to information:
        changed = propagate_alias_info(edges, env)
        pass

    for key in list(env.keys()):
        if not env[key]:
            del env[key]

    return env