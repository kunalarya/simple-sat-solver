from __future__ import print_function

import argparse
import logging
from collections import namedtuple

import parser
from util import Success, Failure


class Instance(object):
    def __init__(self, var_count, clauses, recipe=None):
        self.var_count = var_count
        self.clauses = clauses

        # maps variables -> 0, 1, or None. Note that SAT variables are 1-indexed.
        self.asgs = {i + 1: None for i in xrange(var_count)}

        self.asg_vars = set()
        self.unasg_vars = set(i + 1 for i in range(var_count))

        # Pick variables in this order, if given.
        self.recipe = recipe
        self.recipe_index = 0

        # Store any valid satisfying assignments here.
        self.solutions = []

    def resolve(self, lit):
        """Resolve the value of a literal if set, None otherwise.

        If the literal is assigned and non-negated, it will return its current
        assignment. If the literal is negated, it will return the negated
        value.
        """
        val = self.asgs[abs(lit)]
        if val is None:
            return None
        else:
            if lit < 0:
                return 1 - val  # invert
            else:
                return val

    def is_unit(self, clause):
        """Determine if a clause is unit (has one unassigned variable).

        Returns:
            Success | Failure
            Will return Failure if the clause is UNSAT, Success otherwise with
            the result being a tuple of [bool, int]:
                (is_unit, unassigned literal)
            whether the clause is unit, and if so, which literal is now implied.
            Note that the literal may be negated, thus the implied value is
            False.
        """
        default_ret = (False, -1)
        count0 = 0
        count_unasg = 0
        last_unit = -1 # Which literal is now implied

        for lit in clause:
            val = self.resolve(lit)
            if val == 0:
                count0 += 1
            elif val == 1:
                # Any True assignment fails unit
                return Success(default_ret)
            elif val is None:
                count_unasg += 1
                last_unit = lit
                if count_unasg > 1:
                    break
        if count0 == len(clause):
            logging.debug('is_unit: detected UNSAT: %s', clause)
            reason = 'is_unit detected UNSAT on clause {}'.format(clause)
            return Failure(reason)

        result = (count_unasg == 1, last_unit)
        return Success(result)

    def set_lit(self, lit, value):
        """Assign a literal with a value."""
        assert lit > 0
        current_value = self.asgs[lit]
        if current_value == None:
            logging.debug('new assignment %d = %d', lit, value)
            self.asgs[lit] = value
            self.unasg_vars.remove(lit)
            self.asg_vars.add(lit)
        else:
            if current_value != value:
                reason = ('Conflict! Tried {}={} but its already {}'
                          .format(lit, value, current_value))
                logging.error(reason)
                return Failure(reason)
        return Success()

    def unset_lit(self, lit):
        self.asgs[lit] = None
        self.unasg_vars.add(lit)
        self.asg_vars.remove(lit)

    def set_lits(self, lits, value):
        """Set multiple literals at once. Useful for testing."""
        for lit in lits:
            r = self.set_lit(lit, value)
            if not r.success:
                return r
        return Success()

    def determine_next_var(self):
        """Choose the next variable to assign.

        It will run the recipe if given, otherwise select a random unassigned
        variable.

        Returns:
            tuple(variable, value)
        """
        if self.recipe is not None:
            if len(self.recipe) > 0:
                next_var_and_value = self.recipe[0]
                self.recipe = self.recipe[1:]
                return next_var_and_value

        # Otherwise, choose a variable randomly.
        next_var = next(iter(self.unasg_vars))

        return next_var, 1

    def verify(self):
        if len(self.unasg_vars) != 0:
            raise Exception('cannot verify! unassigned vars: {}'
                            .format(self.unasg_vars))

        # decisions is a list of Decisions
        for clause in self.clauses:
            clause_sat = False
            for i in clause:
                v = self.resolve(i)
                if v == 1:
                    clause_sat = True
                    break
            if not clause_sat:
                return False

        # otherwise it's sat
        return True

    def save_solution(self):
        self.solutions.append(dict(self.asgs))


class IGNode(object):
    def __init__(self, lit, asg, level):
        assert lit > 0
        self.lit = lit
        self.asg = asg
        self.level = level
    def __repr__(self):
        return '<x_{} = {} @ {}>'.format(
                self.lit, self.asg, self.level)


def get_value(lit):
    if lit < 0:
        return abs(lit), 0
    else:
        return lit, 1


class IGraph(object):
    """Implication Graph"""
    def __init__(self):
        self.nodes = set()
        self.lits = set() # set of literals in nodes

        # map lit -> nodes w/assignments
        # dict[int, list[IGNode]]
        self.nodes_by_lit = {}

        self.fwd_edges = {}

        # maps (x -> y) tuple edge to clause
        self.edge_annot = {}

    def add_node(self, node):
        self.nodes.add(node)
        self.lits.add(node.lit)
        self.fwd_edges[node] = []
        self.nodes_by_lit[node.lit] = node

    def del_node(self, node):
        self.lits.remove(node.lit)
        self.nodes.remove(node)
        del self.fwd_edges[node]
        del self.nodes_by_lit[node.lit]

    def add_edge(self, src, dst, reason):
        self.fwd_edges[src].append(dst)
        self.edge_annot[src, dst] = reason


Implication = namedtuple('Implication', ['clause', 'lit', 'value'])
def bcp(instance, decision_level, igraph):
    """Boolean Constrain Propagation

    Returns:
        Success | Failure
        Success result:
            {lit: Implication}
        Failure means UNSAT

    """
    any_unit = True

    implications = {} # Keyed on int
    while any_unit:
        any_unit = False
        for clause_index, clause in enumerate(instance.clauses):
            r = instance.is_unit(clause)
            if not r.success: return r
            is_unit, implied = r.result

            if is_unit:
                lit = abs(implied)
                if implied > 0:
                    r = instance.set_lit(lit, 1)
                    if not r.success: return r
                    implications[lit] = Implication(clause_index, lit, 1)
                    value = 1
                else:
                    r = instance.set_lit(lit, 0)
                    if not r.success: return r
                    implications[lit] = Implication(clause_index, lit, 0)
                    value = 0

                logging.debug('implied=%d -> %d', lit, value)

                # Create a node in the IGraph if it doesn't yet exist.
                if not lit in igraph.nodes_by_lit:
                    lit_node = IGNode(lit, value, decision_level)
                    igraph.add_node(lit_node)

                # Create any edges
                for implicating_lit in clause:
                    implicating_pair = get_value(implicating_lit)
                    implicating_lit, implicating_value = implicating_pair
                    if implicating_lit != lit:
                        # create the implicating lit if needed
                        if implicating_lit not in igraph.lits:
                            inode = IGNode(implicating_lit, implicating_value,
                                           decision_level)
                            igraph.add_node(inode)
                        else:
                            inode = igraph.nodes_by_lit[implicating_lit]

                        # create an edge for this node
                        lit_node = igraph.nodes_by_lit[lit]
                        igraph.add_edge(inode, lit_node, clause)
                        logging.debug('add edge %s->%s because of %s',
                                       inode, lit_node, clause)

                any_unit = True

    return Success(implications)


Decision = namedtuple('Decision', ['level', 'lit', 'value'])
def decide(instance, decisions, level):
    """
    Args:
        decisions (list[Decision]):
        level (int):

    Returns:
        Success | Failure

    """
    # choose a variable to decide

    print('.', end='')
    logging.debug('______________________________')
    logging.debug('[level: %d]', level)


    # Choose a variable to set.
    next_var, next_value = instance.determine_next_var()

    # Create a new copy of the decisions.
    decisions = list(decisions)
    decisions.append(Decision(level, next_var, next_value))

    logging.debug('try_assignment(level=%d, %d->%d)', level, next_var,
                  next_value)
    result = try_assignment(instance, level, decisions, next_var, next_value)

    if not result.success:
        logging.debug('caused unsat: try_assignment(level=%d, %d->%d)',
                      level, next_var, next_value)
        # try the other branch

        inverted_value = 1 - next_value

        # remove last decision
        decisions = decisions[:-1]

        # add new decision
        decisions.append(Decision(level, next_var, inverted_value))

        r = try_assignment(instance, level, decisions, next_var, inverted_value)
        # If we reached UNSAT here, then there's no solution here, so propagate
        # this issue up.
        if not r.success:
            return r

    else:
        # If all variables have been assigned, store this as a solution.
        if len(instance.unasg_vars) == 0:
            if instance.verify():
                instance.save_solution()
                print('satisfied!')
            else:
                raise ValueError('All variables assigned, but UNSAT')

    return Success()


def try_assignment(instance, level, decisions, lit, value):
    logging.debug('try_assignment: lit = %d -- setting to %d', lit, value)

    # assign it True
    r = instance.set_lit(lit, value)
    if not r.success:
        return r

    igraph = IGraph()

    # build the graph
    for decision in decisions:
        # create a node for each decision
        node = IGNode(decision.lit, decision.value, decision.level)
        igraph.add_node(node)
        logging.debug('adding node %s', node)

    logging.debug('running bcp...')
    r = bcp(instance, level, igraph)
    if not r.success: # Meaning UNSAT:
        logging.debug('decision led to UNSAT. unsetting')
        instance.unset_lit(lit)
        # If it's UNSAT, we need to backtrack
        return Failure('Unsat!')

    # Otherwise it was a Success
    implications = r.result

    if len(instance.unasg_vars) > 0:
        # increase the decision level
        r = decide(instance, decisions, level+1)
        instance.unset_lit(lit)
        return r

    # otherwise, return igraph
    return Success(result=(igraph, None))


def solve(instance):
    """
    Args:
        instance (Instance): parsed SAT instance

    Returns:
        Success | Failure
    """
    result = decide(instance, [], 1)
    if not result.success:
        print('Unsatisfiable')

    return result


def main():
    cmdline_parser = argparse.ArgumentParser()
    cmdline_parser.add_argument('filename', action='store', type=str)
    args = cmdline_parser.parse_args()

    file_parser = parser.CNFFileParser(args.filename)
    inst = Instance(var_count=file_parser.var_count, clauses=file_parser.clauses)

    result = solve(inst)
    if result.success:
        # Print the solutions
        print('Satisfying solutions:')
        for solution in inst.solutions:
            print(solution)

if __name__ == '__main__':
    main()
