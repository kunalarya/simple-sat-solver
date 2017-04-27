from __future__ import print_function

import argparse
import logging
from collections import namedtuple

import satsolver.parser as parser
from satsolver.util import Success, Failure
from satsolver.state import Instance


class Node(object):
    def __init__(self, lit, asg, level):
        assert lit > 0
        self.lit = lit
        self.asg = asg
        self.level = level
    def __repr__(self):
        return '<x_{} = {} @ {}>'.format(
                self.lit, self.asg, self.level)


class ImplicationGraph(object):
    """Implication Graph"""
    def __init__(self):
        self.nodes = set()
        self.lits = set() # set of literals in nodes

        # map lit -> nodes w/assignments
        # dict[int, list[Node]]
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


Decision = namedtuple('Decision', ['level', 'lit', 'value'])
Implication = namedtuple('Implication', ['clause', 'lit', 'value'])

class Solver(object):
    """Main Solver"""
    def __init__(self, instance, recipe=None):

        self.instance = instance

        # Pick variables in this order, if given.
        self.recipe = recipe
        self.recipe_index = 0

    # def new_var(self):
    #     pass

    # def add_clause(self, lits):
    #     pass

    # def simplify_db(self):
    #     pass

    def solve(self):
        result = self.decide([], 1)
        return result

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
        next_var = next(iter(self.instance.unasg_vars))

        return next_var, 1

    def bcp(self, decision_level, igraph):
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
            for clause_index, clause in enumerate(self.instance.clauses):
                r = self.instance.is_unit(clause)
                if not r.success: return r
                is_unit, implied = r.result

                if is_unit:
                    lit = abs(implied)
                    if implied > 0:
                        r = self.instance.set_lit(lit, 1)
                        if not r.success: return r
                        implications[lit] = Implication(clause_index, lit, 1)
                        value = 1
                    else:
                        r = self.instance.set_lit(lit, 0)
                        if not r.success: return r
                        implications[lit] = Implication(clause_index, lit, 0)
                        value = 0

                    logging.debug('implied=%d -> %d', lit, value)

                    # Create a node in the ImplicationGraph if it doesn't yet exist.
                    if not lit in igraph.nodes_by_lit:
                        lit_node = Node(lit, value, decision_level)
                        igraph.add_node(lit_node)

                    # Create any edges
                    for implicating_lit in clause:
                        implicating_pair = self.instance.get_value(implicating_lit)
                        implicating_lit, implicating_value = implicating_pair
                        if implicating_lit != lit:
                            # create the implicating lit if needed
                            if implicating_lit not in igraph.lits:
                                inode = Node(implicating_lit, implicating_value,
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


    def decide(self, decisions, level):
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
        next_var, next_value = self.determine_next_var()

        # Create a new copy of the decisions.
        decisions = list(decisions)
        decisions.append(Decision(level, next_var, next_value))

        logging.debug('try_assignment(level=%d, %d->%d)', level, next_var,
                    next_value)
        result = self.try_assignment(level, decisions, next_var, next_value)

        if not result.success:
            logging.debug('caused unsat: try_assignment(level=%d, %d->%d)',
                        level, next_var, next_value)
            # try the other branch

            inverted_value = 1 - next_value

            # remove last decision
            decisions = decisions[:-1]

            # add new decision
            decisions.append(Decision(level, next_var, inverted_value))

            r = self.try_assignment(level, decisions, next_var, inverted_value)
            # If we reached UNSAT here, then there's no solution here, so propagate
            # this issue up.
            if not r.success:
                return r

        else:
            # If all variables have been assigned, store this as a solution.
            if len(self.instance.unasg_vars) == 0:
                if self.instance.verify():
                    self.instance.save_solution()
                    print('satisfied!')
                else:
                    raise ValueError('All variables assigned, but UNSAT')

        return Success()


    def try_assignment(self, level, decisions, lit, value):
        logging.debug('try_assignment: lit = %d -- setting to %d', lit, value)

        # assign it True
        r = self.instance.set_lit(lit, value)
        if not r.success:
            return r

        igraph = ImplicationGraph()

        # build the graph
        for decision in decisions:
            # create a node for each decision
            node = Node(decision.lit, decision.value, decision.level)
            igraph.add_node(node)
            logging.debug('adding node %s', node)

        logging.debug('running bcp...')
        r = self.bcp(level, igraph)
        if not r.success: # Meaning UNSAT:
            logging.debug('decision led to UNSAT. unsetting')
            self.instance.unset_lit(lit)
            # If it's UNSAT, we need to backtrack
            return Failure('Unsat!')

        # Otherwise it was a Success
        implications = r.result

        if len(self.instance.unasg_vars) > 0:
            # increase the decision level
            r = self.decide(decisions, level+1)
            self.instance.unset_lit(lit)
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

    solver = Solver(instance)
    result = solver.solve()
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
