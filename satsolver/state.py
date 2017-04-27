import logging

from satsolver.util import Success, Failure


class Instance(object):
    """Primary state for Solver"""
    def __init__(self, var_count, clauses):
        self.var_count = var_count
        self.clauses = clauses

        # maps variables -> 0, 1, or None. Note that SAT variables are 1-indexed.
        self.asgs = {i + 1: None for i in xrange(var_count)}

        self.asg_vars = set()
        self.unasg_vars = set(i + 1 for i in range(var_count))

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


    def get_value(self, lit):
        if lit < 0:
            return abs(lit), 0
        else:
            return lit, 1


