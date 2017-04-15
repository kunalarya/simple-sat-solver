import pytest

from satsolver.sat_solver import Instance, bcp, solve
from satsolver.sat_solver import IGraph

# -- is_unit --

def test_is_unit_simple_0None():
    clauses = [[1, 2]]
    inst = Instance(var_count=2, clauses=clauses)
    # if var 1 is 1, then var 2 must be 1
    inst.set_lit(1, 0)
    r = inst.is_unit(clauses[0])
    is_unit, implied = r.result
    assert is_unit
    assert implied == 2

def test_is_unit_simple_None0():
    clauses = [[1, 2]]
    inst = Instance(var_count=2, clauses=clauses)
    # if var 1 is 1, then var 2 must be 1
    inst.set_lit(2, 0)
    r = inst.is_unit(clauses[0])
    is_unit, implied = r.result
    assert is_unit
    assert implied == 1

def test_is_unit_single_lit():
    clauses = [[1]]
    inst = Instance(var_count=1, clauses=clauses)
    r = inst.is_unit(clauses[0])
    is_unit, implied = r.result
    assert is_unit
    assert implied == 1

def test_is_unit_all0():
    clauses = [[1, 2, 3, 4]]
    inst = Instance(var_count=4, clauses=clauses)
    inst.set_lits(range(1, 5), 0)
    result = inst.is_unit(clauses[0])
    r = inst.is_unit(clauses[0])
    assert not r.success

def test_is_unit_one1_oneNone_rest0():
    clauses = [[1, 2, 3, 4]]
    inst = Instance(var_count=4, clauses=clauses)
    inst.set_lit(1, 1)
    inst.set_lits([3, 4], 0)
    r = inst.is_unit(clauses[0])
    is_unit, implied = r.result
    assert not is_unit

def test_is_unit_three0s_twoNones():
    clauses = [[1, 2, 3, 4, 5]]
    inst = Instance(var_count=5, clauses=clauses)
    inst.set_lits([1, 2, 3], 0)
    r = inst.is_unit(clauses[0])
    is_unit, implied = r.result
    assert not is_unit

def test_is_unit_inv_simple():
    clauses = [[1, -2]] # should imply that 2 is False
    inst = Instance(var_count=2, clauses=clauses)
    inst.set_lit(1, 0)
    r = inst.is_unit(clauses[0])
    is_unit, implied = r.result
    assert is_unit
    assert implied == -2

def test_is_unit_inv_one1_twoNone():
    clauses = [[-1, -2, 3, 4]]
    inst = Instance(var_count=4, clauses=clauses)
    inst.set_lits([1, 2], 1)
    r = inst.is_unit(clauses[0])
    is_unit, implied = r.result
    assert not is_unit

def test_is_unit_inv_one1_oneNone_one0():
    clauses = [[-1, -2, 3, 4]]
    inst = Instance(var_count=4, clauses=clauses)
    inst.set_lits([1, 2], 1)
    inst.set_lit(4, 0)
    r = inst.is_unit(clauses[0])
    is_unit, implied = r.result
    assert is_unit
    assert implied == 3

# -- bcp --

def test_bcp_simplest():
    clauses = [[1, 2]]
    inst = Instance(var_count=2, clauses=clauses)
    # if var 1 is 1, then var 2 must be 1
    inst.set_lit(1, 0)
    bcp(inst, 0, IGraph())
    assert inst.asgs[2] == 1


def test_bcp_2cascade():
    # first one implies 2 == 1, second one implies 3 == 1
    clauses = [[1, 2], [-2, 3]]
    inst = Instance(var_count=3, clauses=clauses)
    inst.set_lit(1, 0)
    bcp(inst, 0, IGraph())
    assert inst.asgs[2] == 1
    assert inst.asgs[3] == 1


def test_bcp_3cascade():
    # first one implies 2 == 1, second one implies 3 == 1
    # third clause implies 6 == 0 if 4 & 5 are set to 0
    clauses = [[1, 2], [-2, 3], [-3, 4, 5, -6]]
    inst = Instance(var_count=6, clauses=clauses)
    inst.set_lit(1, 0)
    inst.set_lits([4, 5], 0)
    bcp(inst, 0, IGraph())
    assert inst.asgs[2] == 1
    assert inst.asgs[3] == 1
    assert inst.asgs[6] == 0

def test_bcp_detect_conflict():
    clauses = [[1, 2], [-2, 3]]
    inst = Instance(var_count=6, clauses=clauses)
    inst.set_lit(1, 0) # will imply 2 == 1
    inst.set_lit(3, 0) # now the second clause is UNSAT
    r = bcp(inst, 0, IGraph())
    assert not r.success

def test_bcp_detect_unsat():
    clauses = [[1, 2], [-2, 3], [-2, -3]]
    #
    inst = Instance(var_count=6, clauses=clauses)
    inst.set_lit(1, 0) # will imply 2 == 1
    r = bcp(inst, 0, IGraph())
    assert not r.success

# -------

def test_solver():
    # simple sat problem:
    clauses = [[1, -2], [3, -4], [1, 4]]
    recipe = [(2, 0), (1, 0), (3, 0), (4, 0)]
    inst = Instance(var_count=4, clauses=clauses, recipe=recipe)
    solve(inst)
    # TODO: Add some assertions.


def test_bcp_igraph():
    clauses = [[1, 2], [1, 3, 7], [-2, -3, 4], [-4, 5, 8], [-4, 6, 9],
               [-5, -6]]
    recipe = [(7, 0), (8, 0), (9, 0), (4, 0)]
    inst = Instance(var_count=9, clauses=clauses, recipe=recipe)
    solve(inst)
    # TODO: Add some assertions.


def test_verify_sat():
    clauses = [[1, -2], [4, 5, -6]]
    inst = Instance(var_count=6, clauses=clauses)
    inst.set_lits([1, 4], 1)
    inst.set_lits([2, 3, 5, 6], 0)
    assert inst.verify()


def test_verify_unsat():
    clauses = [[1, -2], [4, 5, -6]]
    inst = Instance(var_count=6, clauses=clauses)
    inst.set_lits([2, 4], 1)
    inst.set_lits([1, 3, 5, 6], 0)
    assert not inst.verify()
