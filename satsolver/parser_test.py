from __future__ import print_function, absolute_import
from cStringIO import StringIO

from satsolver.parser import CNFParser


def test_simple_cnf_parsing():
    buf = StringIO(
    '''p cnf 5 15
    1 2 -3 0
    3 2 0
    1 2 0
    0
    ''')
    parser = CNFParser(buf)

    clauses = parser.clauses
    assert set(clauses[0]) == {1, 2, -3}
    assert set(clauses[1]) == {3, 2}
    assert set(clauses[2]) == {1, 2}
