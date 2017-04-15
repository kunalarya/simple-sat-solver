from __future__ import print_function, absolute_import

import re


class CNFParser(object):
    """Stream parser for DIMACS format"""

    def __init__(self, file_object):
        self.file_object = file_object
        self.var_count = 0
        self.clauses = []

        self.remove_doubles = re.compile(r'\s\s+')

        self._parse()

    def _parse(self):

        # find the header
        line_number, header = self._find_header()
        elms = header.split()
        if len(elms) != 4:
            raise ValueError('Unrecognized cnf header: "{}"'.format(header))

        sig, filetype, var_count, clause_count = elms
        self.var_count = int(var_count)
        self.clause_count = int(clause_count)

        for i, line in enumerate(self.file_object):
            self._parse_line(line_number + i, line)

    def _warn(self, msg):
        print('Warning: {}'.format(msg))

    def _find_header(self):
        for line_number, line in enumerate(self.file_object):
            line = line.strip()
            if line[0] == 'p':
                return line_number, line
            elif line[0] == 'c' or line == '':
                continue
            else:
                raise Exception('Unexpected header on line {}: "{}"'
                                .format(line_number, line))

    def _parse_line(self, line_number, line):

        line = line.strip()
        if len(line) == 0:
            return

        # Be flexible with comments (since some benchmarks use either)
        if line[0] in '#c':
            return

        line = self.remove_doubles.sub(r' ', line)
        elms = line.split()

        clause = []
        for clause_str in elms:
            clause_str = clause_str.strip()
            try:
                literal = int(clause_str)
            except ValueError:
                self._warn('Error in line #{} -- could not parse "{}"'.format(
                           line_number, clause_str))
                continue

            if literal == 0:
                break

            clause.append(literal)

        if len(clause) > 0:
            self.clauses.append(clause)


class CNFFileParser(CNFParser):
    """Parse DIMACS files"""
    def __init__(self, filename):
        self.filename = filename
        with open(filename, 'r') as f:
            super(CNFFileParser, self).__init__(f)
