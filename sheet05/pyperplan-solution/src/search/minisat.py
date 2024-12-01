import sys
import subprocess
import logging

import tools


INPUT = 'input.cnf'
OUTPUT = 'output.txt'
MINISAT = 'minisat'


def minisat_available():
    return tools.command_available([MINISAT, '--help'])


def write_minisat_input(num_variables, cnf_formula, filename):
    assert(isinstance(cnf_formula, list))

    with open(filename, 'w') as cnf_file:
        cnf_file.write("p {} {}\n".format(num_variables, len(cnf_formula)))

        for clause in cnf_formula:
            assert(isinstance(clause, list))
            for literal in clause:
                assert(isinstance(literal, int))
                assert(literal != 0)
                assert(abs(literal) <= num_variables)
                cnf_file.write("{} ".format(literal))
            cnf_file.write("0\n")


def call_minisat(input_filename, output_filename):
    try:
        logging.debug('Solving with %s' % MINISAT)
        process = subprocess.Popen([MINISAT, input_filename, output_filename],
                                   stderr=subprocess.PIPE,
                                   stdout=subprocess.PIPE)
        process.wait()
    except OSError:
        logging.error('Minisat could not be found. '
            'Please make the executable "%s" available on the path '
            '(e.g. /usr/bin).' % MINISAT)
        sys.exit(1)


def parse_minisat_output(output_filename):
    with open(output_filename, 'r') as f:
        lines = f.readlines()
    if lines[0].startswith('SAT'):
        # Last element is always a zero
        literals = lines[1].split()[:-1]
        return [int(literal) for literal in literals]
    return None


def solve(num_variables, cnf_formula):
    write_minisat_input(num_variables, cnf_formula, INPUT)
    call_minisat(INPUT, OUTPUT)
    result = parse_minisat_output(OUTPUT)
    tools.remove(INPUT)
    tools.remove(OUTPUT)
    return result
