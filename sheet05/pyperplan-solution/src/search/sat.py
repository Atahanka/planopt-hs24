from collections import defaultdict
import itertools
import logging

from search import minisat
from task import Operator

# Max number of steps in a plan
HORIZON = 1000


class SATSearch:
    def __init__(self, task, horizon, parallel):
        self.task = task
        self.horizon = horizon
        self.op_vars = {}
        self.fact_vars = {}
        self.var_ids_to_ops = {}
        self.fact_achievers = defaultdict(set)
        self.fact_deleters = defaultdict(set)
        var_id = 1
        for t in range(horizon + 1):
            for op in task.operators:
                self.op_vars[op, t] = var_id
                self.var_ids_to_ops[var_id] = (op, t)
                var_id += 1
                for add in op.add_effects:
                    self.fact_achievers[add].add(op)
                for d in op.del_effects:
                    self.fact_deleters[d].add(op)
            for var in task.facts:
                self.fact_vars[var, t] = var_id
                var_id += 1
        self.num_vars = var_id - 1
        self.clauses = []
        if parallel:
            self.build_parallel_model()
        else:
            self.build_sequential_model()

    def get_op_var(self, op, time_step, negated):
        var = self.op_vars[op, time_step]
        if negated:
            var = -var
        return var

    def get_fact_var(self, fact, time_step, negated):
        var = self.fact_vars[fact, time_step]
        if negated:
            var = -var
        return var

    def add_clause(self, clause):
        self.clauses.append(clause)

    def build_sequential_model(self):
        # initial state clauses
        for i in self.task.initial_state:
            self.add_clause([self.get_fact_var(i, 0, negated=False)])
        for i in self.task.facts - self.task.initial_state:
            self.add_clause([self.get_fact_var(i, 0, negated=True)])

        # goal clauses
        for g in self.task.goals:
            self.add_clause([self.get_fact_var(g, self.horizon, negated=False)])

        for time_step in range(self.horizon):
            next_time_step = time_step + 1
            for op in self.task.operators:
                # precondition clauses: op^t -> pre^t
                for pre in op.preconditions:
                    self.add_clause([self.get_op_var(op, time_step, negated=True),
                                     self.get_fact_var(pre, time_step, negated=False)])

                # effect clauses: op^t -> add^t+1/del^t+1
                for add in op.add_effects:
                    self.add_clause([self.get_op_var(op, time_step, negated=True),
                                     self.get_fact_var(add, next_time_step, negated=False)])
                for d in op.del_effects:
                    self.add_clause([self.get_op_var(op, time_step, negated=True),
                                     self.get_fact_var(d, next_time_step, negated=True)])

            for fact in self.task.facts:
                # positive frame clauses: (fact^t /\ ~fact^t+1) -> \/ op^t for all op with fact in del(o)
                self.add_clause([self.get_fact_var(fact, time_step, negated=True),
                                 self.get_fact_var(fact, next_time_step, negated=False)] +
                                [self.get_op_var(op, time_step, negated=False) for op in self.fact_deleters[fact]])

                # negative frame clauses: (~fact^t /\ fact^t+1) -> \/ op^t for all op with fact in add(o)
                self.add_clause([self.get_fact_var(fact, time_step, negated=False),
                                 self.get_fact_var(fact, next_time_step, negated=True)] +
                                [self.get_op_var(op, time_step, negated=False) for op in self.fact_achievers[fact]])

            # operator exclusion clauses
            for op, op2 in itertools.permutations(self.task.operators, r=2):
                self.add_clause([self.get_op_var(op, time_step, negated=True),
                                 self.get_op_var(op2, time_step, negated=True)])

            # operator selection clause
            self.add_clause([self.get_op_var(op, time_step, negated=False) for op in self.task.operators])

    def build_parallel_model(self):
        # TODO implement parallel encoding.
        pass

    def solve(self):
        result = minisat.solve(self.num_vars, self.clauses)
        if result is not None:
            time_step_to_positive_ops = defaultdict(set)
            for valuation in result:
                if valuation > 0:
                    if valuation in self.var_ids_to_ops:
                        op, time_step = self.var_ids_to_ops[valuation]
                        time_step_to_positive_ops[time_step].add(op)

            plan = []
            for time_step in range(self.horizon):
                ops_in_time_step = time_step_to_positive_ops[time_step]
                assert len(ops_in_time_step) >= 1
                for op in ops_in_time_step:
                    plan.append(op)
            # print(plan)
            return plan
        return result

def sat_solve(task, max_steps, parallel):
    logging.info('Maximum number of plan steps: {0}'.format(max_steps))
    for horizon in range(max_steps + 1):
        logging.info('Horizon: {0}'.format(horizon))
        search = SATSearch (task, horizon, parallel)
        result = search.solve()
        if result is not None:
            return result
    logging.info('Try increasing the maximum number of steps')
    return None

def sat_solve_sequentially(task, max_steps=HORIZON):
    return sat_solve(task, max_steps, parallel=False)

def sat_solve_parallely(task, max_steps=HORIZON):
    return sat_solve(task, max_steps, parallel=True)
