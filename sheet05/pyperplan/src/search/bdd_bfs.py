import itertools
import sys
sys.path.append("/Users/atahankaragoz/Documents/GitHub/planopt-hs24/sheet05/pyperplan/src")
from task import Task
from search.bdd import *


class BDDSearch(object):
    def __init__(self, task):
        self.task = task
        self.fact_to_id = dict()
        for i, f in enumerate(self.task.facts):
            self.fact_to_id[f] = 2 * i
            self.fact_to_id[f + "PRIME"] = 2 * i + 1
            # Uncomment the following two lines and comment out the above two lines for part (b) of Exercise 5.2
            # self.fact_to_id[f] = i
            # self.fact_to_id[f + "PRIME"] = i + len(self.task.facts)
        self.id_to_fact = {i: f for f, i in self.fact_to_id.items()}
        self.transition_relation = self.create_transition_relation()

    def state_to_ids(self, state):
        result = dict()
        for fact in self.task.facts:
            result[self.fact_to_id[fact]] = fact in state
        return result

    def ids_to_state(self, ids):
        result = set()
        for v, value in ids.items():
            if value:
                result.add(self.id_to_fact[v])
        return result

    def get_fact_id(self, fact, primed=False):
        if primed:
            fact = fact + "PRIME"
        return self.fact_to_id[fact]

    def get_atom_bdd(self, fact, primed):
        return bdd_atom(self.get_fact_id(fact, primed))

    def conjunction_to_set(self, conjunction):
        b = one()
        for fact in conjunction:
            fact_bdd = self.get_atom_bdd(fact, False)
            b = bdd_intersection(b, fact_bdd)
        return b

    def create_transition_relation(self):
        t = zero()
        for op in self.task.operators:
            op_pre = one()
            for pre in op.preconditions:
                op_pre = bdd_intersection(op_pre, self.get_atom_bdd(pre, False))
            op_add = one()
            for eff in op.add_effects:
                op_add = bdd_intersection(op_add, self.get_atom_bdd(eff, True))
            op_del = one()
            for eff in op.del_effects:
                if eff not in op.add_effects:
                    op_del = bdd_intersection(op_del, bdd_complement(self.get_atom_bdd(eff, True)))

            unchanged = one()
            for fact in self.task.facts:
                if fact not in op.del_effects and fact not in op.add_effects:
                    unchanged = bdd_intersection(unchanged, bdd_biimplication(self.get_atom_bdd(fact, False),
                                                                               self.get_atom_bdd(fact, True)))
            t = bdd_union(t, bdd_intersection(op_pre, bdd_intersection(op_add, bdd_intersection(op_del, unchanged))))
        return t

    def apply_ops(self, reached):
        next_states = bdd_forget(bdd_intersection(reached, self.transition_relation), 
                                 *[self.fact_to_id[f + "PRIME"] for f in self.task.facts])
        return next_states

    def construct_plan(self, reached):
        goal = self.conjunction_to_set(self.task.goals)
        s_ids = bdd_get_ids_of_arbitrary_state(bdd_intersection(goal, reached[-1]))
        plan = []
        for reached_i in reversed(reached[:-1]):
            s = self.ids_to_state(s_ids)
            for op in self.task.operators:
                regr_s = (s - op.add_effects) | op.preconditions
                p = bdd_state(self.state_to_ids(regr_s))
                c = bdd_intersection(p, reached_i)
                if not bdd_equals(c, zero()):
                    s_ids = bdd_get_ids_of_arbitrary_state(c)
                    plan.insert(0, op)
                    break
        return plan

    def run(self):
        goal = self.conjunction_to_set(self.task.goals)
        reached = [bdd_state(self.state_to_ids(self.task.initial_state))]

        step = 0
        while not bdd_equals(bdd_intersection(goal, reached[-1]), zero()):
            print_bdd_nodes()
            next_reached = self.apply_ops(reached[-1])
            if bdd_equals(next_reached, zero()):
                return None
            reached.append(next_reached)
            step += 1

        return self.construct_plan(reached)


def bdd_bfs_solve(task):
    search = BDDSearch(task)
    return search.run()

def print_bdd_nodes():
    print("Amount of BDD Nodes: {}".format(len(VAR)))
