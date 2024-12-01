import itertools

from task import Task
from search.bdd import *


class BDDSearch(object):
    def __init__(self, task):
        self.task = task
        self.fact_to_id = dict()
        for i, f in enumerate(self.task.facts):
            self.fact_to_id[f] = 2*i
            self.fact_to_id[f + "PRIME"] = 2*i + 1
            # TODO switch the order above with the one below and
            # evaluate the effect in exercise 5.2(b)
#            self.fact_to_id[f] = i
#            self.fact_to_id[f + "PRIME"] = i + len(self.task.facts)
        self.id_to_fact = {i : f for f, i in self.fact_to_id.items()}
        self.transition_relation = self.create_transition_relation()

    def state_to_ids(self, state):
        # result = {self.fact_to_id[fact]: fact in state for fact in self.task.facts}
        result = dict()
        for fact in self.task.facts:
            result[self.fact_to_id[fact]] = fact in state
        return result

    def ids_to_state(self, ids):
        # result = {self.id_to_fact[v] for v, value in ids.items() if value}
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
            t_op = self.conjunction_to_set(op.preconditions)
            for a_fact in op.add_effects:
                a = self.get_atom_bdd(a_fact, primed=True)
                t_op = bdd_intersection(t_op, a)
            for d_fact in op.del_effects - op.add_effects:
                d = self.get_atom_bdd(d_fact, primed=True)
                not_d = bdd_complement(d)
                t_op = bdd_intersection(t_op, not_d)
            for v_fact in self.task.facts - op.del_effects - op.add_effects:
                v_before = self.get_atom_bdd(v_fact, primed=False)
                v_after = self.get_atom_bdd(v_fact, primed=True)
                v_unchanged = bdd_biimplication(v_before, v_after)
                t_op = bdd_intersection(t_op, v_unchanged)
            t = bdd_union(t, t_op)
            print_bdd_nodes()
        return t

    def apply_ops(self, reached):
        b = self.transition_relation
        b = bdd_intersection(b, reached)
        for fact in self.task.facts:
            b = bdd_forget(b, self.get_fact_id(fact, primed=False))
        for fact in self.task.facts:
            b = bdd_rename(b, self.get_fact_id(fact, primed=True), self.get_fact_id(fact, primed=False))
        return b

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
        for i in itertools.count():
            print("g layer", i)
            print_bdd_nodes()
            if not bdd_isempty(bdd_intersection(reached[i], goal)):
                return self.construct_plan(reached)
            ## NOTE: this also works if only appending the newly reached set
            ## of states, i.e., self.apply_ops(reached[i]), but the algorithm
            ## in the lecture assumes the "pizza" approach where reached is
            ## a *single* BDD representing the set of reached states. Here,
            ## we store a list of BDDs where the i-th BDD represents the set
            ## of states reached in up to i steps.
            reached.append(bdd_union(reached[i], self.apply_ops(reached[i])))
            if bdd_equals(reached[i], reached[i+1]):
                return None


def bdd_bfs_solve(task):
    search = BDDSearch(task)
    return search.run()

def print_bdd_nodes():
    print ("Amount of BDD Nodes {}".format(len(VAR)))

