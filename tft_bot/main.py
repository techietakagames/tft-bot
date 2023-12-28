import itertools
import argparse

import z3

from tft_bot.set_data import Set10

"""
Tasks:
[] setup github
[x] refactor
[x] fix akali
[] headliners
[] multi-talent portal
[] discord bot
[] spatulas
[] input requirements for champs
[] input requirements for classes
[] input blacklist for champs
[] collin-mode
"""

tft = Set10()

# z3 vars
# True if a given champ is in the party
champ_bools = {}
# 1 if in party, else 0
champ_ints = {}
# number of champs that have a trait active
traitcount_champ_ints = {}
# True if a given champ is the headliner
headliner_champ_bools = {}
# 1 if headliner, else 0
headliner_champ_ints = {}
# True if a given trait is the headliner trait
headliner_trait_bools = {}
# 1 if headliner trait, else 0
headliner_trait_ints = {}
# True if a given trait is the multi-talent trait
multi_talent_trait_bools = {}
# 1 if multi-talent trait, else 0
multi_talent_trait_ints = {}

solver = z3.Solver()


def parse_options():
    parser = argparse.ArgumentParser()
    parser.add_argument("-n", "--num-champs", help="Number of champs on your board", default=3)
    parser.add_argument("-s", "--spatulas", help="Specify the number of spatulas", default=0)
    parser.add_argument("-m",
                        "--multi-talented",
                        help="Use flag if the double headliner trait portal is active",
                        default=False,
                        action="store_true")
    parser.add_argument( "--list-champs", help="List all possible champ names", default=0)
    parser.add_argument( "--list-traits", help="List all possible trait names", default=0)
    args = parser.parse_args()
    return args


def setup_z3_vars():
    for i in tft.champs:
        champ_bools[i] = z3.Bool(i)
        champ_ints[i] = z3.If(champ_bools[i], 1, 0)
    for champ in tft.champs:
        headliner_champ_bools[champ] = z3.Bool("headliner_" + champ)
        headliner_champ_ints[champ] = z3.If(headliner_champ_bools[champ], 1, 0)
    for trait in tft.get_non_unique_traits():
        headliner_trait_bools[trait] = z3.Bool("headliner_trait_" + trait)
        headliner_trait_ints[trait] = z3.If(headliner_trait_bools[trait], 1, 0)
        multi_talent_trait_bools[trait] = z3.Bool("multi_talent_trait_" + trait)
        multi_talent_trait_ints[trait] = z3.If(multi_talent_trait_bools[trait], 1, 0)

def setup_max_champs(max_champs):
    solver.add(z3.Sum(list(champ_ints.values())) <= max_champs)


def setup_trait_to_champs():
    for t, champs in tft.trait_champs.items():
        traitcount_champ_ints[t] = z3.Int("traitcount_" + t)
        solver.add(traitcount_champ_ints[t] == z3.Sum([champ_ints[i] for i in champs]))

# that's jazz baby (don't consider unique traits)
def max_traits():
    cutoff_constraints = []
    # TODO changes for headliner + spatulas
    for trait in tft.get_non_unique_traits():
        cutoff = tft.trait_cutoffs[trait][0]
        cutoff_constraints.append(z3.If(traitcount_champ_ints[trait] + headliner_trait_ints[trait] + multi_talent_trait_ints[trait] >= cutoff, 1, 0))

    # TODO change
    solver.add(z3.Sum(cutoff_constraints) == 4)


def setup_champ_restrictions():
    solver.add(z3.Not(z3.And([champ_bools["Akali-TD"], champ_bools["Akali-KDA"]])))

def setup_headliners():
    non_unique_traits = tft.get_non_unique_traits()
    # at most one trait can be the headliner
    solver.add(z3.Sum(list(headliner_trait_ints.values())) <= 1)

    # at most one champ can be the headliner
    solver.add(z3.Sum(list(headliner_champ_ints.values())) <= 1)

    # the headliner must be in the party
    for i in headliner_champ_bools.keys():
        solver.add(z3.Implies(headliner_champ_bools[i], champ_bools[i]))

    # if a champ is the headliner, one of their non-unique traits must be the headliner trait
    for champ, traits in tft.champ_traits.items():
        # there is always at least one
        or_traits = list(set(traits).intersection(non_unique_traits))
        c = z3.Or([headliner_trait_bools[t] for t in or_traits])
        solver.add(z3.Implies(headliner_champ_bools[champ], c))

    # if a trait is the headliner trait, some champ with that trait must be the headliner
    for trait, champs in tft.trait_champs.items():
        if trait not in non_unique_traits:
            continue
        big_or = z3.Or([headliner_champ_bools[c] for c in champs])
        solver.add(z3.Implies(headliner_trait_bools[trait], big_or))

# if multi-talent, an extra different trait from that champ is also turned on
def setup_multi_talented(multi_talented=False):
    non_unique_traits = tft.get_non_unique_traits()
    if multi_talented:
        # there's no multi-talent if only one non-unique trait on the headliner, else one
        solver.add(z3.Sum(list(multi_talent_trait_ints.values())) <= 1)

        # if a champ has multiple non-unique traits, there must be a multi-trait
        for champ, traits in tft.champ_traits.items():
            if len(set(non_unique_traits).intersection(traits)) > 1:
                solver.add(
                    z3.Implies(headliner_champ_bools[champ], z3.Sum(list(multi_talent_trait_ints.values())) == 1))

        # multi-talent on implies there exists some headliner on with that trait and a different trait is headliner
        for multi_trait in non_unique_traits:
            big_or = []
            for champ, traits in tft.champ_traits.items():
                if multi_trait not in traits:
                    continue
                champ_non_unique_traits = set(non_unique_traits).intersection(traits).difference([multi_trait])
                if not champ_non_unique_traits:
                    continue
                # champ on and some other trait is the headliner
                c = z3.And(headliner_champ_bools[champ],
                            z3.Or([headliner_trait_bools[i] for i in champ_non_unique_traits]))
                big_or.append(c)

            solver.add(z3.Implies(multi_talent_trait_bools[multi_trait], z3.Or(big_or)))

    else:
        for i in multi_talent_trait_bools.values():
            solver.add(z3.Not(i))

# The following missing constraints could theoretically break model if you specify low champ count + high spatulas:
# has to be on associated with a champ
# champ cannot have 2 of same
# champ cannot have more than 3
# champ cannot have same trait
def setup_spatulas():
    # has to be one of the possible spatula types
    pass

def display_results(args):
    non_unique_traits = tft.get_non_unique_traits()
    is_sat = solver.check()
    if is_sat != z3.sat:
        print("No solution")
        return
    model = solver.model()
    headliner_trait_str = ""
    multi_talent_trait_str = ""
    for trait, b in headliner_trait_bools.items():
        if model.eval(b):
            headliner_trait_str = trait

    if args.multi_talented:
        for trait, b in multi_talent_trait_bools.items():
            if model.eval(b):
                multi_talent_trait_str = ", " + trait

    for champ, b in champ_bools.items():
        headliner_str = ""
        if model.eval(headliner_champ_bools[champ]):
            headliner_str = "(" + headliner_trait_str + multi_talent_trait_str + ")"
        if model.eval(b):
            print(champ + " " + headliner_str)

    print("---------")

    for trait, champs in tft.trait_champs.items():
        count = 0
        for champ in champs:
            if model.eval(champ_bools[champ]):
                count += 1
        if trait in non_unique_traits and model.eval(headliner_trait_bools[trait]):
            count += 1

        achieved_cutoffs = [i for i in tft.trait_cutoffs[trait] if count >= i]
        if achieved_cutoffs:
            print(trait, achieved_cutoffs[-1])


def main(args):
    setup_z3_vars()
    setup_max_champs(args.num_champs)
    setup_trait_to_champs()
    setup_champ_restrictions()
    setup_headliners()
    setup_multi_talented(args.multi_talented)
    setup_spatulas()
    max_traits()
    display_results(args)


if __name__ == '__main__':
    main(parse_options())
