import itertools
import argparse
import sys
import time

import z3

from tft_bot.set_data import Set10

"""
Tasks:
[x] setup github
[x] refactor
[x] fix akali
[x] headliners
[x] multi-talent portal
[x] mode argument
[x] change max-traits to find max without int parameter
[x] spatulas
[x] input requirements for champs
[x] input requirements for classes
[] input blacklist for champs
[x] output help lists
[x] add basic tests
[x] specify my headliner
[] specify my headliner trait
[x] return result as a string rather than printing
[x] discord bot
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
# number of spatulas allocated to each trait
spatula_trait_ints = {}

solver = z3.Solver()

example_usage = """
examples:
  **NOTE: All messages must start by tagging @TFTBot.**

  That's Jazz, Baby - output a comp with Jazz 4 enabled, at most 5 champions on my board, with the max possible non-unique traits turned on:
  `--num-champs 5 -t Jazz 4 -m max-non-unique-traits`
  
  
  ... and I also have 2 spatulas to use:
  `--num-champs 6 -t Jazz 4 -m max-non-unique-traits -s 2`
  
  
  ... and it's a multi-talent game (double headliner trait):
  `--num-champs 6 -t Jazz 4 -m max-non-unique-traits -s 2 --multi-talented`
  
  
  ... and I want Jhin and Qiyana on my team:
  `--num-champs 6 -t Jazz 4 -m max-non-unique-traits -s 2 --multi-talented -c Jhin Qiyana`
  
  
  ... and I don't want Miss Fortune or Vex on my team:
  `--num-champs 6 -t Jazz 4 -m max-non-unique-traits -s 2 --multi-talented -c Jhin Qiyana -b MissFortune Vex`
  
  I don't know the names of all champs or traits:
  `--list-champs --list-traits`
"""

def parse_options():
    parser = argparse.ArgumentParser(prog="@TFTBot", epilog="Use `@TFTBot --examples` for some ideas.")
    parser.add_argument("--mode", "-m", choices=["max-traits", "max-non-unique-traits"], default="max-traits")
    parser.add_argument("-n", "--num-champs", help="Number of champs in your comp", default=3, type=int, choices=range(0, 16), metavar="[0-16]")
    parser.add_argument("-s", "--spatulas", help="Specify the number of spatulas", default=0, type=int, choices=range(0, 6), metavar="[0-5]")
    parser.add_argument("-l", "--headliner", help="Specify the champ that must be my headliner", choices=tft.champs, metavar="CHAMP")
    parser.add_argument("-p",
                        "--multi-talented",
                        help="Use flag if the double headliner trait portal is active",
                        default=False,
                        action="store_true")
    parser.add_argument('-c', "--champs", nargs='*', help="Champs that must be in your comp", choices=tft.champs, metavar="CHAMP NAMES")
    parser.add_argument('-t', "--traits", nargs='*',
                        help="Traits that must be in your comp (example usage: -t Jazz 4 Emo 2)")
    parser.add_argument('-b', "--blacklist-champs", nargs='*', help="Champs that must not be in your comp", choices=tft.champs, metavar="TRAIT NAMES")

    parser.add_argument( "--list-champs", help="List all possible champ names", default=False, action="store_true")
    parser.add_argument( "--list-traits", help="List all possible trait names", default=False, action="store_true")
    parser.add_argument("--examples", help="List some example usages", default=False, action="store_true")
    return parser


def process_list_args(list_champs, list_traits):
    result = ""
    if list_champs:
        result += "Champs: " + ", ".join(tft.champs) + "\n"
    if list_traits:
        result += "Traits: " + ", ".join(tft.traits) + "\n"
    return result

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
    for trait in tft.spatula_traits:
        spatula_trait_ints[trait] = z3.Int("spatula_trait_" + trait)
def setup_max_champs(max_champs):
    solver.add(z3.Sum(list(champ_ints.values())) <= max_champs)


def setup_trait_to_champs():
    for t, champs in tft.trait_champs.items():
        traitcount_champ_ints[t] = z3.Int("traitcount_" + t)
        solver.add(traitcount_champ_ints[t] == z3.Sum([champ_ints[i] for i in champs]))

# that's jazz baby (don't consider unique traits)
def max_traits(args):
    cutoff_constraints = []
    non_unique_traits = tft.get_non_unique_traits()
    if args.mode == "max-traits":
        traits = tft.traits
    else:
        traits = non_unique_traits

    for trait in traits:
        cutoff = tft.trait_cutoffs[trait][0]
        c = traitcount_champ_ints[trait]
        if trait in non_unique_traits:
            c = c + headliner_trait_ints[trait] + multi_talent_trait_ints[trait]
        if trait in tft.spatula_traits:
            c = c + spatula_trait_ints[trait]
        cutoff_constraints.append(z3.If(c >= cutoff, 1, 0))

    num_traits = 1
    model = None
    is_sat = z3.sat
    prev_is_sat = z3.sat
    while is_sat == z3.sat:
        solver.push()
        solver.add(z3.Sum(cutoff_constraints) >= num_traits)
        is_sat = solver.check()
        if is_sat == z3.sat:
            prev_is_sat = z3.sat
            model = solver.model()
            num_traits += 1
        solver.pop()
    return prev_is_sat, model



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
def setup_spatulas(spatulas):
    # sum of all spatula traits is upper bounded
    for trait in tft.spatula_traits:
        solver.add(spatula_trait_ints[trait] >= 0)
    solver.add(z3.Sum(list(spatula_trait_ints.values())) <= spatulas)

# TODO change for spatulas
def display_results(args, is_sat, model):
    non_unique_traits = tft.get_non_unique_traits()
    result = ""
    if is_sat != z3.sat:
        result = "Impossible"
        return result

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
            result += champ + " " + headliner_str + "\n"

    if args.spatulas:
        result += "---------\n"
        has_spatula = False
        for trait in spatula_trait_ints.keys():
            count = model.eval(spatula_trait_ints[trait])
            if int(str(count)) > 0:
                result += trait + " Spatulas " + str(count) + "\n"
                has_spatula = True
        if not has_spatula:
            result += "No spatulas used\n"


    result += "---------\n"
    for trait, champs in tft.trait_champs.items():
        count = 0
        for champ in champs:
            if model.eval(champ_bools[champ]):
                count += 1
        if trait in non_unique_traits and model.eval(headliner_trait_bools[trait]):
            count += 1
        if trait in non_unique_traits and model.eval(multi_talent_trait_bools[trait]):
            count += 1
        if trait in tft.spatula_traits:
            count += int(str(model.eval(spatula_trait_ints[trait])))

        achieved_cutoffs = [i for i in tft.trait_cutoffs[trait] if count >= i]
        if achieved_cutoffs:
            result += trait + " " + str(achieved_cutoffs[-1]) + "\n"
    return result


def run_mode(args):
    if args.mode in ["max-traits", "max-non-unique-traits"]:
        return max_traits(args)


def setup_champ_requirements(champs):
    if not champs:
        return
    solver.add(z3.And([champ_bools[c] for c in champs]))

def setup_champ_blacklist(champs):
    if not champs:
        return
    solver.add(z3.And([z3.Not(champ_bools[c]) for c in champs]))


def setup_trait_requirements(traits):
    if not traits:
        return
    trait_cutoff_pairs = []
    for i in range(len(traits) // 2):
        trait_cutoff_pairs.append((traits[i*2], traits[i*2 + 1]))
    non_unique_traits = tft.get_non_unique_traits()
    for trait, cutoff in trait_cutoff_pairs:
        c = traitcount_champ_ints[trait]
        if trait in non_unique_traits:
            c = c + headliner_trait_ints[trait] + multi_talent_trait_ints[trait]
        if trait in tft.spatula_traits:
            c = c + spatula_trait_ints[trait]
        solver.add(c >= cutoff)

def setup_specified_headliner(specified_headlienr):
    if specified_headlienr:
        solver.add(headliner_champ_bools[specified_headlienr])

def main(args):
    print("MAIN", args)
    time.sleep(1)
    parser = parse_options()
    print("MAIN3")
    print("MAIN4", args)
    args = parser.parse_args(args)
    print("MAIN2")
    result = process_list_args(args.list_champs, args.list_traits)
    if result:
        return result
    if args.examples:
        return example_usage
    setup_z3_vars()
    setup_max_champs(args.num_champs)
    setup_trait_to_champs()
    setup_champ_restrictions()
    setup_headliners()
    setup_specified_headliner(args.headliner)
    setup_multi_talented(args.multi_talented)
    print("MAIN2")
    setup_spatulas(args.spatulas)
    setup_champ_requirements(args.champs)
    setup_trait_requirements(args.traits)
    setup_champ_blacklist(args.blacklist_champs)
    print("END2")
    is_sat, model = run_mode(args)
    result = display_results(args, is_sat, model)
    print("END")
    return result

if __name__ == '__main__':
    result = main(sys.argv[1:])
    print(result)