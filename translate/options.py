# -*- coding: utf-8 -*-

import argparse
import sys


def parse_args():
    argparser = argparse.ArgumentParser()
    argparser.add_argument(
        "domain", nargs="?", help="path to domain pddl file")
    argparser.add_argument(
        "task", help="path to task pddl file")
    argparser.add_argument(
        "--relaxed", dest="generate_relaxed_task", action="store_true",
        help="output relaxed task (no delete effects)")
    argparser.add_argument(
        "--full-encoding",
        dest="use_partial_encoding", action="store_false",
        help="By default we represent facts that occur in multiple "
        "mutex groups only in one variable. Using this parameter adds "
        "these facts to multiple variables. This can make the meaning "
        "of the variables clearer, but increases the number of facts.")
    argparser.add_argument(
        "--invariant-generation-max-candidates", default=100000, type=int,
        help="max number of candidates for invariant generation "
        "(default: %(default)d). Set to 0 to disable invariant "
        "generation and obtain only binary variables. The limit is "
        "needed for grounded input files that would otherwise produce "
        "too many candidates.")
    argparser.add_argument(
        "--invariant-generation-max-time", default=300, type=int,
        help="max time for invariant generation (default: %(default)ds)")
    argparser.add_argument(
        "--add-implied-preconditions", action="store_true",
        help="infer additional preconditions. This setting can cause a "
        "severe performance penalty due to weaker relevance analysis "
        "(see issue7).")
    argparser.add_argument(
        "--keep-unreachable-facts",
        dest="filter_unreachable_facts", action="store_false",
        help="keep facts that can't be reached from the initial state")
    argparser.add_argument(
        "--dump-task", action="store_true",
        help="dump human-readable SAS+ representation of the task")
    argparser.add_argument(
        "--writeout_reformulated_pddl", action="store_true",
        help="Generate PDDL output file for debugging purposes")
    argparser.add_argument(
        "--writeout_reformulation_logic", action="store_true",
        help="Print reformulation logic to terminal")
    argparser.add_argument(
        "--solution", default = "", type = str, help = "Transformed solution file to translate back")
    argparser.add_argument(
        "--mappings", default = "", type = str, help = "Mappings file for actions and bags")
    argparser.add_argument(
        "--enable_pddl_repair", action="store_true", help = "Do you want to enable pddl repair?")
    argparser.add_argument(
        "--bag_conditional_effects", action="store_true", help = "Do you want to try and bag conditional effects?")
    argparser.add_argument(
        "--ground_operators", action="store_true", help = "Ground operators after reformulation to reduce sas variable number")
    argparser.add_argument(
        "--syntax_check", action="store_true",
        help="Turn on syntax check")
    argparser.add_argument(
        "--enforce_GTE", action="store_true", default=False,
        help="Enforce all baggable types to have a GTE system")
    argparser.add_argument(
        "--add_mutexes", action="store_true", default=False,
        help="Create files containing mutexes for all macropredicates")
    argparser.add_argument(
        "--dont_bag", default = "", type = str,
        help="Which types do you want to avoid bagging? Parse types as a string without spaces, separated with commas eg. --dont_bag hand,ball")
    argparser.add_argument(
        "--direction", default = "", type = str,
        help="Enter 'bck' for backwards bagging only or 'fwd' for forwards bagging only (defaults to both directions)")
    argparser.add_argument(
        "--from_to_count", default = "", type = str,
        help="Add file to tell Baggy which bags to use (experimental)")     
        
        
    return argparser.parse_args()


def copy_args_to_module(args):
    module_dict = sys.modules[__name__].__dict__
    for key, value in vars(args).items():
        module_dict[key] = value


def setup():
    args = parse_args()
    copy_args_to_module(args)


setup()
