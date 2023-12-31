try:
    # Python 3.x
    import builtins
except ImportError:
    # Python 2.x
    import __builtin__ as builtins

import os.path
import re

import options

from . import lisp_parser
from . import parsing_functions


def parse_pddl_file(type, filename):
    try:
        # The builtin open function is shadowed by this module's open function.
        return lisp_parser.parse_nested_list(builtins.open(filename))
    except IOError as e:
        raise SystemExit("Error: Could not read file: %s\nReason: %s." %
                         (e.filename, e))
    except lisp_parser.ParseError as e:
        raise SystemExit("Error: Could not parse %s file: %s\n" % (type, filename))

def get_filenames(task_filename=None, domain_filename=None):
    task_filename = task_filename or options.task
    domain_filename = domain_filename or options.domain

    if not domain_filename:
        dirname, basename = os.path.split(task_filename)
        domain_filename = os.path.join(dirname, "domain.pddl")
        if not os.path.exists(domain_filename) and re.match(r"p[0-9][0-9]\b", basename):
            domain_filename = os.path.join(dirname, basename[:4] + "domain.pddl")
        if not os.path.exists(domain_filename) and re.match(r"p[0-9][0-9]\b", basename):
            domain_filename = os.path.join(dirname, basename[:3] + "-domain.pddl")
        if not os.path.exists(domain_filename) and re.match(r"p[0-9][0-9]\b", basename):
            domain_filename = os.path.join(dirname, "domain_" + basename)
        if not os.path.exists(domain_filename) and basename.endswith("-problem.pddl"):
            domain_filename = os.path.join(dirname, basename[:-13] + "-domain.pddl")
        if not os.path.exists(domain_filename):
            raise SystemExit("Error: Could not find domain file using "
                             "automatic naming rules.")
    return task_filename, domain_filename

def parse(task_filename=None, domain_filename=None):
    task_filename, domain_filename = get_filenames(task_filename, domain_filename)
    domain_pddl = parse_pddl_file("domain", domain_filename)
    task_pddl = parse_pddl_file("task", task_filename)
    return parsing_functions.parse_task(domain_pddl, task_pddl)

def writeout_reformulated_pddl(task, original = False):
    task_filename, domain_filename = get_filenames()
    task_filename = ('original-' if original else 'reformulated-') + os.path.basename(task_filename)
    domain_filename = ('original-' if original else 'reformulated-') + os.path.basename(domain_filename)
    try:
        # The builtin open function is shadowed by this module's open function.
        builtins.open(task_filename, mode='w').write(task.unparse_task())
    except IOError as e:
        raise SystemExit("Error: Could not write to file: %s\nReason: %s." %
                         (e.filename, e))

    try:
        # The builtin open function is shadowed by this module's open function.
        builtins.open(domain_filename, mode='w').write(task.unparse_domain())
    except IOError as e:
        raise SystemExit("Error: Could not write to file: %s\nReason: %s." %
                         (e.filename, e))
    return task_filename, domain_filename
