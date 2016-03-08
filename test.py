#!/usr/bin/python

from glob import glob
from subprocess import check_output, CalledProcessError
from difflib import unified_diff
import sys

GREEN = '\033[92m'
RED = '\033[91m'
YELLOW = '\033[93m'
END = '\033[0m'
    

grades = [
  ("01-expr", 20),
  ("02-assignment", 15),
  ("03-if", 7),
  ("04-switch", 8),
  ("05-while", 5),
  ("06-for", 5),
  ("07-prepost", 5),
  ("08-functions", 10),
  ("09-pointers", 7),
  ("10-arrays", 8),
  # extra credit
  ("11-recursion", 18),
  ("12-brcont", 10),
  ("13-nested", 7),
  # extra-extra credit, requires features above
  ("14-global", 10)
]

sum = 0

VERBOSE = len(sys.argv) == 2 and sys.argv[1] == "-v"

for dir, val in grades:
  files = glob("tests/" + dir + "/*.cf")
  if len(files) == 0:
    print YELLOW + ("Skipping %s, no tests" % dir) + END
    continue
  tval = float(val)/len(files)
  for file in files:
    try:
      out = check_output("./main " + file + " 2>&1", shell=True)
    except CalledProcessError as e:
      out = "Interpreter error: \n" + e.output
    test_fout = file.replace(".cf", ".out")
    test_out = open(test_fout).read()
    if test_out == out:
      print GREEN + ("Test %s passed (worth %s)" % (file, tval)) + END
      sum += tval
    else:
      diff = unified_diff(out.splitlines(), test_out.splitlines(), "your input", test_fout)
      print RED + ("Test %s failed (worth %s)" % (file, tval)) + END
      if VERBOSE:
        print "Differences:"
        for d in diff:
          print d
        # print repr(out)
        # print repr(test_out)

print "Final grade: %s" % sum
