#!/usr/bin/env python3

#Copyright 2023 Ian Jauslin
#
#Licensed under the Apache License, Version 2.0 (the "License");
#you may not use this file except in compliance with the License.
#You may obtain a copy of the License at
#
#    http://www.apache.org/licenses/LICENSE-2.0
#
#Unless required by applicable law or agreed to in writing, software
#distributed under the License is distributed on an "AS IS" BASIS,
#WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#See the License for the specific language governing permissions and
#limitations under the License.

"""
This script removes the proofs from a lean3 file and replaces them by sorry's,
in a lean 4 format.

The resulting code is written to stdout

Usage:
    sorrify_3to4.py <input_file>
"""

import sys
import re

__author__ = "Ian Jauslin"
__copyright__ = "Copyright 2023"
__credits__ = ["Ian Jauslin"]
__license__ = "Apache 2.0"
__version__ = "1.0"
__maintainer__ = "Ian Jauslin"
__email__ = "ian.jauslin@rutgers.edu"
__status__ = "Development"

def print_usage(outfile):
    print("usage: sorrify_3to4.py <input_file>", file=outfile)

# input file
if len(sys.argv)!=2:
    print_usage(sys.stderr)
    exit(-1)

outfile=open(sys.argv[1],'r')
text=outfile.read()
outfile.close()


# replace one line proofs
text=re.sub(r'((lemma|theorem).*?:=\s*)', r'\1 by sorry\n -- ', text, flags=re.DOTALL)

# replace begin/end
text=re.sub(r'(^|\s)begin($|\s)', r'\n/-begin', text, flags=re.MULTILINE)
text=re.sub(r'(^|\s)end($|\s)', r'  end-/', text, flags=re.MULTILINE)

print(text)
