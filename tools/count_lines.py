# Determines the number of code lines (i.e. excluding empty and comment, presentation lines)
# of the theory files.

import re
import sys
import glob

def readfile(name):
    f = open(name, mode='r',)
    r = f.read()
    f.close()
    return r

t = 0
for file in glob.glob(sys.argv[1]+"**/*.thy", recursive=True):
    a = readfile(file)
    a = re.sub(r'section\s*\\<open>(.|\n)*?\\<close>','',a)
    a = re.sub(r'text\s*\\<open>(.|\n)*?\\<close>','',a)
    a = re.sub(r'\(\*(.|\n)*?\*\)','',a)
    a = re.sub(r'\n\s*\n','\n',a)
    c = a.count('\n')
    t += c
    print('{} {}'.format(file, c))

print('Total: {}'.format(t))