#! /bin/python3

import re

def remove_student_blocks(filename):
    f = open(filename, 'r')
    
    output = ""

    remove_mode = False
    unindent = 0

    for line in f:

        if not remove_mode:
            l = line.replace(' ', '')
            if (l == "..BEGINHIDE\n"):
                remove_mode = True
            elif (l == "..BEGINBLOCK\n"):
                unindent += 2
            elif (l == "..ENDBLOCK\n"):
                unindent += -2
            else:                
                if unindent == 0:
                    output += line
                else:
                    r = "^" + " " * unindent
                    output += re.compile(r).sub("", line)

        else:
            l = line.replace(' ', '')
            if l == "..ENDHIDE\n":
                remove_mode = False

    f.close()

    return output

def output_file(filename, contents):
    file = open(filename, 'w')
    file.write(contents)
    file.close()

def append_mode(filename, mode):
    import os.path

    basename = os.path.basename(filename)
    dirname = os.path.dirname(filename)
    if dirname == '':
        dirname = '.'
    name, ext = basename.split('.', 1)

    return "{dirname}/{name}.{mode}.{ext}".format(**locals())

if __name__ == "__main__":

    import sys

    filename = sys.argv[1]

    print("Studentizing '{}'".format(filename))
    contents = remove_student_blocks(filename)

    ofilename = append_mode(filename, "student")
    print("Output to '{}'".format(ofilename))
    output_file(ofilename, contents)

    print("Done ...")


