import os
import subprocess


rootdir = "./unit"
termdir = os.path.join(rootdir, "term")
kbdir = os.path.join(rootdir, "kb")
ckb = "./main.native"

def check_yes(args, fail): 
  p = subprocess.Popen(args, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
  out, err = p.communicate()
  return not fail == ("YES" in out)

def check_term(filename):
  name = filename[0:filename.find(".")]
  nameparts = name.split('_')
  strategy = nameparts[1]
  fail = nameparts[2] == "fail" if len(nameparts) > 2 else False 
  args = [ckb, "-term", "-M", strategy, os.path.join(termdir, filename)]
  return check_yes(args, fail)

def check_kb(filename):
  name = filename[0:filename.find(".")]
  nameparts = name.split('_')
  strategy = nameparts[1]
  fail = nameparts[2] == "fail" if len(nameparts) > 2 else False 
  args = [ckb, "-M", strategy, os.path.join(kbdir, filename)]
  return check_yes(args, fail)

print("TERMINATION TESTS")
for subdir, dirs, files in os.walk(termdir):
    for file in files:
        if check_term(file):
            print("  " + file + " succeeds")
        else:
            print("  " + file + " fails")

print("KB TESTS")
for subdir, dirs, files in os.walk(kbdir):
    for file in files:
        if check_kb(file):
            print("  " + file + " succeeds")
        else:
            print("  " + file + " fails")