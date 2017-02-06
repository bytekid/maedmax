import os
import subprocess


rootdir = "./unit"
termdir = os.path.join(rootdir, "term")
kbdir = os.path.join(rootdir, "kb")
okbdir = os.path.join(rootdir, "okb")
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

def check_okb(filename):
  name = filename[0:filename.find(".")]
  nameparts = name.split('_')
  strategy = nameparts[1]
  fail = nameparts[2] == "fail" if len(nameparts) > 2 else False
  args = [ckb, "-o", "-M", strategy, os.path.join(okbdir, filename)]
  return check_yes(args, fail)

def check(name, dir, check_fun):
    print(name + " TESTS")
    for subdir, dirs, files in os.walk(dir):
        for file in files:
            if check_fun(file):
                print("  " + file + " succeeds")
            else:
                print("  " + file + " fails")

check("TERMINATION", termdir, check_term)
check("KB", kbdir, check_kb)
check("OKB", okbdir, check_okb)