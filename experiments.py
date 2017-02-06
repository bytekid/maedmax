import os, subprocess, multiprocessing, sys
import tempfile
import json
from datetime import datetime
import time

# get settings from command line
if len(sys.argv) < 3:
  print("usage: test.py <directory> <timeout> <config file> <processes>? <codename>?")
problems = sys.argv[1]
srcdir = sys.argv[1]
timeout = sys.argv[2]
config_file = sys.argv[3]
numprocs = int(sys.argv[4]) if len(sys.argv) > 4 else 2
codename = sys.argv[5] if len(sys.argv) > 5 else "madmax"
tool = "./madmax"
jobs = []


def get_configs():
  configs = []
  for c in open(config_file, "r").readlines():
    configs.append(c.rstrip())
  return configs

def result_data(problem, result):
  name = problem['file']
  name = name[0:name.index('.')]
  data = {"config": problem['config'], "result": result, "system": name}
  return data

def error_data(problem):
  return result_data(problem, "ERROR")

def timeout_data(problem):
  return result_data(problem, "TIMEOUT")


def work(problem):
  f = str(srcdir) + "/" + problem["file"]
  config = problem['config']
  with tempfile.NamedTemporaryFile() as temp:
    cmd = "./sandbox {} {} {} {} > {}".format(timeout, tool, config, f, temp.name)
    #print cmd
    out,err = subprocess.Popen(cmd, shell=True).communicate()
    file = open(temp.name, "r") 
    res = file.read()
    code = "TIMEOUT" if "TIMEOUT" in res else "SUCCESS" if "YES" in res else "ERROR"
    print(str(problem["number"]) + ": " + problem["file"] + " " + code)
    if "TIMEOUT" in res:
      return timeout_data(problem)
    elif "YES" in res:
      return json.loads(res)
    else:
      return error_data(problem)

def accumulate(results, configs):
  t=datetime.fromtimestamp(time.time())
  tstamp = t.strftime('%Y-%m-%d %H:%M')
  data = {"timestamp": tstamp, "configurations": configs, "results": results}
  res = json.dumps(data, sort_keys=True, indent=2)
  rname = t.strftime('%Y-%m-%d') + codename + ".json"
  rfile = open("results/"+rname, "w")
  rfile.write(res)


if __name__ == "__main__":

  # create job list
  i = 0
  configs = get_configs()
  for subdir, dirs, problems in os.walk(problems):
    for p in problems:
      for c in configs:
        job = { "number" : i, "file" : p, "config": c}
        jobs.append(job)
        i = i + 1

  # run jobsfrom datetime import datetime
  print("There are {} CPUs on this machine".format(multiprocessing.cpu_count()))
  print("Doing {} jobs with {} processes".format(i,numprocs))
  pool = multiprocessing.Pool(numprocs)
  total_tasks = i
  results = pool.map_async(work, jobs)
  pool.close()
  pool.join()
  print accumulate(results.get(), configs)
