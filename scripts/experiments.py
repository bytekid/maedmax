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
codename = sys.argv[5] if len(sys.argv) > 5 else "maedmax"
comment = sys.argv[6] if len(sys.argv) > 6 else ""
tool = "./maedmax"
jobs = []
stats = {}


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
  data = result_data(problem, "TIMEOUT")
  data['time'] = timeout
  return data

def success_data(problem, data):
  name = problem['file']
  name = name[0:name.index('.')]
  data['system'] = name
  data['config'] = problem['config']
  return data


def work(problem):
  f = str(srcdir) + "/" + problem["file"]
  config = problem['config']
  with tempfile.NamedTemporaryFile() as temp:
    cmd = "./sandbox {} {} {} {} > {}".format(timeout, tool, config, f, temp.name)
    #print cmd
    out,err = subprocess.Popen(cmd, shell=True).communicate()
    file = open(temp.name, "r") 
    res = file.read()
    code = "TIMEOUT" if "TIMEOUT" in res else "UNSAT" if "UNSAT" in res else "SAT" if "SAT" in res in res else "ERROR"
    print(str(problem["number"]) + ": " + problem["file"] + " " + code)
    if "TIMEOUT" in res:
      d = timeout_data(problem)
      cmd = tool + " -analyze " + f + " > " + temp.name
      os.system(cmd)
      file = open(temp.name, "r") 
      res = file.read()
      d["characteristics"] = json.loads(res)
      return d
    elif "SAT" in res:
      return success_data(problem, json.loads(res))
    else:
      return error_data(problem)

def accumulate(results, configs):
  global stats
  t=datetime.fromtimestamp(time.time())
  tstamp = t.strftime('%Y-%m-%d %H:%M')
  data = {"timestamp": tstamp, "configurations": configs, "comment": comment, "results": results}
  res = json.dumps(data, sort_keys=True, indent=2)
  rname = t.strftime('%Y-%m-%d') + codename + ".json"
  rfile = open("results/"+rname, "w")
  rfile.write(res)
  for r in results:
    conf = r['config']
    if r['result'] == "SAT":
      stats[conf]['SAT'] = stats[conf]['SAT'] + 1
    if r['result'] == "UNSAT":
      stats[conf]['UNSAT'] = stats[conf]['UNSAT'] + 1
    elif r['result'] == "TIMEOUT":
      stats[conf]['timeouts'] = stats[conf]['timeouts'] + 1
    else:
      stats[conf]['errors'] = stats[conf]['errors'] + 1




if __name__ == "__main__":

  # create job list
  i = 0
  configs = get_configs()
  for c in configs:
    stats[c] = { "SAT" : 0, "UNSAT" : 0, "timeouts" : 0, "errors": 0}
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
  accumulate(results.get(), configs)
  for c in configs:
    s = stats[c]
    print "{}: {} SAT, {} UNSAT, {} timeouts, {} errors".format(c, s['SAT'], s['UNSAT'], s['timeouts'], s['errors'])
