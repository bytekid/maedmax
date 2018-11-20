import os, sys
import json
import re
import numpy as np
from sklearn.neural_network import MLPClassifier
from sklearn.svm import SVC, LinearSVC
from sklearn.tree import DecisionTreeClassifier, export_graphviz
from sklearn.ensemble import RandomForestClassifier, AdaBoostClassifier
from sklearn.naive_bayes import GaussianNB
from sklearn.discriminant_analysis import QuadraticDiscriminantAnalysis, LinearDiscriminantAnalysis
from sklearn.model_selection import cross_val_score
from sklearn.model_selection import train_test_split
from sklearn.neighbors import KNeighborsClassifier
from sklearn.decomposition import PCA
import matplotlib
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from treeinterpreter import treeinterpreter as ti
from sklearn.gaussian_process import GaussianProcessClassifier
from sklearn.gaussian_process.kernels import RBF
from sklearn.metrics import roc_curve, precision_recall_curve, auc, make_scorer, recall_score, accuracy_score, precision_score, confusion_matrix
from sklearn.ensemble import ExtraTreesClassifier

from sklearn import tree,metrics
from sklearn.tree import _tree
from os import system
import pandas as pd

from random import randint


########################## getting X ########################################

labels = [
  "is_goal",
  "node_size", "node_size_diff",
  "is_linear",
  "age",
  "orientable_lr", "orientable_rl",
  "duplicating_lr", "duplicating_rl",
  "matches", "cps",
  "state_equations", "state_goals", "state_iterations"
]

def get_X_file(filename):
  file = open(filename, "r")
  X = []
  target = []
  cnt = 0
  #print(filename)
  for line in file.readlines():
    if "goal proofs" in line:
      line = line[0:line.find("goal")]
    if line.startswith("-") or ("Timeout" in line) or ("TIMEOUT" in line) or line.strip() == "":
      continue
    cnt = cnt + 1
    parts = line.strip().split(" ")
    if len(parts) != 15:
      continue # timeout/printing?
    features = []
    for p in parts[0:-1]:
      features.append(float(p.strip()))
    X.append(features)

    # the target (0-=not used or 1=used)
    t = float(parts[-1].strip())
    target.append(t)
  #print(filename + ": " + str(cnt - 1) + " - " + str(len(target)))
  return [X, target]

def get_X_dir(dir):
  X = []
  target = []
  cnt = 0
  fs = []
  for subdir, dirs, logs in os.walk(dir):
    for filename in logs:
      f = os.path.join(subdir,filename)
      d,t = get_X_file(f)
      X = X + d
      target = target + t
      if len(t) > 0:
        fs.append(subdir[subdir.rfind("/"):])
        cnt = cnt + 1
  fs.sort()
  for f in fs:
    print(f)
  return X, target, cnt

def randBalanceData(X,y):
  X0 = [ xi for (xi,yi) in zip(X, y) if yi == 0 ]
  X1 = [ xi for (xi,yi) in zip(X, y) if yi == 1 ]
  X0sel = []
  n = len(X1)
  for i in range(0,n):
    i = randint(0,len(X0)-1)
    X0sel.append(X0[i])
    del X0[i]
  y = [0 for i in range(0,n)] + [1 for i in range(0,n)]
  X = X0sel + X1
  return (X,y)


########################## analysis ############################################

# classification

def pca(data, target):
  print("PCA")
  np.random.seed(5)
  centers = [[1, 1], [-1, -1], [1, -1]]

  pca = PCA(n_components=2)
  pca.fit(data)
  print("  explained variance ratios: ", pca.explained_variance_ratio_)
  print("  components: ", pca.components_)

  X = pca.transform(data)
  y = target


  size = 5000
  #ax.contourf(xx, yy, cmap=cm, alpha=.8)

  f0 = [x[0] for (x,v) in zip(X,y)[0:size] if v == 0]
  f1 = [x[1] for (x,v) in zip(X,y)[0:size] if v == 0]
  plt.scatter(f0, f1, c="red")
  f0 = [x[0] for (x,v) in zip(X,y)[0:size] if v == 1]
  f1 = [x[1] for (x,v) in zip(X,y)[0:size] if v == 1]
  plt.scatter(f0, f1, c="blue")
  plt.show()

def classify(name, clf, X, y):
  print(name)
  #scores = cross_val_score(clf, X, y, cv=10)
  #print("  crossval: order %0.2f (+/- %0.2f)" % (scores.mean(), scores.std() * 2))

  X_train, X_test, y_train, y_test = train_test_split(X,y, test_size=0.3, random_state=42)
  clf = clf.fit(X_train, y_train)
  y_pred = clf.predict(X_test)
  tp = len([ (y,z) for (y,z) in zip(y_test, y_pred) if y == 1 and z == 1 ])
  fp = len([ (y,z) for (y,z) in zip(y_test, y_pred) if y == 0 and z == 1 ])
  fn = len([ (y,z) for (y,z) in zip(y_test, y_pred) if y == 1 and z == 0 ])
  tn = len([ (y,z) for (y,z) in zip(y_test, y_pred) if y == 0 and z == 0 ])
  print("  true positives: %d, false positives: %d, true negatives: %d, false negatives: %d (from %d)" % (tp, fp, tn, fn, len(y_test)))
  prec = float(tp) / (tp + fp) if tp + fp != 0 else -1
  recall = float(tp) / (tp + fn) if tp + fn != 0 else -1
  my_f1 = 2 * prec * recall / (prec + recall) if prec + recall != 0 else -1
  print("  precision: %0.2f, recall: %0.2f, f1: %0.2f" % (prec, recall, my_f1))

  if "SVM" in name:
    print("coefficients and intercept:")
    print(clf.coef_)
    print(clf.intercept_)
    for x, (yt, yp) in zip(X_test, zip(y_test, y_pred)):
      z = sum([a*b for a,b in zip(x,clf.coef_[0])]) + clf.intercept_[0]
      assert(yp == (1 if z > 0 else 0))
      #print("real: %d, predicted:%d, computed: %.3f" % (yt, yp, z))


def pcaClassify(name, clf, X, y, dim):
  print(name)

  pca = PCA(n_components=dim)
  pca.fit(X)
  print("  PCA-explained variance ratios: ", pca.explained_variance_ratio_)
  X = pca.fit_transform(X)
  print("transformed")
  classify(name, clf, X, y)

def bayes(X, y):
  print("Naive Bayes (2)")

  X_train, X_test, y_train, y_test = train_test_split(X,y, test_size=0.3, random_state=42)
  clf = GaussianNB(var_smoothing=1e-12).fit(X_train, y_train)
  y_pred = clf.predict(X_test)
  tp = len([ (y,z) for (y,z) in zip(y_test, y_pred) if y == 1 and z == 1 ])
  fp = len([ (y,z) for (y,z) in zip(y_test, y_pred) if y == 0 and z == 1 ])
  fn = len([ (y,z) for (y,z) in zip(y_test, y_pred) if y == 1 and z == 0 ])
  tn = len([ (y,z) for (y,z) in zip(y_test, y_pred) if y == 0 and z == 0 ])
  print("  true positives: %d, false positives: %d, true negatives: %d, false negatives: %d (from %d)" % (tp, fp, tn, fn, len(y_test)))
  prec = float(tp) / (tp + fp) if tp + fp != 0 else -1
  recall = float(tp) / (tp + fn) if tp + fn != 0 else -1
  my_f1 = 2 * prec * recall / (prec + recall) if prec + recall != 0 else -1
  print("  precision: %0.2f, recall: %0.2f, f1: %0.2f" % (prec, recall, my_f1))
  print(clf.theta_)
  print(clf.sigma_)
  print(clf.epsilon_)

  t = 0.15
  y_scores = clf.predict_proba(X_test)[:, 1]
  p, r, thresholds = precision_recall_curve(y_test, y_scores)
  print(thresholds)
  y_pred_adj = [1 if y >= t else 0 for y in y_scores]
  print(pd.DataFrame(confusion_matrix(y_test, y_pred_adj),
                       columns=['pred_neg', 'pred_pos'], index=['neg', 'pos']))
  plt.figure(figsize=(8,8))
  plt.title("Precision and Recall curve ^ = current threshold")
  plt.step(r, p, color='b', alpha=0.2, where='post')
  plt.fill_between(r, p, step='post', alpha=0.2, color='b')
  plt.ylim([-.1, 1.2]);
  plt.xlim([-.1, 1.2]);
  plt.xlabel('Recall');
  plt.ylabel('Precision');

  close_default_clf = np.argmin(np.abs(thresholds - t))
  plt.plot(r[close_default_clf], p[close_default_clf], '^', c='k', markersize=15)
  plt.show()


def showTree(tree):
  ocaml_features = [ "n.is_goal", "n.size", "n.size_diff", "n.linear", "n.age",
    "fst n.orientable", "snd n.orientable", "fst n.duplicating",
    "snd n.duplicating", "n.matchings", "n.cps",
    "s.equations", "s.goals", "s.iterations"
  ]
  print("let tree %s =" % (" ".join(ocaml_features)))

  def recurse(node, depth):
    indent = "  " * depth
    if tree.feature[node] != _tree.TREE_UNDEFINED:
      name = ocaml_features[tree.feature[node]]
      threshold = tree.threshold[node]
      print("%sif %s <= %d then" % (indent, name, int(threshold)))
      recurse(tree.children_left[node], depth + 1)
      print("%selse (* if %s > %d *)" % (indent, name, int(threshold)))
      recurse(tree.children_right[node], depth + 1)
    else:
      v_max = 0
      i_max = 0
      for i, cnt in enumerate(tree.value[node][0]):
        (v_max, i_max) = (cnt, i) if cnt > v_max else (v_max, i_max)
      answer = "true" if i_max == 1 else "false"
      print("{}{} (*{}*)".format(indent, answer, tree.value[node]))
      #print("%s%d %d" % (indent, int(tree.value[node][0][0]), int(tree.value[node][0][1])))

  recurse(0, 1)

def tree2json(tree):
  def json_of_node(node):
    if tree.feature[node] != _tree.TREE_UNDEFINED:
      name = labels[tree.feature[node]]
      threshold = tree.threshold[node]
      leq = json_of_node(tree.children_left[node])
      gt = json_of_node(tree.children_right[node])
      return {"attr" : name, "thresh" : threshold, "leq" : leq, "gt" : gt}
    else:
      v_max = 0
      i_max = 0
      # count which class has more members
      for i, cnt in enumerate(tree.value[node][0]):
        (v_max, i_max) = (cnt, i) if cnt > v_max else (v_max, i_max)
      return i_max

  return json_of_node(0)  


def precision_recall_graph(r, p, thresholds, t):
  plt.figure(figsize=(8,8))
  plt.title("Precision and Recall curve ^ = current threshold")
  plt.step(r, p, color='b', alpha=0.2, where='post')
  plt.fill_between(r, p, step='post', alpha=0.2, color='b')
  plt.ylim([-.1, 1.2]);
  plt.xlim([-.1, 1.2]);
  plt.xlabel('Recall');
  plt.ylabel('Precision');

  close_default_clf = np.argmin(np.abs(thresholds - t))
  plt.plot(r[close_default_clf], p[close_default_clf], '^', c='k', markersize=15)
  plt.show()

def dtrees(X, y):
  print("decision trees (depth 3)")

  X_train, X_test, y_train, y_test = train_test_split(X,y, test_size=0.3, random_state=42)
  clf = DecisionTreeClassifier(max_depth=5).fit(X_train, y_train)
  y_pred = clf.predict(X_test)
  tp = len([ (y,z) for (y,z) in zip(y_test, y_pred) if y == 1 and z == 1 ])
  fp = len([ (y,z) for (y,z) in zip(y_test, y_pred) if y == 0 and z == 1 ])
  fn = len([ (y,z) for (y,z) in zip(y_test, y_pred) if y == 1 and z == 0 ])
  tn = len([ (y,z) for (y,z) in zip(y_test, y_pred) if y == 0 and z == 0 ])
  print("  true positives: %d, false positives: %d, true negatives: %d, false negatives: %d (from %d)" % (tp, fp, tn, fn, len(y_test)))
  prec = float(tp) / (tp + fp) if tp + fp != 0 else -1
  recall = float(tp) / (tp + fn) if tp + fn != 0 else -1
  my_f1 = 2 * prec * recall / (prec + recall) if prec + recall != 0 else -1
  print("  precision: %0.2f, recall: %0.2f, f1: %0.2f" % (prec, recall, my_f1))

  t = 0.15
  y_scores = clf.predict_proba(X_test)[:, 1]
  p, r, thresholds = precision_recall_curve(y_test, y_scores)
  y_pred_adj = [1 if y >= t else 0 for y in y_scores]
  print(pd.DataFrame(confusion_matrix(y_test, y_pred_adj),
                      columns=['pred_neg', 'pred_pos'], index=['neg', 'pos']))
  #precision_recall_graph(r, p, thresholds, t)
  #showTree(clf.tree_)
  print(json.dumps([tree2json(clf.tree_)]))

def xtrees(X, y):
  estimators = 10
  print("extra trees (%d est)" % (estimators))

  X_train, X_test, y_train, y_test = train_test_split(X,y, test_size=0.3, random_state=42)
  clf = ExtraTreesClassifier(n_estimators=estimators, random_state=0, max_depth=8).fit(X_train, y_train)
  y_pred = clf.predict(X_test)
  tp = len([ (y,z) for (y,z) in zip(y_test, y_pred) if y == 1 and z == 1 ])
  fp = len([ (y,z) for (y,z) in zip(y_test, y_pred) if y == 0 and z == 1 ])
  fn = len([ (y,z) for (y,z) in zip(y_test, y_pred) if y == 1 and z == 0 ])
  tn = len([ (y,z) for (y,z) in zip(y_test, y_pred) if y == 0 and z == 0 ])
  print("  true positives: %d, false positives: %d, true negatives: %d, false negatives: %d (from %d)" % (tp, fp, tn, fn, len(y_test)))
  prec = float(tp) / (tp + fp) if tp + fp != 0 else -1
  recall = float(tp) / (tp + fn) if tp + fn != 0 else -1
  my_f1 = 2 * prec * recall / (prec + recall) if prec + recall != 0 else -1
  print("  precision: %0.2f, recall: %0.2f, f1: %0.2f" % (prec, recall, my_f1))

  #print("Feature importance:")
  #print(zip(labels,clf.feature_importances_))

  trees = []
  for i in range(0, estimators):
    t = clf.estimators_[i].tree_
    trees.append(tree2json(t))
  #print(json.dumps(trees))

def random_forest(X, y):
  estimators = 10
  print("random forest (%d est)" % (estimators))

  X_train, X_test, y_train, y_test = train_test_split(X,y, test_size=0.3, random_state=42)
  clf = RandomForestClassifier(n_estimators=estimators, max_features=1, max_depth=8).fit(X_train, y_train)
  y_pred = clf.predict(X_test)
  tp = len([ (y,z) for (y,z) in zip(y_test, y_pred) if y == 1 and z == 1 ])
  fp = len([ (y,z) for (y,z) in zip(y_test, y_pred) if y == 0 and z == 1 ])
  fn = len([ (y,z) for (y,z) in zip(y_test, y_pred) if y == 1 and z == 0 ])
  tn = len([ (y,z) for (y,z) in zip(y_test, y_pred) if y == 0 and z == 0 ])
  print("  true positives: %d, false positives: %d, true negatives: %d, false negatives: %d (from %d)" % (tp, fp, tn, fn, len(y_test)))
  prec = float(tp) / (tp + fp) if tp + fp != 0 else -1
  recall = float(tp) / (tp + fn) if tp + fn != 0 else -1
  my_f1 = 2 * prec * recall / (prec + recall) if prec + recall != 0 else -1
  print("  precision: %0.2f, recall: %0.2f, f1: %0.2f" % (prec, recall, my_f1))

  trees = []
  for i in range(0, estimators):
    t = clf.estimators_[i].tree_
    trees.append(tree2json(t))
  print(json.dumps(trees))


def graphs(X,y):
  #usefulness vs size
  pos = [x for (x,c) in zip(X,y) if c == 1 and x[0] == 0]
  neg = [x for (x,c) in zip(X,y) if c == 0 and x[0] == 0]
  avg_pos = float(sum([x[1] for x in pos])) / len(pos)
  avg_neg = float(sum([x[1] for x in neg])) / len(neg)
  print("average positive size: %.2f, negative size: %.2f" % (avg_pos, avg_neg))
  max_pos = max([x[1] for x in pos])
  max_neg = max([x[1] for x in neg])
  print("max positive size: %d, negative size: %d" % (max_pos, max_neg))
  plt.figure(figsize=(8,8))
  plt.title("usefulness vs size")
  plt.scatter([x[1] for x in X], y)
  plt.xlabel('size')
  plt.ylabel('used')
  plt.show()
  

def classifyWithAll(X,y):
  names = ["5 Nearest Neighbors",
         "Linear SVM", #"RBF SVM", 
         #"SVM",
         #"Gaussian",
         "Decision Tree",
         "Random Forest 8", "Random Forest 12",
         "Neural Nets",
         "AdaBoost",
         "Naive Bayes",
         "Extra Trees 8", "Extra Trees 12"
         #"QDA"
         ]

  classifiers = [
        KNeighborsClassifier(5),
        SVC(kernel="linear", C=0.025), # slow
        #SVC(gamma=2, C=1),
        DecisionTreeClassifier(max_depth=4),
        RandomForestClassifier(n_estimators=10, max_features=1, max_depth=8),
        RandomForestClassifier(n_estimators=10, max_features=1, max_depth=12),
        MLPClassifier(alpha=1),
        AdaBoostClassifier(),
        GaussianNB(),
        ExtraTreesClassifier(n_estimators=10, max_features=1, max_depth=10),
        ExtraTreesClassifier(n_estimators=10, max_features=1, max_depth=12)
        #QuadraticDiscriminantAnalysis()
        ]
  
  for name, clf in zip(names, classifiers):
    classify(name, clf, X, y)

########################## main ################################################
if __name__ == "__main__":
  if len(sys.argv) < 2:
    print("usage: classify_selections.py <results dir>")
  dir = sys.argv[1]
  X, y, cnt = get_X_dir(dir)

  #labels = [
  #  "is_goal",
  #  "node_size", "node_size_diff",
  #  "is_linear",
  #  "age",
  #  "orientable_lr", "orientable_rl",
  #  "duplicating_lr", "duplicating_lr",
  #  "matches", "cps",
  #  "state_equations", "state_goals", "state_iterations"
  #]

  #X = np.delete(X, 10, 1) # drop CPs
  #X = np.delete(X, 11, 1) 
  #X = np.delete(X, 11, 1) 

  # PCA
  #pca(X,y)

  print("Classification (" + str(len(X)) + " selections from " + str(cnt)+ " files)")
  pos = sum(y)
  neg = len(y) - pos
  print("true: %d, false: %d  (balance %0.2f)" %
    (pos, neg, pos / len(y)))

  X,y = randBalanceData(X,y)
  pos = sum(y)
  neg = len(y) - pos
  print("balanced: true: %d, false: %d  (balance %0.2f)" %
    (pos, neg, pos / len(y)))

  classifyWithAll(X,y)
  

  #graphs(X,y)

  #bayes(X,y)
  #dtrees(X,y)
  #xtrees(X,y)
  random_forest(X,y)
  #pcaClassify("Gaussian",  GaussianProcessClassifier(kernel=1.0 * RBF(1.0), random_state=0), X, y, 3)
  #pcaClassify("SVC linear",  SVC(kernel="linear", C=0.025), X, y, 2)
