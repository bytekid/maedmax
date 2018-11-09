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

from sklearn import tree,metrics
from os import system


########################## getting X ########################################

labels = [
  "is_goal",
  "node_size", "node_size_diff",
  "is_linear",
  "age",
  "orientable_lr", "orientable_rl",
  "duplicating_lr", "duplicating_lr",
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
  for subdir, dirs, logs in os.walk(dir):
    for filename in logs:
      f = os.path.join(subdir,filename)
      d,t = get_X_file(f)
      X = X + d
      target = target + t
      if len(t) > 0:
        cnt = cnt + 1
  return X, target, cnt


########################## analysis ############################################

# classification
def dtrees(X,y):
  global labels
  print("decision trees (classification)")
  X_train, X_test, y_train, y_test = train_test_split(X,y, test_size=0.3, random_state=42)
  
  clf = DecisionTreeClassifier(max_depth=5)
  clf = clf.fit(X_train, y_train)
  y_pred = clf.predict(X_test)
  f1 = metrics.f1_score(y_test,y_pred) # best at 1, worst at 0
  scores = cross_val_score(clf, X, y, cv=10)
  print("  crossval: order %0.2f (+/- %0.2f)" % (scores.mean(), scores.std() * 2))

  tp = len([ (y,z) for (y,z) in zip(y_test, y_pred) if y == 1 and z == 1 ])
  fp = len([ (y,z) for (y,z) in zip(y_test, y_pred) if y == 0 and z == 1 ])
  fn = len([ (y,z) for (y,z) in zip(y_test, y_pred) if y == 0 and z == 0 ])
  tn = len([ (y,z) for (y,z) in zip(y_test, y_pred) if y == 1 and z == 0 ])
  print("  true positives: %d, false positives: %d, true negatives: %d, false negatives: %d (from %d)" % (tp, fp, tn, fn, len(y_test)))
  prec = tp / (tp+fp)
  recall = tp/(tp+tn)
  my_f1 = 2 * prec * recall / (prec + recall)
  print("  precision: %0.2f, recall: %0.2f, f1: %0.2f" % (prec, recall, my_f1))

  dotfile = open("graph.dot", 'w')
  export_graphviz(clf, out_file=dotfile, 
                         feature_names=labels,  
                         class_names=["0","1"],  
                         filled=True, rounded=True,
                         special_characters=True)
  dotfile.close()

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
  fn = len([ (y,z) for (y,z) in zip(y_test, y_pred) if y == 0 and z == 0 ])
  tn = len([ (y,z) for (y,z) in zip(y_test, y_pred) if y == 1 and z == 0 ])
  print("  true positives: %d, false positives: %d, true negatives: %d, false negatives: %d (from %d)" % (tp, fp, tn, fn, len(y_test)))
  prec = float(tp) / (tp + fp) if tp + fp != 0 else -1
  recall = float(tp) / (tp + tn) if tp + tn != 0 else -1
  my_f1 = 2 * prec * recall / (prec + recall) if prec + recall != 0 else -1
  print("  precision: %0.2f, recall: %0.2f, f1: %0.2f" % (prec, recall, my_f1))


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
  fn = len([ (y,z) for (y,z) in zip(y_test, y_pred) if y == 0 and z == 0 ])
  tn = len([ (y,z) for (y,z) in zip(y_test, y_pred) if y == 1 and z == 0 ])
  print("  true positives: %d, false positives: %d, true negatives: %d, false negatives: %d (from %d)" % (tp, fp, tn, fn, len(y_test)))
  prec = float(tp) / (tp + fp) if tp + fp != 0 else -1
  recall = float(tp) / (tp + tn) if tp + tn != 0 else -1
  my_f1 = 2 * prec * recall / (prec + recall) if prec + recall != 0 else -1
  print("  precision: %0.2f, recall: %0.2f, f1: %0.2f" % (prec, recall, my_f1))
  print(clf.theta_)
  print(clf.sigma_)
  print(clf.epsilon_)



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

  #X = np.delete(X, 0, 1) # drop goal
  #X = np.delete(X, 2, 1) # drop linear
  #X = np.delete(X, 5, 1) # drop dup
  #X = np.delete(X, 5, 1) # drop dup

  # no PCA for now
  #pca(X,y)

  print("Classification (" + str(len(X)) + " selections from " + str(cnt)+ " files)")
  pos = sum(y)
  neg = len(y) - pos
  print("true: %d, false: %d  (balance %0.2f)" %
    (pos, neg, pos / len(y)))

  names = ["3 Nearest Neighbors", "5 Nearest Neighbors", #"Linear SVM", #"RBF SVM", 
         #"SVM",
         #"Gaussian",
         "Decision Tree", "Random Forest",
         #"Neural Nets",
         "AdaBoost",
         "Naive Bayes",
         "LDA", "QDA"]

  classifiers = [
      KNeighborsClassifier(3),
      KNeighborsClassifier(5),
      #SVC(kernel="linear", C=0.025), # slow
      #SVC(gamma=2, C=1),
      DecisionTreeClassifier(max_depth=7),
      RandomForestClassifier(max_depth=5, n_estimators=10, max_features=1), #bad
      #MLPClassifier(alpha=1),
      AdaBoostClassifier(),
      GaussianNB(),
      LinearDiscriminantAnalysis(n_components=2),
      QuadraticDiscriminantAnalysis()]
 
  for name, clf in zip(names, classifiers):
    classify(name, clf, X, y)
  
  bayes(X,y)
  #pcaClassify("Gaussian",  GaussianProcessClassifier(kernel=1.0 * RBF(1.0), random_state=0), X, y, 3)
  #pcaClassify("SVC linear",  SVC(kernel="linear", C=0.025), X, y, 2)
