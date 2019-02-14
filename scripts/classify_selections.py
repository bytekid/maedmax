import os, sys
import json
import re
import numpy as np
import random
from sklearn.svm import SVC, LinearSVC
from sklearn.tree import DecisionTreeClassifier, export_graphviz
from sklearn.ensemble import RandomForestClassifier, AdaBoostClassifier
from sklearn.naive_bayes import GaussianNB
from sklearn.discriminant_analysis import QuadraticDiscriminantAnalysis, LinearDiscriminantAnalysis
from sklearn.model_selection import cross_val_score
from sklearn.model_selection import train_test_split
from sklearn.neighbors import KNeighborsClassifier
from sklearn.decomposition import PCA
from treeinterpreter import treeinterpreter as ti
from sklearn.gaussian_process import GaussianProcessClassifier
from sklearn.gaussian_process.kernels import RBF
from sklearn.metrics import roc_curve, precision_recall_curve, auc, make_scorer, recall_score, accuracy_score, precision_score, confusion_matrix
from sklearn.ensemble import ExtraTreesClassifier

from sklearn import tree, metrics
from sklearn.tree import _tree
from os import system
import pandas as pd

from random import randint

import tensorflow as tf
from keras.models import Sequential
from keras.layers import Dense
from keras.utils import to_categorical
from keras.wrappers.scikit_learn import KerasClassifier
from sklearn.model_selection import StratifiedKFold
from sklearn.preprocessing import StandardScaler
from sklearn.pipeline import Pipeline


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
pq_grams = [str(i) for i in range(0,211)]

def get_X_file(filename):
  file = open(filename, "r")
  cnt = 0
  #print(filename)
  lines = file.readlines()
  i = 0
  data = []
  while i < len(lines):
    line = lines[i]
    if ("Timeout" in line) or ("TIMEOUT" in line) or line.strip() == "" or i + 4 >= len(lines):
      break
    if not (line.startswith("--")):
      print ("%dth line: %s" % (i, line))
    assert(line.startswith("--"))
    eqn = line[2:]
    syntactic_features = lines[i + 1].strip()
    eqn_features = lines[i + 2][1:].strip()
    eqn_features_named = lines[i + 3][1:].strip()
    useful = lines[i + 4]
    cnt = cnt + 1
    data.append ([eqn, syntactic_features, eqn_features, "0", useful]) # eqn_features_named
    i = i + 5
  
  X_syn = []
  X_syn_terms = []
  X_syn_named_terms = []
  X_all = []
  y = []
  for d in data:
    s_eqn, s_syn, s_terms, s_named_terms, s_useful = d
    syn = [float(f) for f in s_syn.split(" ")]
    terms = [float(f) for f in s_terms.split(" ")]
    named_terms = [float(f) for f in s_named_terms.split(" ")]
    useful = float(s_useful)
    #if len(parts) < 225 or "export" in line:
    #  continue # timeout/printing?
    X_syn.append(syn)
    X_syn_terms.append(syn + terms)
    X_syn_named_terms.append(syn + named_terms)
    X_all.append(syn + terms + named_terms) 
    y.append(useful)
  #print(filename + ": " + str(cnt))
  return [X_syn, X_syn_terms, X_syn_named_terms, X_all, y]

def get_X_dir(dir):
  X_syn = []
  X_syn_terms = []
  X_syn_named_terms = []
  X_all = []
  y = []
  cnt = 0
  fs = []
  for subdir, dirs, logs in os.walk(dir):
    for filename in logs:
      if "json" in filename:
        continue
      f = os.path.join(subdir,filename)
      Xs, Xst, Xsnt, Xa, u = get_X_file(f)
      X_syn = X_syn + Xs
      X_syn_terms = X_syn_terms + Xst
      X_syn_named_terms = X_syn_named_terms + Xsnt
      X_all = X_all + Xa
      y = y + u
      if len(u) > 0:
        fs.append(subdir[subdir.rfind("/"):])
        cnt = cnt + 1
  return X_syn, X_syn_terms, X_syn_named_terms, X_all, y, cnt

def balanceData(X,y):
  X0 = [ xi for (xi,yi) in zip(X, y) if yi == 0 ]
  X1 = [ xi for (xi,yi) in zip(X, y) if yi == 1 ]
  y01 = [ 0 for x in X0] + [ 1 for x in X0]
  assert(len(X1) <= len(X0))
  random.shuffle(X1)
  len1 = len(X1)
  len0 = len(X0)
  for i in range(0,len0):
    X0.append(X1[i % len1])
  assert(len(y01) == len(X0))
  assert(sum(y01) == len0)
  return (X0,y01)


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
  global labels, pq_grams
  names = labels + pq_grams
  def json_of_node(node):
    if tree.feature[node] != _tree.TREE_UNDEFINED:
      name = names[tree.feature[node]]
      threshold = tree.threshold[node]
      leq = json_of_node(tree.children_left[node])
      gt = json_of_node(tree.children_right[node])
      return {"attr" : name, "thresh" : threshold, "leq" : leq, "gt" : gt}
    else:
      v_max = 0
      i_max = 0
      # count which class has more members
      neg = tree.value[node][0][0]
      pos = tree.value[node][0][1]
      prob = pos / (pos + neg)
      #print("pos: %d, neg: %d, imax: %d, p: %.2f" % (pos, neg, i_max, prob))
      return prob

  return json_of_node(0) 

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

  #trees = []
  #for i in range(0, estimators):
  #  t = clf.estimators_[i].tree_
  #  trees.append(tree2json(t))
  #print(json.dumps(trees))


def randomForest(X, y):
  estimators = 100
  print("random forest (%d est) using %d features" % (estimators, len(X[0])))

  X_train, X_test, y_train, y_test = train_test_split(X,y, test_size=0.3, random_state=42)
  clf = RandomForestClassifier(n_estimators=estimators, max_features=1, max_depth=14).fit(X_train, y_train)
  y_pred = clf.predict(X_test)
  from sklearn.preprocessing import LabelBinarizer

  lb = LabelBinarizer()
  y_train = np.array([number[0] for number in lb.fit_transform(y_train)])

  recall = cross_val_score(clf, X_train, y_train, cv=5, scoring='recall')
  print('Recall', np.mean(recall), recall)
  precision = cross_val_score(clf, X_train, y_train, cv=5, scoring='precision')
  print('Precision', np.mean(precision), precision)

  for l,i in zip(labels, clf.feature_importances_):
    print("%s: %.3f" % (l,i))

  trees = []
  for i in range(0, estimators):
    t = clf.estimators_[i].tree_
    trees.append(tree2json(t))
  print(json.dumps(trees))


### # # # # # # # # # NEURAL NETS # # # # # # # # # # # # # # # # # # # # # # ##
def as_keras_metric(method):
    import functools
    from keras import backend as K
    @functools.wraps(method)
    def wrapper(self, args, **kwargs):
        """ Wrapper for turning tensorflow metrics into keras metrics """
        value, update_op = method(self, args, **kwargs)
        K.get_session().run(tf.local_variables_initializer())
        with tf.control_dependencies([update_op]):
            value = tf.identity(value)
        return value
    return wrapper

def neuralNets(X, y):
  print("neural nets")

  def run(create):
    estimators = []
    estimators.append(('standardize', StandardScaler()))
    estimators.append(('mlp', KerasClassifier(build_fn=create, epochs=10, batch_size=5, verbose=0)))
    pipeline = Pipeline(estimators)
    kfold = StratifiedKFold(n_splits=2, shuffle=True, random_state=seed)
    results = cross_val_score(pipeline, np.array(X), y, cv=kfold)
    return results

  def create_baseline():
    model = Sequential()
    model.add(Dense(units=224, kernel_initializer='normal', activation='relu', input_dim=224))
    model.add(Dense(units=1, kernel_initializer='normal', activation='sigmoid'))
    #model.add(Dense(units=10, activation='softmax'))
    precision = as_keras_metric(tf.metrics.precision)
    recall = as_keras_metric(tf.metrics.recall)
    model.compile(loss='binary_crossentropy',
              optimizer='adam',
              metrics=['accuracy', precision, recall])
    return model

  seed = 7
  #estimator = KerasClassifier(build_fn=create_baseline, epochs=10, batch_size=5, verbose=0)
  #kfold = StratifiedKFold(n_splits=2, shuffle=True, random_state=seed)
  #results = cross_val_score(estimator, np.array(X), y, cv=kfold)
  #print("Results: %.2f%% (%.2f%%)" % (results.mean()*100, results.std()*100))
  # Results: 81.55% (0.18%) on random

  #estimators = []
  #estimators.append(('standardize', StandardScaler()))
  #estimators.append(('mlp', KerasClassifier(build_fn=create_baseline, epochs=10, batch_size=5, verbose=0)))
  #pipeline = Pipeline(estimators)
  #kfold = StratifiedKFold(n_splits=2, shuffle=True, random_state=seed)
  #results = cross_val_score(pipeline, np.array(X), y, cv=kfold)
  #print("Standardized: %.2f%% (%.2f%%)" % (results.mean()*100, results.std()*100))
  # Standardized: 85.92% (0.23%)

  def create_smaller():
	  model = Sequential()
	  model.add(Dense(112, input_dim=224, kernel_initializer='normal', activation='relu'))
	  model.add(Dense(1, kernel_initializer='normal', activation='sigmoid'))
	  # Compile model
	  model.compile(loss='binary_crossentropy', optimizer='adam', metrics=['accuracy'])
	  return model

  results = run(create_smaller)
  print("Smaller: %.2f%% (%.2f%%)" % (results.mean()*100, results.std()*100)) #Smaller: 83.96% (0.03%)

  def create_larger():
    model = Sequential()
    model.add(Dense(units=224, kernel_initializer='normal', activation='relu', input_dim=224))
    model.add(Dense(112, kernel_initializer='normal', activation='relu'))
    model.add(Dense(1, kernel_initializer='normal', activation='sigmoid'))
    model.compile(loss='binary_crossentropy', optimizer='adam', metrics=['accuracy'])
    return model
  
  results = run(create_larger)
  print("Larger: %.2f%% (%.2f%%)" % (results.mean()*100, results.std()*100)) # Larger: 88.03% (0.32%)


def classifyWithAll(X,y):
  names = [#"5 Nearest Neighbors",
         #"Linear SVM", #"RBF SVM", 
         #"SVM",
         #"Gaussian",
         "Decision Tree",
         "Random Forest 25", "Random Forest 12",
         "SciKit Neural Nets",
         "AdaBoost",
         "Naive Bayes",
         "Extra Trees inf", "Extra Trees 12"
         #"QDA"
         ]

  classifiers = [
        #KNeighborsClassifier(5),
        #SVC(kernel="linear", C=0.025), # slow
        #SVC(gamma=2, C=1),
        DecisionTreeClassifier(max_depth=4),
        RandomForestClassifier(n_estimators=10, max_features=1, max_depth=20),
        RandomForestClassifier(n_estimators=100, max_features=1, max_depth=8),
        MLPClassifier(alpha=1),
        AdaBoostClassifier(),
        GaussianNB(),
        ExtraTreesClassifier(n_estimators=10, max_features=1, max_depth=25),
        ExtraTreesClassifier(n_estimators=100, max_features=1, max_depth=8)
        #QuadraticDiscriminantAnalysis()
        ]
  
  for name, clf in zip(names, classifiers):
    classify(name, clf, X, y)

########################## main ################################################
if __name__ == "__main__":
  if len(sys.argv) < 2:
    print("usage: classify_selections.py <results dir>")
  dir = sys.argv[1]
  X_syn, X_syn_terms, X_syn_named_terms, X_all, y, cnt = get_X_dir(dir)

  X = X_syn

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

  X = np.delete(X, 11, 1) # drop state
  X = np.delete(X, 11, 1) 
  X = np.delete(X, 11, 1) 

  # PCA
  #pca(X,y)

  print("Classification (" + str(len(X)) + " selections from " + str(cnt)+ " files)")
  pos = sum(y)
  neg = len(y) - pos
  print("true: %d, false: %d  (balance %0.2f)" %
    (pos, neg, pos / len(y)))

  X,y = balanceData(X,y)
  pos = sum(y)
  neg = len(y) - pos
  print("balanced: true: %d, false: %d  (balance %0.3f)" %
    (pos, neg, pos / len(y)))

  #classifyWithAll(X,y)
  
  #neuralNets(X,y)

  #xtrees(X,y)
  randomForest(X,y)
