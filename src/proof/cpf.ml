(*** MODULES *****************************************************************)
module R = Rule
module T = Term
module Tc = Trace
module X = Xml

(*** FUNCTIONS ***************************************************************)
let variant_free ee =
  let vcheck e l = if not (List.exists (Rule.variant e) l) then e :: l else l in
  List.fold_right vcheck ee []
;; 

let xml_str s = Xml.PCData s

let pos_to_xml p =
  (* CeTA positions start at 1 *)
  let px i = X.Element("position", [], [xml_str (string_of_int (i + 1))]) in
  X.Element("positionInTerm", [], List.map px p)
;;

let equation_to_xml (l,r) =
  X.Element("inequality", [], [Term.to_xml l; Term.to_xml r])
;;

let input_to_xml es g_opt =
  let es0 = [Variant.normalize_rule e | e <- es] in
  let xes = X.Element("equations", [], [Rules.to_xml es0] ) in
  let xgs = match g_opt with None -> [] | Some g -> [equation_to_xml g] in
  let input = X.Element("equationalReasoningInput", [], xes :: xgs) in
  X.Element("input", [], [input])
;;

let step_to_xml (p, rl, dir, _, t) =
  let dirstr = function Trace.LeftRight -> "leftRight" | _ -> "rightLeft" in
  let dirxml = X.Element(dirstr dir, [], []) in
  let components = [pos_to_xml p; Rule.to_xml rl; dirxml; T.to_xml t] in
  X.Element("equationStep", [], components)
;;

let conversion_to_xml (t, steps) =
  let start = X.Element("startTerm", [], [T.to_xml t]) in
  X.Element("conversion", [], start :: (List.map step_to_xml steps))
;;

let rule_sub_to_xml ((s, t), (s', steps)) =
  let xconv = conversion_to_xml (s', steps) in
  X.Element("ruleSubsumptionProof", [], [Rule.to_xml (s, t); xconv])
;;

let eqproof_to_xml cs =
  let xsub = X.Element("subsumptionProof", [], List.map rule_sub_to_xml cs) in
  let xconv = X.Element("convertibleInstance", [], [xsub]) in
  X.Element("equationalDisproof", [], [xconv])
;;

let inference_to_xml step =
  let t3_to_xml ((s, t), u) = [T.to_xml v | v <- [s; t; u]] in
  let to_xml = function
    | Tc.Deduce (s, t, u) -> X.Element("deduce", [], t3_to_xml ((s, t), u))
    | Tc.Delete s -> X.Element("delete", [], [T.to_xml s])
    | Tc.SimplifyL (st, u) -> X.Element("simplifyl", [], t3_to_xml (st, u))
    | Tc.SimplifyR (st, u) -> X.Element("simplifyr", [], t3_to_xml (st, u))
    | Tc.OrientL (s, t) -> X.Element("orientl", [], [T.to_xml s; T.to_xml t])
    | Tc.OrientR (s, t) -> X.Element("orientr", [], [T.to_xml s; T.to_xml t])
    | Tc.Compose (st, u) -> X.Element("compose", [], t3_to_xml (st, u))
    | Tc.Collapse (st, u) -> X.Element("collapse", [], t3_to_xml (R.flip st, u))
  in
  X.Element("orderedCompletionStep", [], [ to_xml step ])
;;

let run_to_xml steps = X.Element("run", [], [inference_to_xml s | s <- steps])

let ordered_completion_input_to_xml ee0 (rr, ee, ord) =
  let ee0 = [Variant.normalize_rule e | e <- ee0] in
  let xes0 = X.Element("equations", [], [Rules.to_xml ee0]) in
  let xrs = X.Element("trs", [], [Rules.to_xml rr]) in
  let xes = X.Element("equations", [], [Rules.to_xml ee]) in
  let xord = X.Element("reductionOrder", [], [ord#to_xml]) in
  let oxi = X.Element("orderedCompletionInput", [], [xes0; xrs; xes; xord]) in
  X.Element("input", [], [oxi])
;;

let eqdisproof_to_xml ee0 (rr, ee, ord) ((s, t), (rs, rt)) =
  let xconv_s = conversion_to_xml (s, Tc.rewrite_conv' s rs) in
  let xconv_t = conversion_to_xml (t, Tc.rewrite_conv' t rt) in
  let xnorm = X.Element("normalization", [], [xconv_s; xconv_t]) in
  let steps, _ = Tc.reconstruct_run ee0 ee rr in
  let comps = run_to_xml steps :: [xnorm ] in
  let xconv = X.Element("groundCompletionAndNormalization", [], comps) in
  X.Element("equationalDisproof", [], [xconv])
;;

let xml_proof_wrapper xinput xproof =
  let xversion = X.Element("cpfVersion", [], [xml_str "2.1"]) in
  let name = X.Element("name", [], [xml_str "maedmax"]) in
  let version = X.Element("version", [], [xml_str "1.0"]) in
  let xt = X.Element("tool", [], [name; version]) in
  let xo = X.Element("origin", [], [ X.Element("proofOrigin", [], [xt]) ]) in
  let a1 = "xmlns:xsi","http://www.w3.org/2001/XMLSchema-instance" in
  let a2 = "xsi:noNamespaceSchemaLocation","../xml/cpf.xsd" in
  X.Element("certificationProblem", [a1; a2], [xinput; xversion; xproof; xo])
;;

let goal_proof es0 g_orig ((s, t), (rs, rt), sigma) =
  let g = Variant.normalize_rule g_orig in
  let rulesubs = Tc.goal_proof g (s, t) (rs, rt) sigma in
  let xproof = X.Element("proof", [], [ eqproof_to_xml rulesubs ]) in
  xml_proof_wrapper (input_to_xml es0 (Some g)) xproof
;;

let goal_disproof es0 g_orig res rst =
  let g = Variant.normalize_rule g_orig in
  let xproof = X.Element("proof", [], [eqdisproof_to_xml es0 res (g, rst)]) in
  xml_proof_wrapper (input_to_xml es0 (Some g)) xproof
;;

let ground_completion ee0 (rr, ee, ord) =
  let steps, (ee', rr') = Tc.reconstruct_run ee0 ee rr in
  let ee' = variant_free ee' in
  let xcproof = X.Element("orderedCompletionProof", [], [run_to_xml steps]) in
  let xproof = X.Element("proof", [], [xcproof]) in
  let xinput = ordered_completion_input_to_xml ee0 (rr', ee', ord) in
  xml_proof_wrapper xinput xproof
;;
