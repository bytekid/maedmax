let ei i n = 
 let a = Array.make n 0 in
 Array.set a (i-1) 1;
 Array.to_list a

let rec add = function
  | [],[] -> []
  | x :: xs, y :: ys -> (x + y) :: (add (xs,ys))
  | _ -> failwith "invalid arg in AC.add"

let zero n = Array.to_list (Array.make n 0)

let p_init m n = [ ei i m, zero n | i <- (Listx.interval 1 m) ] 

let rec sum_lists = function 
  | [], [] -> 0
  | a :: aa, e::ee -> (a * e) + (sum_lists (aa,ee))
  | _ -> failwith "invalid arg in AC.sum_lists"

let d_of_p aa bb (px,py) = 
 (sum_lists (aa,px)) - (sum_lists (bb,py))

let rec less = function
  | [], [] -> true
  | a :: aa, b :: bb -> 
      if a <= b 
      then less (aa,bb) else false
  | _ -> failwith "invalid arg in AC.less"
	  

let minimal (px,py) mmm = 
 let p_mm1k = (px,py) :: (Listx.unique (List.flatten mmm)) in
 [ qx,qy | qx,qy <- p_mm1k; not (less (px,qx) && less (py,qy)) ] == []
 
 
let rec complete (d,m,n) pp mm mmm qq = 
  if pp = [] then Listx.unique (List.flatten mmm)
  else 
    let qqk = Listx.unique 
      ([ px, (add (py,(ei j n))) | (px,py) <- pp; d (px,py) > 0; j <- Listx.interval 1 n ] @
       [ (add (px,(ei i m))), py | (px,py) <- pp; d (px,py) < 0; i <- Listx.interval 1 m ])
    in                                  
    let mmk = [ p | p <- qqk; d p = 0 ] in
    let ppk = [ p | p <- Listset.diff qqk mmk; minimal p mmm ] in
    complete (d,m,n) ppk mmk (mmk :: mmm) qqk

    
let basis aa bb = 
 let m = List.length aa in
 let n = List.length bb in 
 let d = d_of_p aa bb in 
 complete (d,m,n) (p_init m n) [] [[]] [] 
