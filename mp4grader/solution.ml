open Mp4common

(* Problem 1 *)
let import_list lst = List.fold_right (fun b l -> BinExp(Cons,ConExp (Bool b),l)) lst (ConExp Nil)

(* Problem 2 *)
let filter = RecExp("filter","p",FunExp("xs"
                 ,IfExp(BinExp(Eq,VarExp "xs",ConExp (Nil))
                       ,ConExp (Nil)
                       ,IfExp(AppExp(VarExp "p",MonExp(Head,VarExp "xs"))
                             ,BinExp(Cons, MonExp(Head,VarExp "xs"), AppExp(AppExp(VarExp "filter", VarExp "p"), MonExp(Tail, VarExp "xs")))
                             ,AppExp(AppExp(VarExp "filter",VarExp "p")
                                    ,MonExp(Tail,VarExp "xs")))))
                 ,VarExp "filter")

(* Problem 3 *)
let rec num_of_vars expression =
  match expression with
  | VarExp _ -> 1
  | ConExp _ -> 0
  | AppExp (e1,e2) -> num_of_vars e1 + num_of_vars e2
  | OAppExp (e1,e2) -> num_of_vars e1 + num_of_vars e2
  | BinExp (_,e1,e2) -> num_of_vars e1 + num_of_vars e2
  | MonExp (_,e) -> num_of_vars e
  | IfExp (c,t,f) -> num_of_vars c + num_of_vars t + num_of_vars f
  | FunExp (_,e) -> num_of_vars e
  | LetExp (_,e1,e2) -> num_of_vars e1 + num_of_vars e2
  | RecExp (_,_,e1,e2) -> num_of_vars e1 + num_of_vars e2

(* Assorted Examples *)
let id = FunExp("i",VarExp "i")

let fac = RecExp("fac","n"
     ,IfExp(BinExp(Eq,VarExp "n",ConExp(Int 0))
        ,ConExp(Int 1)
        ,BinExp(Mul,VarExp "n",AppExp(VarExp "fac",BinExp(Sub,VarExp "n",ConExp(Int 1)))))
     ,VarExp "fac")

let factest n = AppExp(fac,ConExp(Int n))

let fib = RecExp("fib","n"
     ,IfExp(BinExp(Eq,VarExp "n",ConExp(Int 0))
        ,ConExp(Int 0)
        ,IfExp(BinExp(Eq,VarExp "n",ConExp(Int 1))
           ,ConExp(Int 1)
           ,BinExp(Add,AppExp(VarExp "fib",BinExp(Sub,VarExp "n",ConExp(Int 1)))
                   ,AppExp(VarExp "fib",BinExp(Sub,VarExp "n",ConExp(Int 2))))))
     ,VarExp "fib")

let fibtest n = AppExp(fib,ConExp(Int n))

let omega = AppExp(FunExp("x",AppExp(VarExp "x",VarExp "x")),FunExp("x",AppExp(VarExp "x",VarExp "x")))

let omegatest = RecExp("div","x",omega,ConExp (Int 0))

(* Problem 4 *)
let rec freeVars expression =
  match expression with
  | ConExp v -> []
  | VarExp v -> [v]
  | FunExp (i,e) -> List.filter (fun s -> not (s = i)) (freeVars e)
  | IfExp (c,t,f) -> freeVars c @ freeVars t @ freeVars f
  | AppExp (e1,e2) -> freeVars e1 @ freeVars e2
  | MonExp (_,e) -> freeVars e
  | BinExp (_,e1,e2) -> freeVars e1 @ freeVars e2
  | LetExp (i,e1,e2) -> freeVars e1 @ List.filter (fun s -> not (s = i)) (freeVars e2)
  | RecExp (i,a,e1,e2) -> (List.filter (fun s -> not (s = i || s = a)) (freeVars e1))
                        @ (List.filter (fun s -> not (s = i)) (freeVars e2))
(* Problem 6 *)
  | OAppExp (e1,e2) -> freeVars e1 @ freeVars e2

(* Problem 5 *)
let rec cps expression cont =
  match expression with
  | ConExp v -> AppExp(cont,ConExp v)
  | VarExp v -> AppExp(cont,VarExp v)
  | FunExp (i,e) -> let k = freshFor (freeVars e)
                 in AppExp(cont,FunExp(i,FunExp(k,cps e (VarExp k))))
  | MonExp(op,e) -> let v = freshFor (freeVars e @ freeVars cont)
                 in cps e (FunExp(v,AppExp(cont,MonExp(op,VarExp v))))
  | BinExp(op,e1,e2) -> let v1 = freshFor (freeVars expression @ freeVars cont)
                     in let v2 = freshFor (v1::freeVars expression @ freeVars cont)
                     in cps e1 (FunExp(v1,cps e2 (FunExp(v2,AppExp(cont,BinExp(op,VarExp v1,VarExp v2))))))
  | IfExp(c,t,f) -> let v = freshFor (freeVars expression @ freeVars cont)
                 in cps c (FunExp (v,IfExp(VarExp v,cps t cont,cps f cont)))
  | AppExp(e1,e2) -> let v1 = freshFor (freeVars expression @ freeVars cont)
                  in let v2 = freshFor (v1::freeVars expression @ freeVars cont)
                  in cps e1 (FunExp(v1,cps e2 (FunExp(v2,AppExp(AppExp(VarExp v1,VarExp v2),cont)))))
  | LetExp(i,e1,e2) -> cps e1 (FunExp(i,cps e2 cont))
  | RecExp(i,a,e1,e2) -> let k = freshFor (freeVars e1 @ freeVars e2 @ freeVars cont)
                      in RecExp(i,a,FunExp(k,cps e1 (VarExp k)),cps e2 cont)
(* Problem 6 *)
  | OAppExp(e1,e2) -> let v1 = freshFor (freeVars expression @ freeVars cont)
                  in let v2 = freshFor (v1::freeVars expression @ freeVars cont)
                  in cps e2 (FunExp(v2,cps e1 (FunExp(v1,AppExp(AppExp(VarExp v1,VarExp v2),cont)))))