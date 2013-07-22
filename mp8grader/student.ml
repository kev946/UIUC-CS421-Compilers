open Mp8common;;

let const_to_val c =
	match c with
	| Int i -> Intval i
	| Bool b -> Boolval b
	| Float f -> Floatval f
	| String s -> Stringval s
	| Nil -> Listval []
	| Unit -> Unitval

let monApply unop v =
	match unop with
	| Head -> (match v with Listval x -> List.hd x)
	| Tail -> (match v with Listval x -> Listval (List.tl x))
	| Fst -> (match v with Pairval (x, y) -> x)
	| Snd -> (match v with Pairval (x, y) -> y)
	| Neg -> (match v with Intval x -> (Intval (0 - x)) | Floatval f -> (Floatval (0.0 -. f)))
	| Print -> (match v with Intval x -> (print_int x; (Unitval)))


let binApply binop (v1, v2) =
	match binop with
	| Add -> (match v1 with Intval x -> match v2 with Intval y -> Intval(x + y))
	| Sub -> (match v1 with Intval x -> match v2 with Intval y -> Intval(x - y))
	| Mul -> (match v1 with Intval x -> match v2 with Intval y -> Intval(x * y))
	| Div -> (match v1 with Intval x -> match v2 with Intval y -> Intval(x / y))
	| Exp -> (match v1 with Floatval x -> match v2 with Floatval y -> Floatval(x ** y))
	| FAdd -> (match v1 with Floatval x -> match v2 with Floatval y -> Floatval(x +. y))
	| FSub -> (match v1 with Floatval x -> match v2 with Floatval y -> Floatval(x -. y))
	| FMul -> (match v1 with Floatval x -> match v2 with Floatval y -> Floatval(x *. y))
	| FDiv -> (match v1 with Floatval x -> match v2 with Floatval y -> Floatval(x /. y))
	| Concat -> (match v1 with Stringval s1 -> match v2 with Stringval s2 -> Stringval(s1 ^ s2))
	| Cons -> (match v2 with Listval l -> Listval (v1 :: l))
	| Comma -> Pairval (v1, v2)
	| Eq -> Boolval (v1 = v2)
	| Less -> Boolval (v1 < v2)

let rec eval_exp (exp, m) =
	match exp with
	| ConExp c -> const_to_val c
	| VarExp x -> (let v = (lookup_mem m x) in match v with Recvar(y, e, m') -> Closure(y, e, (ins_mem m' x v)) | _ -> v)
	| MonExp (mon, e) -> (monApply mon (eval_exp (e, m)))
	| BinExp (binOp, exp1, exp2) -> (binApply binOp ((eval_exp (exp1, m)), (eval_exp (exp2, m))))
	| LetExp (str, e1, e2) -> (let x = (eval_exp (e1, m)) in (let m' = (ins_mem m str x) in (eval_exp (e2, m'))))
	| FunExp (str, exp) -> (Closure (str, exp, m))
	| AppExp (f, e) -> (let c = eval_exp(f, m) in (match c with Closure (str, e1, m1) -> eval_exp(e1, (ins_mem m1 str (eval_exp (e, m))))))
	| IfExp (e1, e2, e3) -> let b = eval_exp(e1, m) in (if b = Boolval true then eval_exp(e2, m) else eval_exp(e3, m))
	| RecExp (s1, s2, e1, e2) -> eval_exp(e2, (ins_mem m s1 (Recvar (s2, e1, m))))

let eval_dec (dec, m) =
	match dec with
	| Anon e -> let x = eval_exp(e,m) in ((None, x), m)
	| TopLet (s, e) -> let x = eval_exp(e, m) in ((Some s, x), (ins_mem m s x))
	| TopRec (s1, s2, e) -> let rvar =Recvar(s2, e, m) in ((Some s1, rvar),
	(ins_mem m s1 rvar))

