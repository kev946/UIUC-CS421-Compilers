open Mp5common

let rec gather_ty_substitution judgement =
	let {gamma = gamma; exp = exp; monoTy = tau} = judgement in
	match exp with
	| ConExp c -> (
		let tau' = const_signature c in
		match unify [(tau, freshInstance tau')] with
		| Some sigma ->
			Some ({antecedents = []; conclusion = judgement}, sigma)
		| _ -> None
	)
	| VarExp x -> (
		let x' = lookup_env gamma x in
			match x' with 
			Some tau' -> ( 
				match unify [(tau, freshInstance tau')] with
				| Some sigma ->
					Some({antecedents = []; conclusion = judgement}, sigma)
				| _ -> None
			)
			| _ -> None
	)
	| BinExp(binop, exp1, exp2) -> (
		let tau' = binop_signature binop in
		let tau1' = fresh () in 
		let tau2' = fresh () in
		match gather_ty_substitution {gamma = gamma; exp = exp1; monoTy = tau1'} with
		| Some (p1, subs1) -> 
			match gather_ty_substitution {gamma = gamma; exp = exp2; monoTy = tau2'} with
			| Some (p2, subs2) ->
				let subst = subst_compose subs2 subs1 in 
				match unify [(monoTy_lift_subst subst (mk_fun_ty tau1' (mk_fun_ty tau2' tau))), freshInstance tau'] with
				| Some sigma ->
					Some({antecedents = [p1;p2]; conclusion = judgement}, subst_compose sigma subst)
				| _ -> None
			| _ -> None
		| _ -> None
	)
	| MonExp(monop, exp1) -> (
		let tau' = monop_signature monop in 
		let tau1' = fresh () in
		match gather_ty_substitution {gamma = gamma; exp = exp1; monoTy = tau1'} with
		| Some (p1, subs1) -> 
			match unify [(monoTy_lift_subst subs1 (mk_fun_ty tau1' tau), freshInstance tau')] with
			| Some sigma -> 
				Some({antecedents = [p1]; conclusion = judgement}, subst_compose sigma subs1)
			| _ -> None
		| _ -> None
	)
	| IfExp(exp1, exp2, exp3) -> (
		match gather_ty_substitution {gamma = gamma; exp = exp1; monoTy = bool_ty} with
		| Some (p1, subs1) ->
			match gather_ty_substitution {gamma = env_lift_subst subs1 gamma; exp = exp2; monoTy = monoTy_lift_subst subs1 tau} with
			| Some (p2, subs2) ->
				match gather_ty_substitution {gamma = (env_lift_subst (subst_compose subs1 subs2) gamma); exp = exp3; monoTy = monoTy_lift_subst (subst_compose subs2 subs1) tau} with
				| Some (p3, subs3) ->
					Some({antecedents = [p1;p2;p3]; conclusion = judgement}, subst_compose subs1 (subst_compose subs2 subs3))
				| _ -> None
			| _ -> None
		| _ -> None
	)
	| FunExp(str, exp1) -> (
		let tau' = fresh () in
		let tau1' = fresh () in
		match gather_ty_substitution {gamma = ins_env gamma str ([], tau'); exp = exp1; monoTy = tau1'} with
		| Some (p1, subs1) ->
			match unify [(monoTy_lift_subst subs1 tau, monoTy_lift_subst subs1 (mk_fun_ty tau' tau1'))] with 
			| Some sigma ->
				Some({antecedents = [p1]; conclusion = judgement}, subst_compose sigma subs1)
			| _ -> None 

		| _ -> None
	)
	| AppExp(e1, e2) -> (
		let tau' = fresh () in
		match gather_ty_substitution {gamma = gamma; exp = e1; monoTy = mk_fun_ty tau' tau} with
		| Some (p1, subst1) -> 
			match gather_ty_substitution {gamma = env_lift_subst subst1 gamma; exp = e2; monoTy = monoTy_lift_subst subst1 tau'} with
			| Some (p2, subst2) ->
				Some({antecedents = [p1;p2]; conclusion = judgement}, subst_compose subst2 subst1)
			| _ -> None

		| _ -> None
	)

	|  LetExp(x, e1, e2) -> (
		let tau1 = fresh () in 
		match gather_ty_substitution {gamma = gamma; exp = e1; monoTy = tau1} with
		| Some(p1, subst1) -> 
			match gather_ty_substitution {gamma = ins_env (env_lift_subst subst1 gamma) x (gen(env_lift_subst subst1 gamma) (monoTy_lift_subst subst1 tau1)); exp = e2; monoTy = monoTy_lift_subst subst1 tau} with
			| Some (p2, subst2) ->
				Some ({antecedents = [p1;p2]; conclusion = judgement}, subst_compose subst2 subst1)
			| _ -> None
		| _ -> None
			
	)
	
	(* idk RecExp ...*)
			

	| RaiseExp(e) -> (
		match gather_ty_substitution {gamma = gamma; exp = e; monoTy = int_ty} with
		| Some(p1, subst1) ->
			Some({antecedents = [p1]; conclusion = judgement}, subst1)
		| _ -> None
	)






