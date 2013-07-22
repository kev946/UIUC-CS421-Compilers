(*
 * File: mp5-sol.ml
 *)

open Mp5common

let rec gather_ty_substitution (judgment:judgment) =
    let {gamma = gamma; exp = exp; monoTy = tau} = judgment in
    match exp
    with ConExp c ->
      let tau' = const_signature c in 
      (match unify [(tau, freshInstance(tau'))] with None -> None
       | Some sigma ->
         Some ({antecedents = []; conclusion = judgment}, sigma))
    | VarExp x ->
      (match lookup_env gamma x
       with None -> None
       | Some x_ty ->
       (match unify [(tau, freshInstance(x_ty))]
        with None -> None
       | Some sigma ->
         Some ({antecedents = []; conclusion = judgment}, sigma)))
    | BinExp (binop, e1, e2) ->
       let (tau1, tau2) = (fresh(),fresh()) in
       let tau' = binop_signature binop in
       (match gather_ty_substitution {gamma = gamma; exp = e1; monoTy = tau1}
        with None -> None
        | Some (proof1, sigma1) ->
          (match gather_ty_substitution {gamma = env_lift_subst sigma1 gamma;
                                         exp = e2; monoTy = tau2}
           with None -> None
           | Some (proof2, sigma2) ->
             let sigma21 = subst_compose sigma2 sigma1 in
             (match unify [(monoTy_lift_subst sigma21
                            (mk_fun_ty tau1 (mk_fun_ty tau2 tau)),
                           freshInstance tau')]
              with None -> None
              | Some sigma ->
                Some ({antecedents = [proof1; proof2]; conclusion = judgment},
                  subst_compose sigma sigma21))))
    | MonExp (monop, e1) ->
      let tau1 = fresh() in
      let tau' = monop_signature monop in
      (match gather_ty_substitution {gamma = gamma; exp = e1; monoTy = tau1}
       with None -> None
       | Some (proof, sigma) ->
         (match unify [(monoTy_lift_subst sigma (mk_fun_ty tau1 tau),
                        freshInstance(tau'))] with None -> None
              | Some unify_subst -> 
                Some ({antecedents = [proof]; conclusion = judgment},
                  subst_compose unify_subst sigma)))
    | IfExp (bool_exp, then_exp, else_exp) ->
      (match
        gather_ty_substitution {gamma = gamma; exp = bool_exp; monoTy = bool_ty}
        with None -> None
        | Some (bool_pf,sigma1) -> 
          (match
           gather_ty_substitution {gamma = env_lift_subst sigma1 gamma;
                                   exp = then_exp;
                                   monoTy = monoTy_lift_subst sigma1 tau}
           with None -> None
           | Some (then_pf, sigma2) ->
             (let sigma21 = subst_compose sigma2 sigma1 in
              match
              gather_ty_substitution {gamma = env_lift_subst sigma21 gamma;
                                      exp = else_exp;
                                      monoTy = monoTy_lift_subst sigma21 tau}
              with None -> None
              | Some (else_pf, sigma3) ->
                Some({antecedents = [bool_pf; then_pf; else_pf];
                      conclusion = judgment},
                      (subst_compose sigma3 sigma21)))))
    | AppExp (e1, e2) ->
      let tau1 = fresh() in
      (match
       gather_ty_substitution {gamma = gamma; exp = e1; monoTy = mk_fun_ty tau1 tau}
       with None -> None
       | Some (e1_pf, sigma1) ->
         (match 
          gather_ty_substitution {gamma = env_lift_subst sigma1 gamma;
                                  exp = e2; monoTy = monoTy_lift_subst sigma1 tau1}
          with None -> None
          | Some(e2_pf, sigma2) ->
            Some({antecedents = [e1_pf; e2_pf]; conclusion = judgment},
                   subst_compose sigma2 sigma1)))
    | FunExp (x,e) ->
      let (tau1, tau2) = (fresh(), fresh()) in
      (match gather_ty_substitution {gamma = (ins_env gamma x ([],tau1));
                                     exp = e; monoTy = tau2}
       with None -> None
       | Some (pf, sigma) ->
         (match unify[(monoTy_lift_subst sigma tau,
                       monoTy_lift_subst sigma (mk_fun_ty tau1 tau2))]
          with None -> None
          | Some unify_subst ->
            Some ({antecedents = [pf]; conclusion = judgment},
	           subst_compose unify_subst sigma)))
    | LetExp (x, e1, e2) ->
      let tau1 = fresh() in
      (match gather_ty_substitution {gamma = gamma; exp = e1; monoTy = tau1}
       with None -> None
       | Some(e1_pf, sigma1) ->
         let sigma1_gamma = env_lift_subst sigma1 gamma in
         let x_ty = gen sigma1_gamma (monoTy_lift_subst sigma1 tau1) in
         match gather_ty_substitution{gamma =(ins_env sigma1_gamma x x_ty);
                                      exp = e2;
                                      monoTy = monoTy_lift_subst sigma1 tau}
         with None -> None
         | Some(e2_pf, sigma2) ->
           Some({antecedents = [e1_pf; e2_pf]; conclusion = judgment},
                 subst_compose sigma2 sigma1))
    | RecExp (f, x, e1, e2) ->
      let (tau1, tau2) = (fresh(),fresh()) in
      (match gather_ty_substitution
             {gamma =
              ins_env (ins_env gamma x ([],tau1)) f ([],(mk_fun_ty tau1 tau2));
              exp = e1; monoTy = tau2}
       with None -> None
       | Some (e1_pf, sigma1) ->
         (let sigma1_gamma = env_lift_subst sigma1 gamma in
          let f_ty =
            gen sigma1_gamma (monoTy_lift_subst sigma1 (mk_fun_ty tau1 tau2)) in
          match gather_ty_substitution
                {gamma = (ins_env sigma1_gamma f f_ty); exp = e2;
                 monoTy = monoTy_lift_subst sigma1 tau}
          with None -> None
          | Some (e2_pf, sigma2) ->
            Some({antecedents = [e1_pf; e2_pf]; conclusion = judgment},
                  subst_compose sigma2 sigma1)))
    | RaiseExp e ->
      (match gather_ty_substitution {gamma = gamma; exp = e; monoTy = int_ty}
       with None -> None
       | Some (pf, sigma) -> 
         Some ({antecedents = [pf]; conclusion = judgment}, sigma))
    | TryWithExp (e, match1, more_matches) ->
      let rec get_match_pf_subst sigma0 matches =
          (match matches with [] -> Some ([], sigma0)
           | (int_opt, exp) :: more ->
             (match gather_ty_substitution
                    {gamma = env_lift_subst sigma0 gamma; exp = exp;
                     monoTy = monoTy_lift_subst sigma0 tau}
              with None -> None
              | Some (pf, sigma) ->
                (match get_match_pf_subst (subst_compose sigma sigma0) more
                 with None -> None
                 | Some (pfl', sigma') -> Some(pf::pfl', sigma'))))
      in
      (match gather_ty_substitution {gamma = gamma; exp = e; monoTy = tau}
       with None -> None
       | Some (e_pf, sigma0) -> 
         (match get_match_pf_subst sigma0 (match1 :: more_matches)
          with None -> None
          | Some (match_pfs, sigma0m) ->
            Some({antecedents=e_pf::match_pfs; conclusion = judgment},sigma0m)))

