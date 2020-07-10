(** val rw_uncurry : (exp_univ, exp_univ trivial_delay_t, r_C, s) rewriter **)

let rec rw_uncurry x a c e _ r s0 =
  match x with
  | XI _ | XO _ ->
    (match a with
     | Exp_univ_prod_ctor_tag_exp ->
       let Pair (c0, e0) = e in
       let { resTree = x0; resState = s1 } =
         rw_uncurry (Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_prod_ctor_tag_exp,
           Exp_univ_exp, ((Pair_ctor_tag_exp1 c0)), c)) e0 Tt r s0
       in
       { resTree = (Pair (c0, x0)); resState = s1 }
     | Exp_univ_list_prod_ctor_tag_exp ->
       (match e with
         | Nil -> { resTree = Nil; resState = s0 }
         | Cons (lpcte, r_C0) ->
           let { resTree = x0; resState = s1 } =
             rw_uncurry (Pos.pred x) Exp_univ_prod_ctor_tag_exp (Frames_cons (Exp_univ_prod_ctor_tag_exp,
               Exp_univ_list_prod_ctor_tag_exp, Exp_univ_exp, Cons_prod_ctor_tag_exp0 lpcte, c))
               p Tt r_C0 s0
           in
           let { resTree = x1; resState = s2 } =
             rw_uncurry (Pos.pred x) Exp_univ_list_prod_ctor_tag_exp (Frames_cons
               (Exp_univ_list_prod_ctor_tag_exp, Exp_univ_list_prod_ctor_tag_exp, Exp_univ_exp,
               Cons_prod_ctor_tag_exp1 x0, c)) lpcte Tt r_C0 s1
           in
           { resTree = Cons (x0, (x1)); resState = s2 })
     | Exp_univ_fundef ->
       let Ffun (f, ft, xs, e0) = e in
       let { resTree = x2; resState = s1 } =
         rw_uncurry (Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_fundef, Exp_univ_exp,
           Ffun3 (f, ft, xs), c)) e0 Tt r s0
       in
       { resTree = Ffun (f, ft, xs, x2); resState = s1 }
     | Exp_univ_list_fundef ->
       let { resTree = e'; resState = s' } =
         match e, s0 with
         | Nil, _ -> { resTree = Nil; resState = s0 }
         | Cons (
             Ffun (f0, ft, Cons (v, l0),
               Efun0 (Cons (Ffun (f2, ft0, xs0, e2), Nil), Eapp0 (f3, ft1, Cons (v0, Nil)))),
             u), Pair (Pair (Pair (Pair (Pair (b, _), x0), _), _), s1)
           when (match eq_var v f3, eq_var f2 v0, r,
                       negb (match Coq0_M.get f2 x0 with Some b0 -> b0 | None -> False),
                       occurs_in_exp f2 (iso_exp.isoBofA e2),
                       occurs_in_exp v (iso_exp.isoBofA e2)
                 with
                 | True, True, True, True, False, False -> true
                 | _, _ -> false) ->
           let Pair (ft2, ms') = get_fun_tag (N.of_nat (add (length l0) (length xs0))) ms in
           let Pair (next_x0, gv1) = gensyms s1 xs0 in
           let Pair (next_x1, fv1) = gensyms next_x0 l0 in
           let f4 = f0 in
           let f5 = next_x1 in
           let ft3 = ft in
           let ft4 = ft2 in
           let k = v in
           let kt = ft1 in
           let fv = l0 in
           let fv2 = fv1 in
           let g = f2 in
           let gt = ft0 in
           let gv = xs0 in
           let gv2 = gv1 in
           let ge = e2 in
           let { resTree = x1; resState = s2 } =
             rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons
               (Exp_univ_list_fundef, Exp_univ_list_fundef, Exp_univ_exp,
               ((Cons_fundef1 (Ffun (f5, ft4, (app gv fv), ge)))),
               (Frames_cons (Exp_univ_list_fundef, Exp_univ_list_fundef,
               Exp_univ_exp,
               ((Cons_fundef1 (Ffun (f4, ft3, (Cons (k, fv2)), (Efun0
                 ((Cons ((Ffun (g, gt, gv2, (Eapp0 (f5, ft4, (app gv2 fv2))))),
                 Nil)), (Eapp0 (k, kt, (Cons (g, Nil)))))))))), c))))
               u Tt b
               (Pair ((metadata_update f0 (iso_var.isoAofB f2)
                      (iso_var.isoAofB next_x1) (add (length l0) (length xs0))
                      l0 xs0 fv1 gv1 ms'), (Pos.add next_x1 XH)))
           in
           { resTree =
             Cons (Ffun (f4, ft3, Cons (k, fv2), (Efun0 (Cons
               (Ffun (g, gt, gv2, Eapp0 (f5, ft4, app gv2 fv2)), Nil),
               Eapp0 (k, kt, (Cons (g, Nil)))))),
               Cons (Ffun (f5, ft4, app gv fv, ge), x1)); resState = s2 }
         | ... -> ...
       in
       { resTree = e'; resState = s' }
     | Exp_univ_exp ->
       (match e with
        | Econstr0 (x0, c0, ys, u) ->
          let { resTree = x2; resState = s1 } =
            rw_uncurry (Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_exp, Exp_univ_exp,
              Econstr4 (x0, c0, ys), c)) u Tt r s0
          in
          { resTree = Econstr0 (x0, c0, ys, x2); resState = s1 }
        | Ecase0 (x0, ces) ->
          let { resTree = x1; resState = s1 } =
            rw_uncurry (Pos.pred x) Exp_univ_list_prod_ctor_tag_exp (Frames_cons
              (Exp_univ_list_prod_ctor_tag_exp, Exp_univ_exp, Exp_univ_exp, Ecase2 x0, c)) ces Tt r s0 
          in
          { resTree = Ecase0 (x0, x1); resState = s1 }
        | Eproj0 (x0, c0, n0, y, u) ->
          let { resTree = x3; resState = s1 } =
            rw_uncurry (Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_exp, Exp_univ_exp,
              Eproj5 (x0, c0, n0, y), c)) u Tt r s0
          in
          { resTree = Eproj0 (x0, c0, n0, y, x3); resState = s1 }
        | Eletapp0 (x0, f, ft, ys, u) ->
          let { resTree = x3; resState = s1 } =
            rw_uncurry (Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_exp, Exp_univ_exp,
              Eletapp5 (x0, f, ft, ys), c)) u Tt r s0 
          in
          { resTree = Eletapp0 (x0, f, ft, ys, x3); resState = s1 }
        | Efun0 (fds, e0) ->
          let { resTree = x0; resState = s1 } =
            rw_uncurry (Pos.pred x) Exp_univ_list_fundef (Frames_cons (Exp_univ_list_fundef, Exp_univ_exp,
              Exp_univ_exp, Efun1 e0, c)) fds Tt r s0
          in
          let { resTree = x1; resState = s2 } =
            rw_uncurry (Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_exp, Exp_univ_exp,
              Efun2 x0, c)) e0 Tt r s1
          in
          { resTree = Efun0 (x0, x1); resState = s2 }
        | Eapp0 (f, ft, xs) -> { resTree = Eapp0 (f, ft, xs); resState = s0 }
        | Eprim0 (x0, p, ys, u) ->
          let { resTree = x2; resState = s1 } =
            rw_uncurry (Pos.pred x) Exp_univ_exp (Frames_cons (Exp_univ_exp, Exp_univ_exp, Exp_univ_exp,
              Eprim4 (x0, p, ys), c)) u Tt r s0 
          in
          { resTree = Eprim0 (x0, p, ys, x2); resState = s1 }
        | Ehalt0 x0 ->
          { resTree = Ehalt0 x0; resState = s0 })
     | _ -> { resTree = e; resState = s0 })
  | XH -> { resTree = e; resState = s0 }
