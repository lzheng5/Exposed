From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.

From Framework Require Import Util ANF SemSubst.

(* Defunc

[[ let gf = fun [w_gf] () {f_work}
   let t = gf [w_gf] ()
   in case [w_work] t
      C => let t' = proj [w_work] t in t'
      ... ]]

let f_wrap = fun [w_wrap] (x) ->
                let f_work = C [w_work] f_wrap
                let g0 = fun [w_g0] () ->
                           [[ case [w_work] {f_work}
                              C => let t = proj [w_work] {f_work}
                                   in t
                              ... ]]
                let f = g0 [w_g0] ()
                in x + 1
let f_work = C [w_work] f_wrap
let g1 = fun [w_g1] () ->
            [[ case [w_work] {f_work}
               C => let t = proj [w_work] {f_work}
                    in t
               ... ]]
let f = g1 [w_g1] ()
let h = fun [w_h] (f') -> f' [w_wrap] 0
in h [w_h] f

~~>

let f_wrap = fun [w_wrap] (x) ->
                let f_work = C [w_work] f_wrap
                let g0 = fun [w_g0] () -> f_work
                let f = g0 [w_g0] ()
                in x + 1
let f_work = C [w_work] f_wrap
let g1 = fun [w_g1] () -> f_work
let f = g1 [w_g1] ()
let h = fun [w_h] (f') ->
          let g2 = fun [w_g2] () ->
                     case [w_work] f'
                     C => let t = proj [w_work] f'
                          in t
                     ...
          let f' = g2 [w_g2] ()
          f' [w_wrap] 0
in h [w_h] f

*)
