From Coq Require Import ZArith.ZArith Sets.Ensembles Lists.List Classes.RelationClasses.
From compcert.lib Require Export Maps.
From CertiCoq.LambdaANF Require Import Ensembles_util map_util set_util List_util tactics.
From CertiCoq.Libraries Require Import maps_util.
Import ListNotations.
Require Import Lia.

From Framework Require Import Comp1 TrivialAnnotate.

Module CompWithTrivialAnnotate := Comp1.M TrivialAnnotate.M.
