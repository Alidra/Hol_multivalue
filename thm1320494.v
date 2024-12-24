Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1320494_term_abbrevs.
Require Import NADD_ADD_LCANCEL_spec.
Require Import thm1317906_spec.
Require Import thm1317911_spec.
Require Import thm1318759_spec.
Require Import thm1318760_spec.
Require Import thm1318766_spec.
Require Import thm1318767_spec.
Lemma lem1320338 (x : nadd) (y : nadd) : (nadd_eq x y) = ((term0 x) = (term0 y)).
Proof. exact (EQ_MP (@lem1318767 x y) (@lem1318766 x y)). Qed.
Lemma lem1320339 (y : nadd) (x : nadd) (z : nadd) : (term1 y x z) = ((term2 x y) = (term2 x z)).
Proof. exact (@lem1320338 (nadd_add x y) (nadd_add x z)). Qed.
Lemma lem1320343 (x : nadd) (y : nadd) : (term2 x y) = (term3 x y).
Proof. exact (EQ_MP (@lem1317911 x y) (@lem1317906 x y)). Qed.
Lemma lem1320344 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1320345 (x : nadd) (y : nadd) : (term4 x y) = (term5 x y).
Proof. exact (MK_COMB (@lem1320344) (@lem1320343 x y)). Qed.
Lemma lem1320347 (x : nadd) (y : nadd) : (term2 x y) = (term3 x y).
Proof. exact (EQ_MP (@lem1317911 x y) (@lem1317906 x y)). Qed.
Lemma lem1320348 (x : nadd) (z : nadd) : (term2 x z) = (term3 x z).
Proof. exact (@lem1320347 x z). Qed.
Lemma lem1320349 (y : nadd) (x : nadd) (z : nadd) : ((term2 x y) = (term2 x z)) = ((term3 x y) = (term3 x z)).
Proof. exact (MK_COMB (@lem1320345 x y) (@lem1320348 x z)). Qed.
Lemma lem1320352 (y : nadd) (x : nadd) (z : nadd) : (term1 y x z) = ((term3 x y) = (term3 x z)).
Proof. exact (TRANS (@lem1320339 y x z) (@lem1320349 y x z)). Qed.
Lemma lem1320353 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1320354 (y : nadd) (x : nadd) (z : nadd) : (term6 y x z) = (term7 y x z).
Proof. exact (MK_COMB (@lem1320353) (@lem1320352 y x z)). Qed.
Lemma lem1320356 (x : nadd) (y : nadd) : (nadd_eq x y) = ((term0 x) = (term0 y)).
Proof. exact (EQ_MP (@lem1318767 x y) (@lem1318766 x y)). Qed.
Lemma lem1320357 (y : nadd) (z : nadd) : (nadd_eq y z) = ((term0 y) = (term0 z)).
Proof. exact (@lem1320356 y z). Qed.
Lemma lem1320360 (x : nadd) (y : nadd) (z : nadd) : (term8 x y z) = (term9 x y z).
Proof. exact (MK_COMB (@lem1320354 y x z) (@lem1320357 y z)). Qed.
Lemma lem1320365 (x : nadd) (y : nadd) : (term10 x y) = (term11 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1320360 x y z)). Qed.
Lemma lem1320366 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1320367 (x : nadd) (y : nadd) : (term12 x y) = (term13 x y).
Proof. exact (MK_COMB (@lem1320366) (@lem1320365 x y)). Qed.
Lemma lem1320373 (P : hreal -> Prop) : (term14 P) = (term15 P).
Proof. exact (EQ_MP (@lem1318760 P) (@lem1318759 P)). Qed.
Lemma lem1320374 (x : nadd) (y : nadd) : (term16 x y) = (term17 x y).
Proof. exact (@lem1320373 (term18 x y)). Qed.
Lemma lem1320375 (x : nadd) (y : nadd) (z : nadd) : (term19 x y z) = (term9 x y z).
Proof. exact (eq_refl (term19 x y z)). Qed.
Lemma lem1320376 (x : nadd) (y : nadd) : (term20 x y) = (term11 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1320375 x y z)). Qed.
Lemma lem1320377 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1320378 (x : nadd) (y : nadd) : (term16 x y) = (term13 x y).
Proof. exact (MK_COMB (@lem1320377) (@lem1320376 x y)). Qed.
Lemma lem1320379 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1320380 (x : nadd) (y : nadd) : (term21 x y) = (term22 x y).
Proof. exact (MK_COMB (@lem1320379) (@lem1320378 x y)). Qed.
Lemma lem1320381 (x : nadd) (y : nadd) (z : hreal) : (term23 x y z) = (term24 x y z).
Proof. exact (eq_refl (term23 x y z)). Qed.
Lemma lem1320382 (x : nadd) (y : nadd) : (term25 x y) = (term18 x y).
Proof. exact (fun_ext (fun z : hreal => @lem1320381 x y z)). Qed.
Lemma lem1320383 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1320384 (x : nadd) (y : nadd) : (term17 x y) = (term26 x y).
Proof. exact (MK_COMB (@lem1320383) (@lem1320382 x y)). Qed.
Lemma lem1320385 (x : nadd) (y : nadd) : ((term16 x y) = (term17 x y)) = ((term13 x y) = (term26 x y)).
Proof. exact (MK_COMB (@lem1320380 x y) (@lem1320384 x y)). Qed.
Lemma lem1320386 (x : nadd) (y : nadd) : (term13 x y) = (term26 x y).
Proof. exact (EQ_MP (@lem1320385 x y) (@lem1320374 x y)). Qed.
Lemma lem1320401 (x : nadd) (y : nadd) : (term12 x y) = (term26 x y).
Proof. exact (TRANS (@lem1320367 x y) (@lem1320386 x y)). Qed.
Lemma lem1320402 (x : nadd) : (term27 x) = (term28 x).
Proof. exact (fun_ext (fun y : nadd => @lem1320401 x y)). Qed.
Lemma lem1320403 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1320404 (x : nadd) : (term29 x) = (term30 x).
Proof. exact (MK_COMB (@lem1320403) (@lem1320402 x)). Qed.
Lemma lem1320410 (P : hreal -> Prop) : (term14 P) = (term15 P).
Proof. exact (EQ_MP (@lem1318760 P) (@lem1318759 P)). Qed.
Lemma lem1320411 (x : nadd) : (term31 x) = (term32 x).
Proof. exact (@lem1320410 (term33 x)). Qed.
Lemma lem1320412 (x : nadd) (y : nadd) : (term34 x y) = (term26 x y).
Proof. exact (eq_refl (term34 x y)). Qed.
Lemma lem1320413 (x : nadd) : (term35 x) = (term28 x).
Proof. exact (fun_ext (fun y : nadd => @lem1320412 x y)). Qed.
Lemma lem1320414 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1320415 (x : nadd) : (term31 x) = (term30 x).
Proof. exact (MK_COMB (@lem1320414) (@lem1320413 x)). Qed.
Lemma lem1320416 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1320417 (x : nadd) : (term36 x) = (term37 x).
Proof. exact (MK_COMB (@lem1320416) (@lem1320415 x)). Qed.
Lemma lem1320418 (x : nadd) (y : hreal) : (term38 x y) = (term39 x y).
Proof. exact (eq_refl (term38 x y)). Qed.
Lemma lem1320419 (x : nadd) : (term40 x) = (term33 x).
Proof. exact (fun_ext (fun y : hreal => @lem1320418 x y)). Qed.
Lemma lem1320420 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1320421 (x : nadd) : (term32 x) = (term41 x).
Proof. exact (MK_COMB (@lem1320420) (@lem1320419 x)). Qed.
Lemma lem1320422 (x : nadd) : ((term31 x) = (term32 x)) = ((term30 x) = (term41 x)).
Proof. exact (MK_COMB (@lem1320417 x) (@lem1320421 x)). Qed.
Lemma lem1320423 (x : nadd) : (term30 x) = (term41 x).
Proof. exact (EQ_MP (@lem1320422 x) (@lem1320411 x)). Qed.
Lemma lem1320444 (x : nadd) : (term29 x) = (term41 x).
Proof. exact (TRANS (@lem1320404 x) (@lem1320423 x)). Qed.
Lemma lem1320445 : term42 = term43.
Proof. exact (fun_ext (fun x : nadd => @lem1320444 x)). Qed.
Lemma lem1320446 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1320447 : term44 = term45.
Proof. exact (MK_COMB (@lem1320446) (@lem1320445)). Qed.
Lemma lem1320453 (P : hreal -> Prop) : (term14 P) = (term15 P).
Proof. exact (EQ_MP (@lem1318760 P) (@lem1318759 P)). Qed.
Lemma lem1320454 : term46 = term47.
Proof. exact (@lem1320453 term48). Qed.
Lemma lem1320455 (x : nadd) : (term49 x) = (term41 x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem1320456 : term50 = term43.
Proof. exact (fun_ext (fun x : nadd => @lem1320455 x)). Qed.
Lemma lem1320457 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1320458 : term46 = term45.
Proof. exact (MK_COMB (@lem1320457) (@lem1320456)). Qed.
Lemma lem1320459 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1320460 : term51 = term52.
Proof. exact (MK_COMB (@lem1320459) (@lem1320458)). Qed.
Lemma lem1320461 (x : hreal) : (term53 x) = (term54 x).
Proof. exact (eq_refl (term53 x)). Qed.
Lemma lem1320462 : term55 = term48.
Proof. exact (fun_ext (fun x : hreal => @lem1320461 x)). Qed.
Lemma lem1320463 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1320464 : term47 = term56.
Proof. exact (MK_COMB (@lem1320463) (@lem1320462)). Qed.
Lemma lem1320465 : (term46 = term47) = (term45 = term56).
Proof. exact (MK_COMB (@lem1320460) (@lem1320464)). Qed.
Lemma lem1320466 : term45 = term56.
Proof. exact (EQ_MP (@lem1320465) (@lem1320454)). Qed.
Lemma lem1320493 : term44 = term56.
Proof. exact (TRANS (@lem1320447) (@lem1320466)). Qed.
Lemma lem1320494 : term56.
Proof. exact (EQ_MP (@lem1320493) (@lem1274950)). Qed.
