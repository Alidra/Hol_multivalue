Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_IN_CROSS_term_abbrevs.
Require Import CONJ_ASSOC_spec.
Require Import EXISTS_PAIR_THM_spec.
Require Import IN_CROSS_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem4334375 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term0 t1 t2 t3) = (term1 t1 t2 t3)) : (term0 t1 t2 t3) = (term1 t1 t2 t3).
Proof. exact (h1). Qed.
Lemma lem4334376 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term0 t1 t2 t3) = (term1 t1 t2 t3)) : (term1 t1 t2 t3) = (term0 t1 t2 t3).
Proof. exact (SYM (@lem4334375 t1 t2 t3 h1)). Qed.
Lemma lem4334377 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term1 t1 t2 t3) = (term0 t1 t2 t3)) : (term1 t1 t2 t3) = (term0 t1 t2 t3).
Proof. exact (h1). Qed.
Lemma lem4334378 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term1 t1 t2 t3) = (term0 t1 t2 t3)) : (term0 t1 t2 t3) = (term1 t1 t2 t3).
Proof. exact (SYM (@lem4334377 t1 t2 t3 h1)). Qed.
Lemma lem4334379 (t1 : Prop) (t2 : Prop) (t3 : Prop) : ((term0 t1 t2 t3) = (term1 t1 t2 t3)) = ((term1 t1 t2 t3) = (term0 t1 t2 t3)).
Proof. exact (prop_ext (fun h1 : (term0 t1 t2 t3) = (term1 t1 t2 t3) => @lem4334376 t1 t2 t3 h1) (fun h1 : (term1 t1 t2 t3) = (term0 t1 t2 t3) => @lem4334378 t1 t2 t3 h1)). Qed.
Lemma lem4334380 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (fun_ext (fun t3 : Prop => @lem4334379 t1 t2 t3)). Qed.
Lemma lem4334381 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem4334382 (t1 : Prop) (t2 : Prop) : (term4 t1 t2) = (term5 t1 t2).
Proof. exact (MK_COMB (@lem4334381) (@lem4334380 t1 t2)). Qed.
Lemma lem4334383 (t1 : Prop) : (term6 t1) = (term7 t1).
Proof. exact (fun_ext (fun t2 : Prop => @lem4334382 t1 t2)). Qed.
Lemma lem4334384 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem4334385 (t1 : Prop) : (term8 t1) = (term9 t1).
Proof. exact (MK_COMB (@lem4334384) (@lem4334383 t1)). Qed.
Lemma lem4334386 : term10 = term11.
Proof. exact (fun_ext (fun t1 : Prop => @lem4334385 t1)). Qed.
Lemma lem4334387 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem4334388 : term12 = term13.
Proof. exact (MK_COMB (@lem4334387) (@lem4334386)). Qed.
Lemma lem4334389 : term13.
Proof. exact (EQ_MP (@lem4334388) (@lem512)). Qed.
Lemma lem4334390 {_103718 _103721 : Type'} (x : _103718) : term14 _103718 _103721 x.
Proof. exact (@lem4325365 _103718 _103721 x). Qed.
Lemma lem4334391 {_103718 _103721 : Type'} (x : _103718) : (term14 _103718 _103721 x) = (term15 _103718 _103721 x).
Proof. exact (eq_refl (term14 _103718 _103721 x)). Qed.
Lemma lem4334392 {_103718 _103721 : Type'} (x : _103718) : term15 _103718 _103721 x.
Proof. exact (EQ_MP (@lem4334391 _103718 _103721 x) (@lem4334390 _103718 _103721 x)). Qed.
Lemma lem4334393 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : term16 _103718 _103721 x y.
Proof. exact (@lem4334392 _103718 _103721 x y). Qed.
Lemma lem4334394 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : (term16 _103718 _103721 x y) = (term17 _103718 _103721 x y).
Proof. exact (eq_refl (term16 _103718 _103721 x y)). Qed.
Lemma lem4334395 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : term17 _103718 _103721 x y.
Proof. exact (EQ_MP (@lem4334394 _103718 _103721 x y) (@lem4334393 _103718 _103721 x y)). Qed.
Lemma lem4334396 {_103718 _103721 : Type'} (x : _103718) (y : _103721) (s : _103718 -> Prop) : term18 _103718 _103721 x y s.
Proof. exact (@lem4334395 _103718 _103721 x y s). Qed.
Lemma lem4334397 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : (term18 _103718 _103721 x y s) = (term19 _103718 _103721 x s y).
Proof. exact (eq_refl (term18 _103718 _103721 x y s)). Qed.
Lemma lem4334398 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : term19 _103718 _103721 x s y.
Proof. exact (EQ_MP (@lem4334397 _103718 _103721 x s y) (@lem4334396 _103718 _103721 x y s)). Qed.
Lemma lem4334399 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : term20 _103718 _103721 x s y t.
Proof. exact (@lem4334398 _103718 _103721 x s y t). Qed.
Lemma lem4334400 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term20 _103718 _103721 x s y t) = ((term21 _103718 _103721 x y s t) = (term22 _103718 _103721 x s y t)).
Proof. exact (eq_refl (term20 _103718 _103721 x s y t)). Qed.
Lemma lem4334402 (t1 : Prop) : term23 t1.
Proof. exact (@lem4334389 t1). Qed.
Lemma lem4334403 (t1 : Prop) : (term23 t1) = (term9 t1).
Proof. exact (eq_refl (term23 t1)). Qed.
Lemma lem4334404 (t1 : Prop) : term9 t1.
Proof. exact (EQ_MP (@lem4334403 t1) (@lem4334402 t1)). Qed.
Lemma lem4334405 (t1 : Prop) (t2 : Prop) : term24 t1 t2.
Proof. exact (@lem4334404 t1 t2). Qed.
Lemma lem4334406 (t1 : Prop) (t2 : Prop) : (term24 t1 t2) = (term5 t1 t2).
Proof. exact (eq_refl (term24 t1 t2)). Qed.
Lemma lem4334407 (t1 : Prop) (t2 : Prop) : term5 t1 t2.
Proof. exact (EQ_MP (@lem4334406 t1 t2) (@lem4334405 t1 t2)). Qed.
Lemma lem4334408 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term25 t1 t2 t3.
Proof. exact (@lem4334407 t1 t2 t3). Qed.
Lemma lem4334409 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term25 t1 t2 t3) = ((term1 t1 t2 t3) = (term0 t1 t2 t3)).
Proof. exact (eq_refl (term25 t1 t2 t3)). Qed.
Lemma lem4334411 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : term26 _5131 _5132 P.
Proof. exact (@lem51006 _5131 _5132 P). Qed.
Lemma lem4334412 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term26 _5131 _5132 P) = ((term27 _5131 _5132 P) = (term28 _5131 _5132 P)).
Proof. exact (eq_refl (term26 _5131 _5132 P)). Qed.
Lemma lem4334433 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term27 _5131 _5132 P) = (term28 _5131 _5132 P).
Proof. exact (EQ_MP (@lem4334412 _5131 _5132 P) (@lem4334411 _5131 _5132 P)). Qed.
Lemma lem4334434 {_104151 _104152 : Type'} (P : type1223 _104151 _104152) : (term27 _104151 _104152 P) = (term28 _104151 _104152 P).
Proof. exact (@lem4334433 _104151 _104152 P). Qed.
Lemma lem4334435 {_104151 _104152 : Type'} (s : _104152 -> Prop) (t : _104151 -> Prop) (P : type1223 _104151 _104152) : (term29 _104151 _104152 s t P) = (term30 _104151 _104152 s t P).
Proof. exact (@lem4334434 _104151 _104152 (term31 _104151 _104152 s t P)). Qed.
Lemma lem4334436 {_104151 _104152 : Type'} (s : _104152 -> Prop) (t : _104151 -> Prop) (P : type1223 _104151 _104152) (z : prod _104152 _104151) : (term32 _104151 _104152 s t P z) = (term33 _104151 _104152 s t P z).
Proof. exact (eq_refl (term32 _104151 _104152 s t P z)). Qed.
Lemma lem4334437 {_104151 _104152 : Type'} (s : _104152 -> Prop) (t : _104151 -> Prop) (P : type1223 _104151 _104152) : (term34 _104151 _104152 s t P) = (term31 _104151 _104152 s t P).
Proof. exact (fun_ext (fun z : prod _104152 _104151 => @lem4334436 _104151 _104152 s t P z)). Qed.
Lemma lem4334438 {_104151 _104152 : Type'} : (@ex (prod _104152 _104151)) = (@ex (prod _104152 _104151)).
Proof. exact (eq_refl (@ex (prod _104152 _104151))). Qed.
Lemma lem4334439 {_104151 _104152 : Type'} (s : _104152 -> Prop) (t : _104151 -> Prop) (P : type1223 _104151 _104152) : (term29 _104151 _104152 s t P) = (term35 _104151 _104152 s t P).
Proof. exact (MK_COMB (@lem4334438 _104151 _104152) (@lem4334437 _104151 _104152 s t P)). Qed.
Lemma lem4334440 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4334441 {_104151 _104152 : Type'} (s : _104152 -> Prop) (t : _104151 -> Prop) (P : type1223 _104151 _104152) : (term36 _104151 _104152 s t P) = (term37 _104151 _104152 s t P).
Proof. exact (MK_COMB (@lem4334440) (@lem4334439 _104151 _104152 s t P)). Qed.
Lemma lem4334442 {_104151 _104152 : Type'} (s : _104152 -> Prop) (t : _104151 -> Prop) (P : type1223 _104151 _104152) (p1 : _104152) (p2 : _104151) : (term38 _104151 _104152 s t P p1 p2) = (term39 _104151 _104152 s t P p1 p2).
Proof. exact (eq_refl (term38 _104151 _104152 s t P p1 p2)). Qed.
Lemma lem4334443 {_104151 _104152 : Type'} (s : _104152 -> Prop) (t : _104151 -> Prop) (P : type1223 _104151 _104152) (p1 : _104152) : (term40 _104151 _104152 s t P p1) = (term41 _104151 _104152 s t P p1).
Proof. exact (fun_ext (fun p2 : _104151 => @lem4334442 _104151 _104152 s t P p1 p2)). Qed.
Lemma lem4334444 {_104151 : Type'} : (@ex _104151) = (@ex _104151).
Proof. exact (eq_refl (@ex _104151)). Qed.
Lemma lem4334445 {_104151 _104152 : Type'} (s : _104152 -> Prop) (t : _104151 -> Prop) (P : type1223 _104151 _104152) (p1 : _104152) : (term42 _104151 _104152 s t P p1) = (term43 _104151 _104152 s t P p1).
Proof. exact (MK_COMB (@lem4334444 _104151) (@lem4334443 _104151 _104152 s t P p1)). Qed.
Lemma lem4334446 {_104151 _104152 : Type'} (s : _104152 -> Prop) (t : _104151 -> Prop) (P : type1223 _104151 _104152) : (term44 _104151 _104152 s t P) = (term45 _104151 _104152 s t P).
Proof. exact (fun_ext (fun p1 : _104152 => @lem4334445 _104151 _104152 s t P p1)). Qed.
Lemma lem4334447 {_104152 : Type'} : (@ex _104152) = (@ex _104152).
Proof. exact (eq_refl (@ex _104152)). Qed.
Lemma lem4334448 {_104151 _104152 : Type'} (s : _104152 -> Prop) (t : _104151 -> Prop) (P : type1223 _104151 _104152) : (term30 _104151 _104152 s t P) = (term46 _104151 _104152 s t P).
Proof. exact (MK_COMB (@lem4334447 _104152) (@lem4334446 _104151 _104152 s t P)). Qed.
Lemma lem4334449 {_104151 _104152 : Type'} (s : _104152 -> Prop) (t : _104151 -> Prop) (P : type1223 _104151 _104152) : ((term29 _104151 _104152 s t P) = (term30 _104151 _104152 s t P)) = ((term35 _104151 _104152 s t P) = (term46 _104151 _104152 s t P)).
Proof. exact (MK_COMB (@lem4334441 _104151 _104152 s t P) (@lem4334448 _104151 _104152 s t P)). Qed.
Lemma lem4334450 {_104151 _104152 : Type'} (s : _104152 -> Prop) (t : _104151 -> Prop) (P : type1223 _104151 _104152) : (term35 _104151 _104152 s t P) = (term46 _104151 _104152 s t P).
Proof. exact (EQ_MP (@lem4334449 _104151 _104152 s t P) (@lem4334435 _104151 _104152 s t P)). Qed.
Lemma lem4334466 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term21 _103718 _103721 x y s t) = (term22 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4334400 _103718 _103721 x s y t) (@lem4334399 _103718 _103721 x s y t)). Qed.
Lemma lem4334467 {_104151 _104152 : Type'} (x : _104152) (s : _104152 -> Prop) (y : _104151) (t : _104151 -> Prop) : (term47 _104151 _104152 x y s t) = (term48 _104151 _104152 x s y t).
Proof. exact (@lem4334466 _104152 _104151 x s y t). Qed.
Lemma lem4334468 {_104151 _104152 : Type'} (p1 : _104152) (s : _104152 -> Prop) (p2 : _104151) (t : _104151 -> Prop) : (term47 _104151 _104152 p1 p2 s t) = (term48 _104151 _104152 p1 s p2 t).
Proof. exact (@lem4334467 _104151 _104152 p1 s p2 t). Qed.
Lemma lem4334471 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4334472 {_104151 _104152 : Type'} (p1 : _104152) (s : _104152 -> Prop) (p2 : _104151) (t : _104151 -> Prop) : (term49 _104151 _104152 p1 p2 s t) = (term50 _104151 _104152 p1 s p2 t).
Proof. exact (MK_COMB (@lem4334471) (@lem4334468 _104151 _104152 p1 s p2 t)). Qed.
Lemma lem4334473 {_104151 _104152 : Type'} (P : type1223 _104151 _104152) (p1 : _104152) (p2 : _104151) : (term51 _104151 _104152 P p1 p2) = (term51 _104151 _104152 P p1 p2).
Proof. exact (eq_refl (term51 _104151 _104152 P p1 p2)). Qed.
Lemma lem4334474 {_104151 _104152 : Type'} (s : _104152 -> Prop) (t : _104151 -> Prop) (P : type1223 _104151 _104152) (p1 : _104152) (p2 : _104151) : (term39 _104151 _104152 s t P p1 p2) = (term52 _104151 _104152 s t P p1 p2).
Proof. exact (MK_COMB (@lem4334472 _104151 _104152 p1 s p2 t) (@lem4334473 _104151 _104152 P p1 p2)). Qed.
Lemma lem4334476 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term1 t1 t2 t3) = (term0 t1 t2 t3).
Proof. exact (EQ_MP (@lem4334409 t1 t2 t3) (@lem4334408 t1 t2 t3)). Qed.
Lemma lem4334477 {_104151 _104152 : Type'} (s : _104152 -> Prop) (t : _104151 -> Prop) (P : type1223 _104151 _104152) (p1 : _104152) (p2 : _104151) : (term52 _104151 _104152 s t P p1 p2) = (term53 _104151 _104152 s t P p1 p2).
Proof. exact (@lem4334476 (@IN _104152 p1 s) (@IN _104151 p2 t) (term51 _104151 _104152 P p1 p2)). Qed.
Lemma lem4334482 {_104151 _104152 : Type'} (s : _104152 -> Prop) (t : _104151 -> Prop) (P : type1223 _104151 _104152) (p1 : _104152) (p2 : _104151) : (term39 _104151 _104152 s t P p1 p2) = (term53 _104151 _104152 s t P p1 p2).
Proof. exact (TRANS (@lem4334474 _104151 _104152 s t P p1 p2) (@lem4334477 _104151 _104152 s t P p1 p2)). Qed.
Lemma lem4334483 {_104151 _104152 : Type'} (s : _104152 -> Prop) (t : _104151 -> Prop) (P : type1223 _104151 _104152) (p1 : _104152) : (term41 _104151 _104152 s t P p1) = (term54 _104151 _104152 s t P p1).
Proof. exact (fun_ext (fun p2 : _104151 => @lem4334482 _104151 _104152 s t P p1 p2)). Qed.
Lemma lem4334484 {_104151 : Type'} : (@ex _104151) = (@ex _104151).
Proof. exact (eq_refl (@ex _104151)). Qed.
Lemma lem4334485 {_104151 _104152 : Type'} (s : _104152 -> Prop) (t : _104151 -> Prop) (P : type1223 _104151 _104152) (p1 : _104152) : (term43 _104151 _104152 s t P p1) = (term55 _104151 _104152 s t P p1).
Proof. exact (MK_COMB (@lem4334484 _104151) (@lem4334483 _104151 _104152 s t P p1)). Qed.
Lemma lem4334492 {_104151 _104152 : Type'} (s : _104152 -> Prop) (t : _104151 -> Prop) (P : type1223 _104151 _104152) : (term45 _104151 _104152 s t P) = (term56 _104151 _104152 s t P).
Proof. exact (fun_ext (fun p1 : _104152 => @lem4334485 _104151 _104152 s t P p1)). Qed.
Lemma lem4334493 {_104152 : Type'} : (@ex _104152) = (@ex _104152).
Proof. exact (eq_refl (@ex _104152)). Qed.
Lemma lem4334494 {_104151 _104152 : Type'} (s : _104152 -> Prop) (t : _104151 -> Prop) (P : type1223 _104151 _104152) : (term46 _104151 _104152 s t P) = (term57 _104151 _104152 s t P).
Proof. exact (MK_COMB (@lem4334493 _104152) (@lem4334492 _104151 _104152 s t P)). Qed.
Lemma lem4334501 {_104151 _104152 : Type'} (s : _104152 -> Prop) (t : _104151 -> Prop) (P : type1223 _104151 _104152) : (term35 _104151 _104152 s t P) = (term57 _104151 _104152 s t P).
Proof. exact (TRANS (@lem4334450 _104151 _104152 s t P) (@lem4334494 _104151 _104152 s t P)). Qed.
Lemma lem4334502 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4334503 {_104151 _104152 : Type'} (s : _104152 -> Prop) (t : _104151 -> Prop) (P : type1223 _104151 _104152) : (term37 _104151 _104152 s t P) = (term58 _104151 _104152 s t P).
Proof. exact (MK_COMB (@lem4334502) (@lem4334501 _104151 _104152 s t P)). Qed.
Lemma lem4334520 {_104151 _104152 : Type'} (s : _104152 -> Prop) (t : _104151 -> Prop) (P : type1223 _104151 _104152) : (term57 _104151 _104152 s t P) = (term57 _104151 _104152 s t P).
Proof. exact (eq_refl (term57 _104151 _104152 s t P)). Qed.
Lemma lem4334521 {_104151 _104152 : Type'} (s : _104152 -> Prop) (t : _104151 -> Prop) (P : type1223 _104151 _104152) : ((term35 _104151 _104152 s t P) = (term57 _104151 _104152 s t P)) = ((term57 _104151 _104152 s t P) = (term57 _104151 _104152 s t P)).
Proof. exact (MK_COMB (@lem4334503 _104151 _104152 s t P) (@lem4334520 _104151 _104152 s t P)). Qed.
Lemma lem4334523 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4334524 (x : Prop) : (x = x) = True.
Proof. exact (@lem4334523 Prop x). Qed.
Lemma lem4334525 {_104151 _104152 : Type'} (s : _104152 -> Prop) (t : _104151 -> Prop) (P : type1223 _104151 _104152) : ((term57 _104151 _104152 s t P) = (term57 _104151 _104152 s t P)) = True.
Proof. exact (@lem4334524 (term57 _104151 _104152 s t P)). Qed.
Lemma lem4334528 {_104151 _104152 : Type'} (s : _104152 -> Prop) (t : _104151 -> Prop) (P : type1223 _104151 _104152) : (term59 _104151 _104152 s t P) = (term59 _104151 _104152 s t P).
Proof. exact (eq_refl (term59 _104151 _104152 s t P)). Qed.
Lemma lem4334529 {_104151 _104152 : Type'} (s : _104152 -> Prop) (t : _104151 -> Prop) (P : type1223 _104151 _104152) : (term59 _104151 _104152 s t P) = (((term57 _104151 _104152 s t P) = (term57 _104151 _104152 s t P)) = True).
Proof. exact (eq_refl (term59 _104151 _104152 s t P)). Qed.
Lemma lem4334530 {_104151 _104152 : Type'} (s : _104152 -> Prop) (t : _104151 -> Prop) (P : type1223 _104151 _104152) : (term60 _104151 _104152 s t P) = (term60 _104151 _104152 s t P).
Proof. exact (eq_refl (term60 _104151 _104152 s t P)). Qed.
Lemma lem4334531 {_104151 _104152 : Type'} (s : _104152 -> Prop) (t : _104151 -> Prop) (P : type1223 _104151 _104152) : ((term59 _104151 _104152 s t P) = (term59 _104151 _104152 s t P)) = ((term59 _104151 _104152 s t P) = (((term57 _104151 _104152 s t P) = (term57 _104151 _104152 s t P)) = True)).
Proof. exact (MK_COMB (@lem4334530 _104151 _104152 s t P) (@lem4334529 _104151 _104152 s t P)). Qed.
Lemma lem4334532 {_104151 _104152 : Type'} (s : _104152 -> Prop) (t : _104151 -> Prop) (P : type1223 _104151 _104152) : (term59 _104151 _104152 s t P) = (((term57 _104151 _104152 s t P) = (term57 _104151 _104152 s t P)) = True).
Proof. exact (eq_refl (term59 _104151 _104152 s t P)). Qed.
Lemma lem4334533 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4334534 {_104151 _104152 : Type'} (s : _104152 -> Prop) (t : _104151 -> Prop) (P : type1223 _104151 _104152) : (term60 _104151 _104152 s t P) = (term61 _104151 _104152 s t P).
Proof. exact (MK_COMB (@lem4334533) (@lem4334532 _104151 _104152 s t P)). Qed.
Lemma lem4334535 {_104151 _104152 : Type'} (s : _104152 -> Prop) (t : _104151 -> Prop) (P : type1223 _104151 _104152) : (((term57 _104151 _104152 s t P) = (term57 _104151 _104152 s t P)) = True) = (((term57 _104151 _104152 s t P) = (term57 _104151 _104152 s t P)) = True).
Proof. exact (eq_refl (((term57 _104151 _104152 s t P) = (term57 _104151 _104152 s t P)) = True)). Qed.
Lemma lem4334536 {_104151 _104152 : Type'} (s : _104152 -> Prop) (t : _104151 -> Prop) (P : type1223 _104151 _104152) : ((term59 _104151 _104152 s t P) = (((term57 _104151 _104152 s t P) = (term57 _104151 _104152 s t P)) = True)) = ((((term57 _104151 _104152 s t P) = (term57 _104151 _104152 s t P)) = True) = (((term57 _104151 _104152 s t P) = (term57 _104151 _104152 s t P)) = True)).
Proof. exact (MK_COMB (@lem4334534 _104151 _104152 s t P) (@lem4334535 _104151 _104152 s t P)). Qed.
Lemma lem4334537 {_104151 _104152 : Type'} (s : _104152 -> Prop) (t : _104151 -> Prop) (P : type1223 _104151 _104152) : ((term59 _104151 _104152 s t P) = (term59 _104151 _104152 s t P)) = ((((term57 _104151 _104152 s t P) = (term57 _104151 _104152 s t P)) = True) = (((term57 _104151 _104152 s t P) = (term57 _104151 _104152 s t P)) = True)).
Proof. exact (TRANS (@lem4334531 _104151 _104152 s t P) (@lem4334536 _104151 _104152 s t P)). Qed.
Lemma lem4334538 {_104151 _104152 : Type'} (s : _104152 -> Prop) (t : _104151 -> Prop) (P : type1223 _104151 _104152) : (((term57 _104151 _104152 s t P) = (term57 _104151 _104152 s t P)) = True) = (((term57 _104151 _104152 s t P) = (term57 _104151 _104152 s t P)) = True).
Proof. exact (EQ_MP (@lem4334537 _104151 _104152 s t P) (@lem4334528 _104151 _104152 s t P)). Qed.
Lemma lem4334539 {_104151 _104152 : Type'} (s : _104152 -> Prop) (t : _104151 -> Prop) (P : type1223 _104151 _104152) : ((term57 _104151 _104152 s t P) = (term57 _104151 _104152 s t P)) = True.
Proof. exact (EQ_MP (@lem4334538 _104151 _104152 s t P) (@lem4334525 _104151 _104152 s t P)). Qed.
Lemma lem4334540 {_104151 _104152 : Type'} (s : _104152 -> Prop) (t : _104151 -> Prop) (P : type1223 _104151 _104152) : ((term35 _104151 _104152 s t P) = (term57 _104151 _104152 s t P)) = True.
Proof. exact (TRANS (@lem4334521 _104151 _104152 s t P) (@lem4334539 _104151 _104152 s t P)). Qed.
Lemma lem4334541 {_104151 _104152 : Type'} (s : _104152 -> Prop) (P : type1223 _104151 _104152) : (term62 _104151 _104152 s P) = (term63 _104151).
Proof. exact (fun_ext (fun t : _104151 -> Prop => @lem4334540 _104151 _104152 s t P)). Qed.
Lemma lem4334542 {_104151 : Type'} : (@all (_104151 -> Prop)) = (@all (_104151 -> Prop)).
Proof. exact (eq_refl (@all (_104151 -> Prop))). Qed.
Lemma lem4334543 {_104151 _104152 : Type'} (s : _104152 -> Prop) (P : type1223 _104151 _104152) : (term64 _104151 _104152 s P) = (term65 _104151).
Proof. exact (MK_COMB (@lem4334542 _104151) (@lem4334541 _104151 _104152 s P)). Qed.
Lemma lem4334545 {A : Type'} (t : Prop) : (term66 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4334546 {_104151 : Type'} (t : Prop) : (term67 _104151 t) = t.
Proof. exact (@lem4334545 (_104151 -> Prop) t). Qed.
Lemma lem4334547 {_104151 : Type'} : (term65 _104151) = True.
Proof. exact (@lem4334546 _104151 True). Qed.
Lemma lem4334548 {_104151 _104152 : Type'} (s : _104152 -> Prop) (P : type1223 _104151 _104152) : (term64 _104151 _104152 s P) = True.
Proof. exact (TRANS (@lem4334543 _104151 _104152 s P) (@lem4334547 _104151)). Qed.
Lemma lem4334549 {_104151 _104152 : Type'} (P : type1223 _104151 _104152) : (term68 _104151 _104152 P) = (term63 _104152).
Proof. exact (fun_ext (fun s : _104152 -> Prop => @lem4334548 _104151 _104152 s P)). Qed.
Lemma lem4334550 {_104152 : Type'} : (@all (_104152 -> Prop)) = (@all (_104152 -> Prop)).
Proof. exact (eq_refl (@all (_104152 -> Prop))). Qed.
Lemma lem4334551 {_104151 _104152 : Type'} (P : type1223 _104151 _104152) : (term69 _104151 _104152 P) = (term65 _104152).
Proof. exact (MK_COMB (@lem4334550 _104152) (@lem4334549 _104151 _104152 P)). Qed.
Lemma lem4334553 {A : Type'} (t : Prop) : (term66 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4334554 {_104152 : Type'} (t : Prop) : (term67 _104152 t) = t.
Proof. exact (@lem4334553 (_104152 -> Prop) t). Qed.
Lemma lem4334555 {_104152 : Type'} : (term65 _104152) = True.
Proof. exact (@lem4334554 _104152 True). Qed.
Lemma lem4334556 {_104151 _104152 : Type'} (P : type1223 _104151 _104152) : (term69 _104151 _104152 P) = True.
Proof. exact (TRANS (@lem4334551 _104151 _104152 P) (@lem4334555 _104152)). Qed.
Lemma lem4334557 {_104151 _104152 : Type'} : (term70 _104151 _104152) = (term71 _104151 _104152).
Proof. exact (fun_ext (fun P : type1223 _104151 _104152 => @lem4334556 _104151 _104152 P)). Qed.
Lemma lem4334558 {_104151 _104152 : Type'} : (@all ((prod _104152 _104151) -> Prop)) = (@all ((prod _104152 _104151) -> Prop)).
Proof. exact (eq_refl (@all ((prod _104152 _104151) -> Prop))). Qed.
Lemma lem4334559 {_104151 _104152 : Type'} : (term72 _104151 _104152) = (term73 _104151 _104152).
Proof. exact (MK_COMB (@lem4334558 _104151 _104152) (@lem4334557 _104151 _104152)). Qed.
Lemma lem4334561 {A : Type'} (t : Prop) : (term66 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4334562 {_104151 _104152 : Type'} (t : Prop) : (term74 _104151 _104152 t) = t.
Proof. exact (@lem4334561 (type1223 _104151 _104152) t). Qed.
Lemma lem4334563 {_104151 _104152 : Type'} : (term73 _104151 _104152) = True.
Proof. exact (@lem4334562 _104151 _104152 True). Qed.
Lemma lem4334564 {_104151 _104152 : Type'} : (term72 _104151 _104152) = True.
Proof. exact (TRANS (@lem4334559 _104151 _104152) (@lem4334563 _104151 _104152)). Qed.
Lemma lem4334565 {_104151 _104152 : Type'} : True = (term72 _104151 _104152).
Proof. exact (SYM (@lem4334564 _104151 _104152)). Qed.
Lemma lem4334566 {_104151 _104152 : Type'} : term72 _104151 _104152.
Proof. exact (EQ_MP (@lem4334565 _104151 _104152) (@lem0)). Qed.
