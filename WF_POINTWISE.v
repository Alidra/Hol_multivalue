Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import WF_POINTWISE_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import FORALL_PAIR_THM_spec.
Require Import WF_LEX_spec.
Require Import WF_SUBSET_spec.
Require Import thm0_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm48805_spec.
Require Import thm48806_spec.
Require Import thm48811_spec.
Require Import thm48812_spec.
Require Import thm48920_spec.
Require Import thm51128_spec.
Require Import thm51159_spec.
Require Import thm7_spec.
Lemma lem364346 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem364347 {A B : Type'} (R : type1402 A) (h1 : term0 A B) : term1 A B R.
Proof. exact (@lem364346 A B h1 R). Qed.
Lemma lem364348 {A B : Type'} (R : type1402 A) : (term1 A B R) = (term2 A B R).
Proof. exact (eq_refl (term1 A B R)). Qed.
Lemma lem364349 {A B : Type'} (R : type1402 A) (h1 : term0 A B) : term2 A B R.
Proof. exact (EQ_MP (@lem364348 A B R) (@lem364347 A B R h1)). Qed.
Lemma lem364350 {A B : Type'} (R : type1402 A) (S' : type1402 B) (h1 : term0 A B) : term3 A B R S'.
Proof. exact (@lem364349 A B R h1 S'). Qed.
Lemma lem364351 {A B : Type'} (R : type1402 A) (S' : type1402 B) : (term3 A B R S') = (term4 A B R S').
Proof. exact (eq_refl (term3 A B R S')). Qed.
Lemma lem364352 {A B : Type'} (R : type1402 A) (S' : type1402 B) (h1 : term0 A B) : term4 A B R S'.
Proof. exact (EQ_MP (@lem364351 A B R S') (@lem364350 A B R S' h1)). Qed.
Lemma lem364353 {A B : Type'} (R : type1402 A) (S' : type1402 B) (h1 : term5 A B R S') : term5 A B R S'.
Proof. exact (h1). Qed.
Lemma lem364354 {A B : Type'} (R : type1402 A) (S' : type1402 B) (h1 : term0 A B) (h2 : term5 A B R S') : term6 A B R S'.
Proof. exact (@lem364352 A B R S' h1 (@lem364353 A B R S' h2)). Qed.
Lemma lem364355 {A B : Type'} (R : type1402 A) (S' : type1402 B) (h1 : term5 A B R S') : term7 A B R S'.
Proof. exact (fun h0 : term0 A B => @lem364354 A B R S' h0 h1). Qed.
Lemma lem364356 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem364357 {A B : Type'} (R : type1402 A) (S' : type1402 B) (h1 : term0 A B) (h2 : term5 A B R S') : term6 A B R S'.
Proof. exact (@lem364355 A B R S' h2 (@lem364356 A B h1)). Qed.
Lemma lem364358 {A B : Type'} (R : type1402 A) (S' : type1402 B) (h1 : term0 A B) : term4 A B R S'.
Proof. exact (fun h0 : term5 A B R S' => @lem364357 A B R S' h1 h0). Qed.
Lemma lem364359 {A B : Type'} (R : type1402 A) (h1 : term0 A B) : term2 A B R.
Proof. exact (fun S' : type1402 B => @lem364358 A B R S' h1). Qed.
Lemma lem364360 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (fun R : type1402 A => @lem364359 A B R h1). Qed.
Lemma lem364361 {A B : Type'} : term8 A B.
Proof. exact (fun h0 : term0 A B => @lem364360 A B h0). Qed.
Lemma lem364362 {A B : Type'} : term0 A B.
Proof. exact (@lem364361 A B (@lem364345 A B)). Qed.
Lemma lem364363 {A B : Type'} (R : type1402 A) : term1 A B R.
Proof. exact (@lem364362 A B R). Qed.
Lemma lem364364 {A B : Type'} (R : type1402 A) : (term1 A B R) = (term2 A B R).
Proof. exact (eq_refl (term1 A B R)). Qed.
Lemma lem364365 {A B : Type'} (R : type1402 A) : term2 A B R.
Proof. exact (EQ_MP (@lem364364 A B R) (@lem364363 A B R)). Qed.
Lemma lem364366 {A B : Type'} (R : type1402 A) (S' : type1402 B) : term3 A B R S'.
Proof. exact (@lem364365 A B R S'). Qed.
Lemma lem364367 {A B : Type'} (R : type1402 A) (S' : type1402 B) : (term3 A B R S') = (term4 A B R S').
Proof. exact (eq_refl (term3 A B R S')). Qed.
Lemma lem364369 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term9 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem364370 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term9 _5106 _5107 P) = ((term10 _5106 _5107 P) = (term11 _5106 _5107 P)).
Proof. exact (eq_refl (term9 _5106 _5107 P)). Qed.
Lemma lem364372 {A : Type'} (h1 : term12 A) : term12 A.
Proof. exact (h1). Qed.
Lemma lem364373 {A : Type'} (lt2 : type1402 A) (h1 : term12 A) : term13 A lt2.
Proof. exact (@lem364372 A h1 lt2). Qed.
Lemma lem364374 {A : Type'} (lt2 : type1402 A) : (term13 A lt2) = (term14 A lt2).
Proof. exact (eq_refl (term13 A lt2)). Qed.
Lemma lem364375 {A : Type'} (lt2 : type1402 A) (h1 : term12 A) : term14 A lt2.
Proof. exact (EQ_MP (@lem364374 A lt2) (@lem364373 A lt2 h1)). Qed.
Lemma lem364376 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (h1 : term12 A) : term15 A lt2 lt3.
Proof. exact (@lem364375 A lt2 h1 lt3). Qed.
Lemma lem364377 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) : (term15 A lt2 lt3) = (term16 A lt3 lt2).
Proof. exact (eq_refl (term15 A lt2 lt3)). Qed.
Lemma lem364378 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (h1 : term12 A) : term16 A lt3 lt2.
Proof. exact (EQ_MP (@lem364377 A lt3 lt2) (@lem364376 A lt2 lt3 h1)). Qed.
Lemma lem364379 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (h1 : term17 A lt2 lt3) : term17 A lt2 lt3.
Proof. exact (h1). Qed.
Lemma lem364380 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (h1 : term12 A) (h2 : term17 A lt2 lt3) : @WF A lt2.
Proof. exact (@lem364378 A lt3 lt2 h1 (@lem364379 A lt2 lt3 h2)). Qed.
Lemma lem364381 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (h1 : term17 A lt2 lt3) : term18 A lt2.
Proof. exact (fun h0 : term12 A => @lem364380 A lt2 lt3 h0 h1). Qed.
Lemma lem364382 {A : Type'} (lt2 : type1402 A) (h1 : term19 A lt2) : term19 A lt2.
Proof. exact (h1). Qed.
Lemma lem364383 {A : Type'} (lt2 : type1402 A) (h1 : term19 A lt2) : term18 A lt2.
Proof. exact (ex_elim (@lem364382 A lt2 h1) (fun lt3 : type1402 A => fun h0 : term20 A lt2 lt3 => @lem364381 A lt2 lt3 h0)). Qed.
Lemma lem364384 {A : Type'} (h1 : term12 A) : term12 A.
Proof. exact (h1). Qed.
Lemma lem364385 {A : Type'} (lt2 : type1402 A) (h1 : term12 A) (h2 : term19 A lt2) : @WF A lt2.
Proof. exact (@lem364383 A lt2 h2 (@lem364384 A h1)). Qed.
Lemma lem364386 {A : Type'} (lt2 : type1402 A) (h1 : term12 A) : term21 A lt2.
Proof. exact (fun h0 : term19 A lt2 => @lem364385 A lt2 h1 h0). Qed.
Lemma lem364387 {A : Type'} (h1 : term12 A) : term22 A.
Proof. exact (fun lt2 : type1402 A => @lem364386 A lt2 h1). Qed.
Lemma lem364388 {A : Type'} : term23 A.
Proof. exact (fun h0 : term12 A => @lem364387 A h0). Qed.
Lemma lem364389 {A : Type'} : term22 A.
Proof. exact (@lem364388 A (@lem359527 A)). Qed.
Lemma lem364390 {A : Type'} (lt2 : type1402 A) : term24 A lt2.
Proof. exact (@lem364389 A lt2). Qed.
Lemma lem364391 {A : Type'} (lt2 : type1402 A) : (term24 A lt2) = (term21 A lt2).
Proof. exact (eq_refl (term24 A lt2)). Qed.
Lemma lem364393 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (h1 : term5 A B lt2 lt3) : term5 A B lt2 lt3.
Proof. exact (h1). Qed.
Lemma lem364394 {B : Type'} (lt3 : type1402 B) (h1 : @WF B lt3) : @WF B lt3.
Proof. exact (h1). Qed.
Lemma lem364395 {A : Type'} (lt2 : type1402 A) (h1 : @WF A lt2) : @WF A lt2.
Proof. exact (h1). Qed.
Lemma lem364397 {A : Type'} (lt2 : type1402 A) : term21 A lt2.
Proof. exact (EQ_MP (@lem364391 A lt2) (@lem364390 A lt2)). Qed.
Lemma lem364398 {A B : Type'} (lt2 : type1204 A B) : term25 A B lt2.
Proof. exact (@lem364397 (prod A B) lt2). Qed.
Lemma lem364399 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) : term26 A B lt2 lt3.
Proof. exact (@lem364398 A B (term27 A B lt2 lt3)). Qed.
Lemma lem364405 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term10 _5106 _5107 P) = (term11 _5106 _5107 P).
Proof. exact (EQ_MP (@lem364370 _5106 _5107 P) (@lem364369 _5106 _5107 P)). Qed.
Lemma lem364406 {A B : Type'} (P : type1210 A B) : (term28 A B P) = (term29 A B P).
Proof. exact (@lem364405 B A P). Qed.
Lemma lem364407 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) : (term30 A B lt2 lt3) = (term31 A B lt2 lt3).
Proof. exact (@lem364406 A B (term32 A B lt2 lt3)). Qed.
Lemma lem364408 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (x : prod A B) : (term33 A B lt2 lt3 x) = (term34 A B lt2 lt3 x).
Proof. exact (eq_refl (term33 A B lt2 lt3 x)). Qed.
Lemma lem364409 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) : (term35 A B lt2 lt3) = (term32 A B lt2 lt3).
Proof. exact (fun_ext (fun x : prod A B => @lem364408 A B lt2 lt3 x)). Qed.
Lemma lem364410 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem364411 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) : (term30 A B lt2 lt3) = (term36 A B lt2 lt3).
Proof. exact (MK_COMB (@lem364410 A B) (@lem364409 A B lt2 lt3)). Qed.
Lemma lem364412 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem364413 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) : (term37 A B lt2 lt3) = (term38 A B lt2 lt3).
Proof. exact (MK_COMB (@lem364412) (@lem364411 A B lt2 lt3)). Qed.
Lemma lem364414 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (p1 : A) (p2 : B) : (term39 A B lt2 lt3 p1 p2) = (term40 A B lt2 lt3 p1 p2).
Proof. exact (eq_refl (term39 A B lt2 lt3 p1 p2)). Qed.
Lemma lem364415 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (p1 : A) : (term41 A B lt2 lt3 p1) = (term42 A B lt2 lt3 p1).
Proof. exact (fun_ext (fun p2 : B => @lem364414 A B lt2 lt3 p1 p2)). Qed.
Lemma lem364416 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem364417 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (p1 : A) : (term43 A B lt2 lt3 p1) = (term44 A B lt2 lt3 p1).
Proof. exact (MK_COMB (@lem364416 B) (@lem364415 A B lt2 lt3 p1)). Qed.
Lemma lem364418 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) : (term45 A B lt2 lt3) = (term46 A B lt2 lt3).
Proof. exact (fun_ext (fun p1 : A => @lem364417 A B lt2 lt3 p1)). Qed.
Lemma lem364419 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem364420 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) : (term31 A B lt2 lt3) = (term47 A B lt2 lt3).
Proof. exact (MK_COMB (@lem364419 A) (@lem364418 A B lt2 lt3)). Qed.
Lemma lem364421 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) : ((term30 A B lt2 lt3) = (term31 A B lt2 lt3)) = ((term36 A B lt2 lt3) = (term47 A B lt2 lt3)).
Proof. exact (MK_COMB (@lem364413 A B lt2 lt3) (@lem364420 A B lt2 lt3)). Qed.
Lemma lem364422 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) : (term36 A B lt2 lt3) = (term47 A B lt2 lt3).
Proof. exact (EQ_MP (@lem364421 A B lt2 lt3) (@lem364407 A B lt2 lt3)). Qed.
Lemma lem364440 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term10 _5106 _5107 P) = (term11 _5106 _5107 P).
Proof. exact (EQ_MP (@lem364370 _5106 _5107 P) (@lem364369 _5106 _5107 P)). Qed.
Lemma lem364441 {A B : Type'} (P : type1210 A B) : (term28 A B P) = (term29 A B P).
Proof. exact (@lem364440 B A P). Qed.
Lemma lem364442 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (p1 : A) (p2 : B) : (term48 A B lt2 lt3 p1 p2) = (term49 A B lt2 lt3 p1 p2).
Proof. exact (@lem364441 A B (term50 A B lt2 lt3 p1 p2)). Qed.
Lemma lem364443 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (p1 : A) (p2 : B) (y : prod A B) : (term51 A B lt2 lt3 p1 p2 y) = (term52 A B lt2 lt3 p1 p2 y).
Proof. exact (eq_refl (term51 A B lt2 lt3 p1 p2 y)). Qed.
Lemma lem364444 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (p1 : A) (p2 : B) : (term53 A B lt2 lt3 p1 p2) = (term50 A B lt2 lt3 p1 p2).
Proof. exact (fun_ext (fun y : prod A B => @lem364443 A B lt2 lt3 p1 p2 y)). Qed.
Lemma lem364445 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem364446 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (p1 : A) (p2 : B) : (term48 A B lt2 lt3 p1 p2) = (term40 A B lt2 lt3 p1 p2).
Proof. exact (MK_COMB (@lem364445 A B) (@lem364444 A B lt2 lt3 p1 p2)). Qed.
Lemma lem364447 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem364448 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (p1 : A) (p2 : B) : (term54 A B lt2 lt3 p1 p2) = (term55 A B lt2 lt3 p1 p2).
Proof. exact (MK_COMB (@lem364447) (@lem364446 A B lt2 lt3 p1 p2)). Qed.
Lemma lem364449 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (p1 : A) (p2 : B) (p1' : A) (p2' : B) : (term56 A B lt2 lt3 p1 p2 p1' p2') = (term57 A B lt2 lt3 p1 p2 p1' p2').
Proof. exact (eq_refl (term56 A B lt2 lt3 p1 p2 p1' p2')). Qed.
Lemma lem364450 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (p1 : A) (p2 : B) (p1' : A) : (term58 A B lt2 lt3 p1 p2 p1') = (term59 A B lt2 lt3 p1 p2 p1').
Proof. exact (fun_ext (fun p2' : B => @lem364449 A B lt2 lt3 p1 p2 p1' p2')). Qed.
Lemma lem364451 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem364452 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (p1 : A) (p2 : B) (p1' : A) : (term60 A B lt2 lt3 p1 p2 p1') = (term61 A B lt2 lt3 p1 p2 p1').
Proof. exact (MK_COMB (@lem364451 B) (@lem364450 A B lt2 lt3 p1 p2 p1')). Qed.
Lemma lem364453 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (p1 : A) (p2 : B) : (term62 A B lt2 lt3 p1 p2) = (term63 A B lt2 lt3 p1 p2).
Proof. exact (fun_ext (fun p1' : A => @lem364452 A B lt2 lt3 p1 p2 p1')). Qed.
Lemma lem364454 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem364455 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (p1 : A) (p2 : B) : (term49 A B lt2 lt3 p1 p2) = (term64 A B lt2 lt3 p1 p2).
Proof. exact (MK_COMB (@lem364454 A) (@lem364453 A B lt2 lt3 p1 p2)). Qed.
Lemma lem364456 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (p1 : A) (p2 : B) : ((term48 A B lt2 lt3 p1 p2) = (term49 A B lt2 lt3 p1 p2)) = ((term40 A B lt2 lt3 p1 p2) = (term64 A B lt2 lt3 p1 p2)).
Proof. exact (MK_COMB (@lem364448 A B lt2 lt3 p1 p2) (@lem364455 A B lt2 lt3 p1 p2)). Qed.
Lemma lem364457 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (p1 : A) (p2 : B) : (term40 A B lt2 lt3 p1 p2) = (term64 A B lt2 lt3 p1 p2).
Proof. exact (EQ_MP (@lem364456 A B lt2 lt3 p1 p2) (@lem364442 A B lt2 lt3 p1 p2)). Qed.
Lemma lem364472 {A B : Type'} (a0 : A) (a1 : B) : a0 = (term65 A B a0 a1).
Proof. exact (@lem51128 A B a0 a1). Qed.
Lemma lem364473 {A B : Type'} (x1 : A) (y1 : B) : x1 = (term65 A B x1 y1).
Proof. exact (@lem364472 A B x1 y1). Qed.
Lemma lem364474 {A B : Type'} (a0 : A) (a1 : B) : a1 = (term66 A B a0 a1).
Proof. exact (@lem51159 A B a0 a1). Qed.
Lemma lem364475 {A B : Type'} (x1 : A) (y1 : B) : y1 = (term66 A B x1 y1).
Proof. exact (@lem364474 A B x1 y1). Qed.
Lemma lem364476 {A : Type'} (x1 : A) : x1 = x1.
Proof. exact (eq_refl x1). Qed.
Lemma lem364477 {A : Type'} : (term67 A) = (term67 A).
Proof. exact (eq_refl (term67 A)). Qed.
Lemma lem364478 {A B : Type'} (x1 : A) (y1 : B) : (term68 A x1) = (term69 A B x1 y1).
Proof. exact (MK_COMB (@lem364477 A) (@lem364473 A B x1 y1)). Qed.
Lemma lem364479 {A B : Type'} (x1 : A) (y1 : B) : (term69 A B x1 y1) = (term65 A B x1 y1).
Proof. exact (eq_refl (term69 A B x1 y1)). Qed.
Lemma lem364480 {A : Type'} (x1 : A) : (term70 A x1) = (term70 A x1).
Proof. exact (eq_refl (term70 A x1)). Qed.
Lemma lem364481 {A B : Type'} (x1 : A) (y1 : B) : ((term68 A x1) = (term69 A B x1 y1)) = ((term68 A x1) = (term65 A B x1 y1)).
Proof. exact (MK_COMB (@lem364480 A x1) (@lem364479 A B x1 y1)). Qed.
Lemma lem364482 {A : Type'} (x1 : A) : (term68 A x1) = x1.
Proof. exact (eq_refl (term68 A x1)). Qed.
Lemma lem364483 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem364484 {A : Type'} (x1 : A) : (term70 A x1) = (@eq A x1).
Proof. exact (MK_COMB (@lem364483 A) (@lem364482 A x1)). Qed.
Lemma lem364485 {A B : Type'} (x1 : A) (y1 : B) : (term65 A B x1 y1) = (term65 A B x1 y1).
Proof. exact (eq_refl (term65 A B x1 y1)). Qed.
Lemma lem364486 {A B : Type'} (x1 : A) (y1 : B) : ((term68 A x1) = (term65 A B x1 y1)) = (x1 = (term65 A B x1 y1)).
Proof. exact (MK_COMB (@lem364484 A x1) (@lem364485 A B x1 y1)). Qed.
Lemma lem364487 {A B : Type'} (x1 : A) (y1 : B) : ((term68 A x1) = (term69 A B x1 y1)) = (x1 = (term65 A B x1 y1)).
Proof. exact (TRANS (@lem364481 A B x1 y1) (@lem364486 A B x1 y1)). Qed.
Lemma lem364488 {A B : Type'} (x1 : A) (y1 : B) : x1 = (term65 A B x1 y1).
Proof. exact (EQ_MP (@lem364487 A B x1 y1) (@lem364478 A B x1 y1)). Qed.
Lemma lem364489 {A : Type'} (x1 : A) : (@eq A x1) = (@eq A x1).
Proof. exact (eq_refl (@eq A x1)). Qed.
Lemma lem364490 {A B : Type'} (x1 : A) (y1 : B) : (x1 = x1) = (x1 = (term65 A B x1 y1)).
Proof. exact (MK_COMB (@lem364489 A x1) (@lem364488 A B x1 y1)). Qed.
Lemma lem364491 {A B : Type'} (x1 : A) (y1 : B) : x1 = (term65 A B x1 y1).
Proof. exact (EQ_MP (@lem364490 A B x1 y1) (@lem364476 A x1)). Qed.
Lemma lem364492 {B : Type'} (y1 : B) : y1 = y1.
Proof. exact (eq_refl y1). Qed.
Lemma lem364493 {B : Type'} : (term67 B) = (term67 B).
Proof. exact (eq_refl (term67 B)). Qed.
Lemma lem364494 {A B : Type'} (x1 : A) (y1 : B) : (term68 B y1) = (term71 A B x1 y1).
Proof. exact (MK_COMB (@lem364493 B) (@lem364475 A B x1 y1)). Qed.
Lemma lem364495 {A B : Type'} (x1 : A) (y1 : B) : (term71 A B x1 y1) = (term66 A B x1 y1).
Proof. exact (eq_refl (term71 A B x1 y1)). Qed.
Lemma lem364496 {B : Type'} (y1 : B) : (term70 B y1) = (term70 B y1).
Proof. exact (eq_refl (term70 B y1)). Qed.
Lemma lem364497 {A B : Type'} (x1 : A) (y1 : B) : ((term68 B y1) = (term71 A B x1 y1)) = ((term68 B y1) = (term66 A B x1 y1)).
Proof. exact (MK_COMB (@lem364496 B y1) (@lem364495 A B x1 y1)). Qed.
Lemma lem364498 {B : Type'} (y1 : B) : (term68 B y1) = y1.
Proof. exact (eq_refl (term68 B y1)). Qed.
Lemma lem364499 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem364500 {B : Type'} (y1 : B) : (term70 B y1) = (@eq B y1).
Proof. exact (MK_COMB (@lem364499 B) (@lem364498 B y1)). Qed.
Lemma lem364501 {A B : Type'} (x1 : A) (y1 : B) : (term66 A B x1 y1) = (term66 A B x1 y1).
Proof. exact (eq_refl (term66 A B x1 y1)). Qed.
Lemma lem364502 {A B : Type'} (x1 : A) (y1 : B) : ((term68 B y1) = (term66 A B x1 y1)) = (y1 = (term66 A B x1 y1)).
Proof. exact (MK_COMB (@lem364500 B y1) (@lem364501 A B x1 y1)). Qed.
Lemma lem364503 {A B : Type'} (x1 : A) (y1 : B) : ((term68 B y1) = (term71 A B x1 y1)) = (y1 = (term66 A B x1 y1)).
Proof. exact (TRANS (@lem364497 A B x1 y1) (@lem364502 A B x1 y1)). Qed.
Lemma lem364504 {A B : Type'} (x1 : A) (y1 : B) : y1 = (term66 A B x1 y1).
Proof. exact (EQ_MP (@lem364503 A B x1 y1) (@lem364494 A B x1 y1)). Qed.
Lemma lem364505 {B : Type'} (y1 : B) : (@eq B y1) = (@eq B y1).
Proof. exact (eq_refl (@eq B y1)). Qed.
Lemma lem364506 {A B : Type'} (x1 : A) (y1 : B) : (y1 = y1) = (y1 = (term66 A B x1 y1)).
Proof. exact (MK_COMB (@lem364505 B y1) (@lem364504 A B x1 y1)). Qed.
Lemma lem364507 {A B : Type'} (x1 : A) (y1 : B) : y1 = (term66 A B x1 y1).
Proof. exact (EQ_MP (@lem364506 A B x1 y1) (@lem364492 B y1)). Qed.
Lemma lem364508 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) : (term72 A B lt2 lt3) = (term72 A B lt2 lt3).
Proof. exact (eq_refl (term72 A B lt2 lt3)). Qed.
Lemma lem364509 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (x1 : A) (y1 : B) : (term73 A B lt2 lt3 x1) = (term74 A B lt2 lt3 x1 y1).
Proof. exact (MK_COMB (@lem364508 A B lt2 lt3) (@lem364491 A B x1 y1)). Qed.
Lemma lem364510 {A B : Type'} (lt2 : type1402 A) (x1 : A) (y1 : B) (lt3 : type1402 B) : (term74 A B lt2 lt3 x1 y1) = (term75 A B lt2 x1 y1 lt3).
Proof. exact (eq_refl (term74 A B lt2 lt3 x1 y1)). Qed.
Lemma lem364511 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (x1 : A) : (term76 A B lt2 lt3 x1) = (term76 A B lt2 lt3 x1).
Proof. exact (eq_refl (term76 A B lt2 lt3 x1)). Qed.
Lemma lem364512 {A B : Type'} (lt2 : type1402 A) (x1 : A) (y1 : B) (lt3 : type1402 B) : ((term73 A B lt2 lt3 x1) = (term74 A B lt2 lt3 x1 y1)) = ((term73 A B lt2 lt3 x1) = (term75 A B lt2 x1 y1 lt3)).
Proof. exact (MK_COMB (@lem364511 A B lt2 lt3 x1) (@lem364510 A B lt2 x1 y1 lt3)). Qed.
Lemma lem364513 {A B : Type'} (lt2 : type1402 A) (x1 : A) (lt3 : type1402 B) : (term73 A B lt2 lt3 x1) = (term77 A B lt2 x1 lt3).
Proof. exact (eq_refl (term73 A B lt2 lt3 x1)). Qed.
Lemma lem364514 {A B : Type'} : (@eq (B -> (prod A B) -> Prop)) = (@eq (B -> (prod A B) -> Prop)).
Proof. exact (eq_refl (@eq (B -> (prod A B) -> Prop))). Qed.
Lemma lem364515 {A B : Type'} (lt2 : type1402 A) (x1 : A) (lt3 : type1402 B) : (term76 A B lt2 lt3 x1) = (term78 A B lt2 x1 lt3).
Proof. exact (MK_COMB (@lem364514 A B) (@lem364513 A B lt2 x1 lt3)). Qed.
Lemma lem364516 {A B : Type'} (lt2 : type1402 A) (x1 : A) (y1 : B) (lt3 : type1402 B) : (term75 A B lt2 x1 y1 lt3) = (term75 A B lt2 x1 y1 lt3).
Proof. exact (eq_refl (term75 A B lt2 x1 y1 lt3)). Qed.
Lemma lem364517 {A B : Type'} (lt2 : type1402 A) (x1 : A) (y1 : B) (lt3 : type1402 B) : ((term73 A B lt2 lt3 x1) = (term75 A B lt2 x1 y1 lt3)) = ((term77 A B lt2 x1 lt3) = (term75 A B lt2 x1 y1 lt3)).
Proof. exact (MK_COMB (@lem364515 A B lt2 x1 lt3) (@lem364516 A B lt2 x1 y1 lt3)). Qed.
Lemma lem364518 {A B : Type'} (lt2 : type1402 A) (x1 : A) (y1 : B) (lt3 : type1402 B) : ((term73 A B lt2 lt3 x1) = (term74 A B lt2 lt3 x1 y1)) = ((term77 A B lt2 x1 lt3) = (term75 A B lt2 x1 y1 lt3)).
Proof. exact (TRANS (@lem364512 A B lt2 x1 y1 lt3) (@lem364517 A B lt2 x1 y1 lt3)). Qed.
Lemma lem364519 {A B : Type'} (lt2 : type1402 A) (x1 : A) (y1 : B) (lt3 : type1402 B) : (term77 A B lt2 x1 lt3) = (term75 A B lt2 x1 y1 lt3).
Proof. exact (EQ_MP (@lem364518 A B lt2 x1 y1 lt3) (@lem364509 A B lt2 lt3 x1 y1)). Qed.
Lemma lem364520 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (x1 : A) (y1 : B) : (term79 A B lt2 x1 lt3 y1) = (term80 A B lt2 lt3 x1 y1).
Proof. exact (MK_COMB (@lem364519 A B lt2 x1 y1 lt3) (@lem364507 A B x1 y1)). Qed.
Lemma lem364521 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (x1 : A) (y1 : B) : (term80 A B lt2 lt3 x1 y1) = (term81 A B lt2 lt3 x1 y1).
Proof. exact (eq_refl (term80 A B lt2 lt3 x1 y1)). Qed.
Lemma lem364522 {A B : Type'} (lt2 : type1402 A) (x1 : A) (lt3 : type1402 B) (y1 : B) : (term82 A B lt2 x1 lt3 y1) = (term82 A B lt2 x1 lt3 y1).
Proof. exact (eq_refl (term82 A B lt2 x1 lt3 y1)). Qed.
Lemma lem364523 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (x1 : A) (y1 : B) : ((term79 A B lt2 x1 lt3 y1) = (term80 A B lt2 lt3 x1 y1)) = ((term79 A B lt2 x1 lt3 y1) = (term81 A B lt2 lt3 x1 y1)).
Proof. exact (MK_COMB (@lem364522 A B lt2 x1 lt3 y1) (@lem364521 A B lt2 lt3 x1 y1)). Qed.
Lemma lem364524 {A B : Type'} (lt2 : type1402 A) (x1 : A) (lt3 : type1402 B) (y1 : B) : (term79 A B lt2 x1 lt3 y1) = (term83 A B lt2 x1 lt3 y1).
Proof. exact (eq_refl (term79 A B lt2 x1 lt3 y1)). Qed.
Lemma lem364525 {A B : Type'} : (@eq ((prod A B) -> Prop)) = (@eq ((prod A B) -> Prop)).
Proof. exact (eq_refl (@eq ((prod A B) -> Prop))). Qed.
Lemma lem364526 {A B : Type'} (lt2 : type1402 A) (x1 : A) (lt3 : type1402 B) (y1 : B) : (term82 A B lt2 x1 lt3 y1) = (term84 A B lt2 x1 lt3 y1).
Proof. exact (MK_COMB (@lem364525 A B) (@lem364524 A B lt2 x1 lt3 y1)). Qed.
Lemma lem364527 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (x1 : A) (y1 : B) : (term81 A B lt2 lt3 x1 y1) = (term81 A B lt2 lt3 x1 y1).
Proof. exact (eq_refl (term81 A B lt2 lt3 x1 y1)). Qed.
Lemma lem364528 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (x1 : A) (y1 : B) : ((term79 A B lt2 x1 lt3 y1) = (term81 A B lt2 lt3 x1 y1)) = ((term83 A B lt2 x1 lt3 y1) = (term81 A B lt2 lt3 x1 y1)).
Proof. exact (MK_COMB (@lem364526 A B lt2 x1 lt3 y1) (@lem364527 A B lt2 lt3 x1 y1)). Qed.
Lemma lem364529 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (x1 : A) (y1 : B) : ((term79 A B lt2 x1 lt3 y1) = (term80 A B lt2 lt3 x1 y1)) = ((term83 A B lt2 x1 lt3 y1) = (term81 A B lt2 lt3 x1 y1)).
Proof. exact (TRANS (@lem364523 A B lt2 lt3 x1 y1) (@lem364528 A B lt2 lt3 x1 y1)). Qed.
Lemma lem364530 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (x1 : A) (y1 : B) : (term83 A B lt2 x1 lt3 y1) = (term81 A B lt2 lt3 x1 y1).
Proof. exact (EQ_MP (@lem364529 A B lt2 lt3 x1 y1) (@lem364520 A B lt2 lt3 x1 y1)). Qed.
Lemma lem364531 {A B : Type'} (lt2 : type1402 A) (x1 : A) (lt3 : type1402 B) (y1 : B) : (term81 A B lt2 lt3 x1 y1) = (term83 A B lt2 x1 lt3 y1).
Proof. exact (SYM (@lem364530 A B lt2 lt3 x1 y1)). Qed.
Lemma lem364532 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (x1 : A) (y1 : B) : (term85 A B lt2 lt3 x1 y1) = (term81 A B lt2 lt3 x1 y1).
Proof. exact (eq_refl (term85 A B lt2 lt3 x1 y1)). Qed.
Lemma lem364533 {A B : Type'} (lt2 : type1402 A) (x1 : A) (lt3 : type1402 B) (y1 : B) : (term85 A B lt2 lt3 x1 y1) = (term83 A B lt2 x1 lt3 y1).
Proof. exact (TRANS (@lem364532 A B lt2 lt3 x1 y1) (@lem364531 A B lt2 x1 lt3 y1)). Qed.
Lemma lem364534 {A B : Type'} (lt2 : type1402 A) (x1 : A) (lt3 : type1402 B) : term86 A B lt2 x1 lt3.
Proof. exact (fun y1 : B => @lem364533 A B lt2 x1 lt3 y1). Qed.
Lemma lem364535 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) : term87 A B lt2 lt3.
Proof. exact (fun x1 : A => @lem364534 A B lt2 x1 lt3). Qed.
Lemma lem364536 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) : term88 A B lt2 lt3.
Proof. exact (ex_intro (term89 A B lt2 lt3) (term90 A B lt2 lt3) (@lem364535 A B lt2 lt3)). Qed.
Lemma lem364538 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem364539 {A B : Type'} (a : type1210 A B) (b : type1210 A B) : (a = b) = (@GEQ ((prod A B) -> Prop) a b).
Proof. exact (@lem364538 (type1210 A B) a b). Qed.
Lemma lem364540 {A B : Type'} (_7889 : type1204 A B) (lt2 : type1402 A) (x1 : A) (lt3 : type1402 B) (y1 : B) : ((term91 A B _7889 x1 y1) = (term83 A B lt2 x1 lt3 y1)) = (term92 A B _7889 lt2 x1 lt3 y1).
Proof. exact (@lem364539 A B (term91 A B _7889 x1 y1) (term83 A B lt2 x1 lt3 y1)). Qed.
Lemma lem364541 {A B : Type'} (_7889 : type1204 A B) (lt2 : type1402 A) (x1 : A) (lt3 : type1402 B) : (term93 A B _7889 lt2 x1 lt3) = (term94 A B _7889 lt2 x1 lt3).
Proof. exact (fun_ext (fun y1 : B => @lem364540 A B _7889 lt2 x1 lt3 y1)). Qed.
Lemma lem364542 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem364543 {A B : Type'} (_7889 : type1204 A B) (lt2 : type1402 A) (x1 : A) (lt3 : type1402 B) : (term95 A B _7889 lt2 x1 lt3) = (term96 A B _7889 lt2 x1 lt3).
Proof. exact (MK_COMB (@lem364542 B) (@lem364541 A B _7889 lt2 x1 lt3)). Qed.
Lemma lem364544 {A B : Type'} (_7889 : type1204 A B) (lt2 : type1402 A) (lt3 : type1402 B) : (term97 A B _7889 lt2 lt3) = (term98 A B _7889 lt2 lt3).
Proof. exact (fun_ext (fun x1 : A => @lem364543 A B _7889 lt2 x1 lt3)). Qed.
Lemma lem364545 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem364546 {A B : Type'} (_7889 : type1204 A B) (lt2 : type1402 A) (lt3 : type1402 B) : (term99 A B _7889 lt2 lt3) = (term100 A B _7889 lt2 lt3).
Proof. exact (MK_COMB (@lem364545 A) (@lem364544 A B _7889 lt2 lt3)). Qed.
Lemma lem364547 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) : (term89 A B lt2 lt3) = (term101 A B lt2 lt3).
Proof. exact (fun_ext (fun _7889 : type1204 A B => @lem364546 A B _7889 lt2 lt3)). Qed.
Lemma lem364548 {A B : Type'} : (@ex ((prod A B) -> (prod A B) -> Prop)) = (@ex ((prod A B) -> (prod A B) -> Prop)).
Proof. exact (eq_refl (@ex ((prod A B) -> (prod A B) -> Prop))). Qed.
Lemma lem364549 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) : (term88 A B lt2 lt3) = (term102 A B lt2 lt3).
Proof. exact (MK_COMB (@lem364548 A B) (@lem364547 A B lt2 lt3)). Qed.
Lemma lem364550 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) : term102 A B lt2 lt3.
Proof. exact (EQ_MP (@lem364549 A B lt2 lt3) (@lem364536 A B lt2 lt3)). Qed.
Lemma lem364552 {_5076 : Type'} (P : _5076 -> Prop) : term103 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem364553 {A B : Type'} (P : type315 A B) : term104 A B P.
Proof. exact (@lem364552 (type1204 A B) P). Qed.
Lemma lem364554 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) : term105 A B lt2 lt3.
Proof. exact (@lem364553 A B (term101 A B lt2 lt3)). Qed.
Lemma lem364555 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) : term106 A B lt2 lt3.
Proof. exact (@lem364554 A B lt2 lt3 (@lem364550 A B lt2 lt3)). Qed.
Lemma lem364556 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) : (term106 A B lt2 lt3) = (term107 A B lt2 lt3).
Proof. exact (eq_refl (term106 A B lt2 lt3)). Qed.
Lemma lem364557 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) : term107 A B lt2 lt3.
Proof. exact (EQ_MP (@lem364556 A B lt2 lt3) (@lem364555 A B lt2 lt3)). Qed.
Lemma lem364558 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (x1 : A) : term108 A B lt2 lt3 x1.
Proof. exact (@lem364557 A B lt2 lt3 x1). Qed.
Lemma lem364559 {A B : Type'} (lt2 : type1402 A) (x1 : A) (lt3 : type1402 B) : (term108 A B lt2 lt3 x1) = (term109 A B lt2 x1 lt3).
Proof. exact (eq_refl (term108 A B lt2 lt3 x1)). Qed.
Lemma lem364560 {A B : Type'} (lt2 : type1402 A) (x1 : A) (lt3 : type1402 B) : term109 A B lt2 x1 lt3.
Proof. exact (EQ_MP (@lem364559 A B lt2 x1 lt3) (@lem364558 A B lt2 lt3 x1)). Qed.
Lemma lem364561 {A B : Type'} (lt2 : type1402 A) (x1 : A) (lt3 : type1402 B) (y1 : B) : term110 A B lt2 x1 lt3 y1.
Proof. exact (@lem364560 A B lt2 x1 lt3 y1). Qed.
Lemma lem364562 {A B : Type'} (lt2 : type1402 A) (x1 : A) (lt3 : type1402 B) (y1 : B) : (term110 A B lt2 x1 lt3 y1) = (term111 A B lt2 x1 lt3 y1).
Proof. exact (eq_refl (term110 A B lt2 x1 lt3 y1)). Qed.
Lemma lem364563 {A B : Type'} (lt2 : type1402 A) (x1 : A) (lt3 : type1402 B) (y1 : B) : term111 A B lt2 x1 lt3 y1.
Proof. exact (EQ_MP (@lem364562 A B lt2 x1 lt3 y1) (@lem364561 A B lt2 x1 lt3 y1)). Qed.
Lemma lem364565 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem364566 {A B : Type'} (a : type1210 A B) (b : type1210 A B) : (@GEQ ((prod A B) -> Prop) a b) = (a = b).
Proof. exact (@lem364565 (type1210 A B) a b). Qed.
Lemma lem364567 {A B : Type'} (lt2 : type1402 A) (x1 : A) (lt3 : type1402 B) (y1 : B) : (term111 A B lt2 x1 lt3 y1) = ((term112 A B lt2 lt3 x1 y1) = (term83 A B lt2 x1 lt3 y1)).
Proof. exact (@lem364566 A B (term112 A B lt2 lt3 x1 y1) (term83 A B lt2 x1 lt3 y1)). Qed.
Lemma lem364568 {A B : Type'} (lt2 : type1402 A) (x1 : A) (lt3 : type1402 B) (y1 : B) : (term112 A B lt2 lt3 x1 y1) = (term83 A B lt2 x1 lt3 y1).
Proof. exact (EQ_MP (@lem364567 A B lt2 x1 lt3 y1) (@lem364563 A B lt2 x1 lt3 y1)). Qed.
Lemma lem364569 {A B : Type'} (lt2 : type1402 A) (x1 : A) (lt3 : type1402 B) (y1 : B) : (term112 A B lt2 lt3 x1 y1) = (term83 A B lt2 x1 lt3 y1).
Proof. exact (@lem364568 A B lt2 x1 lt3 y1). Qed.
Lemma lem364570 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) : (term112 A B lt2 lt3 p1 p2) = (term83 A B lt2 p1 lt3 p2).
Proof. exact (@lem364569 A B lt2 p1 lt3 p2). Qed.
Lemma lem364585 {A B : Type'} (p1' : A) (p2' : B) : (@pair A B p1' p2') = (@pair A B p1' p2').
Proof. exact (eq_refl (@pair A B p1' p2')). Qed.
Lemma lem364586 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) (p1' : A) (p2' : B) : (term113 A B lt2 lt3 p1 p2 p1' p2') = (term114 A B lt2 p1 lt3 p2 p1' p2').
Proof. exact (MK_COMB (@lem364570 A B lt2 p1 lt3 p2) (@lem364585 A B p1' p2')). Qed.
Lemma lem364587 {A B : Type'} (a0 : A) (a1 : B) : a0 = (term65 A B a0 a1).
Proof. exact (@lem51128 A B a0 a1). Qed.
Lemma lem364588 {A B : Type'} (x2 : A) (y2 : B) : x2 = (term65 A B x2 y2).
Proof. exact (@lem364587 A B x2 y2). Qed.
Lemma lem364589 {A B : Type'} (a0 : A) (a1 : B) : a1 = (term66 A B a0 a1).
Proof. exact (@lem51159 A B a0 a1). Qed.
Lemma lem364590 {A B : Type'} (x2 : A) (y2 : B) : y2 = (term66 A B x2 y2).
Proof. exact (@lem364589 A B x2 y2). Qed.
Lemma lem364591 {A : Type'} (x2 : A) : x2 = x2.
Proof. exact (eq_refl x2). Qed.
Lemma lem364592 {A : Type'} : (term67 A) = (term67 A).
Proof. exact (eq_refl (term67 A)). Qed.
Lemma lem364593 {A B : Type'} (x2 : A) (y2 : B) : (term68 A x2) = (term69 A B x2 y2).
Proof. exact (MK_COMB (@lem364592 A) (@lem364588 A B x2 y2)). Qed.
Lemma lem364594 {A B : Type'} (x2 : A) (y2 : B) : (term69 A B x2 y2) = (term65 A B x2 y2).
Proof. exact (eq_refl (term69 A B x2 y2)). Qed.
Lemma lem364595 {A : Type'} (x2 : A) : (term70 A x2) = (term70 A x2).
Proof. exact (eq_refl (term70 A x2)). Qed.
Lemma lem364596 {A B : Type'} (x2 : A) (y2 : B) : ((term68 A x2) = (term69 A B x2 y2)) = ((term68 A x2) = (term65 A B x2 y2)).
Proof. exact (MK_COMB (@lem364595 A x2) (@lem364594 A B x2 y2)). Qed.
Lemma lem364597 {A : Type'} (x2 : A) : (term68 A x2) = x2.
Proof. exact (eq_refl (term68 A x2)). Qed.
Lemma lem364598 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem364599 {A : Type'} (x2 : A) : (term70 A x2) = (@eq A x2).
Proof. exact (MK_COMB (@lem364598 A) (@lem364597 A x2)). Qed.
Lemma lem364600 {A B : Type'} (x2 : A) (y2 : B) : (term65 A B x2 y2) = (term65 A B x2 y2).
Proof. exact (eq_refl (term65 A B x2 y2)). Qed.
Lemma lem364601 {A B : Type'} (x2 : A) (y2 : B) : ((term68 A x2) = (term65 A B x2 y2)) = (x2 = (term65 A B x2 y2)).
Proof. exact (MK_COMB (@lem364599 A x2) (@lem364600 A B x2 y2)). Qed.
Lemma lem364602 {A B : Type'} (x2 : A) (y2 : B) : ((term68 A x2) = (term69 A B x2 y2)) = (x2 = (term65 A B x2 y2)).
Proof. exact (TRANS (@lem364596 A B x2 y2) (@lem364601 A B x2 y2)). Qed.
Lemma lem364603 {A B : Type'} (x2 : A) (y2 : B) : x2 = (term65 A B x2 y2).
Proof. exact (EQ_MP (@lem364602 A B x2 y2) (@lem364593 A B x2 y2)). Qed.
Lemma lem364604 {A : Type'} (x2 : A) : (@eq A x2) = (@eq A x2).
Proof. exact (eq_refl (@eq A x2)). Qed.
Lemma lem364605 {A B : Type'} (x2 : A) (y2 : B) : (x2 = x2) = (x2 = (term65 A B x2 y2)).
Proof. exact (MK_COMB (@lem364604 A x2) (@lem364603 A B x2 y2)). Qed.
Lemma lem364606 {A B : Type'} (x2 : A) (y2 : B) : x2 = (term65 A B x2 y2).
Proof. exact (EQ_MP (@lem364605 A B x2 y2) (@lem364591 A x2)). Qed.
Lemma lem364607 {B : Type'} (y2 : B) : y2 = y2.
Proof. exact (eq_refl y2). Qed.
Lemma lem364608 {B : Type'} : (term67 B) = (term67 B).
Proof. exact (eq_refl (term67 B)). Qed.
Lemma lem364609 {A B : Type'} (x2 : A) (y2 : B) : (term68 B y2) = (term71 A B x2 y2).
Proof. exact (MK_COMB (@lem364608 B) (@lem364590 A B x2 y2)). Qed.
Lemma lem364610 {A B : Type'} (x2 : A) (y2 : B) : (term71 A B x2 y2) = (term66 A B x2 y2).
Proof. exact (eq_refl (term71 A B x2 y2)). Qed.
Lemma lem364611 {B : Type'} (y2 : B) : (term70 B y2) = (term70 B y2).
Proof. exact (eq_refl (term70 B y2)). Qed.
Lemma lem364612 {A B : Type'} (x2 : A) (y2 : B) : ((term68 B y2) = (term71 A B x2 y2)) = ((term68 B y2) = (term66 A B x2 y2)).
Proof. exact (MK_COMB (@lem364611 B y2) (@lem364610 A B x2 y2)). Qed.
Lemma lem364613 {B : Type'} (y2 : B) : (term68 B y2) = y2.
Proof. exact (eq_refl (term68 B y2)). Qed.
Lemma lem364614 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem364615 {B : Type'} (y2 : B) : (term70 B y2) = (@eq B y2).
Proof. exact (MK_COMB (@lem364614 B) (@lem364613 B y2)). Qed.
Lemma lem364616 {A B : Type'} (x2 : A) (y2 : B) : (term66 A B x2 y2) = (term66 A B x2 y2).
Proof. exact (eq_refl (term66 A B x2 y2)). Qed.
Lemma lem364617 {A B : Type'} (x2 : A) (y2 : B) : ((term68 B y2) = (term66 A B x2 y2)) = (y2 = (term66 A B x2 y2)).
Proof. exact (MK_COMB (@lem364615 B y2) (@lem364616 A B x2 y2)). Qed.
Lemma lem364618 {A B : Type'} (x2 : A) (y2 : B) : ((term68 B y2) = (term71 A B x2 y2)) = (y2 = (term66 A B x2 y2)).
Proof. exact (TRANS (@lem364612 A B x2 y2) (@lem364617 A B x2 y2)). Qed.
Lemma lem364619 {A B : Type'} (x2 : A) (y2 : B) : y2 = (term66 A B x2 y2).
Proof. exact (EQ_MP (@lem364618 A B x2 y2) (@lem364609 A B x2 y2)). Qed.
Lemma lem364620 {B : Type'} (y2 : B) : (@eq B y2) = (@eq B y2).
Proof. exact (eq_refl (@eq B y2)). Qed.
Lemma lem364621 {A B : Type'} (x2 : A) (y2 : B) : (y2 = y2) = (y2 = (term66 A B x2 y2)).
Proof. exact (MK_COMB (@lem364620 B y2) (@lem364619 A B x2 y2)). Qed.
Lemma lem364622 {A B : Type'} (x2 : A) (y2 : B) : y2 = (term66 A B x2 y2).
Proof. exact (EQ_MP (@lem364621 A B x2 y2) (@lem364607 B y2)). Qed.
Lemma lem364623 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) : (term115 A B lt2 p1 lt3 p2) = (term115 A B lt2 p1 lt3 p2).
Proof. exact (eq_refl (term115 A B lt2 p1 lt3 p2)). Qed.
Lemma lem364624 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) (x2 : A) (y2 : B) : (term116 A B lt2 p1 lt3 p2 x2) = (term117 A B lt2 p1 lt3 p2 x2 y2).
Proof. exact (MK_COMB (@lem364623 A B lt2 p1 lt3 p2) (@lem364606 A B x2 y2)). Qed.
Lemma lem364625 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (y2 : B) (lt3 : type1402 B) (p2 : B) : (term117 A B lt2 p1 lt3 p2 x2 y2) = (term118 A B lt2 p1 x2 y2 lt3 p2).
Proof. exact (eq_refl (term117 A B lt2 p1 lt3 p2 x2 y2)). Qed.
Lemma lem364626 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) (x2 : A) : (term119 A B lt2 p1 lt3 p2 x2) = (term119 A B lt2 p1 lt3 p2 x2).
Proof. exact (eq_refl (term119 A B lt2 p1 lt3 p2 x2)). Qed.
Lemma lem364627 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (y2 : B) (lt3 : type1402 B) (p2 : B) : ((term116 A B lt2 p1 lt3 p2 x2) = (term117 A B lt2 p1 lt3 p2 x2 y2)) = ((term116 A B lt2 p1 lt3 p2 x2) = (term118 A B lt2 p1 x2 y2 lt3 p2)).
Proof. exact (MK_COMB (@lem364626 A B lt2 p1 lt3 p2 x2) (@lem364625 A B lt2 p1 x2 y2 lt3 p2)). Qed.
Lemma lem364628 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (lt3 : type1402 B) (p2 : B) : (term116 A B lt2 p1 lt3 p2 x2) = (term120 A B lt2 p1 x2 lt3 p2).
Proof. exact (eq_refl (term116 A B lt2 p1 lt3 p2 x2)). Qed.
Lemma lem364629 {B : Type'} : (@eq (B -> Prop)) = (@eq (B -> Prop)).
Proof. exact (eq_refl (@eq (B -> Prop))). Qed.
Lemma lem364630 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (lt3 : type1402 B) (p2 : B) : (term119 A B lt2 p1 lt3 p2 x2) = (term121 A B lt2 p1 x2 lt3 p2).
Proof. exact (MK_COMB (@lem364629 B) (@lem364628 A B lt2 p1 x2 lt3 p2)). Qed.
Lemma lem364631 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (y2 : B) (lt3 : type1402 B) (p2 : B) : (term118 A B lt2 p1 x2 y2 lt3 p2) = (term118 A B lt2 p1 x2 y2 lt3 p2).
Proof. exact (eq_refl (term118 A B lt2 p1 x2 y2 lt3 p2)). Qed.
Lemma lem364632 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (y2 : B) (lt3 : type1402 B) (p2 : B) : ((term116 A B lt2 p1 lt3 p2 x2) = (term118 A B lt2 p1 x2 y2 lt3 p2)) = ((term120 A B lt2 p1 x2 lt3 p2) = (term118 A B lt2 p1 x2 y2 lt3 p2)).
Proof. exact (MK_COMB (@lem364630 A B lt2 p1 x2 lt3 p2) (@lem364631 A B lt2 p1 x2 y2 lt3 p2)). Qed.
Lemma lem364633 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (y2 : B) (lt3 : type1402 B) (p2 : B) : ((term116 A B lt2 p1 lt3 p2 x2) = (term117 A B lt2 p1 lt3 p2 x2 y2)) = ((term120 A B lt2 p1 x2 lt3 p2) = (term118 A B lt2 p1 x2 y2 lt3 p2)).
Proof. exact (TRANS (@lem364627 A B lt2 p1 x2 y2 lt3 p2) (@lem364632 A B lt2 p1 x2 y2 lt3 p2)). Qed.
Lemma lem364634 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (y2 : B) (lt3 : type1402 B) (p2 : B) : (term120 A B lt2 p1 x2 lt3 p2) = (term118 A B lt2 p1 x2 y2 lt3 p2).
Proof. exact (EQ_MP (@lem364633 A B lt2 p1 x2 y2 lt3 p2) (@lem364624 A B lt2 p1 lt3 p2 x2 y2)). Qed.
Lemma lem364635 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) (x2 : A) (y2 : B) : (term122 A B lt2 p1 x2 lt3 p2 y2) = (term123 A B lt2 p1 lt3 p2 x2 y2).
Proof. exact (MK_COMB (@lem364634 A B lt2 p1 x2 y2 lt3 p2) (@lem364622 A B x2 y2)). Qed.
Lemma lem364636 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) (x2 : A) (y2 : B) : (term123 A B lt2 p1 lt3 p2 x2 y2) = (term124 A B lt2 p1 lt3 p2 x2 y2).
Proof. exact (eq_refl (term123 A B lt2 p1 lt3 p2 x2 y2)). Qed.
Lemma lem364637 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (lt3 : type1402 B) (p2 : B) (y2 : B) : (term125 A B lt2 p1 x2 lt3 p2 y2) = (term125 A B lt2 p1 x2 lt3 p2 y2).
Proof. exact (eq_refl (term125 A B lt2 p1 x2 lt3 p2 y2)). Qed.
Lemma lem364638 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) (x2 : A) (y2 : B) : ((term122 A B lt2 p1 x2 lt3 p2 y2) = (term123 A B lt2 p1 lt3 p2 x2 y2)) = ((term122 A B lt2 p1 x2 lt3 p2 y2) = (term124 A B lt2 p1 lt3 p2 x2 y2)).
Proof. exact (MK_COMB (@lem364637 A B lt2 p1 x2 lt3 p2 y2) (@lem364636 A B lt2 p1 lt3 p2 x2 y2)). Qed.
Lemma lem364639 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (lt3 : type1402 B) (p2 : B) (y2 : B) : (term122 A B lt2 p1 x2 lt3 p2 y2) = (term126 A B lt2 p1 x2 lt3 p2 y2).
Proof. exact (eq_refl (term122 A B lt2 p1 x2 lt3 p2 y2)). Qed.
Lemma lem364640 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem364641 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (lt3 : type1402 B) (p2 : B) (y2 : B) : (term125 A B lt2 p1 x2 lt3 p2 y2) = (term127 A B lt2 p1 x2 lt3 p2 y2).
Proof. exact (MK_COMB (@lem364640) (@lem364639 A B lt2 p1 x2 lt3 p2 y2)). Qed.
Lemma lem364642 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) (x2 : A) (y2 : B) : (term124 A B lt2 p1 lt3 p2 x2 y2) = (term124 A B lt2 p1 lt3 p2 x2 y2).
Proof. exact (eq_refl (term124 A B lt2 p1 lt3 p2 x2 y2)). Qed.
Lemma lem364643 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) (x2 : A) (y2 : B) : ((term122 A B lt2 p1 x2 lt3 p2 y2) = (term124 A B lt2 p1 lt3 p2 x2 y2)) = ((term126 A B lt2 p1 x2 lt3 p2 y2) = (term124 A B lt2 p1 lt3 p2 x2 y2)).
Proof. exact (MK_COMB (@lem364641 A B lt2 p1 x2 lt3 p2 y2) (@lem364642 A B lt2 p1 lt3 p2 x2 y2)). Qed.
Lemma lem364644 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) (x2 : A) (y2 : B) : ((term122 A B lt2 p1 x2 lt3 p2 y2) = (term123 A B lt2 p1 lt3 p2 x2 y2)) = ((term126 A B lt2 p1 x2 lt3 p2 y2) = (term124 A B lt2 p1 lt3 p2 x2 y2)).
Proof. exact (TRANS (@lem364638 A B lt2 p1 lt3 p2 x2 y2) (@lem364643 A B lt2 p1 lt3 p2 x2 y2)). Qed.
Lemma lem364645 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) (x2 : A) (y2 : B) : (term126 A B lt2 p1 x2 lt3 p2 y2) = (term124 A B lt2 p1 lt3 p2 x2 y2).
Proof. exact (EQ_MP (@lem364644 A B lt2 p1 lt3 p2 x2 y2) (@lem364635 A B lt2 p1 lt3 p2 x2 y2)). Qed.
Lemma lem364646 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (lt3 : type1402 B) (p2 : B) (y2 : B) : (term124 A B lt2 p1 lt3 p2 x2 y2) = (term126 A B lt2 p1 x2 lt3 p2 y2).
Proof. exact (SYM (@lem364645 A B lt2 p1 lt3 p2 x2 y2)). Qed.
Lemma lem364647 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) (x2 : A) (y2 : B) : (term128 A B lt2 p1 lt3 p2 x2 y2) = (term124 A B lt2 p1 lt3 p2 x2 y2).
Proof. exact (eq_refl (term128 A B lt2 p1 lt3 p2 x2 y2)). Qed.
Lemma lem364648 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (lt3 : type1402 B) (p2 : B) (y2 : B) : (term128 A B lt2 p1 lt3 p2 x2 y2) = (term126 A B lt2 p1 x2 lt3 p2 y2).
Proof. exact (TRANS (@lem364647 A B lt2 p1 lt3 p2 x2 y2) (@lem364646 A B lt2 p1 x2 lt3 p2 y2)). Qed.
Lemma lem364649 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (lt3 : type1402 B) (p2 : B) : term129 A B lt2 p1 x2 lt3 p2.
Proof. exact (fun y2 : B => @lem364648 A B lt2 p1 x2 lt3 p2 y2). Qed.
Lemma lem364650 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) : term130 A B lt2 p1 lt3 p2.
Proof. exact (fun x2 : A => @lem364649 A B lt2 p1 x2 lt3 p2). Qed.
Lemma lem364651 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) : term131 A B lt2 p1 lt3 p2.
Proof. exact (ex_intro (term132 A B lt2 p1 lt3 p2) (term133 A B lt2 p1 lt3 p2) (@lem364650 A B lt2 p1 lt3 p2)). Qed.
Lemma lem364653 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem364654 (a : Prop) (b : Prop) : (a = b) = (@GEQ Prop a b).
Proof. exact (@lem364653 Prop a b). Qed.
Lemma lem364655 {A B : Type'} (_7901 : type1210 A B) (lt2 : type1402 A) (p1 : A) (x2 : A) (lt3 : type1402 B) (p2 : B) (y2 : B) : ((term134 A B _7901 x2 y2) = (term126 A B lt2 p1 x2 lt3 p2 y2)) = (term135 A B _7901 lt2 p1 x2 lt3 p2 y2).
Proof. exact (@lem364654 (term134 A B _7901 x2 y2) (term126 A B lt2 p1 x2 lt3 p2 y2)). Qed.
Lemma lem364656 {A B : Type'} (_7901 : type1210 A B) (lt2 : type1402 A) (p1 : A) (x2 : A) (lt3 : type1402 B) (p2 : B) : (term136 A B _7901 lt2 p1 x2 lt3 p2) = (term137 A B _7901 lt2 p1 x2 lt3 p2).
Proof. exact (fun_ext (fun y2 : B => @lem364655 A B _7901 lt2 p1 x2 lt3 p2 y2)). Qed.
Lemma lem364657 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem364658 {A B : Type'} (_7901 : type1210 A B) (lt2 : type1402 A) (p1 : A) (x2 : A) (lt3 : type1402 B) (p2 : B) : (term138 A B _7901 lt2 p1 x2 lt3 p2) = (term139 A B _7901 lt2 p1 x2 lt3 p2).
Proof. exact (MK_COMB (@lem364657 B) (@lem364656 A B _7901 lt2 p1 x2 lt3 p2)). Qed.
Lemma lem364659 {A B : Type'} (_7901 : type1210 A B) (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) : (term140 A B _7901 lt2 p1 lt3 p2) = (term141 A B _7901 lt2 p1 lt3 p2).
Proof. exact (fun_ext (fun x2 : A => @lem364658 A B _7901 lt2 p1 x2 lt3 p2)). Qed.
Lemma lem364660 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem364661 {A B : Type'} (_7901 : type1210 A B) (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) : (term142 A B _7901 lt2 p1 lt3 p2) = (term143 A B _7901 lt2 p1 lt3 p2).
Proof. exact (MK_COMB (@lem364660 A) (@lem364659 A B _7901 lt2 p1 lt3 p2)). Qed.
Lemma lem364662 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) : (term132 A B lt2 p1 lt3 p2) = (term144 A B lt2 p1 lt3 p2).
Proof. exact (fun_ext (fun _7901 : type1210 A B => @lem364661 A B _7901 lt2 p1 lt3 p2)). Qed.
Lemma lem364663 {A B : Type'} : (@ex ((prod A B) -> Prop)) = (@ex ((prod A B) -> Prop)).
Proof. exact (eq_refl (@ex ((prod A B) -> Prop))). Qed.
Lemma lem364664 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) : (term131 A B lt2 p1 lt3 p2) = (term145 A B lt2 p1 lt3 p2).
Proof. exact (MK_COMB (@lem364663 A B) (@lem364662 A B lt2 p1 lt3 p2)). Qed.
Lemma lem364665 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) : term145 A B lt2 p1 lt3 p2.
Proof. exact (EQ_MP (@lem364664 A B lt2 p1 lt3 p2) (@lem364651 A B lt2 p1 lt3 p2)). Qed.
Lemma lem364667 {_5076 : Type'} (P : _5076 -> Prop) : term103 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem364668 {A B : Type'} (P : type324 A B) : term146 A B P.
Proof. exact (@lem364667 (type1210 A B) P). Qed.
Lemma lem364669 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) : term147 A B lt2 p1 lt3 p2.
Proof. exact (@lem364668 A B (term144 A B lt2 p1 lt3 p2)). Qed.
Lemma lem364670 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) : term148 A B lt2 p1 lt3 p2.
Proof. exact (@lem364669 A B lt2 p1 lt3 p2 (@lem364665 A B lt2 p1 lt3 p2)). Qed.
Lemma lem364671 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) : (term148 A B lt2 p1 lt3 p2) = (term149 A B lt2 p1 lt3 p2).
Proof. exact (eq_refl (term148 A B lt2 p1 lt3 p2)). Qed.
Lemma lem364672 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) : term149 A B lt2 p1 lt3 p2.
Proof. exact (EQ_MP (@lem364671 A B lt2 p1 lt3 p2) (@lem364670 A B lt2 p1 lt3 p2)). Qed.
Lemma lem364673 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) (x2 : A) : term150 A B lt2 p1 lt3 p2 x2.
Proof. exact (@lem364672 A B lt2 p1 lt3 p2 x2). Qed.
Lemma lem364674 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (lt3 : type1402 B) (p2 : B) : (term150 A B lt2 p1 lt3 p2 x2) = (term151 A B lt2 p1 x2 lt3 p2).
Proof. exact (eq_refl (term150 A B lt2 p1 lt3 p2 x2)). Qed.
Lemma lem364675 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (lt3 : type1402 B) (p2 : B) : term151 A B lt2 p1 x2 lt3 p2.
Proof. exact (EQ_MP (@lem364674 A B lt2 p1 x2 lt3 p2) (@lem364673 A B lt2 p1 lt3 p2 x2)). Qed.
Lemma lem364676 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (lt3 : type1402 B) (p2 : B) (y2 : B) : term152 A B lt2 p1 x2 lt3 p2 y2.
Proof. exact (@lem364675 A B lt2 p1 x2 lt3 p2 y2). Qed.
Lemma lem364677 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (lt3 : type1402 B) (p2 : B) (y2 : B) : (term152 A B lt2 p1 x2 lt3 p2 y2) = (term153 A B lt2 p1 x2 lt3 p2 y2).
Proof. exact (eq_refl (term152 A B lt2 p1 x2 lt3 p2 y2)). Qed.
Lemma lem364678 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (lt3 : type1402 B) (p2 : B) (y2 : B) : term153 A B lt2 p1 x2 lt3 p2 y2.
Proof. exact (EQ_MP (@lem364677 A B lt2 p1 x2 lt3 p2 y2) (@lem364676 A B lt2 p1 x2 lt3 p2 y2)). Qed.
Lemma lem364680 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem364681 (a : Prop) (b : Prop) : (@GEQ Prop a b) = (a = b).
Proof. exact (@lem364680 Prop a b). Qed.
Lemma lem364682 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (lt3 : type1402 B) (p2 : B) (y2 : B) : (term153 A B lt2 p1 x2 lt3 p2 y2) = ((term114 A B lt2 p1 lt3 p2 x2 y2) = (term126 A B lt2 p1 x2 lt3 p2 y2)).
Proof. exact (@lem364681 (term114 A B lt2 p1 lt3 p2 x2 y2) (term126 A B lt2 p1 x2 lt3 p2 y2)). Qed.
Lemma lem364683 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (lt3 : type1402 B) (p2 : B) (y2 : B) : (term114 A B lt2 p1 lt3 p2 x2 y2) = (term126 A B lt2 p1 x2 lt3 p2 y2).
Proof. exact (EQ_MP (@lem364682 A B lt2 p1 x2 lt3 p2 y2) (@lem364678 A B lt2 p1 x2 lt3 p2 y2)). Qed.
Lemma lem364684 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (lt3 : type1402 B) (p2 : B) (y2 : B) : (term114 A B lt2 p1 lt3 p2 x2 y2) = (term126 A B lt2 p1 x2 lt3 p2 y2).
Proof. exact (@lem364683 A B lt2 p1 x2 lt3 p2 y2). Qed.
Lemma lem364685 {A B : Type'} (lt2 : type1402 A) (p1 : A) (p1' : A) (lt3 : type1402 B) (p2 : B) (p2' : B) : (term114 A B lt2 p1 lt3 p2 p1' p2') = (term126 A B lt2 p1 p1' lt3 p2 p2').
Proof. exact (@lem364684 A B lt2 p1 p1' lt3 p2 p2'). Qed.
Lemma lem364688 {A B : Type'} (lt2 : type1402 A) (p1 : A) (p1' : A) (lt3 : type1402 B) (p2 : B) (p2' : B) : (term113 A B lt2 lt3 p1 p2 p1' p2') = (term126 A B lt2 p1 p1' lt3 p2 p2').
Proof. exact (TRANS (@lem364586 A B lt2 p1 lt3 p2 p1' p2') (@lem364685 A B lt2 p1 p1' lt3 p2 p2')). Qed.
Lemma lem364689 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem364690 {A B : Type'} (lt2 : type1402 A) (p1 : A) (p1' : A) (lt3 : type1402 B) (p2 : B) (p2' : B) : (term154 A B lt2 lt3 p1 p2 p1' p2') = (term155 A B lt2 p1 p1' lt3 p2 p2').
Proof. exact (MK_COMB (@lem364689) (@lem364688 A B lt2 p1 p1' lt3 p2 p2')). Qed.
Lemma lem364691 {A B : Type'} (a0 : A) (a1 : B) : a0 = (term65 A B a0 a1).
Proof. exact (@lem51128 A B a0 a1). Qed.
Lemma lem364692 {A B : Type'} (x1 : A) (y1 : B) : x1 = (term65 A B x1 y1).
Proof. exact (@lem364691 A B x1 y1). Qed.
Lemma lem364693 {A B : Type'} (a0 : A) (a1 : B) : a1 = (term66 A B a0 a1).
Proof. exact (@lem51159 A B a0 a1). Qed.
Lemma lem364694 {A B : Type'} (x1 : A) (y1 : B) : y1 = (term66 A B x1 y1).
Proof. exact (@lem364693 A B x1 y1). Qed.
Lemma lem364695 {A : Type'} (x1 : A) : x1 = x1.
Proof. exact (eq_refl x1). Qed.
Lemma lem364696 {A : Type'} : (term67 A) = (term67 A).
Proof. exact (eq_refl (term67 A)). Qed.
Lemma lem364697 {A B : Type'} (x1 : A) (y1 : B) : (term68 A x1) = (term69 A B x1 y1).
Proof. exact (MK_COMB (@lem364696 A) (@lem364692 A B x1 y1)). Qed.
Lemma lem364698 {A B : Type'} (x1 : A) (y1 : B) : (term69 A B x1 y1) = (term65 A B x1 y1).
Proof. exact (eq_refl (term69 A B x1 y1)). Qed.
Lemma lem364699 {A : Type'} (x1 : A) : (term70 A x1) = (term70 A x1).
Proof. exact (eq_refl (term70 A x1)). Qed.
Lemma lem364700 {A B : Type'} (x1 : A) (y1 : B) : ((term68 A x1) = (term69 A B x1 y1)) = ((term68 A x1) = (term65 A B x1 y1)).
Proof. exact (MK_COMB (@lem364699 A x1) (@lem364698 A B x1 y1)). Qed.
Lemma lem364701 {A : Type'} (x1 : A) : (term68 A x1) = x1.
Proof. exact (eq_refl (term68 A x1)). Qed.
Lemma lem364702 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem364703 {A : Type'} (x1 : A) : (term70 A x1) = (@eq A x1).
Proof. exact (MK_COMB (@lem364702 A) (@lem364701 A x1)). Qed.
Lemma lem364704 {A B : Type'} (x1 : A) (y1 : B) : (term65 A B x1 y1) = (term65 A B x1 y1).
Proof. exact (eq_refl (term65 A B x1 y1)). Qed.
Lemma lem364705 {A B : Type'} (x1 : A) (y1 : B) : ((term68 A x1) = (term65 A B x1 y1)) = (x1 = (term65 A B x1 y1)).
Proof. exact (MK_COMB (@lem364703 A x1) (@lem364704 A B x1 y1)). Qed.
Lemma lem364706 {A B : Type'} (x1 : A) (y1 : B) : ((term68 A x1) = (term69 A B x1 y1)) = (x1 = (term65 A B x1 y1)).
Proof. exact (TRANS (@lem364700 A B x1 y1) (@lem364705 A B x1 y1)). Qed.
Lemma lem364707 {A B : Type'} (x1 : A) (y1 : B) : x1 = (term65 A B x1 y1).
Proof. exact (EQ_MP (@lem364706 A B x1 y1) (@lem364697 A B x1 y1)). Qed.
Lemma lem364708 {A : Type'} (x1 : A) : (@eq A x1) = (@eq A x1).
Proof. exact (eq_refl (@eq A x1)). Qed.
Lemma lem364709 {A B : Type'} (x1 : A) (y1 : B) : (x1 = x1) = (x1 = (term65 A B x1 y1)).
Proof. exact (MK_COMB (@lem364708 A x1) (@lem364707 A B x1 y1)). Qed.
Lemma lem364710 {A B : Type'} (x1 : A) (y1 : B) : x1 = (term65 A B x1 y1).
Proof. exact (EQ_MP (@lem364709 A B x1 y1) (@lem364695 A x1)). Qed.
Lemma lem364711 {B : Type'} (y1 : B) : y1 = y1.
Proof. exact (eq_refl y1). Qed.
Lemma lem364712 {B : Type'} : (term67 B) = (term67 B).
Proof. exact (eq_refl (term67 B)). Qed.
Lemma lem364713 {A B : Type'} (x1 : A) (y1 : B) : (term68 B y1) = (term71 A B x1 y1).
Proof. exact (MK_COMB (@lem364712 B) (@lem364694 A B x1 y1)). Qed.
Lemma lem364714 {A B : Type'} (x1 : A) (y1 : B) : (term71 A B x1 y1) = (term66 A B x1 y1).
Proof. exact (eq_refl (term71 A B x1 y1)). Qed.
Lemma lem364715 {B : Type'} (y1 : B) : (term70 B y1) = (term70 B y1).
Proof. exact (eq_refl (term70 B y1)). Qed.
Lemma lem364716 {A B : Type'} (x1 : A) (y1 : B) : ((term68 B y1) = (term71 A B x1 y1)) = ((term68 B y1) = (term66 A B x1 y1)).
Proof. exact (MK_COMB (@lem364715 B y1) (@lem364714 A B x1 y1)). Qed.
Lemma lem364717 {B : Type'} (y1 : B) : (term68 B y1) = y1.
Proof. exact (eq_refl (term68 B y1)). Qed.
Lemma lem364718 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem364719 {B : Type'} (y1 : B) : (term70 B y1) = (@eq B y1).
Proof. exact (MK_COMB (@lem364718 B) (@lem364717 B y1)). Qed.
Lemma lem364720 {A B : Type'} (x1 : A) (y1 : B) : (term66 A B x1 y1) = (term66 A B x1 y1).
Proof. exact (eq_refl (term66 A B x1 y1)). Qed.
Lemma lem364721 {A B : Type'} (x1 : A) (y1 : B) : ((term68 B y1) = (term66 A B x1 y1)) = (y1 = (term66 A B x1 y1)).
Proof. exact (MK_COMB (@lem364719 B y1) (@lem364720 A B x1 y1)). Qed.
Lemma lem364722 {A B : Type'} (x1 : A) (y1 : B) : ((term68 B y1) = (term71 A B x1 y1)) = (y1 = (term66 A B x1 y1)).
Proof. exact (TRANS (@lem364716 A B x1 y1) (@lem364721 A B x1 y1)). Qed.
Lemma lem364723 {A B : Type'} (x1 : A) (y1 : B) : y1 = (term66 A B x1 y1).
Proof. exact (EQ_MP (@lem364722 A B x1 y1) (@lem364713 A B x1 y1)). Qed.
Lemma lem364724 {B : Type'} (y1 : B) : (@eq B y1) = (@eq B y1).
Proof. exact (eq_refl (@eq B y1)). Qed.
Lemma lem364725 {A B : Type'} (x1 : A) (y1 : B) : (y1 = y1) = (y1 = (term66 A B x1 y1)).
Proof. exact (MK_COMB (@lem364724 B y1) (@lem364723 A B x1 y1)). Qed.
Lemma lem364726 {A B : Type'} (x1 : A) (y1 : B) : y1 = (term66 A B x1 y1).
Proof. exact (EQ_MP (@lem364725 A B x1 y1) (@lem364711 B y1)). Qed.
Lemma lem364727 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) : (term156 A B lt2 lt3) = (term156 A B lt2 lt3).
Proof. exact (eq_refl (term156 A B lt2 lt3)). Qed.
Lemma lem364728 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (x1 : A) (y1 : B) : (term157 A B lt2 lt3 x1) = (term158 A B lt2 lt3 x1 y1).
Proof. exact (MK_COMB (@lem364727 A B lt2 lt3) (@lem364710 A B x1 y1)). Qed.
Lemma lem364729 {A B : Type'} (lt2 : type1402 A) (x1 : A) (y1 : B) (lt3 : type1402 B) : (term158 A B lt2 lt3 x1 y1) = (term159 A B lt2 x1 y1 lt3).
Proof. exact (eq_refl (term158 A B lt2 lt3 x1 y1)). Qed.
Lemma lem364730 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (x1 : A) : (term160 A B lt2 lt3 x1) = (term160 A B lt2 lt3 x1).
Proof. exact (eq_refl (term160 A B lt2 lt3 x1)). Qed.
Lemma lem364731 {A B : Type'} (lt2 : type1402 A) (x1 : A) (y1 : B) (lt3 : type1402 B) : ((term157 A B lt2 lt3 x1) = (term158 A B lt2 lt3 x1 y1)) = ((term157 A B lt2 lt3 x1) = (term159 A B lt2 x1 y1 lt3)).
Proof. exact (MK_COMB (@lem364730 A B lt2 lt3 x1) (@lem364729 A B lt2 x1 y1 lt3)). Qed.
Lemma lem364732 {A B : Type'} (lt2 : type1402 A) (x1 : A) (lt3 : type1402 B) : (term157 A B lt2 lt3 x1) = (term161 A B lt2 x1 lt3).
Proof. exact (eq_refl (term157 A B lt2 lt3 x1)). Qed.
Lemma lem364733 {A B : Type'} : (@eq (B -> (prod A B) -> Prop)) = (@eq (B -> (prod A B) -> Prop)).
Proof. exact (eq_refl (@eq (B -> (prod A B) -> Prop))). Qed.
Lemma lem364734 {A B : Type'} (lt2 : type1402 A) (x1 : A) (lt3 : type1402 B) : (term160 A B lt2 lt3 x1) = (term162 A B lt2 x1 lt3).
Proof. exact (MK_COMB (@lem364733 A B) (@lem364732 A B lt2 x1 lt3)). Qed.
Lemma lem364735 {A B : Type'} (lt2 : type1402 A) (x1 : A) (y1 : B) (lt3 : type1402 B) : (term159 A B lt2 x1 y1 lt3) = (term159 A B lt2 x1 y1 lt3).
Proof. exact (eq_refl (term159 A B lt2 x1 y1 lt3)). Qed.
Lemma lem364736 {A B : Type'} (lt2 : type1402 A) (x1 : A) (y1 : B) (lt3 : type1402 B) : ((term157 A B lt2 lt3 x1) = (term159 A B lt2 x1 y1 lt3)) = ((term161 A B lt2 x1 lt3) = (term159 A B lt2 x1 y1 lt3)).
Proof. exact (MK_COMB (@lem364734 A B lt2 x1 lt3) (@lem364735 A B lt2 x1 y1 lt3)). Qed.
Lemma lem364737 {A B : Type'} (lt2 : type1402 A) (x1 : A) (y1 : B) (lt3 : type1402 B) : ((term157 A B lt2 lt3 x1) = (term158 A B lt2 lt3 x1 y1)) = ((term161 A B lt2 x1 lt3) = (term159 A B lt2 x1 y1 lt3)).
Proof. exact (TRANS (@lem364731 A B lt2 x1 y1 lt3) (@lem364736 A B lt2 x1 y1 lt3)). Qed.
Lemma lem364738 {A B : Type'} (lt2 : type1402 A) (x1 : A) (y1 : B) (lt3 : type1402 B) : (term161 A B lt2 x1 lt3) = (term159 A B lt2 x1 y1 lt3).
Proof. exact (EQ_MP (@lem364737 A B lt2 x1 y1 lt3) (@lem364728 A B lt2 lt3 x1 y1)). Qed.
Lemma lem364739 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (x1 : A) (y1 : B) : (term163 A B lt2 x1 lt3 y1) = (term164 A B lt2 lt3 x1 y1).
Proof. exact (MK_COMB (@lem364738 A B lt2 x1 y1 lt3) (@lem364726 A B x1 y1)). Qed.
Lemma lem364740 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (x1 : A) (y1 : B) : (term164 A B lt2 lt3 x1 y1) = (term165 A B lt2 lt3 x1 y1).
Proof. exact (eq_refl (term164 A B lt2 lt3 x1 y1)). Qed.
Lemma lem364741 {A B : Type'} (lt2 : type1402 A) (x1 : A) (lt3 : type1402 B) (y1 : B) : (term166 A B lt2 x1 lt3 y1) = (term166 A B lt2 x1 lt3 y1).
Proof. exact (eq_refl (term166 A B lt2 x1 lt3 y1)). Qed.
Lemma lem364742 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (x1 : A) (y1 : B) : ((term163 A B lt2 x1 lt3 y1) = (term164 A B lt2 lt3 x1 y1)) = ((term163 A B lt2 x1 lt3 y1) = (term165 A B lt2 lt3 x1 y1)).
Proof. exact (MK_COMB (@lem364741 A B lt2 x1 lt3 y1) (@lem364740 A B lt2 lt3 x1 y1)). Qed.
Lemma lem364743 {A B : Type'} (lt2 : type1402 A) (x1 : A) (lt3 : type1402 B) (y1 : B) : (term163 A B lt2 x1 lt3 y1) = (term167 A B lt2 x1 lt3 y1).
Proof. exact (eq_refl (term163 A B lt2 x1 lt3 y1)). Qed.
Lemma lem364744 {A B : Type'} : (@eq ((prod A B) -> Prop)) = (@eq ((prod A B) -> Prop)).
Proof. exact (eq_refl (@eq ((prod A B) -> Prop))). Qed.
Lemma lem364745 {A B : Type'} (lt2 : type1402 A) (x1 : A) (lt3 : type1402 B) (y1 : B) : (term166 A B lt2 x1 lt3 y1) = (term168 A B lt2 x1 lt3 y1).
Proof. exact (MK_COMB (@lem364744 A B) (@lem364743 A B lt2 x1 lt3 y1)). Qed.
Lemma lem364746 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (x1 : A) (y1 : B) : (term165 A B lt2 lt3 x1 y1) = (term165 A B lt2 lt3 x1 y1).
Proof. exact (eq_refl (term165 A B lt2 lt3 x1 y1)). Qed.
Lemma lem364747 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (x1 : A) (y1 : B) : ((term163 A B lt2 x1 lt3 y1) = (term165 A B lt2 lt3 x1 y1)) = ((term167 A B lt2 x1 lt3 y1) = (term165 A B lt2 lt3 x1 y1)).
Proof. exact (MK_COMB (@lem364745 A B lt2 x1 lt3 y1) (@lem364746 A B lt2 lt3 x1 y1)). Qed.
Lemma lem364748 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (x1 : A) (y1 : B) : ((term163 A B lt2 x1 lt3 y1) = (term164 A B lt2 lt3 x1 y1)) = ((term167 A B lt2 x1 lt3 y1) = (term165 A B lt2 lt3 x1 y1)).
Proof. exact (TRANS (@lem364742 A B lt2 lt3 x1 y1) (@lem364747 A B lt2 lt3 x1 y1)). Qed.
Lemma lem364749 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (x1 : A) (y1 : B) : (term167 A B lt2 x1 lt3 y1) = (term165 A B lt2 lt3 x1 y1).
Proof. exact (EQ_MP (@lem364748 A B lt2 lt3 x1 y1) (@lem364739 A B lt2 lt3 x1 y1)). Qed.
Lemma lem364750 {A B : Type'} (lt2 : type1402 A) (x1 : A) (lt3 : type1402 B) (y1 : B) : (term165 A B lt2 lt3 x1 y1) = (term167 A B lt2 x1 lt3 y1).
Proof. exact (SYM (@lem364749 A B lt2 lt3 x1 y1)). Qed.
Lemma lem364751 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (x1 : A) (y1 : B) : (term169 A B lt2 lt3 x1 y1) = (term165 A B lt2 lt3 x1 y1).
Proof. exact (eq_refl (term169 A B lt2 lt3 x1 y1)). Qed.
Lemma lem364752 {A B : Type'} (lt2 : type1402 A) (x1 : A) (lt3 : type1402 B) (y1 : B) : (term169 A B lt2 lt3 x1 y1) = (term167 A B lt2 x1 lt3 y1).
Proof. exact (TRANS (@lem364751 A B lt2 lt3 x1 y1) (@lem364750 A B lt2 x1 lt3 y1)). Qed.
Lemma lem364753 {A B : Type'} (lt2 : type1402 A) (x1 : A) (lt3 : type1402 B) : term170 A B lt2 x1 lt3.
Proof. exact (fun y1 : B => @lem364752 A B lt2 x1 lt3 y1). Qed.
Lemma lem364754 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) : term171 A B lt2 lt3.
Proof. exact (fun x1 : A => @lem364753 A B lt2 x1 lt3). Qed.
Lemma lem364755 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) : term172 A B lt2 lt3.
Proof. exact (ex_intro (term173 A B lt2 lt3) (term174 A B lt2 lt3) (@lem364754 A B lt2 lt3)). Qed.
Lemma lem364757 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem364758 {A B : Type'} (a : type1210 A B) (b : type1210 A B) : (a = b) = (@GEQ ((prod A B) -> Prop) a b).
Proof. exact (@lem364757 (type1210 A B) a b). Qed.
Lemma lem364759 {A B : Type'} (_7913 : type1204 A B) (lt2 : type1402 A) (x1 : A) (lt3 : type1402 B) (y1 : B) : ((term91 A B _7913 x1 y1) = (term167 A B lt2 x1 lt3 y1)) = (term175 A B _7913 lt2 x1 lt3 y1).
Proof. exact (@lem364758 A B (term91 A B _7913 x1 y1) (term167 A B lt2 x1 lt3 y1)). Qed.
Lemma lem364760 {A B : Type'} (_7913 : type1204 A B) (lt2 : type1402 A) (x1 : A) (lt3 : type1402 B) : (term176 A B _7913 lt2 x1 lt3) = (term177 A B _7913 lt2 x1 lt3).
Proof. exact (fun_ext (fun y1 : B => @lem364759 A B _7913 lt2 x1 lt3 y1)). Qed.
Lemma lem364761 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem364762 {A B : Type'} (_7913 : type1204 A B) (lt2 : type1402 A) (x1 : A) (lt3 : type1402 B) : (term178 A B _7913 lt2 x1 lt3) = (term179 A B _7913 lt2 x1 lt3).
Proof. exact (MK_COMB (@lem364761 B) (@lem364760 A B _7913 lt2 x1 lt3)). Qed.
Lemma lem364763 {A B : Type'} (_7913 : type1204 A B) (lt2 : type1402 A) (lt3 : type1402 B) : (term180 A B _7913 lt2 lt3) = (term181 A B _7913 lt2 lt3).
Proof. exact (fun_ext (fun x1 : A => @lem364762 A B _7913 lt2 x1 lt3)). Qed.
Lemma lem364764 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem364765 {A B : Type'} (_7913 : type1204 A B) (lt2 : type1402 A) (lt3 : type1402 B) : (term182 A B _7913 lt2 lt3) = (term183 A B _7913 lt2 lt3).
Proof. exact (MK_COMB (@lem364764 A) (@lem364763 A B _7913 lt2 lt3)). Qed.
Lemma lem364766 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) : (term173 A B lt2 lt3) = (term184 A B lt2 lt3).
Proof. exact (fun_ext (fun _7913 : type1204 A B => @lem364765 A B _7913 lt2 lt3)). Qed.
Lemma lem364767 {A B : Type'} : (@ex ((prod A B) -> (prod A B) -> Prop)) = (@ex ((prod A B) -> (prod A B) -> Prop)).
Proof. exact (eq_refl (@ex ((prod A B) -> (prod A B) -> Prop))). Qed.
Lemma lem364768 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) : (term172 A B lt2 lt3) = (term185 A B lt2 lt3).
Proof. exact (MK_COMB (@lem364767 A B) (@lem364766 A B lt2 lt3)). Qed.
Lemma lem364769 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) : term185 A B lt2 lt3.
Proof. exact (EQ_MP (@lem364768 A B lt2 lt3) (@lem364755 A B lt2 lt3)). Qed.
Lemma lem364771 {_5076 : Type'} (P : _5076 -> Prop) : term103 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem364772 {A B : Type'} (P : type315 A B) : term104 A B P.
Proof. exact (@lem364771 (type1204 A B) P). Qed.
Lemma lem364773 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) : term186 A B lt2 lt3.
Proof. exact (@lem364772 A B (term184 A B lt2 lt3)). Qed.
Lemma lem364774 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) : term187 A B lt2 lt3.
Proof. exact (@lem364773 A B lt2 lt3 (@lem364769 A B lt2 lt3)). Qed.
Lemma lem364775 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) : (term187 A B lt2 lt3) = (term188 A B lt2 lt3).
Proof. exact (eq_refl (term187 A B lt2 lt3)). Qed.
Lemma lem364776 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) : term188 A B lt2 lt3.
Proof. exact (EQ_MP (@lem364775 A B lt2 lt3) (@lem364774 A B lt2 lt3)). Qed.
Lemma lem364777 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (x1 : A) : term189 A B lt2 lt3 x1.
Proof. exact (@lem364776 A B lt2 lt3 x1). Qed.
Lemma lem364778 {A B : Type'} (lt2 : type1402 A) (x1 : A) (lt3 : type1402 B) : (term189 A B lt2 lt3 x1) = (term190 A B lt2 x1 lt3).
Proof. exact (eq_refl (term189 A B lt2 lt3 x1)). Qed.
Lemma lem364779 {A B : Type'} (lt2 : type1402 A) (x1 : A) (lt3 : type1402 B) : term190 A B lt2 x1 lt3.
Proof. exact (EQ_MP (@lem364778 A B lt2 x1 lt3) (@lem364777 A B lt2 lt3 x1)). Qed.
Lemma lem364780 {A B : Type'} (lt2 : type1402 A) (x1 : A) (lt3 : type1402 B) (y1 : B) : term191 A B lt2 x1 lt3 y1.
Proof. exact (@lem364779 A B lt2 x1 lt3 y1). Qed.
Lemma lem364781 {A B : Type'} (lt2 : type1402 A) (x1 : A) (lt3 : type1402 B) (y1 : B) : (term191 A B lt2 x1 lt3 y1) = (term192 A B lt2 x1 lt3 y1).
Proof. exact (eq_refl (term191 A B lt2 x1 lt3 y1)). Qed.
Lemma lem364782 {A B : Type'} (lt2 : type1402 A) (x1 : A) (lt3 : type1402 B) (y1 : B) : term192 A B lt2 x1 lt3 y1.
Proof. exact (EQ_MP (@lem364781 A B lt2 x1 lt3 y1) (@lem364780 A B lt2 x1 lt3 y1)). Qed.
Lemma lem364784 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem364785 {A B : Type'} (a : type1210 A B) (b : type1210 A B) : (@GEQ ((prod A B) -> Prop) a b) = (a = b).
Proof. exact (@lem364784 (type1210 A B) a b). Qed.
Lemma lem364786 {A B : Type'} (lt2 : type1402 A) (x1 : A) (lt3 : type1402 B) (y1 : B) : (term192 A B lt2 x1 lt3 y1) = ((term193 A B lt2 lt3 x1 y1) = (term167 A B lt2 x1 lt3 y1)).
Proof. exact (@lem364785 A B (term193 A B lt2 lt3 x1 y1) (term167 A B lt2 x1 lt3 y1)). Qed.
Lemma lem364787 {A B : Type'} (lt2 : type1402 A) (x1 : A) (lt3 : type1402 B) (y1 : B) : (term193 A B lt2 lt3 x1 y1) = (term167 A B lt2 x1 lt3 y1).
Proof. exact (EQ_MP (@lem364786 A B lt2 x1 lt3 y1) (@lem364782 A B lt2 x1 lt3 y1)). Qed.
Lemma lem364788 {A B : Type'} (lt2 : type1402 A) (x1 : A) (lt3 : type1402 B) (y1 : B) : (term193 A B lt2 lt3 x1 y1) = (term167 A B lt2 x1 lt3 y1).
Proof. exact (@lem364787 A B lt2 x1 lt3 y1). Qed.
Lemma lem364789 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) : (term193 A B lt2 lt3 p1 p2) = (term167 A B lt2 p1 lt3 p2).
Proof. exact (@lem364788 A B lt2 p1 lt3 p2). Qed.
Lemma lem364808 {A B : Type'} (p1' : A) (p2' : B) : (@pair A B p1' p2') = (@pair A B p1' p2').
Proof. exact (eq_refl (@pair A B p1' p2')). Qed.
Lemma lem364809 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) (p1' : A) (p2' : B) : (term194 A B lt2 lt3 p1 p2 p1' p2') = (term195 A B lt2 p1 lt3 p2 p1' p2').
Proof. exact (MK_COMB (@lem364789 A B lt2 p1 lt3 p2) (@lem364808 A B p1' p2')). Qed.
Lemma lem364810 {A B : Type'} (a0 : A) (a1 : B) : a0 = (term65 A B a0 a1).
Proof. exact (@lem51128 A B a0 a1). Qed.
Lemma lem364811 {A B : Type'} (x2 : A) (y2 : B) : x2 = (term65 A B x2 y2).
Proof. exact (@lem364810 A B x2 y2). Qed.
Lemma lem364812 {A B : Type'} (a0 : A) (a1 : B) : a1 = (term66 A B a0 a1).
Proof. exact (@lem51159 A B a0 a1). Qed.
Lemma lem364813 {A B : Type'} (x2 : A) (y2 : B) : y2 = (term66 A B x2 y2).
Proof. exact (@lem364812 A B x2 y2). Qed.
Lemma lem364814 {A : Type'} (x2 : A) : x2 = x2.
Proof. exact (eq_refl x2). Qed.
Lemma lem364815 {A : Type'} : (term67 A) = (term67 A).
Proof. exact (eq_refl (term67 A)). Qed.
Lemma lem364816 {A B : Type'} (x2 : A) (y2 : B) : (term68 A x2) = (term69 A B x2 y2).
Proof. exact (MK_COMB (@lem364815 A) (@lem364811 A B x2 y2)). Qed.
Lemma lem364817 {A B : Type'} (x2 : A) (y2 : B) : (term69 A B x2 y2) = (term65 A B x2 y2).
Proof. exact (eq_refl (term69 A B x2 y2)). Qed.
Lemma lem364818 {A : Type'} (x2 : A) : (term70 A x2) = (term70 A x2).
Proof. exact (eq_refl (term70 A x2)). Qed.
Lemma lem364819 {A B : Type'} (x2 : A) (y2 : B) : ((term68 A x2) = (term69 A B x2 y2)) = ((term68 A x2) = (term65 A B x2 y2)).
Proof. exact (MK_COMB (@lem364818 A x2) (@lem364817 A B x2 y2)). Qed.
Lemma lem364820 {A : Type'} (x2 : A) : (term68 A x2) = x2.
Proof. exact (eq_refl (term68 A x2)). Qed.
Lemma lem364821 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem364822 {A : Type'} (x2 : A) : (term70 A x2) = (@eq A x2).
Proof. exact (MK_COMB (@lem364821 A) (@lem364820 A x2)). Qed.
Lemma lem364823 {A B : Type'} (x2 : A) (y2 : B) : (term65 A B x2 y2) = (term65 A B x2 y2).
Proof. exact (eq_refl (term65 A B x2 y2)). Qed.
Lemma lem364824 {A B : Type'} (x2 : A) (y2 : B) : ((term68 A x2) = (term65 A B x2 y2)) = (x2 = (term65 A B x2 y2)).
Proof. exact (MK_COMB (@lem364822 A x2) (@lem364823 A B x2 y2)). Qed.
Lemma lem364825 {A B : Type'} (x2 : A) (y2 : B) : ((term68 A x2) = (term69 A B x2 y2)) = (x2 = (term65 A B x2 y2)).
Proof. exact (TRANS (@lem364819 A B x2 y2) (@lem364824 A B x2 y2)). Qed.
Lemma lem364826 {A B : Type'} (x2 : A) (y2 : B) : x2 = (term65 A B x2 y2).
Proof. exact (EQ_MP (@lem364825 A B x2 y2) (@lem364816 A B x2 y2)). Qed.
Lemma lem364827 {A : Type'} (x2 : A) : (@eq A x2) = (@eq A x2).
Proof. exact (eq_refl (@eq A x2)). Qed.
Lemma lem364828 {A B : Type'} (x2 : A) (y2 : B) : (x2 = x2) = (x2 = (term65 A B x2 y2)).
Proof. exact (MK_COMB (@lem364827 A x2) (@lem364826 A B x2 y2)). Qed.
Lemma lem364829 {A B : Type'} (x2 : A) (y2 : B) : x2 = (term65 A B x2 y2).
Proof. exact (EQ_MP (@lem364828 A B x2 y2) (@lem364814 A x2)). Qed.
Lemma lem364830 {B : Type'} (y2 : B) : y2 = y2.
Proof. exact (eq_refl y2). Qed.
Lemma lem364831 {B : Type'} : (term67 B) = (term67 B).
Proof. exact (eq_refl (term67 B)). Qed.
Lemma lem364832 {A B : Type'} (x2 : A) (y2 : B) : (term68 B y2) = (term71 A B x2 y2).
Proof. exact (MK_COMB (@lem364831 B) (@lem364813 A B x2 y2)). Qed.
Lemma lem364833 {A B : Type'} (x2 : A) (y2 : B) : (term71 A B x2 y2) = (term66 A B x2 y2).
Proof. exact (eq_refl (term71 A B x2 y2)). Qed.
Lemma lem364834 {B : Type'} (y2 : B) : (term70 B y2) = (term70 B y2).
Proof. exact (eq_refl (term70 B y2)). Qed.
Lemma lem364835 {A B : Type'} (x2 : A) (y2 : B) : ((term68 B y2) = (term71 A B x2 y2)) = ((term68 B y2) = (term66 A B x2 y2)).
Proof. exact (MK_COMB (@lem364834 B y2) (@lem364833 A B x2 y2)). Qed.
Lemma lem364836 {B : Type'} (y2 : B) : (term68 B y2) = y2.
Proof. exact (eq_refl (term68 B y2)). Qed.
Lemma lem364837 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem364838 {B : Type'} (y2 : B) : (term70 B y2) = (@eq B y2).
Proof. exact (MK_COMB (@lem364837 B) (@lem364836 B y2)). Qed.
Lemma lem364839 {A B : Type'} (x2 : A) (y2 : B) : (term66 A B x2 y2) = (term66 A B x2 y2).
Proof. exact (eq_refl (term66 A B x2 y2)). Qed.
Lemma lem364840 {A B : Type'} (x2 : A) (y2 : B) : ((term68 B y2) = (term66 A B x2 y2)) = (y2 = (term66 A B x2 y2)).
Proof. exact (MK_COMB (@lem364838 B y2) (@lem364839 A B x2 y2)). Qed.
Lemma lem364841 {A B : Type'} (x2 : A) (y2 : B) : ((term68 B y2) = (term71 A B x2 y2)) = (y2 = (term66 A B x2 y2)).
Proof. exact (TRANS (@lem364835 A B x2 y2) (@lem364840 A B x2 y2)). Qed.
Lemma lem364842 {A B : Type'} (x2 : A) (y2 : B) : y2 = (term66 A B x2 y2).
Proof. exact (EQ_MP (@lem364841 A B x2 y2) (@lem364832 A B x2 y2)). Qed.
Lemma lem364843 {B : Type'} (y2 : B) : (@eq B y2) = (@eq B y2).
Proof. exact (eq_refl (@eq B y2)). Qed.
Lemma lem364844 {A B : Type'} (x2 : A) (y2 : B) : (y2 = y2) = (y2 = (term66 A B x2 y2)).
Proof. exact (MK_COMB (@lem364843 B y2) (@lem364842 A B x2 y2)). Qed.
Lemma lem364845 {A B : Type'} (x2 : A) (y2 : B) : y2 = (term66 A B x2 y2).
Proof. exact (EQ_MP (@lem364844 A B x2 y2) (@lem364830 B y2)). Qed.
Lemma lem364846 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) : (term196 A B lt2 p1 lt3 p2) = (term196 A B lt2 p1 lt3 p2).
Proof. exact (eq_refl (term196 A B lt2 p1 lt3 p2)). Qed.
Lemma lem364847 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) (x2 : A) (y2 : B) : (term197 A B lt2 p1 lt3 p2 x2) = (term198 A B lt2 p1 lt3 p2 x2 y2).
Proof. exact (MK_COMB (@lem364846 A B lt2 p1 lt3 p2) (@lem364829 A B x2 y2)). Qed.
Lemma lem364848 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (y2 : B) (lt3 : type1402 B) (p2 : B) : (term198 A B lt2 p1 lt3 p2 x2 y2) = (term199 A B lt2 p1 x2 y2 lt3 p2).
Proof. exact (eq_refl (term198 A B lt2 p1 lt3 p2 x2 y2)). Qed.
Lemma lem364849 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) (x2 : A) : (term200 A B lt2 p1 lt3 p2 x2) = (term200 A B lt2 p1 lt3 p2 x2).
Proof. exact (eq_refl (term200 A B lt2 p1 lt3 p2 x2)). Qed.
Lemma lem364850 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (y2 : B) (lt3 : type1402 B) (p2 : B) : ((term197 A B lt2 p1 lt3 p2 x2) = (term198 A B lt2 p1 lt3 p2 x2 y2)) = ((term197 A B lt2 p1 lt3 p2 x2) = (term199 A B lt2 p1 x2 y2 lt3 p2)).
Proof. exact (MK_COMB (@lem364849 A B lt2 p1 lt3 p2 x2) (@lem364848 A B lt2 p1 x2 y2 lt3 p2)). Qed.
Lemma lem364851 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (lt3 : type1402 B) (p2 : B) : (term197 A B lt2 p1 lt3 p2 x2) = (term201 A B lt2 p1 x2 lt3 p2).
Proof. exact (eq_refl (term197 A B lt2 p1 lt3 p2 x2)). Qed.
Lemma lem364852 {B : Type'} : (@eq (B -> Prop)) = (@eq (B -> Prop)).
Proof. exact (eq_refl (@eq (B -> Prop))). Qed.
Lemma lem364853 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (lt3 : type1402 B) (p2 : B) : (term200 A B lt2 p1 lt3 p2 x2) = (term202 A B lt2 p1 x2 lt3 p2).
Proof. exact (MK_COMB (@lem364852 B) (@lem364851 A B lt2 p1 x2 lt3 p2)). Qed.
Lemma lem364854 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (y2 : B) (lt3 : type1402 B) (p2 : B) : (term199 A B lt2 p1 x2 y2 lt3 p2) = (term199 A B lt2 p1 x2 y2 lt3 p2).
Proof. exact (eq_refl (term199 A B lt2 p1 x2 y2 lt3 p2)). Qed.
Lemma lem364855 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (y2 : B) (lt3 : type1402 B) (p2 : B) : ((term197 A B lt2 p1 lt3 p2 x2) = (term199 A B lt2 p1 x2 y2 lt3 p2)) = ((term201 A B lt2 p1 x2 lt3 p2) = (term199 A B lt2 p1 x2 y2 lt3 p2)).
Proof. exact (MK_COMB (@lem364853 A B lt2 p1 x2 lt3 p2) (@lem364854 A B lt2 p1 x2 y2 lt3 p2)). Qed.
Lemma lem364856 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (y2 : B) (lt3 : type1402 B) (p2 : B) : ((term197 A B lt2 p1 lt3 p2 x2) = (term198 A B lt2 p1 lt3 p2 x2 y2)) = ((term201 A B lt2 p1 x2 lt3 p2) = (term199 A B lt2 p1 x2 y2 lt3 p2)).
Proof. exact (TRANS (@lem364850 A B lt2 p1 x2 y2 lt3 p2) (@lem364855 A B lt2 p1 x2 y2 lt3 p2)). Qed.
Lemma lem364857 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (y2 : B) (lt3 : type1402 B) (p2 : B) : (term201 A B lt2 p1 x2 lt3 p2) = (term199 A B lt2 p1 x2 y2 lt3 p2).
Proof. exact (EQ_MP (@lem364856 A B lt2 p1 x2 y2 lt3 p2) (@lem364847 A B lt2 p1 lt3 p2 x2 y2)). Qed.
Lemma lem364858 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) (x2 : A) (y2 : B) : (term203 A B lt2 p1 x2 lt3 p2 y2) = (term204 A B lt2 p1 lt3 p2 x2 y2).
Proof. exact (MK_COMB (@lem364857 A B lt2 p1 x2 y2 lt3 p2) (@lem364845 A B x2 y2)). Qed.
Lemma lem364859 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) (x2 : A) (y2 : B) : (term204 A B lt2 p1 lt3 p2 x2 y2) = (term205 A B lt2 p1 lt3 p2 x2 y2).
Proof. exact (eq_refl (term204 A B lt2 p1 lt3 p2 x2 y2)). Qed.
Lemma lem364860 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (lt3 : type1402 B) (p2 : B) (y2 : B) : (term206 A B lt2 p1 x2 lt3 p2 y2) = (term206 A B lt2 p1 x2 lt3 p2 y2).
Proof. exact (eq_refl (term206 A B lt2 p1 x2 lt3 p2 y2)). Qed.
Lemma lem364861 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) (x2 : A) (y2 : B) : ((term203 A B lt2 p1 x2 lt3 p2 y2) = (term204 A B lt2 p1 lt3 p2 x2 y2)) = ((term203 A B lt2 p1 x2 lt3 p2 y2) = (term205 A B lt2 p1 lt3 p2 x2 y2)).
Proof. exact (MK_COMB (@lem364860 A B lt2 p1 x2 lt3 p2 y2) (@lem364859 A B lt2 p1 lt3 p2 x2 y2)). Qed.
Lemma lem364862 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (lt3 : type1402 B) (p2 : B) (y2 : B) : (term203 A B lt2 p1 x2 lt3 p2 y2) = (term207 A B lt2 p1 x2 lt3 p2 y2).
Proof. exact (eq_refl (term203 A B lt2 p1 x2 lt3 p2 y2)). Qed.
Lemma lem364863 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem364864 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (lt3 : type1402 B) (p2 : B) (y2 : B) : (term206 A B lt2 p1 x2 lt3 p2 y2) = (term208 A B lt2 p1 x2 lt3 p2 y2).
Proof. exact (MK_COMB (@lem364863) (@lem364862 A B lt2 p1 x2 lt3 p2 y2)). Qed.
Lemma lem364865 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) (x2 : A) (y2 : B) : (term205 A B lt2 p1 lt3 p2 x2 y2) = (term205 A B lt2 p1 lt3 p2 x2 y2).
Proof. exact (eq_refl (term205 A B lt2 p1 lt3 p2 x2 y2)). Qed.
Lemma lem364866 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) (x2 : A) (y2 : B) : ((term203 A B lt2 p1 x2 lt3 p2 y2) = (term205 A B lt2 p1 lt3 p2 x2 y2)) = ((term207 A B lt2 p1 x2 lt3 p2 y2) = (term205 A B lt2 p1 lt3 p2 x2 y2)).
Proof. exact (MK_COMB (@lem364864 A B lt2 p1 x2 lt3 p2 y2) (@lem364865 A B lt2 p1 lt3 p2 x2 y2)). Qed.
Lemma lem364867 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) (x2 : A) (y2 : B) : ((term203 A B lt2 p1 x2 lt3 p2 y2) = (term204 A B lt2 p1 lt3 p2 x2 y2)) = ((term207 A B lt2 p1 x2 lt3 p2 y2) = (term205 A B lt2 p1 lt3 p2 x2 y2)).
Proof. exact (TRANS (@lem364861 A B lt2 p1 lt3 p2 x2 y2) (@lem364866 A B lt2 p1 lt3 p2 x2 y2)). Qed.
Lemma lem364868 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) (x2 : A) (y2 : B) : (term207 A B lt2 p1 x2 lt3 p2 y2) = (term205 A B lt2 p1 lt3 p2 x2 y2).
Proof. exact (EQ_MP (@lem364867 A B lt2 p1 lt3 p2 x2 y2) (@lem364858 A B lt2 p1 lt3 p2 x2 y2)). Qed.
Lemma lem364869 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (lt3 : type1402 B) (p2 : B) (y2 : B) : (term205 A B lt2 p1 lt3 p2 x2 y2) = (term207 A B lt2 p1 x2 lt3 p2 y2).
Proof. exact (SYM (@lem364868 A B lt2 p1 lt3 p2 x2 y2)). Qed.
Lemma lem364870 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) (x2 : A) (y2 : B) : (term209 A B lt2 p1 lt3 p2 x2 y2) = (term205 A B lt2 p1 lt3 p2 x2 y2).
Proof. exact (eq_refl (term209 A B lt2 p1 lt3 p2 x2 y2)). Qed.
Lemma lem364871 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (lt3 : type1402 B) (p2 : B) (y2 : B) : (term209 A B lt2 p1 lt3 p2 x2 y2) = (term207 A B lt2 p1 x2 lt3 p2 y2).
Proof. exact (TRANS (@lem364870 A B lt2 p1 lt3 p2 x2 y2) (@lem364869 A B lt2 p1 x2 lt3 p2 y2)). Qed.
Lemma lem364872 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (lt3 : type1402 B) (p2 : B) : term210 A B lt2 p1 x2 lt3 p2.
Proof. exact (fun y2 : B => @lem364871 A B lt2 p1 x2 lt3 p2 y2). Qed.
Lemma lem364873 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) : term211 A B lt2 p1 lt3 p2.
Proof. exact (fun x2 : A => @lem364872 A B lt2 p1 x2 lt3 p2). Qed.
Lemma lem364874 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) : term212 A B lt2 p1 lt3 p2.
Proof. exact (ex_intro (term213 A B lt2 p1 lt3 p2) (term214 A B lt2 p1 lt3 p2) (@lem364873 A B lt2 p1 lt3 p2)). Qed.
Lemma lem364876 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem364877 (a : Prop) (b : Prop) : (a = b) = (@GEQ Prop a b).
Proof. exact (@lem364876 Prop a b). Qed.
Lemma lem364878 {A B : Type'} (_7925 : type1210 A B) (lt2 : type1402 A) (p1 : A) (x2 : A) (lt3 : type1402 B) (p2 : B) (y2 : B) : ((term134 A B _7925 x2 y2) = (term207 A B lt2 p1 x2 lt3 p2 y2)) = (term215 A B _7925 lt2 p1 x2 lt3 p2 y2).
Proof. exact (@lem364877 (term134 A B _7925 x2 y2) (term207 A B lt2 p1 x2 lt3 p2 y2)). Qed.
Lemma lem364879 {A B : Type'} (_7925 : type1210 A B) (lt2 : type1402 A) (p1 : A) (x2 : A) (lt3 : type1402 B) (p2 : B) : (term216 A B _7925 lt2 p1 x2 lt3 p2) = (term217 A B _7925 lt2 p1 x2 lt3 p2).
Proof. exact (fun_ext (fun y2 : B => @lem364878 A B _7925 lt2 p1 x2 lt3 p2 y2)). Qed.
Lemma lem364880 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem364881 {A B : Type'} (_7925 : type1210 A B) (lt2 : type1402 A) (p1 : A) (x2 : A) (lt3 : type1402 B) (p2 : B) : (term218 A B _7925 lt2 p1 x2 lt3 p2) = (term219 A B _7925 lt2 p1 x2 lt3 p2).
Proof. exact (MK_COMB (@lem364880 B) (@lem364879 A B _7925 lt2 p1 x2 lt3 p2)). Qed.
Lemma lem364882 {A B : Type'} (_7925 : type1210 A B) (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) : (term220 A B _7925 lt2 p1 lt3 p2) = (term221 A B _7925 lt2 p1 lt3 p2).
Proof. exact (fun_ext (fun x2 : A => @lem364881 A B _7925 lt2 p1 x2 lt3 p2)). Qed.
Lemma lem364883 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem364884 {A B : Type'} (_7925 : type1210 A B) (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) : (term222 A B _7925 lt2 p1 lt3 p2) = (term223 A B _7925 lt2 p1 lt3 p2).
Proof. exact (MK_COMB (@lem364883 A) (@lem364882 A B _7925 lt2 p1 lt3 p2)). Qed.
Lemma lem364885 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) : (term213 A B lt2 p1 lt3 p2) = (term224 A B lt2 p1 lt3 p2).
Proof. exact (fun_ext (fun _7925 : type1210 A B => @lem364884 A B _7925 lt2 p1 lt3 p2)). Qed.
Lemma lem364886 {A B : Type'} : (@ex ((prod A B) -> Prop)) = (@ex ((prod A B) -> Prop)).
Proof. exact (eq_refl (@ex ((prod A B) -> Prop))). Qed.
Lemma lem364887 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) : (term212 A B lt2 p1 lt3 p2) = (term225 A B lt2 p1 lt3 p2).
Proof. exact (MK_COMB (@lem364886 A B) (@lem364885 A B lt2 p1 lt3 p2)). Qed.
Lemma lem364888 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) : term225 A B lt2 p1 lt3 p2.
Proof. exact (EQ_MP (@lem364887 A B lt2 p1 lt3 p2) (@lem364874 A B lt2 p1 lt3 p2)). Qed.
Lemma lem364890 {_5076 : Type'} (P : _5076 -> Prop) : term103 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem364891 {A B : Type'} (P : type324 A B) : term146 A B P.
Proof. exact (@lem364890 (type1210 A B) P). Qed.
Lemma lem364892 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) : term226 A B lt2 p1 lt3 p2.
Proof. exact (@lem364891 A B (term224 A B lt2 p1 lt3 p2)). Qed.
Lemma lem364893 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) : term227 A B lt2 p1 lt3 p2.
Proof. exact (@lem364892 A B lt2 p1 lt3 p2 (@lem364888 A B lt2 p1 lt3 p2)). Qed.
Lemma lem364894 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) : (term227 A B lt2 p1 lt3 p2) = (term228 A B lt2 p1 lt3 p2).
Proof. exact (eq_refl (term227 A B lt2 p1 lt3 p2)). Qed.
Lemma lem364895 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) : term228 A B lt2 p1 lt3 p2.
Proof. exact (EQ_MP (@lem364894 A B lt2 p1 lt3 p2) (@lem364893 A B lt2 p1 lt3 p2)). Qed.
Lemma lem364896 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) (x2 : A) : term229 A B lt2 p1 lt3 p2 x2.
Proof. exact (@lem364895 A B lt2 p1 lt3 p2 x2). Qed.
Lemma lem364897 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (lt3 : type1402 B) (p2 : B) : (term229 A B lt2 p1 lt3 p2 x2) = (term230 A B lt2 p1 x2 lt3 p2).
Proof. exact (eq_refl (term229 A B lt2 p1 lt3 p2 x2)). Qed.
Lemma lem364898 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (lt3 : type1402 B) (p2 : B) : term230 A B lt2 p1 x2 lt3 p2.
Proof. exact (EQ_MP (@lem364897 A B lt2 p1 x2 lt3 p2) (@lem364896 A B lt2 p1 lt3 p2 x2)). Qed.
Lemma lem364899 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (lt3 : type1402 B) (p2 : B) (y2 : B) : term231 A B lt2 p1 x2 lt3 p2 y2.
Proof. exact (@lem364898 A B lt2 p1 x2 lt3 p2 y2). Qed.
Lemma lem364900 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (lt3 : type1402 B) (p2 : B) (y2 : B) : (term231 A B lt2 p1 x2 lt3 p2 y2) = (term232 A B lt2 p1 x2 lt3 p2 y2).
Proof. exact (eq_refl (term231 A B lt2 p1 x2 lt3 p2 y2)). Qed.
Lemma lem364901 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (lt3 : type1402 B) (p2 : B) (y2 : B) : term232 A B lt2 p1 x2 lt3 p2 y2.
Proof. exact (EQ_MP (@lem364900 A B lt2 p1 x2 lt3 p2 y2) (@lem364899 A B lt2 p1 x2 lt3 p2 y2)). Qed.
Lemma lem364903 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem364904 (a : Prop) (b : Prop) : (@GEQ Prop a b) = (a = b).
Proof. exact (@lem364903 Prop a b). Qed.
Lemma lem364905 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (lt3 : type1402 B) (p2 : B) (y2 : B) : (term232 A B lt2 p1 x2 lt3 p2 y2) = ((term195 A B lt2 p1 lt3 p2 x2 y2) = (term207 A B lt2 p1 x2 lt3 p2 y2)).
Proof. exact (@lem364904 (term195 A B lt2 p1 lt3 p2 x2 y2) (term207 A B lt2 p1 x2 lt3 p2 y2)). Qed.
Lemma lem364906 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (lt3 : type1402 B) (p2 : B) (y2 : B) : (term195 A B lt2 p1 lt3 p2 x2 y2) = (term207 A B lt2 p1 x2 lt3 p2 y2).
Proof. exact (EQ_MP (@lem364905 A B lt2 p1 x2 lt3 p2 y2) (@lem364901 A B lt2 p1 x2 lt3 p2 y2)). Qed.
Lemma lem364907 {A B : Type'} (lt2 : type1402 A) (p1 : A) (x2 : A) (lt3 : type1402 B) (p2 : B) (y2 : B) : (term195 A B lt2 p1 lt3 p2 x2 y2) = (term207 A B lt2 p1 x2 lt3 p2 y2).
Proof. exact (@lem364906 A B lt2 p1 x2 lt3 p2 y2). Qed.
Lemma lem364908 {A B : Type'} (lt2 : type1402 A) (p1 : A) (p1' : A) (lt3 : type1402 B) (p2 : B) (p2' : B) : (term195 A B lt2 p1 lt3 p2 p1' p2') = (term207 A B lt2 p1 p1' lt3 p2 p2').
Proof. exact (@lem364907 A B lt2 p1 p1' lt3 p2 p2'). Qed.
Lemma lem364915 {A B : Type'} (lt2 : type1402 A) (p1 : A) (p1' : A) (lt3 : type1402 B) (p2 : B) (p2' : B) : (term194 A B lt2 lt3 p1 p2 p1' p2') = (term207 A B lt2 p1 p1' lt3 p2 p2').
Proof. exact (TRANS (@lem364809 A B lt2 p1 lt3 p2 p1' p2') (@lem364908 A B lt2 p1 p1' lt3 p2 p2')). Qed.
Lemma lem364916 {A B : Type'} (lt2 : type1402 A) (p1 : A) (p1' : A) (lt3 : type1402 B) (p2 : B) (p2' : B) : (term57 A B lt2 lt3 p1 p2 p1' p2') = (term233 A B lt2 p1 p1' lt3 p2 p2').
Proof. exact (MK_COMB (@lem364690 A B lt2 p1 p1' lt3 p2 p2') (@lem364915 A B lt2 p1 p1' lt3 p2 p2')). Qed.
Lemma lem364919 {A B : Type'} (lt2 : type1402 A) (p1 : A) (p1' : A) (lt3 : type1402 B) (p2 : B) : (term59 A B lt2 lt3 p1 p2 p1') = (term234 A B lt2 p1 p1' lt3 p2).
Proof. exact (fun_ext (fun p2' : B => @lem364916 A B lt2 p1 p1' lt3 p2 p2')). Qed.
Lemma lem364920 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem364921 {A B : Type'} (lt2 : type1402 A) (p1 : A) (p1' : A) (lt3 : type1402 B) (p2 : B) : (term61 A B lt2 lt3 p1 p2 p1') = (term235 A B lt2 p1 p1' lt3 p2).
Proof. exact (MK_COMB (@lem364920 B) (@lem364919 A B lt2 p1 p1' lt3 p2)). Qed.
Lemma lem364928 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) : (term63 A B lt2 lt3 p1 p2) = (term236 A B lt2 p1 lt3 p2).
Proof. exact (fun_ext (fun p1' : A => @lem364921 A B lt2 p1 p1' lt3 p2)). Qed.
Lemma lem364929 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem364930 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) : (term64 A B lt2 lt3 p1 p2) = (term237 A B lt2 p1 lt3 p2).
Proof. exact (MK_COMB (@lem364929 A) (@lem364928 A B lt2 p1 lt3 p2)). Qed.
Lemma lem364937 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) : (term40 A B lt2 lt3 p1 p2) = (term237 A B lt2 p1 lt3 p2).
Proof. exact (TRANS (@lem364457 A B lt2 lt3 p1 p2) (@lem364930 A B lt2 p1 lt3 p2)). Qed.
Lemma lem364938 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) : (term42 A B lt2 lt3 p1) = (term238 A B lt2 p1 lt3).
Proof. exact (fun_ext (fun p2 : B => @lem364937 A B lt2 p1 lt3 p2)). Qed.
Lemma lem364939 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem364940 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) : (term44 A B lt2 lt3 p1) = (term239 A B lt2 p1 lt3).
Proof. exact (MK_COMB (@lem364939 B) (@lem364938 A B lt2 p1 lt3)). Qed.
Lemma lem364947 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) : (term46 A B lt2 lt3) = (term240 A B lt2 lt3).
Proof. exact (fun_ext (fun p1 : A => @lem364940 A B lt2 p1 lt3)). Qed.
Lemma lem364948 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem364949 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) : (term47 A B lt2 lt3) = (term241 A B lt2 lt3).
Proof. exact (MK_COMB (@lem364948 A) (@lem364947 A B lt2 lt3)). Qed.
Lemma lem364956 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) : (term36 A B lt2 lt3) = (term241 A B lt2 lt3).
Proof. exact (TRANS (@lem364422 A B lt2 lt3) (@lem364949 A B lt2 lt3)). Qed.
Lemma lem364957 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) : (term241 A B lt2 lt3) = (term36 A B lt2 lt3).
Proof. exact (SYM (@lem364956 A B lt2 lt3)). Qed.
Lemma lem364970 {A : Type'} (lt2 : type1402 A) (p1 : A) (p1' : A) : term242 A lt2 p1 p1'.
Proof. exact (@lem9851 (lt2 p1 p1')). Qed.
Lemma lem364971 {A : Type'} (lt2 : type1402 A) (p1 : A) (p1' : A) : (term242 A lt2 p1 p1') = (term243 A lt2 p1 p1').
Proof. exact (eq_refl (term242 A lt2 p1 p1')). Qed.
Lemma lem364972 {A : Type'} (lt2 : type1402 A) (p1 : A) (p1' : A) : term243 A lt2 p1 p1'.
Proof. exact (EQ_MP (@lem364971 A lt2 p1 p1') (@lem364970 A lt2 p1 p1')). Qed.
Lemma lem364973 {A : Type'} (lt2 : type1402 A) (p1 : A) (p1' : A) (h1 : (lt2 p1 p1') = True) : (lt2 p1 p1') = True.
Proof. exact (h1). Qed.
Lemma lem364974 {A : Type'} (lt2 : type1402 A) (p1 : A) (p1' : A) (h1 : (lt2 p1 p1') = False) : (lt2 p1 p1') = False.
Proof. exact (h1). Qed.
Lemma lem364987 {A B : Type'} (p1 : A) (p1' : A) (lt3 : type1402 B) (p2 : B) (p2' : B) : (term244 A B p1 p1' lt3 p2 p2') = (term244 A B p1 p1' lt3 p2 p2').
Proof. exact (eq_refl (term244 A B p1 p1' lt3 p2 p2')). Qed.
Lemma lem364988 {A B : Type'} (lt3 : type1402 B) (p2 : B) (p2' : B) (lt2 : type1402 A) (p1 : A) (p1' : A) (h1 : (lt2 p1 p1') = True) : (term245 A B lt3 p2 p2' lt2 p1 p1') = (term246 A B p1 p1' lt3 p2 p2').
Proof. exact (MK_COMB (@lem364987 A B p1 p1' lt3 p2 p2') (@lem364973 A lt2 p1 p1' h1)). Qed.
Lemma lem364989 {A B : Type'} (p1 : A) (p1' : A) (lt3 : type1402 B) (p2 : B) (p2' : B) : (term246 A B p1 p1' lt3 p2 p2') = (term247 A B p1 p1' lt3 p2 p2').
Proof. exact (eq_refl (term246 A B p1 p1' lt3 p2 p2')). Qed.
Lemma lem364990 {A B : Type'} (lt3 : type1402 B) (p2 : B) (p2' : B) (lt2 : type1402 A) (p1 : A) (p1' : A) : (term248 A B lt3 p2 p2' lt2 p1 p1') = (term248 A B lt3 p2 p2' lt2 p1 p1').
Proof. exact (eq_refl (term248 A B lt3 p2 p2' lt2 p1 p1')). Qed.
Lemma lem364991 {A B : Type'} (lt2 : type1402 A) (p1 : A) (p1' : A) (lt3 : type1402 B) (p2 : B) (p2' : B) : ((term245 A B lt3 p2 p2' lt2 p1 p1') = (term246 A B p1 p1' lt3 p2 p2')) = ((term245 A B lt3 p2 p2' lt2 p1 p1') = (term247 A B p1 p1' lt3 p2 p2')).
Proof. exact (MK_COMB (@lem364990 A B lt3 p2 p2' lt2 p1 p1') (@lem364989 A B p1 p1' lt3 p2 p2')). Qed.
Lemma lem364992 {A B : Type'} (lt2 : type1402 A) (p1 : A) (p1' : A) (lt3 : type1402 B) (p2 : B) (p2' : B) : (term245 A B lt3 p2 p2' lt2 p1 p1') = (term233 A B lt2 p1 p1' lt3 p2 p2').
Proof. exact (eq_refl (term245 A B lt3 p2 p2' lt2 p1 p1')). Qed.
Lemma lem364993 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem364994 {A B : Type'} (lt2 : type1402 A) (p1 : A) (p1' : A) (lt3 : type1402 B) (p2 : B) (p2' : B) : (term248 A B lt3 p2 p2' lt2 p1 p1') = (term249 A B lt2 p1 p1' lt3 p2 p2').
Proof. exact (MK_COMB (@lem364993) (@lem364992 A B lt2 p1 p1' lt3 p2 p2')). Qed.
Lemma lem364995 {A B : Type'} (p1 : A) (p1' : A) (lt3 : type1402 B) (p2 : B) (p2' : B) : (term247 A B p1 p1' lt3 p2 p2') = (term247 A B p1 p1' lt3 p2 p2').
Proof. exact (eq_refl (term247 A B p1 p1' lt3 p2 p2')). Qed.
Lemma lem364996 {A B : Type'} (lt2 : type1402 A) (p1 : A) (p1' : A) (lt3 : type1402 B) (p2 : B) (p2' : B) : ((term245 A B lt3 p2 p2' lt2 p1 p1') = (term247 A B p1 p1' lt3 p2 p2')) = ((term233 A B lt2 p1 p1' lt3 p2 p2') = (term247 A B p1 p1' lt3 p2 p2')).
Proof. exact (MK_COMB (@lem364994 A B lt2 p1 p1' lt3 p2 p2') (@lem364995 A B p1 p1' lt3 p2 p2')). Qed.
Lemma lem364997 {A B : Type'} (lt2 : type1402 A) (p1 : A) (p1' : A) (lt3 : type1402 B) (p2 : B) (p2' : B) : ((term245 A B lt3 p2 p2' lt2 p1 p1') = (term246 A B p1 p1' lt3 p2 p2')) = ((term233 A B lt2 p1 p1' lt3 p2 p2') = (term247 A B p1 p1' lt3 p2 p2')).
Proof. exact (TRANS (@lem364991 A B lt2 p1 p1' lt3 p2 p2') (@lem364996 A B lt2 p1 p1' lt3 p2 p2')). Qed.
Lemma lem364998 {A B : Type'} (lt3 : type1402 B) (p2 : B) (p2' : B) (lt2 : type1402 A) (p1 : A) (p1' : A) (h1 : (lt2 p1 p1') = True) : (term233 A B lt2 p1 p1' lt3 p2 p2') = (term247 A B p1 p1' lt3 p2 p2').
Proof. exact (EQ_MP (@lem364997 A B lt2 p1 p1' lt3 p2 p2') (@lem364988 A B lt3 p2 p2' lt2 p1 p1' h1)). Qed.
Lemma lem364999 {A B : Type'} (lt3 : type1402 B) (p2 : B) (p2' : B) (lt2 : type1402 A) (p1 : A) (p1' : A) (h1 : (lt2 p1 p1') = True) : (term247 A B p1 p1' lt3 p2 p2') = (term233 A B lt2 p1 p1' lt3 p2 p2').
Proof. exact (SYM (@lem364998 A B lt3 p2 p2' lt2 p1 p1' h1)). Qed.
Lemma lem365000 {A B : Type'} (p1 : A) (p1' : A) (lt3 : type1402 B) (p2 : B) (p2' : B) : (term244 A B p1 p1' lt3 p2 p2') = (term244 A B p1 p1' lt3 p2 p2').
Proof. exact (eq_refl (term244 A B p1 p1' lt3 p2 p2')). Qed.
Lemma lem365001 {A B : Type'} (lt3 : type1402 B) (p2 : B) (p2' : B) (lt2 : type1402 A) (p1 : A) (p1' : A) (h1 : (lt2 p1 p1') = False) : (term245 A B lt3 p2 p2' lt2 p1 p1') = (term250 A B p1 p1' lt3 p2 p2').
Proof. exact (MK_COMB (@lem365000 A B p1 p1' lt3 p2 p2') (@lem364974 A lt2 p1 p1' h1)). Qed.
Lemma lem365002 {A B : Type'} (p1 : A) (p1' : A) (lt3 : type1402 B) (p2 : B) (p2' : B) : (term250 A B p1 p1' lt3 p2 p2') = (term251 A B p1 p1' lt3 p2 p2').
Proof. exact (eq_refl (term250 A B p1 p1' lt3 p2 p2')). Qed.
Lemma lem365003 {A B : Type'} (lt3 : type1402 B) (p2 : B) (p2' : B) (lt2 : type1402 A) (p1 : A) (p1' : A) : (term248 A B lt3 p2 p2' lt2 p1 p1') = (term248 A B lt3 p2 p2' lt2 p1 p1').
Proof. exact (eq_refl (term248 A B lt3 p2 p2' lt2 p1 p1')). Qed.
Lemma lem365004 {A B : Type'} (lt2 : type1402 A) (p1 : A) (p1' : A) (lt3 : type1402 B) (p2 : B) (p2' : B) : ((term245 A B lt3 p2 p2' lt2 p1 p1') = (term250 A B p1 p1' lt3 p2 p2')) = ((term245 A B lt3 p2 p2' lt2 p1 p1') = (term251 A B p1 p1' lt3 p2 p2')).
Proof. exact (MK_COMB (@lem365003 A B lt3 p2 p2' lt2 p1 p1') (@lem365002 A B p1 p1' lt3 p2 p2')). Qed.
Lemma lem365005 {A B : Type'} (lt2 : type1402 A) (p1 : A) (p1' : A) (lt3 : type1402 B) (p2 : B) (p2' : B) : (term245 A B lt3 p2 p2' lt2 p1 p1') = (term233 A B lt2 p1 p1' lt3 p2 p2').
Proof. exact (eq_refl (term245 A B lt3 p2 p2' lt2 p1 p1')). Qed.
Lemma lem365006 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem365007 {A B : Type'} (lt2 : type1402 A) (p1 : A) (p1' : A) (lt3 : type1402 B) (p2 : B) (p2' : B) : (term248 A B lt3 p2 p2' lt2 p1 p1') = (term249 A B lt2 p1 p1' lt3 p2 p2').
Proof. exact (MK_COMB (@lem365006) (@lem365005 A B lt2 p1 p1' lt3 p2 p2')). Qed.
Lemma lem365008 {A B : Type'} (p1 : A) (p1' : A) (lt3 : type1402 B) (p2 : B) (p2' : B) : (term251 A B p1 p1' lt3 p2 p2') = (term251 A B p1 p1' lt3 p2 p2').
Proof. exact (eq_refl (term251 A B p1 p1' lt3 p2 p2')). Qed.
Lemma lem365009 {A B : Type'} (lt2 : type1402 A) (p1 : A) (p1' : A) (lt3 : type1402 B) (p2 : B) (p2' : B) : ((term245 A B lt3 p2 p2' lt2 p1 p1') = (term251 A B p1 p1' lt3 p2 p2')) = ((term233 A B lt2 p1 p1' lt3 p2 p2') = (term251 A B p1 p1' lt3 p2 p2')).
Proof. exact (MK_COMB (@lem365007 A B lt2 p1 p1' lt3 p2 p2') (@lem365008 A B p1 p1' lt3 p2 p2')). Qed.
Lemma lem365010 {A B : Type'} (lt2 : type1402 A) (p1 : A) (p1' : A) (lt3 : type1402 B) (p2 : B) (p2' : B) : ((term245 A B lt3 p2 p2' lt2 p1 p1') = (term250 A B p1 p1' lt3 p2 p2')) = ((term233 A B lt2 p1 p1' lt3 p2 p2') = (term251 A B p1 p1' lt3 p2 p2')).
Proof. exact (TRANS (@lem365004 A B lt2 p1 p1' lt3 p2 p2') (@lem365009 A B lt2 p1 p1' lt3 p2 p2')). Qed.
Lemma lem365011 {A B : Type'} (lt3 : type1402 B) (p2 : B) (p2' : B) (lt2 : type1402 A) (p1 : A) (p1' : A) (h1 : (lt2 p1 p1') = False) : (term233 A B lt2 p1 p1' lt3 p2 p2') = (term251 A B p1 p1' lt3 p2 p2').
Proof. exact (EQ_MP (@lem365010 A B lt2 p1 p1' lt3 p2 p2') (@lem365001 A B lt3 p2 p2' lt2 p1 p1' h1)). Qed.
Lemma lem365012 {A B : Type'} (lt3 : type1402 B) (p2 : B) (p2' : B) (lt2 : type1402 A) (p1 : A) (p1' : A) (h1 : (lt2 p1 p1') = False) : (term251 A B p1 p1' lt3 p2 p2') = (term233 A B lt2 p1 p1' lt3 p2 p2').
Proof. exact (SYM (@lem365011 A B lt3 p2 p2' lt2 p1 p1' h1)). Qed.
Lemma lem365016 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem365017 {B : Type'} (lt3 : type1402 B) (p2 : B) (p2' : B) : (term252 B lt3 p2 p2') = (lt3 p2 p2').
Proof. exact (@lem365016 (lt3 p2 p2')). Qed.
Lemma lem365018 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem365019 {B : Type'} (lt3 : type1402 B) (p2 : B) (p2' : B) : (term253 B lt3 p2 p2') = (term254 B lt3 p2 p2').
Proof. exact (MK_COMB (@lem365018) (@lem365017 B lt3 p2 p2')). Qed.
Lemma lem365021 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem365022 {A B : Type'} (p1 : A) (p1' : A) (lt3 : type1402 B) (p2 : B) (p2' : B) : (term255 A B p1 p1' lt3 p2 p2') = True.
Proof. exact (@lem365021 (term256 A B p1 p1' lt3 p2 p2')). Qed.
Lemma lem365023 {A B : Type'} (p1 : A) (p1' : A) (lt3 : type1402 B) (p2 : B) (p2' : B) : (term247 A B p1 p1' lt3 p2 p2') = (term257 B lt3 p2 p2').
Proof. exact (MK_COMB (@lem365019 B lt3 p2 p2') (@lem365022 A B p1 p1' lt3 p2 p2')). Qed.
Lemma lem365025 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem365026 {B : Type'} (lt3 : type1402 B) (p2 : B) (p2' : B) : (term257 B lt3 p2 p2') = True.
Proof. exact (@lem365025 (lt3 p2 p2')). Qed.
Lemma lem365027 {A B : Type'} (p1 : A) (p1' : A) (lt3 : type1402 B) (p2 : B) (p2' : B) : (term247 A B p1 p1' lt3 p2 p2') = True.
Proof. exact (TRANS (@lem365023 A B p1 p1' lt3 p2 p2') (@lem365026 B lt3 p2 p2')). Qed.
Lemma lem365028 {A B : Type'} (p1 : A) (p1' : A) (lt3 : type1402 B) (p2 : B) (p2' : B) : True = (term247 A B p1 p1' lt3 p2 p2').
Proof. exact (SYM (@lem365027 A B p1 p1' lt3 p2 p2')). Qed.
Lemma lem365029 {A B : Type'} (p1 : A) (p1' : A) (lt3 : type1402 B) (p2 : B) (p2' : B) : term247 A B p1 p1' lt3 p2 p2'.
Proof. exact (EQ_MP (@lem365028 A B p1 p1' lt3 p2 p2') (@lem0)). Qed.
Lemma lem365033 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem365034 {B : Type'} (lt3 : type1402 B) (p2 : B) (p2' : B) : (term258 B lt3 p2 p2') = False.
Proof. exact (@lem365033 (lt3 p2 p2')). Qed.
Lemma lem365035 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem365036 {B : Type'} (lt3 : type1402 B) (p2 : B) (p2' : B) : (term259 B lt3 p2 p2') = (imp False).
Proof. exact (MK_COMB (@lem365035) (@lem365034 B lt3 p2 p2')). Qed.
Lemma lem365038 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem365039 {A B : Type'} (p1 : A) (p1' : A) (lt3 : type1402 B) (p2 : B) (p2' : B) : (term260 A B p1 p1' lt3 p2 p2') = (term256 A B p1 p1' lt3 p2 p2').
Proof. exact (@lem365038 (term256 A B p1 p1' lt3 p2 p2')). Qed.
Lemma lem365044 {A B : Type'} (p1 : A) (p1' : A) (lt3 : type1402 B) (p2 : B) (p2' : B) : (term251 A B p1 p1' lt3 p2 p2') = (term261 A B p1 p1' lt3 p2 p2').
Proof. exact (MK_COMB (@lem365036 B lt3 p2 p2') (@lem365039 A B p1 p1' lt3 p2 p2')). Qed.
Lemma lem365046 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem365047 {A B : Type'} (p1 : A) (p1' : A) (lt3 : type1402 B) (p2 : B) (p2' : B) : (term261 A B p1 p1' lt3 p2 p2') = True.
Proof. exact (@lem365046 (term256 A B p1 p1' lt3 p2 p2')). Qed.
Lemma lem365048 {A B : Type'} (p1 : A) (p1' : A) (lt3 : type1402 B) (p2 : B) (p2' : B) : (term251 A B p1 p1' lt3 p2 p2') = True.
Proof. exact (TRANS (@lem365044 A B p1 p1' lt3 p2 p2') (@lem365047 A B p1 p1' lt3 p2 p2')). Qed.
Lemma lem365049 {A B : Type'} (p1 : A) (p1' : A) (lt3 : type1402 B) (p2 : B) (p2' : B) : True = (term251 A B p1 p1' lt3 p2 p2').
Proof. exact (SYM (@lem365048 A B p1 p1' lt3 p2 p2')). Qed.
Lemma lem365050 {A B : Type'} (p1 : A) (p1' : A) (lt3 : type1402 B) (p2 : B) (p2' : B) : term251 A B p1 p1' lt3 p2 p2'.
Proof. exact (EQ_MP (@lem365049 A B p1 p1' lt3 p2 p2') (@lem0)). Qed.
Lemma lem365051 {A B : Type'} (lt3 : type1402 B) (p2 : B) (p2' : B) (lt2 : type1402 A) (p1 : A) (p1' : A) (h1 : (lt2 p1 p1') = False) : term233 A B lt2 p1 p1' lt3 p2 p2'.
Proof. exact (EQ_MP (@lem365012 A B lt3 p2 p2' lt2 p1 p1' h1) (@lem365050 A B p1 p1' lt3 p2 p2')). Qed.
Lemma lem365052 {A B : Type'} (lt3 : type1402 B) (p2 : B) (p2' : B) (lt2 : type1402 A) (p1 : A) (p1' : A) (h1 : (lt2 p1 p1') = True) : term233 A B lt2 p1 p1' lt3 p2 p2'.
Proof. exact (EQ_MP (@lem364999 A B lt3 p2 p2' lt2 p1 p1' h1) (@lem365029 A B p1 p1' lt3 p2 p2')). Qed.
Lemma lem365055 {A B : Type'} (lt2 : type1402 A) (p1 : A) (p1' : A) (lt3 : type1402 B) (p2 : B) (p2' : B) : term233 A B lt2 p1 p1' lt3 p2 p2'.
Proof. exact (or_elim (@lem364972 A lt2 p1 p1') (fun h0 : (lt2 p1 p1') = True => @lem365052 A B lt3 p2 p2' lt2 p1 p1' h0) (fun h0 : (lt2 p1 p1') = False => @lem365051 A B lt3 p2 p2' lt2 p1 p1' h0)). Qed.
Lemma lem365060 {A B : Type'} (lt2 : type1402 A) (p1 : A) (p1' : A) (lt3 : type1402 B) (p2 : B) : term235 A B lt2 p1 p1' lt3 p2.
Proof. exact (fun p2' : B => @lem365055 A B lt2 p1 p1' lt3 p2 p2'). Qed.
Lemma lem365065 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) (p2 : B) : term237 A B lt2 p1 lt3 p2.
Proof. exact (fun p1' : A => @lem365060 A B lt2 p1 p1' lt3 p2). Qed.
Lemma lem365070 {A B : Type'} (lt2 : type1402 A) (p1 : A) (lt3 : type1402 B) : term239 A B lt2 p1 lt3.
Proof. exact (fun p2 : B => @lem365065 A B lt2 p1 lt3 p2). Qed.
Lemma lem365075 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) : term241 A B lt2 lt3.
Proof. exact (fun p1 : A => @lem365070 A B lt2 p1 lt3). Qed.
Lemma lem365076 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) : term36 A B lt2 lt3.
Proof. exact (EQ_MP (@lem364957 A B lt2 lt3) (@lem365075 A B lt2 lt3)). Qed.
Lemma lem365078 {A B : Type'} (R : type1402 A) (S' : type1402 B) : term4 A B R S'.
Proof. exact (EQ_MP (@lem364367 A B R S') (@lem364366 A B R S')). Qed.
Lemma lem365079 {A B : Type'} (R : type1402 A) (S' : type1402 B) : term4 A B R S'.
Proof. exact (@lem365078 A B R S'). Qed.
Lemma lem365080 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) : term4 A B lt2 lt3.
Proof. exact (@lem365079 A B lt2 lt3). Qed.
Lemma lem365081 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = ((@WF A lt2) = True).
Proof. exact (@lem7 (@WF A lt2)). Qed.
Lemma lem365083 {B : Type'} (lt3 : type1402 B) : (@WF B lt3) = ((@WF B lt3) = True).
Proof. exact (@lem7 (@WF B lt3)). Qed.
Lemma lem365088 {A : Type'} (lt2 : type1402 A) (h1 : @WF A lt2) : (@WF A lt2) = True.
Proof. exact (EQ_MP (@lem365081 A lt2) (@lem364395 A lt2 h1)). Qed.
Lemma lem365089 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem365090 {A : Type'} (lt2 : type1402 A) (h1 : @WF A lt2) : (term262 A lt2) = (and True).
Proof. exact (MK_COMB (@lem365089) (@lem365088 A lt2 h1)). Qed.
Lemma lem365092 {B : Type'} (lt3 : type1402 B) (h1 : @WF B lt3) : (@WF B lt3) = True.
Proof. exact (EQ_MP (@lem365083 B lt3) (@lem364394 B lt3 h1)). Qed.
Lemma lem365093 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (h1 : @WF A lt2) (h2 : @WF B lt3) : (term5 A B lt2 lt3) = (True /\ True).
Proof. exact (MK_COMB (@lem365090 A lt2 h1) (@lem365092 B lt3 h2)). Qed.
Lemma lem365095 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem365096 : (True /\ True) = True.
Proof. exact (@lem365095 True). Qed.
Lemma lem365097 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (h1 : @WF A lt2) (h2 : @WF B lt3) : (term5 A B lt2 lt3) = True.
Proof. exact (TRANS (@lem365093 A B lt2 lt3 h1 h2) (@lem365096)). Qed.
Lemma lem365098 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (h1 : @WF A lt2) (h2 : @WF B lt3) : True = (term5 A B lt2 lt3).
Proof. exact (SYM (@lem365097 A B lt2 lt3 h1 h2)). Qed.
Lemma lem365099 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (h1 : @WF A lt2) (h2 : @WF B lt3) : term5 A B lt2 lt3.
Proof. exact (EQ_MP (@lem365098 A B lt2 lt3 h1 h2) (@lem0)). Qed.
Lemma lem365100 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (h1 : @WF A lt2) (h2 : @WF B lt3) : term6 A B lt2 lt3.
Proof. exact (@lem365080 A B lt2 lt3 (@lem365099 A B lt2 lt3 h1 h2)). Qed.
Lemma lem365101 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (h1 : @WF A lt2) (h2 : @WF B lt3) : term263 A B lt2 lt3.
Proof. exact (conj (@lem365076 A B lt2 lt3) (@lem365100 A B lt2 lt3 h1 h2)). Qed.
Lemma lem365102 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (h1 : @WF A lt2) (h2 : @WF B lt3) : term264 A B lt2 lt3.
Proof. exact (ex_intro (term265 A B lt2 lt3) (term266 A B lt2 lt3) (@lem365101 A B lt2 lt3 h1 h2)). Qed.
Lemma lem365103 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (h1 : @WF A lt2) (h2 : @WF B lt3) : term267 A B lt2 lt3.
Proof. exact (@lem364399 A B lt2 lt3 (@lem365102 A B lt2 lt3 h1 h2)). Qed.
Lemma lem365104 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (h1 : term5 A B lt2 lt3) : @WF B lt3.
Proof. exact (proj2 (@lem364393 A B lt2 lt3 h1)). Qed.
Lemma lem365105 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (h1 : term5 A B lt2 lt3) : @WF A lt2.
Proof. exact (proj1 (@lem364393 A B lt2 lt3 h1)). Qed.
Lemma lem365106 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (h1 : @WF A lt2) (h2 : @WF B lt3) : (@WF B lt3) = (term267 A B lt2 lt3).
Proof. exact (prop_ext (fun h3 : @WF B lt3 => @lem365103 A B lt2 lt3 h1 h2) (fun h3 : term267 A B lt2 lt3 => @lem364394 B lt3 h2)). Qed.
Lemma lem365107 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (h1 : @WF A lt2) (h2 : @WF B lt3) : term267 A B lt2 lt3.
Proof. exact (EQ_MP (@lem365106 A B lt2 lt3 h1 h2) (@lem364394 B lt3 h2)). Qed.
Lemma lem365108 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (h1 : @WF A lt2) (h2 : @WF B lt3) : (@WF A lt2) = (term267 A B lt2 lt3).
Proof. exact (prop_ext (fun h3 : @WF A lt2 => @lem365107 A B lt2 lt3 h1 h2) (fun h3 : term267 A B lt2 lt3 => @lem364395 A lt2 h1)). Qed.
Lemma lem365109 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (h1 : @WF A lt2) (h2 : @WF B lt3) : term267 A B lt2 lt3.
Proof. exact (EQ_MP (@lem365108 A B lt2 lt3 h1 h2) (@lem364395 A lt2 h1)). Qed.
Lemma lem365110 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (h1 : @WF A lt2) (h2 : term5 A B lt2 lt3) : (@WF B lt3) = (term267 A B lt2 lt3).
Proof. exact (prop_ext (fun h3 : @WF B lt3 => @lem365109 A B lt2 lt3 h1 h3) (fun h3 : term267 A B lt2 lt3 => @lem365104 A B lt2 lt3 h2)). Qed.
Lemma lem365111 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (h1 : @WF A lt2) (h2 : term5 A B lt2 lt3) : term267 A B lt2 lt3.
Proof. exact (EQ_MP (@lem365110 A B lt2 lt3 h1 h2) (@lem365104 A B lt2 lt3 h2)). Qed.
Lemma lem365112 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (h1 : term5 A B lt2 lt3) : (@WF A lt2) = (term267 A B lt2 lt3).
Proof. exact (prop_ext (fun h2 : @WF A lt2 => @lem365111 A B lt2 lt3 h2 h1) (fun h2 : term267 A B lt2 lt3 => @lem365105 A B lt2 lt3 h1)). Qed.
Lemma lem365113 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) (h1 : term5 A B lt2 lt3) : term267 A B lt2 lt3.
Proof. exact (EQ_MP (@lem365112 A B lt2 lt3 h1) (@lem365105 A B lt2 lt3 h1)). Qed.
Lemma lem365114 {A B : Type'} (lt2 : type1402 A) (lt3 : type1402 B) : term268 A B lt2 lt3.
Proof. exact (fun h0 : term5 A B lt2 lt3 => @lem365113 A B lt2 lt3 h0). Qed.
