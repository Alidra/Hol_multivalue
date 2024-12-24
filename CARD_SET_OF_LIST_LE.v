Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_SET_OF_LIST_LE_term_abbrevs.
Require Import CARD_CLAUSES_spec.
Require Import FINITE_SET_OF_LIST_spec.
Require Import INT_POS_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1011992_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1097080_spec.
Require Import thm12653_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367770_spec.
Require Import thm1367771_spec.
Require Import thm1386578_spec.
Require Import thm16502_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm19158_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980255_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988332_spec.
Require Import thm1988342_spec.
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
Require Import thm2318495_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm2841383_spec.
Require Import thm2841384_spec.
Require Import thm2841407_spec.
Require Import thm2841408_spec.
Require Import thm2841416_spec.
Require Import thm2841417_spec.
Require Import thm37_spec.
Require Import thm4785464_spec.
Require Import thm4785470_spec.
Require Import thm4785471_spec.
Require Import thm7_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Require Import thm996237_spec.
Require Import thm996238_spec.
Lemma lem4895352 {_110366 : Type'} (l : list _110366) : term0 _110366 l.
Proof. exact (@lem4788499 _110366 l). Qed.
Lemma lem4895353 {_110366 : Type'} (l : list _110366) : (term0 _110366 l) = (term1 _110366 l).
Proof. exact (eq_refl (term0 _110366 l)). Qed.
Lemma lem4895354 {_110366 : Type'} (l : list _110366) : term1 _110366 l.
Proof. exact (EQ_MP (@lem4895353 _110366 l) (@lem4895352 _110366 l)). Qed.
Lemma lem4895355 {_110366 : Type'} (l : list _110366) : (term1 _110366 l) = ((term1 _110366 l) = True).
Proof. exact (@lem7 (term1 _110366 l)). Qed.
Lemma lem4895357 {A : Type'} : term2 A.
Proof. exact (proj2 (@lem3840691 A)). Qed.
Lemma lem4895358 {A : Type'} (x : A) : term3 A x.
Proof. exact (@lem4895357 A x). Qed.
Lemma lem4895359 {A : Type'} (x : A) : (term3 A x) = (term4 A x).
Proof. exact (eq_refl (term3 A x)). Qed.
Lemma lem4895360 {A : Type'} (x : A) : term4 A x.
Proof. exact (EQ_MP (@lem4895359 A x) (@lem4895358 A x)). Qed.
Lemma lem4895361 {A : Type'} (x : A) (s : A -> Prop) : term5 A x s.
Proof. exact (@lem4895360 A x s). Qed.
Lemma lem4895362 {A : Type'} (x : A) (s : A -> Prop) : (term5 A x s) = (term6 A x s).
Proof. exact (eq_refl (term5 A x s)). Qed.
Lemma lem4895363 {A : Type'} (x : A) (s : A -> Prop) : term6 A x s.
Proof. exact (EQ_MP (@lem4895362 A x s) (@lem4895361 A x s)). Qed.
Lemma lem4895364 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4895365 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term7 A x s) = (term8 A x s).
Proof. exact (@lem4895363 A x s (@lem4895364 A s h1)). Qed.
Lemma lem4895374 {A : Type'} : term9 A.
Proof. exact (proj2 (@lem1097080 A)). Qed.
Lemma lem4895375 {A : Type'} (h : A) : term10 A h.
Proof. exact (@lem4895374 A h). Qed.
Lemma lem4895376 {A : Type'} (h : A) : (term10 A h) = (term11 A h).
Proof. exact (eq_refl (term10 A h)). Qed.
Lemma lem4895377 {A : Type'} (h : A) : term11 A h.
Proof. exact (EQ_MP (@lem4895376 A h) (@lem4895375 A h)). Qed.
Lemma lem4895378 {A : Type'} (h : A) (t : list A) : term12 A h t.
Proof. exact (@lem4895377 A h t). Qed.
Lemma lem4895379 {A : Type'} (h : A) (t : list A) : (term12 A h t) = ((term13 A h t) = (term14 A t)).
Proof. exact (eq_refl (term12 A h t)). Qed.
Lemma lem4895383 {A : Type'} (P : type1143 A) : term15 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem4895384 {_112846 : Type'} (P : type1143 _112846) : term15 _112846 P.
Proof. exact (@lem4895383 _112846 P). Qed.
Lemma lem4895385 {_112846 : Type'} : term16 _112846.
Proof. exact (@lem4895384 _112846 (term17 _112846)). Qed.
Lemma lem4895386 {_112846 : Type'} : (term18 _112846) = (term19 _112846).
Proof. exact (eq_refl (term18 _112846)). Qed.
Lemma lem4895387 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4895388 {_112846 : Type'} : (term20 _112846) = (term21 _112846).
Proof. exact (MK_COMB (@lem4895387) (@lem4895386 _112846)). Qed.
Lemma lem4895389 {_112846 : Type'} (t : list _112846) : (term22 _112846 t) = (term23 _112846 t).
Proof. exact (eq_refl (term22 _112846 t)). Qed.
Lemma lem4895390 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4895391 {_112846 : Type'} (t : list _112846) : (term24 _112846 t) = (term25 _112846 t).
Proof. exact (MK_COMB (@lem4895390) (@lem4895389 _112846 t)). Qed.
Lemma lem4895392 {_112846 : Type'} (h : _112846) (t : list _112846) : (term26 _112846 h t) = (term27 _112846 h t).
Proof. exact (eq_refl (term26 _112846 h t)). Qed.
Lemma lem4895393 {_112846 : Type'} (h : _112846) (t : list _112846) : (term28 _112846 h t) = (term29 _112846 h t).
Proof. exact (MK_COMB (@lem4895391 _112846 t) (@lem4895392 _112846 h t)). Qed.
Lemma lem4895394 {_112846 : Type'} (h : _112846) : (term30 _112846 h) = (term31 _112846 h).
Proof. exact (fun_ext (fun t : list _112846 => @lem4895393 _112846 h t)). Qed.
Lemma lem4895395 {_112846 : Type'} : (@all (list _112846)) = (@all (list _112846)).
Proof. exact (eq_refl (@all (list _112846))). Qed.
Lemma lem4895396 {_112846 : Type'} (h : _112846) : (term32 _112846 h) = (term33 _112846 h).
Proof. exact (MK_COMB (@lem4895395 _112846) (@lem4895394 _112846 h)). Qed.
Lemma lem4895397 {_112846 : Type'} : (term34 _112846) = (term35 _112846).
Proof. exact (fun_ext (fun h : _112846 => @lem4895396 _112846 h)). Qed.
Lemma lem4895398 {_112846 : Type'} : (@all _112846) = (@all _112846).
Proof. exact (eq_refl (@all _112846)). Qed.
Lemma lem4895399 {_112846 : Type'} : (term36 _112846) = (term37 _112846).
Proof. exact (MK_COMB (@lem4895398 _112846) (@lem4895397 _112846)). Qed.
Lemma lem4895400 {_112846 : Type'} : (term38 _112846) = (term39 _112846).
Proof. exact (MK_COMB (@lem4895388 _112846) (@lem4895399 _112846)). Qed.
Lemma lem4895401 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4895402 {_112846 : Type'} : (term40 _112846) = (term41 _112846).
Proof. exact (MK_COMB (@lem4895401) (@lem4895400 _112846)). Qed.
Lemma lem4895403 {_112846 : Type'} (l : list _112846) : (term22 _112846 l) = (term23 _112846 l).
Proof. exact (eq_refl (term22 _112846 l)). Qed.
Lemma lem4895404 {_112846 : Type'} : (term42 _112846) = (term17 _112846).
Proof. exact (fun_ext (fun l : list _112846 => @lem4895403 _112846 l)). Qed.
Lemma lem4895405 {_112846 : Type'} : (@all (list _112846)) = (@all (list _112846)).
Proof. exact (eq_refl (@all (list _112846))). Qed.
Lemma lem4895406 {_112846 : Type'} : (term43 _112846) = (term44 _112846).
Proof. exact (MK_COMB (@lem4895405 _112846) (@lem4895404 _112846)). Qed.
Lemma lem4895407 {_112846 : Type'} : (term16 _112846) = (term45 _112846).
Proof. exact (MK_COMB (@lem4895402 _112846) (@lem4895406 _112846)). Qed.
Lemma lem4895408 {_112846 : Type'} : term45 _112846.
Proof. exact (EQ_MP (@lem4895407 _112846) (@lem4895385 _112846)). Qed.
Lemma lem4895409 {_112846 : Type'} (t : list _112846) (h1 : term23 _112846 t) : term23 _112846 t.
Proof. exact (h1). Qed.
Lemma lem4895411 {A : Type'} : (@set_of_list A (@nil A)) = (@EMPTY A).
Proof. exact (proj1 (@lem4785464 A)). Qed.
Lemma lem4895412 {_112846 : Type'} : (@set_of_list _112846 (@nil _112846)) = (@EMPTY _112846).
Proof. exact (@lem4895411 _112846). Qed.
Lemma lem4895413 {_112846 : Type'} : (@CARD _112846) = (@CARD _112846).
Proof. exact (eq_refl (@CARD _112846)). Qed.
Lemma lem4895414 {_112846 : Type'} : (term46 _112846) = (@CARD _112846 (@EMPTY _112846)).
Proof. exact (MK_COMB (@lem4895413 _112846) (@lem4895412 _112846)). Qed.
Lemma lem4895416 {A : Type'} : (@CARD A (@EMPTY A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem3840691 A)). Qed.
Lemma lem4895417 {_112846 : Type'} : (@CARD _112846 (@EMPTY _112846)) = (NUMERAL 0).
Proof. exact (@lem4895416 _112846). Qed.
Lemma lem4895418 {_112846 : Type'} : (term46 _112846) = (NUMERAL 0).
Proof. exact (TRANS (@lem4895414 _112846) (@lem4895417 _112846)). Qed.
Lemma lem4895419 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem4895420 {_112846 : Type'} : (term47 _112846) = term48.
Proof. exact (MK_COMB (@lem4895419) (@lem4895418 _112846)). Qed.
Lemma lem4895422 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem4895423 {_112846 : Type'} : (@List.length _112846 (@nil _112846)) = (NUMERAL 0).
Proof. exact (@lem4895422 _112846). Qed.
Lemma lem4895424 {_112846 : Type'} : (term19 _112846) = term49.
Proof. exact (MK_COMB (@lem4895420 _112846) (@lem4895423 _112846)). Qed.
Lemma lem4895425 {_112846 : Type'} : term49 = (term19 _112846).
Proof. exact (SYM (@lem4895424 _112846)). Qed.
Lemma lem4895427 {A : Type'} (h : A) (t : list A) : (term50 A h t) = (term51 A h t).
Proof. exact (EQ_MP (@lem4785471 A h t) (@lem4785470 A h t)). Qed.
Lemma lem4895428 {_112846 : Type'} (h : _112846) (t : list _112846) : (term50 _112846 h t) = (term51 _112846 h t).
Proof. exact (@lem4895427 _112846 h t). Qed.
Lemma lem4895429 {_112846 : Type'} : (@CARD _112846) = (@CARD _112846).
Proof. exact (eq_refl (@CARD _112846)). Qed.
Lemma lem4895430 {_112846 : Type'} (h : _112846) (t : list _112846) : (term52 _112846 h t) = (term53 _112846 h t).
Proof. exact (MK_COMB (@lem4895429 _112846) (@lem4895428 _112846 h t)). Qed.
Lemma lem4895432 {A : Type'} (x : A) (s : A -> Prop) : term6 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem4895365 A x s h0). Qed.
Lemma lem4895433 {_112846 : Type'} (x : _112846) (s : _112846 -> Prop) : term6 _112846 x s.
Proof. exact (@lem4895432 _112846 x s). Qed.
Lemma lem4895434 {_112846 : Type'} (h : _112846) (t : list _112846) : term54 _112846 h t.
Proof. exact (@lem4895433 _112846 h (@set_of_list _112846 t)). Qed.
Lemma lem4895436 {_110366 : Type'} (l : list _110366) : (term1 _110366 l) = True.
Proof. exact (EQ_MP (@lem4895355 _110366 l) (@lem4895354 _110366 l)). Qed.
Lemma lem4895437 {_112846 : Type'} (l : list _112846) : (term1 _112846 l) = True.
Proof. exact (@lem4895436 _112846 l). Qed.
Lemma lem4895438 {_112846 : Type'} (t : list _112846) : (term1 _112846 t) = True.
Proof. exact (@lem4895437 _112846 t). Qed.
Lemma lem4895439 {_112846 : Type'} (t : list _112846) : True = (term1 _112846 t).
Proof. exact (SYM (@lem4895438 _112846 t)). Qed.
Lemma lem4895440 {_112846 : Type'} (t : list _112846) : term1 _112846 t.
Proof. exact (EQ_MP (@lem4895439 _112846 t) (@lem0)). Qed.
Lemma lem4895441 {_112846 : Type'} (h : _112846) (t : list _112846) : (term53 _112846 h t) = (term55 _112846 h t).
Proof. exact (@lem4895434 _112846 h t (@lem4895440 _112846 t)). Qed.
Lemma lem4895475 {_112846 : Type'} (h : _112846) (t : list _112846) : (term52 _112846 h t) = (term55 _112846 h t).
Proof. exact (TRANS (@lem4895430 _112846 h t) (@lem4895441 _112846 h t)). Qed.
Lemma lem4895476 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem4895477 {_112846 : Type'} (h : _112846) (t : list _112846) : (term56 _112846 h t) = (term57 _112846 h t).
Proof. exact (MK_COMB (@lem4895476) (@lem4895475 _112846 h t)). Qed.
Lemma lem4895512 {A : Type'} (h : A) (t : list A) : (term13 A h t) = (term14 A t).
Proof. exact (EQ_MP (@lem4895379 A h t) (@lem4895378 A h t)). Qed.
Lemma lem4895513 {_112846 : Type'} (h : _112846) (t : list _112846) : (term13 _112846 h t) = (term14 _112846 t).
Proof. exact (@lem4895512 _112846 h t). Qed.
Lemma lem4895514 {_112846 : Type'} (h : _112846) (t : list _112846) : (term27 _112846 h t) = (term58 _112846 h t).
Proof. exact (MK_COMB (@lem4895477 _112846 h t) (@lem4895513 _112846 h t)). Qed.
Lemma lem4895548 {_112846 : Type'} (h : _112846) (t : list _112846) : (term58 _112846 h t) = (term27 _112846 h t).
Proof. exact (SYM (@lem4895514 _112846 h t)). Qed.
Lemma lem4895567 : term49 = True.
Proof. exact (@lem1011992 0). Qed.
Lemma lem4895568 : term59 = True.
Proof. exact (@lem2318604 True). Qed.
Lemma lem4895582 : (~ True) = False.
Proof. exact (proj1 (@lem16502)). Qed.
Lemma lem4895586 (t : Prop) : (term60 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4895602 : term61 = False.
Proof. exact (@lem4895586 False). Qed.
Lemma lem4895605 : term62.
Proof. exact (@lem37 term61 False). Qed.
Lemma lem4895606 : term63.
Proof. exact (@lem4895605 (@lem4895602)). Qed.
Lemma lem4895607 : term64.
Proof. exact (@lem1386578 (~ False)). Qed.
Lemma lem4895610 : ~ False.
Proof. exact (@lem4895607 (@lem4895606)). Qed.
Lemma lem4895611 : False = (~ True).
Proof. exact (SYM (@lem4895582)). Qed.
Lemma lem4895612 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4895613 : (~ False) = term59.
Proof. exact (MK_COMB (@lem4895612) (@lem4895611)). Qed.
Lemma lem4895614 : term59.
Proof. exact (EQ_MP (@lem4895613) (@lem4895610)). Qed.
Lemma lem4895615 : True.
Proof. exact (EQ_MP (@lem4895568) (@lem4895614)). Qed.
Lemma lem4895616 : True = term49.
Proof. exact (SYM (@lem4895567)). Qed.
Lemma lem4895617 : term49.
Proof. exact (EQ_MP (@lem4895616) (@lem4895615)). Qed.
Lemma lem4895618 : term49 = (term49 = True).
Proof. exact (@lem7 term49). Qed.
Lemma lem4895619 : term49 = True.
Proof. exact (EQ_MP (@lem4895618) (@lem4895617)). Qed.
Lemma lem4895620 : True = term49.
Proof. exact (SYM (@lem4895619)). Qed.
Lemma lem4895621 : term49.
Proof. exact (EQ_MP (@lem4895620) (@lem0)). Qed.
Lemma lem4895628 {_112846 : Type'} (h : _112846) (t : list _112846) (h1 : (term65 _112846 h t) = False) : (term65 _112846 h t) = False.
Proof. exact (h1). Qed.
Lemma lem4895629 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem4895630 {_112846 : Type'} (h : _112846) (t : list _112846) (h1 : (term65 _112846 h t) = False) : (term66 _112846 h t) = (@COND nat False).
Proof. exact (MK_COMB (@lem4895629) (@lem4895628 _112846 h t h1)). Qed.
Lemma lem4895631 {_112846 : Type'} (t : list _112846) : (term67 _112846 t) = (term67 _112846 t).
Proof. exact (eq_refl (term67 _112846 t)). Qed.
Lemma lem4895632 {_112846 : Type'} (h : _112846) (t : list _112846) (h1 : (term65 _112846 h t) = False) : (term68 _112846 h t) = (term69 _112846 t).
Proof. exact (MK_COMB (@lem4895630 _112846 h t h1) (@lem4895631 _112846 t)). Qed.
Lemma lem4895633 {_112846 : Type'} (t : list _112846) : (term70 _112846 t) = (term70 _112846 t).
Proof. exact (eq_refl (term70 _112846 t)). Qed.
Lemma lem4895634 {_112846 : Type'} (h : _112846) (t : list _112846) (h1 : (term65 _112846 h t) = False) : (term55 _112846 h t) = (term71 _112846 t).
Proof. exact (MK_COMB (@lem4895632 _112846 h t h1) (@lem4895633 _112846 t)). Qed.
Lemma lem4895636 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4895637 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem4895636 nat t1 t2). Qed.
Lemma lem4895638 {_112846 : Type'} (t : list _112846) : (term71 _112846 t) = (term70 _112846 t).
Proof. exact (@lem4895637 (term67 _112846 t) (term70 _112846 t)). Qed.
Lemma lem4895639 {_112846 : Type'} (h : _112846) (t : list _112846) (h1 : (term65 _112846 h t) = False) : (term55 _112846 h t) = (term70 _112846 t).
Proof. exact (TRANS (@lem4895634 _112846 h t h1) (@lem4895638 _112846 t)). Qed.
Lemma lem4895640 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem4895641 {_112846 : Type'} (h : _112846) (t : list _112846) (h1 : (term65 _112846 h t) = False) : (term57 _112846 h t) = (term72 _112846 t).
Proof. exact (MK_COMB (@lem4895640) (@lem4895639 _112846 h t h1)). Qed.
Lemma lem4895642 {_112846 : Type'} (t : list _112846) : (term14 _112846 t) = (term14 _112846 t).
Proof. exact (eq_refl (term14 _112846 t)). Qed.
Lemma lem4895643 {_112846 : Type'} (h : _112846) (t : list _112846) (h1 : (term65 _112846 h t) = False) : (term58 _112846 h t) = (term73 _112846 t).
Proof. exact (MK_COMB (@lem4895641 _112846 h t h1) (@lem4895642 _112846 t)). Qed.
Lemma lem4895644 {_112846 : Type'} (t : list _112846) : (term25 _112846 t) = (term25 _112846 t).
Proof. exact (eq_refl (term25 _112846 t)). Qed.
Lemma lem4895645 {_112846 : Type'} (h : _112846) (t : list _112846) (h1 : (term65 _112846 h t) = False) : (term74 _112846 h t) = (term75 _112846 t).
Proof. exact (MK_COMB (@lem4895644 _112846 t) (@lem4895643 _112846 h t h1)). Qed.
Lemma lem4895648 {_112846 : Type'} (h : _112846) (t : list _112846) : term76 _112846 h t.
Proof. exact (fun h0 : (term65 _112846 h t) = False => @lem4895645 _112846 h t h0). Qed.
Lemma lem4895650 {_112846 : Type'} (h : _112846) (t : list _112846) (h1 : (term65 _112846 h t) = True) : (term65 _112846 h t) = True.
Proof. exact (h1). Qed.
Lemma lem4895651 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem4895652 {_112846 : Type'} (h : _112846) (t : list _112846) (h1 : (term65 _112846 h t) = True) : (term66 _112846 h t) = (@COND nat True).
Proof. exact (MK_COMB (@lem4895651) (@lem4895650 _112846 h t h1)). Qed.
Lemma lem4895653 {_112846 : Type'} (t : list _112846) : (term67 _112846 t) = (term67 _112846 t).
Proof. exact (eq_refl (term67 _112846 t)). Qed.
Lemma lem4895654 {_112846 : Type'} (h : _112846) (t : list _112846) (h1 : (term65 _112846 h t) = True) : (term68 _112846 h t) = (term77 _112846 t).
Proof. exact (MK_COMB (@lem4895652 _112846 h t h1) (@lem4895653 _112846 t)). Qed.
Lemma lem4895655 {_112846 : Type'} (t : list _112846) : (term70 _112846 t) = (term70 _112846 t).
Proof. exact (eq_refl (term70 _112846 t)). Qed.
Lemma lem4895656 {_112846 : Type'} (h : _112846) (t : list _112846) (h1 : (term65 _112846 h t) = True) : (term55 _112846 h t) = (term78 _112846 t).
Proof. exact (MK_COMB (@lem4895654 _112846 h t h1) (@lem4895655 _112846 t)). Qed.
Lemma lem4895658 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4895659 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem4895658 nat t2 t1). Qed.
Lemma lem4895660 {_112846 : Type'} (t : list _112846) : (term78 _112846 t) = (term67 _112846 t).
Proof. exact (@lem4895659 (term70 _112846 t) (term67 _112846 t)). Qed.
Lemma lem4895661 {_112846 : Type'} (h : _112846) (t : list _112846) (h1 : (term65 _112846 h t) = True) : (term55 _112846 h t) = (term67 _112846 t).
Proof. exact (TRANS (@lem4895656 _112846 h t h1) (@lem4895660 _112846 t)). Qed.
Lemma lem4895662 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem4895663 {_112846 : Type'} (h : _112846) (t : list _112846) (h1 : (term65 _112846 h t) = True) : (term57 _112846 h t) = (term79 _112846 t).
Proof. exact (MK_COMB (@lem4895662) (@lem4895661 _112846 h t h1)). Qed.
Lemma lem4895664 {_112846 : Type'} (t : list _112846) : (term14 _112846 t) = (term14 _112846 t).
Proof. exact (eq_refl (term14 _112846 t)). Qed.
Lemma lem4895665 {_112846 : Type'} (h : _112846) (t : list _112846) (h1 : (term65 _112846 h t) = True) : (term58 _112846 h t) = (term80 _112846 t).
Proof. exact (MK_COMB (@lem4895663 _112846 h t h1) (@lem4895664 _112846 t)). Qed.
Lemma lem4895666 {_112846 : Type'} (t : list _112846) : (term25 _112846 t) = (term25 _112846 t).
Proof. exact (eq_refl (term25 _112846 t)). Qed.
Lemma lem4895667 {_112846 : Type'} (h : _112846) (t : list _112846) (h1 : (term65 _112846 h t) = True) : (term74 _112846 h t) = (term81 _112846 t).
Proof. exact (MK_COMB (@lem4895666 _112846 t) (@lem4895665 _112846 h t h1)). Qed.
Lemma lem4895670 {_112846 : Type'} (h : _112846) (t : list _112846) : term82 _112846 h t.
Proof. exact (fun h0 : (term65 _112846 h t) = True => @lem4895667 _112846 h t h0). Qed.
Lemma lem4895671 {_112846 : Type'} (h : _112846) (t : list _112846) : term83 _112846 h t.
Proof. exact (conj (@lem4895648 _112846 h t) (@lem4895670 _112846 h t)). Qed.
Lemma lem4895673 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term84 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem4895674 {_112846 : Type'} (h : _112846) (t : list _112846) : term85 _112846 h t.
Proof. exact (@lem4895673 (term74 _112846 h t) (term81 _112846 t) (term65 _112846 h t) (term75 _112846 t)). Qed.
Lemma lem4895716 {_112846 : Type'} (h : _112846) (t : list _112846) : (term74 _112846 h t) = (term86 _112846 h t).
Proof. exact (@lem4895674 _112846 h t (@lem4895671 _112846 h t)). Qed.
Lemma lem4895724 {_112846 : Type'} (t : list _112846) : (term81 _112846 t) = (term87 _112846 t).
Proof. exact (@lem17265 (term23 _112846 t) (term80 _112846 t)). Qed.
Lemma lem4895726 {_112846 : Type'} (h : _112846) (t : list _112846) : (term88 _112846 h t) = (term88 _112846 h t).
Proof. exact (eq_refl (term88 _112846 h t)). Qed.
Lemma lem4895727 {_112846 : Type'} (h : _112846) (t : list _112846) : (term89 _112846 h t) = (term90 _112846 h t).
Proof. exact (MK_COMB (@lem4895726 _112846 h t) (@lem4895724 _112846 t)). Qed.
Lemma lem4895735 {_112846 : Type'} (t : list _112846) : (term75 _112846 t) = (term91 _112846 t).
Proof. exact (@lem17265 (term23 _112846 t) (term73 _112846 t)). Qed.
Lemma lem4895737 {_112846 : Type'} (h : _112846) (t : list _112846) : (term92 _112846 h t) = (term92 _112846 h t).
Proof. exact (eq_refl (term92 _112846 h t)). Qed.
Lemma lem4895738 {_112846 : Type'} (h : _112846) (t : list _112846) : (term93 _112846 h t) = (term94 _112846 h t).
Proof. exact (MK_COMB (@lem4895737 _112846 h t) (@lem4895735 _112846 t)). Qed.
Lemma lem4895739 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4895740 {_112846 : Type'} (h : _112846) (t : list _112846) : (term95 _112846 h t) = (term96 _112846 h t).
Proof. exact (MK_COMB (@lem4895739) (@lem4895727 _112846 h t)). Qed.
Lemma lem4895741 {_112846 : Type'} (h : _112846) (t : list _112846) : (term86 _112846 h t) = (term97 _112846 h t).
Proof. exact (MK_COMB (@lem4895740 _112846 h t) (@lem4895738 _112846 h t)). Qed.
Lemma lem4895758 {_112846 : Type'} (h : _112846) (t : list _112846) : (term74 _112846 h t) = (term97 _112846 h t).
Proof. exact (TRANS (@lem4895716 _112846 h t) (@lem4895741 _112846 h t)). Qed.
Lemma lem4895760 (m : nat) : (S m) = (term98 m).
Proof. exact (EQ_MP (@lem2841417 m) (@lem2841416 m)). Qed.
Lemma lem4895761 {_112846 : Type'} (t : list _112846) : (term14 _112846 t) = (term99 _112846 t).
Proof. exact (@lem4895760 (@List.length _112846 t)). Qed.
Lemma lem4895762 {_112846 : Type'} (t : list _112846) : (term79 _112846 t) = (term79 _112846 t).
Proof. exact (eq_refl (term79 _112846 t)). Qed.
Lemma lem4895763 {_112846 : Type'} (t : list _112846) : (term80 _112846 t) = (term100 _112846 t).
Proof. exact (MK_COMB (@lem4895762 _112846 t) (@lem4895761 _112846 t)). Qed.
Lemma lem4895764 {_112846 : Type'} (t : list _112846) : (term101 _112846 t) = (term101 _112846 t).
Proof. exact (eq_refl (term101 _112846 t)). Qed.
Lemma lem4895765 {_112846 : Type'} (t : list _112846) : (term87 _112846 t) = (term102 _112846 t).
Proof. exact (MK_COMB (@lem4895764 _112846 t) (@lem4895763 _112846 t)). Qed.
Lemma lem4895766 {_112846 : Type'} (h : _112846) (t : list _112846) : (term88 _112846 h t) = (term88 _112846 h t).
Proof. exact (eq_refl (term88 _112846 h t)). Qed.
Lemma lem4895767 {_112846 : Type'} (h : _112846) (t : list _112846) : (term90 _112846 h t) = (term103 _112846 h t).
Proof. exact (MK_COMB (@lem4895766 _112846 h t) (@lem4895765 _112846 t)). Qed.
Lemma lem4895768 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4895769 {_112846 : Type'} (h : _112846) (t : list _112846) : (term96 _112846 h t) = (term104 _112846 h t).
Proof. exact (MK_COMB (@lem4895768) (@lem4895767 _112846 h t)). Qed.
Lemma lem4895771 (m : nat) : (S m) = (term98 m).
Proof. exact (EQ_MP (@lem2841417 m) (@lem2841416 m)). Qed.
Lemma lem4895772 {_112846 : Type'} (t : list _112846) : (term70 _112846 t) = (term105 _112846 t).
Proof. exact (@lem4895771 (term67 _112846 t)). Qed.
Lemma lem4895773 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem4895774 {_112846 : Type'} (t : list _112846) : (term72 _112846 t) = (term106 _112846 t).
Proof. exact (MK_COMB (@lem4895773) (@lem4895772 _112846 t)). Qed.
Lemma lem4895776 (m : nat) : (S m) = (term98 m).
Proof. exact (EQ_MP (@lem2841417 m) (@lem2841416 m)). Qed.
Lemma lem4895777 {_112846 : Type'} (t : list _112846) : (term14 _112846 t) = (term99 _112846 t).
Proof. exact (@lem4895776 (@List.length _112846 t)). Qed.
Lemma lem4895778 {_112846 : Type'} (t : list _112846) : (term73 _112846 t) = (term107 _112846 t).
Proof. exact (MK_COMB (@lem4895774 _112846 t) (@lem4895777 _112846 t)). Qed.
Lemma lem4895779 {_112846 : Type'} (t : list _112846) : (term101 _112846 t) = (term101 _112846 t).
Proof. exact (eq_refl (term101 _112846 t)). Qed.
Lemma lem4895780 {_112846 : Type'} (t : list _112846) : (term91 _112846 t) = (term108 _112846 t).
Proof. exact (MK_COMB (@lem4895779 _112846 t) (@lem4895778 _112846 t)). Qed.
Lemma lem4895781 {_112846 : Type'} (h : _112846) (t : list _112846) : (term92 _112846 h t) = (term92 _112846 h t).
Proof. exact (eq_refl (term92 _112846 h t)). Qed.
Lemma lem4895782 {_112846 : Type'} (h : _112846) (t : list _112846) : (term94 _112846 h t) = (term109 _112846 h t).
Proof. exact (MK_COMB (@lem4895781 _112846 h t) (@lem4895780 _112846 t)). Qed.
Lemma lem4895783 {_112846 : Type'} (h : _112846) (t : list _112846) : (term97 _112846 h t) = (term110 _112846 h t).
Proof. exact (MK_COMB (@lem4895769 _112846 h t) (@lem4895782 _112846 h t)). Qed.
Lemma lem4895856 {_112846 : Type'} (h : _112846) (t : list _112846) : (term74 _112846 h t) = (term110 _112846 h t).
Proof. exact (TRANS (@lem4895758 _112846 h t) (@lem4895783 _112846 h t)). Qed.
Lemma lem4895858 (m : nat) (n : nat) : (Peano.le m n) = (term111 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem4895859 {_112846 : Type'} (t : list _112846) : (term23 _112846 t) = (term112 _112846 t).
Proof. exact (@lem4895858 (term67 _112846 t) (@List.length _112846 t)). Qed.
Lemma lem4895860 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4895861 {_112846 : Type'} (t : list _112846) : (term113 _112846 t) = (term114 _112846 t).
Proof. exact (MK_COMB (@lem4895860) (@lem4895859 _112846 t)). Qed.
Lemma lem4895862 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4895863 {_112846 : Type'} (t : list _112846) : (term101 _112846 t) = (term115 _112846 t).
Proof. exact (MK_COMB (@lem4895862) (@lem4895861 _112846 t)). Qed.
Lemma lem4895865 (m : nat) (n : nat) : (Peano.le m n) = (term111 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem4895866 {_112846 : Type'} (t : list _112846) : (term100 _112846 t) = (term116 _112846 t).
Proof. exact (@lem4895865 (term67 _112846 t) (term99 _112846 t)). Qed.
Lemma lem4895868 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem4895869 {_112846 : Type'} (t : list _112846) : (term119 _112846 t) = (term120 _112846 t).
Proof. exact (@lem4895868 (@List.length _112846 t) term121). Qed.
Lemma lem4895870 {_112846 : Type'} (t : list _112846) : (term122 _112846 t) = (term122 _112846 t).
Proof. exact (eq_refl (term122 _112846 t)). Qed.
Lemma lem4895871 {_112846 : Type'} (t : list _112846) : (term116 _112846 t) = (term123 _112846 t).
Proof. exact (MK_COMB (@lem4895870 _112846 t) (@lem4895869 _112846 t)). Qed.
Lemma lem4895872 {_112846 : Type'} (t : list _112846) : (term100 _112846 t) = (term123 _112846 t).
Proof. exact (TRANS (@lem4895866 _112846 t) (@lem4895871 _112846 t)). Qed.
Lemma lem4895873 {_112846 : Type'} (t : list _112846) : (term102 _112846 t) = (term124 _112846 t).
Proof. exact (MK_COMB (@lem4895863 _112846 t) (@lem4895872 _112846 t)). Qed.
Lemma lem4895874 {_112846 : Type'} (h : _112846) (t : list _112846) : (term88 _112846 h t) = (term88 _112846 h t).
Proof. exact (eq_refl (term88 _112846 h t)). Qed.
Lemma lem4895875 {_112846 : Type'} (h : _112846) (t : list _112846) : (term103 _112846 h t) = (term125 _112846 h t).
Proof. exact (MK_COMB (@lem4895874 _112846 h t) (@lem4895873 _112846 t)). Qed.
Lemma lem4895876 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4895877 {_112846 : Type'} (h : _112846) (t : list _112846) : (term104 _112846 h t) = (term126 _112846 h t).
Proof. exact (MK_COMB (@lem4895876) (@lem4895875 _112846 h t)). Qed.
Lemma lem4895879 (m : nat) (n : nat) : (Peano.le m n) = (term111 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem4895880 {_112846 : Type'} (t : list _112846) : (term23 _112846 t) = (term112 _112846 t).
Proof. exact (@lem4895879 (term67 _112846 t) (@List.length _112846 t)). Qed.
Lemma lem4895881 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4895882 {_112846 : Type'} (t : list _112846) : (term113 _112846 t) = (term114 _112846 t).
Proof. exact (MK_COMB (@lem4895881) (@lem4895880 _112846 t)). Qed.
Lemma lem4895883 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4895884 {_112846 : Type'} (t : list _112846) : (term101 _112846 t) = (term115 _112846 t).
Proof. exact (MK_COMB (@lem4895883) (@lem4895882 _112846 t)). Qed.
Lemma lem4895886 (m : nat) (n : nat) : (Peano.le m n) = (term111 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem4895887 {_112846 : Type'} (t : list _112846) : (term107 _112846 t) = (term127 _112846 t).
Proof. exact (@lem4895886 (term105 _112846 t) (term99 _112846 t)). Qed.
Lemma lem4895889 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem4895890 {_112846 : Type'} (t : list _112846) : (term128 _112846 t) = (term129 _112846 t).
Proof. exact (@lem4895889 (term67 _112846 t) term121). Qed.
Lemma lem4895891 : int_le = int_le.
Proof. exact (eq_refl int_le). Qed.
Lemma lem4895892 {_112846 : Type'} (t : list _112846) : (term130 _112846 t) = (term131 _112846 t).
Proof. exact (MK_COMB (@lem4895891) (@lem4895890 _112846 t)). Qed.
Lemma lem4895894 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem4895895 {_112846 : Type'} (t : list _112846) : (term119 _112846 t) = (term120 _112846 t).
Proof. exact (@lem4895894 (@List.length _112846 t) term121). Qed.
Lemma lem4895896 {_112846 : Type'} (t : list _112846) : (term127 _112846 t) = (term132 _112846 t).
Proof. exact (MK_COMB (@lem4895892 _112846 t) (@lem4895895 _112846 t)). Qed.
Lemma lem4895897 {_112846 : Type'} (t : list _112846) : (term107 _112846 t) = (term132 _112846 t).
Proof. exact (TRANS (@lem4895887 _112846 t) (@lem4895896 _112846 t)). Qed.
Lemma lem4895898 {_112846 : Type'} (t : list _112846) : (term108 _112846 t) = (term133 _112846 t).
Proof. exact (MK_COMB (@lem4895884 _112846 t) (@lem4895897 _112846 t)). Qed.
Lemma lem4895899 {_112846 : Type'} (h : _112846) (t : list _112846) : (term92 _112846 h t) = (term92 _112846 h t).
Proof. exact (eq_refl (term92 _112846 h t)). Qed.
Lemma lem4895900 {_112846 : Type'} (h : _112846) (t : list _112846) : (term109 _112846 h t) = (term134 _112846 h t).
Proof. exact (MK_COMB (@lem4895899 _112846 h t) (@lem4895898 _112846 t)). Qed.
Lemma lem4895901 {_112846 : Type'} (h : _112846) (t : list _112846) : (term110 _112846 h t) = (term135 _112846 h t).
Proof. exact (MK_COMB (@lem4895877 _112846 h t) (@lem4895900 _112846 h t)). Qed.
Lemma lem4895902 {_112846 : Type'} (h : _112846) (t : list _112846) : (term74 _112846 h t) = (term135 _112846 h t).
Proof. exact (TRANS (@lem4895856 _112846 h t) (@lem4895901 _112846 h t)). Qed.
Lemma lem4895903 {_112846 : Type'} (t : list _112846) : term136 _112846 t.
Proof. exact (@lem2307535 (term67 _112846 t)). Qed.
Lemma lem4895904 {_112846 : Type'} (t : list _112846) : (term136 _112846 t) = (term137 _112846 t).
Proof. exact (eq_refl (term136 _112846 t)). Qed.
Lemma lem4895905 {_112846 : Type'} (t : list _112846) : term137 _112846 t.
Proof. exact (EQ_MP (@lem4895904 _112846 t) (@lem4895903 _112846 t)). Qed.
Lemma lem4895906 {_112846 : Type'} (t : list _112846) : term138 _112846 t.
Proof. exact (@lem2307535 (@List.length _112846 t)). Qed.
Lemma lem4895907 {_112846 : Type'} (t : list _112846) : (term138 _112846 t) = (term139 _112846 t).
Proof. exact (eq_refl (term138 _112846 t)). Qed.
Lemma lem4895908 {_112846 : Type'} (t : list _112846) : term139 _112846 t.
Proof. exact (EQ_MP (@lem4895907 _112846 t) (@lem4895906 _112846 t)). Qed.
Lemma lem4895909 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) : (term140 _112846 h t _60485 _60486) = (term141 _112846 h t _60485 _60486).
Proof. exact (@lem2318604 (term141 _112846 h t _60485 _60486)). Qed.
Lemma lem4895933 {_112846 : Type'} (h : _112846) (t : list _112846) : (term142 _112846 h t) = (term65 _112846 h t).
Proof. exact (@lem16933 (term65 _112846 h t)). Qed.
Lemma lem4895936 (_60485 : int) (_60486 : int) : (term143 _60485 _60486) = (int_le _60485 _60486).
Proof. exact (@lem16933 (int_le _60485 _60486)). Qed.
Lemma lem4895937 (_60485 : int) (_60486 : int) : (term144 _60485 _60486) = (term144 _60485 _60486).
Proof. exact (eq_refl (term144 _60485 _60486)). Qed.
Lemma lem4895938 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4895939 (_60485 : int) (_60486 : int) : (term145 _60485 _60486) = (term146 _60485 _60486).
Proof. exact (MK_COMB (@lem4895938) (@lem4895936 _60485 _60486)). Qed.
Lemma lem4895940 (_60485 : int) (_60486 : int) : (term147 _60485 _60486) = (term148 _60485 _60486).
Proof. exact (MK_COMB (@lem4895939 _60485 _60486) (@lem4895937 _60485 _60486)). Qed.
Lemma lem4895941 (_60485 : int) (_60486 : int) : (term149 _60485 _60486) = (term147 _60485 _60486).
Proof. exact (@lem17160 (term150 _60485 _60486) (term151 _60485 _60486)). Qed.
Lemma lem4895942 (_60485 : int) (_60486 : int) : (term149 _60485 _60486) = (term148 _60485 _60486).
Proof. exact (TRANS (@lem4895941 _60485 _60486) (@lem4895940 _60485 _60486)). Qed.
Lemma lem4895943 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4895944 {_112846 : Type'} (h : _112846) (t : list _112846) : (term152 _112846 h t) = (term153 _112846 h t).
Proof. exact (MK_COMB (@lem4895943) (@lem4895933 _112846 h t)). Qed.
Lemma lem4895945 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) : (term154 _112846 h t _60485 _60486) = (term155 _112846 h t _60485 _60486).
Proof. exact (MK_COMB (@lem4895944 _112846 h t) (@lem4895942 _60485 _60486)). Qed.
Lemma lem4895946 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) : (term156 _112846 h t _60485 _60486) = (term154 _112846 h t _60485 _60486).
Proof. exact (@lem17160 (term157 _112846 h t) (term158 _60485 _60486)). Qed.
Lemma lem4895947 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) : (term156 _112846 h t _60485 _60486) = (term155 _112846 h t _60485 _60486).
Proof. exact (TRANS (@lem4895946 _112846 h t _60485 _60486) (@lem4895945 _112846 h t _60485 _60486)). Qed.
Lemma lem4895951 (_60485 : int) (_60486 : int) : (term143 _60485 _60486) = (int_le _60485 _60486).
Proof. exact (@lem16933 (int_le _60485 _60486)). Qed.
Lemma lem4895952 (_60485 : int) (_60486 : int) : (term159 _60485 _60486) = (term159 _60485 _60486).
Proof. exact (eq_refl (term159 _60485 _60486)). Qed.
Lemma lem4895953 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4895954 (_60485 : int) (_60486 : int) : (term145 _60485 _60486) = (term146 _60485 _60486).
Proof. exact (MK_COMB (@lem4895953) (@lem4895951 _60485 _60486)). Qed.
Lemma lem4895955 (_60485 : int) (_60486 : int) : (term160 _60485 _60486) = (term161 _60485 _60486).
Proof. exact (MK_COMB (@lem4895954 _60485 _60486) (@lem4895952 _60485 _60486)). Qed.
Lemma lem4895956 (_60485 : int) (_60486 : int) : (term162 _60485 _60486) = (term160 _60485 _60486).
Proof. exact (@lem17160 (term150 _60485 _60486) (term163 _60485 _60486)). Qed.
Lemma lem4895957 (_60485 : int) (_60486 : int) : (term162 _60485 _60486) = (term161 _60485 _60486).
Proof. exact (TRANS (@lem4895956 _60485 _60486) (@lem4895955 _60485 _60486)). Qed.
Lemma lem4895959 {_112846 : Type'} (h : _112846) (t : list _112846) : (term164 _112846 h t) = (term164 _112846 h t).
Proof. exact (eq_refl (term164 _112846 h t)). Qed.
Lemma lem4895960 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) : (term165 _112846 h t _60485 _60486) = (term166 _112846 h t _60485 _60486).
Proof. exact (MK_COMB (@lem4895959 _112846 h t) (@lem4895957 _60485 _60486)). Qed.
Lemma lem4895961 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) : (term167 _112846 h t _60485 _60486) = (term165 _112846 h t _60485 _60486).
Proof. exact (@lem17160 (term65 _112846 h t) (term168 _60485 _60486)). Qed.
Lemma lem4895962 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) : (term167 _112846 h t _60485 _60486) = (term166 _112846 h t _60485 _60486).
Proof. exact (TRANS (@lem4895961 _112846 h t _60485 _60486) (@lem4895960 _112846 h t _60485 _60486)). Qed.
Lemma lem4895963 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4895964 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) : (term169 _112846 h t _60485 _60486) = (term170 _112846 h t _60485 _60486).
Proof. exact (MK_COMB (@lem4895963) (@lem4895947 _112846 h t _60485 _60486)). Qed.
Lemma lem4895965 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) : (term171 _112846 h t _60485 _60486) = (term172 _112846 h t _60485 _60486).
Proof. exact (MK_COMB (@lem4895964 _112846 h t _60485 _60486) (@lem4895962 _112846 h t _60485 _60486)). Qed.
Lemma lem4895966 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) : (term173 _112846 h t _60485 _60486) = (term171 _112846 h t _60485 _60486).
Proof. exact (@lem17045 (term174 _112846 h t _60485 _60486) (term175 _112846 h t _60485 _60486)). Qed.
Lemma lem4895967 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) : (term173 _112846 h t _60485 _60486) = (term172 _112846 h t _60485 _60486).
Proof. exact (TRANS (@lem4895966 _112846 h t _60485 _60486) (@lem4895965 _112846 h t _60485 _60486)). Qed.
Lemma lem4895969 (_60486 : int) : (term176 _60486) = (term176 _60486).
Proof. exact (eq_refl (term176 _60486)). Qed.
Lemma lem4895970 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) : (term177 _112846 h t _60485 _60486) = (term178 _112846 h t _60485 _60486).
Proof. exact (MK_COMB (@lem4895969 _60486) (@lem4895967 _112846 h t _60485 _60486)). Qed.
Lemma lem4895971 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) : (term179 _112846 h t _60485 _60486) = (term177 _112846 h t _60485 _60486).
Proof. exact (@lem17362 (term180 _60486) (term181 _112846 h t _60485 _60486)). Qed.
Lemma lem4895972 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) : (term179 _112846 h t _60485 _60486) = (term178 _112846 h t _60485 _60486).
Proof. exact (TRANS (@lem4895971 _112846 h t _60485 _60486) (@lem4895970 _112846 h t _60485 _60486)). Qed.
Lemma lem4895974 (_60485 : int) : (term176 _60485) = (term176 _60485).
Proof. exact (eq_refl (term176 _60485)). Qed.
Lemma lem4895975 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) : (term182 _112846 h t _60485 _60486) = (term183 _112846 h t _60485 _60486).
Proof. exact (MK_COMB (@lem4895974 _60485) (@lem4895972 _112846 h t _60485 _60486)). Qed.
Lemma lem4895976 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) : (term184 _112846 h t _60485 _60486) = (term182 _112846 h t _60485 _60486).
Proof. exact (@lem17362 (term180 _60485) (term185 _112846 h t _60485 _60486)). Qed.
Lemma lem4896014 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) : (term184 _112846 h t _60485 _60486) = (term183 _112846 h t _60485 _60486).
Proof. exact (TRANS (@lem4895976 _112846 h t _60485 _60486) (@lem4895975 _112846 h t _60485 _60486)). Qed.
Lemma lem4896017 (x : int) (y : int) : (int_le x y) = (term186 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem4896018 (_60485 : int) : (term180 _60485) = (term187 _60485).
Proof. exact (@lem4896017 term188 _60485). Qed.
Lemma lem4896020 (n : nat) : (term189 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem4896021 : term190 = term191.
Proof. exact (@lem4896020 (NUMERAL 0)). Qed.
Lemma lem4896022 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4896023 : term192 = term193.
Proof. exact (MK_COMB (@lem4896022) (@lem4896021)). Qed.
Lemma lem4896024 (_60485 : int) : (real_of_int _60485) = (real_of_int _60485).
Proof. exact (eq_refl (real_of_int _60485)). Qed.
Lemma lem4896025 (_60485 : int) : (term187 _60485) = (term194 _60485).
Proof. exact (MK_COMB (@lem4896023) (@lem4896024 _60485)). Qed.
Lemma lem4896027 (_60485 : int) : (term180 _60485) = (term194 _60485).
Proof. exact (TRANS (@lem4896018 _60485) (@lem4896025 _60485)). Qed.
Lemma lem4896030 (x : int) (y : int) : (int_le x y) = (term186 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem4896031 (_60486 : int) : (term180 _60486) = (term187 _60486).
Proof. exact (@lem4896030 term188 _60486). Qed.
Lemma lem4896033 (n : nat) : (term189 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem4896034 : term190 = term191.
Proof. exact (@lem4896033 (NUMERAL 0)). Qed.
Lemma lem4896035 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4896036 : term192 = term193.
Proof. exact (MK_COMB (@lem4896035) (@lem4896034)). Qed.
Lemma lem4896037 (_60486 : int) : (real_of_int _60486) = (real_of_int _60486).
Proof. exact (eq_refl (real_of_int _60486)). Qed.
Lemma lem4896038 (_60486 : int) : (term187 _60486) = (term194 _60486).
Proof. exact (MK_COMB (@lem4896036) (@lem4896037 _60486)). Qed.
Lemma lem4896040 (_60486 : int) : (term180 _60486) = (term194 _60486).
Proof. exact (TRANS (@lem4896031 _60486) (@lem4896038 _60486)). Qed.
Lemma lem4896046 (x : int) (y : int) : (int_le x y) = (term186 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem4896048 (_60485 : int) (_60486 : int) : (int_le _60485 _60486) = (term186 _60485 _60486).
Proof. exact (@lem4896046 _60485 _60486). Qed.
Lemma lem4896050 (y : int) (x : int) : (term150 x y) = (term195 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem4896051 (_60486 : int) (_60485 : int) : (term144 _60485 _60486) = (term196 _60486 _60485).
Proof. exact (@lem4896050 (term197 _60486) _60485). Qed.
Lemma lem4896053 (x : int) (y : int) : (int_le x y) = (term186 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem4896054 (_60486 : int) (_60485 : int) : (term196 _60486 _60485) = (term198 _60486 _60485).
Proof. exact (@lem4896053 (term199 _60486) _60485). Qed.
Lemma lem4896056 (x : int) (y : int) : (term200 x y) = (term201 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem4896057 (_60486 : int) : (term202 _60486) = (term203 _60486).
Proof. exact (@lem4896056 (term197 _60486) term204). Qed.
Lemma lem4896059 (x : int) (y : int) : (term200 x y) = (term201 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem4896060 (_60486 : int) : (term205 _60486) = (term206 _60486).
Proof. exact (@lem4896059 _60486 term204). Qed.
Lemma lem4896062 (n : nat) : (term189 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem4896063 : term207 = term208.
Proof. exact (@lem4896062 term121). Qed.
Lemma lem4896064 (_60486 : int) : (term209 _60486) = (term209 _60486).
Proof. exact (eq_refl (term209 _60486)). Qed.
Lemma lem4896065 (_60486 : int) : (term206 _60486) = (term210 _60486).
Proof. exact (MK_COMB (@lem4896064 _60486) (@lem4896063)). Qed.
Lemma lem4896066 (_60486 : int) : (term205 _60486) = (term210 _60486).
Proof. exact (TRANS (@lem4896060 _60486) (@lem4896065 _60486)). Qed.
Lemma lem4896067 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4896068 (_60486 : int) : (term211 _60486) = (term212 _60486).
Proof. exact (MK_COMB (@lem4896067) (@lem4896066 _60486)). Qed.
Lemma lem4896070 (n : nat) : (term189 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem4896071 : term207 = term208.
Proof. exact (@lem4896070 term121). Qed.
Lemma lem4896072 (_60486 : int) : (term203 _60486) = (term213 _60486).
Proof. exact (MK_COMB (@lem4896068 _60486) (@lem4896071)). Qed.
Lemma lem4896073 (_60486 : int) : (term202 _60486) = (term213 _60486).
Proof. exact (TRANS (@lem4896057 _60486) (@lem4896072 _60486)). Qed.
Lemma lem4896074 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4896075 (_60486 : int) : (term214 _60486) = (term215 _60486).
Proof. exact (MK_COMB (@lem4896074) (@lem4896073 _60486)). Qed.
Lemma lem4896076 (_60485 : int) : (real_of_int _60485) = (real_of_int _60485).
Proof. exact (eq_refl (real_of_int _60485)). Qed.
Lemma lem4896077 (_60486 : int) (_60485 : int) : (term198 _60486 _60485) = (term216 _60486 _60485).
Proof. exact (MK_COMB (@lem4896075 _60486) (@lem4896076 _60485)). Qed.
Lemma lem4896078 (_60486 : int) (_60485 : int) : (term196 _60486 _60485) = (term216 _60486 _60485).
Proof. exact (TRANS (@lem4896054 _60486 _60485) (@lem4896077 _60486 _60485)). Qed.
Lemma lem4896079 (_60486 : int) (_60485 : int) : (term144 _60485 _60486) = (term216 _60486 _60485).
Proof. exact (TRANS (@lem4896051 _60486 _60485) (@lem4896078 _60486 _60485)). Qed.
Lemma lem4896080 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4896081 (_60485 : int) (_60486 : int) : (term146 _60485 _60486) = (term217 _60485 _60486).
Proof. exact (MK_COMB (@lem4896080) (@lem4896048 _60485 _60486)). Qed.
Lemma lem4896082 (_60486 : int) (_60485 : int) : (term148 _60485 _60486) = (term218 _60486 _60485).
Proof. exact (MK_COMB (@lem4896081 _60485 _60486) (@lem4896079 _60486 _60485)). Qed.
Lemma lem4896084 {_112846 : Type'} (h : _112846) (t : list _112846) : (term153 _112846 h t) = (term153 _112846 h t).
Proof. exact (eq_refl (term153 _112846 h t)). Qed.
Lemma lem4896085 {_112846 : Type'} (h : _112846) (t : list _112846) (_60486 : int) (_60485 : int) : (term155 _112846 h t _60485 _60486) = (term219 _112846 h t _60486 _60485).
Proof. exact (MK_COMB (@lem4896084 _112846 h t) (@lem4896082 _60486 _60485)). Qed.
Lemma lem4896091 (x : int) (y : int) : (int_le x y) = (term186 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem4896093 (_60485 : int) (_60486 : int) : (int_le _60485 _60486) = (term186 _60485 _60486).
Proof. exact (@lem4896091 _60485 _60486). Qed.
Lemma lem4896095 (y : int) (x : int) : (term150 x y) = (term195 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem4896096 (_60486 : int) (_60485 : int) : (term159 _60485 _60486) = (term220 _60486 _60485).
Proof. exact (@lem4896095 (term197 _60486) (term197 _60485)). Qed.
Lemma lem4896098 (x : int) (y : int) : (int_le x y) = (term186 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem4896099 (_60486 : int) (_60485 : int) : (term220 _60486 _60485) = (term221 _60486 _60485).
Proof. exact (@lem4896098 (term199 _60486) (term197 _60485)). Qed.
Lemma lem4896101 (x : int) (y : int) : (term200 x y) = (term201 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem4896102 (_60486 : int) : (term202 _60486) = (term203 _60486).
Proof. exact (@lem4896101 (term197 _60486) term204). Qed.
Lemma lem4896104 (x : int) (y : int) : (term200 x y) = (term201 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem4896105 (_60486 : int) : (term205 _60486) = (term206 _60486).
Proof. exact (@lem4896104 _60486 term204). Qed.
Lemma lem4896107 (n : nat) : (term189 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem4896108 : term207 = term208.
Proof. exact (@lem4896107 term121). Qed.
Lemma lem4896109 (_60486 : int) : (term209 _60486) = (term209 _60486).
Proof. exact (eq_refl (term209 _60486)). Qed.
Lemma lem4896110 (_60486 : int) : (term206 _60486) = (term210 _60486).
Proof. exact (MK_COMB (@lem4896109 _60486) (@lem4896108)). Qed.
Lemma lem4896111 (_60486 : int) : (term205 _60486) = (term210 _60486).
Proof. exact (TRANS (@lem4896105 _60486) (@lem4896110 _60486)). Qed.
Lemma lem4896112 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4896113 (_60486 : int) : (term211 _60486) = (term212 _60486).
Proof. exact (MK_COMB (@lem4896112) (@lem4896111 _60486)). Qed.
Lemma lem4896115 (n : nat) : (term189 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem4896116 : term207 = term208.
Proof. exact (@lem4896115 term121). Qed.
Lemma lem4896117 (_60486 : int) : (term203 _60486) = (term213 _60486).
Proof. exact (MK_COMB (@lem4896113 _60486) (@lem4896116)). Qed.
Lemma lem4896118 (_60486 : int) : (term202 _60486) = (term213 _60486).
Proof. exact (TRANS (@lem4896102 _60486) (@lem4896117 _60486)). Qed.
Lemma lem4896119 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4896120 (_60486 : int) : (term214 _60486) = (term215 _60486).
Proof. exact (MK_COMB (@lem4896119) (@lem4896118 _60486)). Qed.
Lemma lem4896122 (x : int) (y : int) : (term200 x y) = (term201 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem4896123 (_60485 : int) : (term205 _60485) = (term206 _60485).
Proof. exact (@lem4896122 _60485 term204). Qed.
Lemma lem4896125 (n : nat) : (term189 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem4896126 : term207 = term208.
Proof. exact (@lem4896125 term121). Qed.
Lemma lem4896127 (_60485 : int) : (term209 _60485) = (term209 _60485).
Proof. exact (eq_refl (term209 _60485)). Qed.
Lemma lem4896128 (_60485 : int) : (term206 _60485) = (term210 _60485).
Proof. exact (MK_COMB (@lem4896127 _60485) (@lem4896126)). Qed.
Lemma lem4896129 (_60485 : int) : (term205 _60485) = (term210 _60485).
Proof. exact (TRANS (@lem4896123 _60485) (@lem4896128 _60485)). Qed.
Lemma lem4896130 (_60486 : int) (_60485 : int) : (term221 _60486 _60485) = (term222 _60486 _60485).
Proof. exact (MK_COMB (@lem4896120 _60486) (@lem4896129 _60485)). Qed.
Lemma lem4896131 (_60486 : int) (_60485 : int) : (term220 _60486 _60485) = (term222 _60486 _60485).
Proof. exact (TRANS (@lem4896099 _60486 _60485) (@lem4896130 _60486 _60485)). Qed.
Lemma lem4896132 (_60486 : int) (_60485 : int) : (term159 _60485 _60486) = (term222 _60486 _60485).
Proof. exact (TRANS (@lem4896096 _60486 _60485) (@lem4896131 _60486 _60485)). Qed.
Lemma lem4896133 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4896134 (_60485 : int) (_60486 : int) : (term146 _60485 _60486) = (term217 _60485 _60486).
Proof. exact (MK_COMB (@lem4896133) (@lem4896093 _60485 _60486)). Qed.
Lemma lem4896135 (_60486 : int) (_60485 : int) : (term161 _60485 _60486) = (term223 _60486 _60485).
Proof. exact (MK_COMB (@lem4896134 _60485 _60486) (@lem4896132 _60486 _60485)). Qed.
Lemma lem4896137 {_112846 : Type'} (h : _112846) (t : list _112846) : (term164 _112846 h t) = (term164 _112846 h t).
Proof. exact (eq_refl (term164 _112846 h t)). Qed.
Lemma lem4896138 {_112846 : Type'} (h : _112846) (t : list _112846) (_60486 : int) (_60485 : int) : (term166 _112846 h t _60485 _60486) = (term224 _112846 h t _60486 _60485).
Proof. exact (MK_COMB (@lem4896137 _112846 h t) (@lem4896135 _60486 _60485)). Qed.
Lemma lem4896139 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4896140 {_112846 : Type'} (h : _112846) (t : list _112846) (_60486 : int) (_60485 : int) : (term170 _112846 h t _60485 _60486) = (term225 _112846 h t _60486 _60485).
Proof. exact (MK_COMB (@lem4896139) (@lem4896085 _112846 h t _60486 _60485)). Qed.
Lemma lem4896141 {_112846 : Type'} (h : _112846) (t : list _112846) (_60486 : int) (_60485 : int) : (term172 _112846 h t _60485 _60486) = (term226 _112846 h t _60486 _60485).
Proof. exact (MK_COMB (@lem4896140 _112846 h t _60486 _60485) (@lem4896138 _112846 h t _60486 _60485)). Qed.
Lemma lem4896142 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4896143 (_60486 : int) : (term176 _60486) = (term227 _60486).
Proof. exact (MK_COMB (@lem4896142) (@lem4896040 _60486)). Qed.
Lemma lem4896144 {_112846 : Type'} (h : _112846) (t : list _112846) (_60486 : int) (_60485 : int) : (term178 _112846 h t _60485 _60486) = (term228 _112846 h t _60486 _60485).
Proof. exact (MK_COMB (@lem4896143 _60486) (@lem4896141 _112846 h t _60486 _60485)). Qed.
Lemma lem4896145 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4896146 (_60485 : int) : (term176 _60485) = (term227 _60485).
Proof. exact (MK_COMB (@lem4896145) (@lem4896027 _60485)). Qed.
Lemma lem4896147 {_112846 : Type'} (h : _112846) (t : list _112846) (_60486 : int) (_60485 : int) : (term183 _112846 h t _60485 _60486) = (term229 _112846 h t _60486 _60485).
Proof. exact (MK_COMB (@lem4896146 _60485) (@lem4896144 _112846 h t _60486 _60485)). Qed.
Lemma lem4896148 {_112846 : Type'} (h : _112846) (t : list _112846) (_60486 : int) (_60485 : int) : (term184 _112846 h t _60485 _60486) = (term229 _112846 h t _60486 _60485).
Proof. exact (TRANS (@lem4896014 _112846 h t _60485 _60486) (@lem4896147 _112846 h t _60486 _60485)). Qed.
Lemma lem4896152 (t : Prop) : (term60 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4896230 {_112846 : Type'} (h : _112846) (t : list _112846) (_60486 : int) (_60485 : int) : (term230 _112846 h t _60486 _60485) = (term229 _112846 h t _60486 _60485).
Proof. exact (@lem4896152 (term229 _112846 h t _60486 _60485)). Qed.
Lemma lem4896231 (_60485 : int) : (term194 _60485) = (term231 _60485).
Proof. exact (@lem1988287 (real_of_int _60485) term191). Qed.
Lemma lem4896237 (_60485 : int) : (term232 _60485) = (term233 _60485).
Proof. exact (@lem1982792 (real_of_int _60485) term191). Qed.
Lemma lem4896239 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4896240 : term191 = term235.
Proof. exact (@lem4896239 (NUMERAL 0)). Qed.
Lemma lem4896242 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4896243 : term238 = term239.
Proof. exact (@lem4896242 term121). Qed.
Lemma lem4896244 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4896245 : term240 = term241.
Proof. exact (MK_COMB (@lem4896244) (@lem4896243)). Qed.
Lemma lem4896246 : term242 = term243.
Proof. exact (MK_COMB (@lem4896245) (@lem4896240)). Qed.
Lemma lem4896247 : term243 = term244.
Proof. exact (@lem1981613 term238 term191 term208 term208). Qed.
Lemma lem4896249 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4896250 : term247 = term248.
Proof. exact (@lem4896249 term121 term121). Qed.
Lemma lem4896251 : (term249 = (BIT1 0)) = (term250 = term121).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4896252 : term250 = term121.
Proof. exact (EQ_MP (@lem4896251) (@lem940073)). Qed.
Lemma lem4896253 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4896254 : term248 = term208.
Proof. exact (MK_COMB (@lem4896253) (@lem4896252)). Qed.
Lemma lem4896255 : term247 = term208.
Proof. exact (TRANS (@lem4896250) (@lem4896254)). Qed.
Lemma lem4896257 (x : nat) : (term251 x) = term191.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem4896258 : term242 = term191.
Proof. exact (@lem4896257 term121). Qed.
Lemma lem4896259 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem4896260 : term252 = term253.
Proof. exact (MK_COMB (@lem4896259) (@lem4896258)). Qed.
Lemma lem4896261 : term244 = term235.
Proof. exact (MK_COMB (@lem4896260) (@lem4896255)). Qed.
Lemma lem4896262 : term243 = term235.
Proof. exact (TRANS (@lem4896247) (@lem4896261)). Qed.
Lemma lem4896263 : term242 = term235.
Proof. exact (TRANS (@lem4896246) (@lem4896262)). Qed.
Lemma lem4896265 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem4896266 : term235 = term191.
Proof. exact (@lem4896265 term191). Qed.
Lemma lem4896267 : term242 = term191.
Proof. exact (TRANS (@lem4896263) (@lem4896266)). Qed.
Lemma lem4896268 (_60485 : int) : (term209 _60485) = (term209 _60485).
Proof. exact (eq_refl (term209 _60485)). Qed.
Lemma lem4896269 (_60485 : int) : (term233 _60485) = (term255 _60485).
Proof. exact (MK_COMB (@lem4896268 _60485) (@lem4896267)). Qed.
Lemma lem4896270 (_60485 : int) : (term255 _60485) = (real_of_int _60485).
Proof. exact (@lem1982723 (real_of_int _60485)). Qed.
Lemma lem4896271 (_60485 : int) : (term233 _60485) = (real_of_int _60485).
Proof. exact (TRANS (@lem4896269 _60485) (@lem4896270 _60485)). Qed.
Lemma lem4896273 (_60485 : int) : (term232 _60485) = (real_of_int _60485).
Proof. exact (TRANS (@lem4896237 _60485) (@lem4896271 _60485)). Qed.
Lemma lem4896274 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4896275 (_60485 : int) : (term256 _60485) = (term257 _60485).
Proof. exact (MK_COMB (@lem4896274) (@lem4896273 _60485)). Qed.
Lemma lem4896276 : term191 = term191.
Proof. exact (eq_refl term191). Qed.
Lemma lem4896277 (_60485 : int) : (term231 _60485) = (term258 _60485).
Proof. exact (MK_COMB (@lem4896275 _60485) (@lem4896276)). Qed.
Lemma lem4896278 (_60485 : int) : (term194 _60485) = (term258 _60485).
Proof. exact (TRANS (@lem4896231 _60485) (@lem4896277 _60485)). Qed.
Lemma lem4896279 (_60486 : int) : (term194 _60486) = (term231 _60486).
Proof. exact (@lem1988287 (real_of_int _60486) term191). Qed.
Lemma lem4896285 (_60486 : int) : (term232 _60486) = (term233 _60486).
Proof. exact (@lem1982792 (real_of_int _60486) term191). Qed.
Lemma lem4896287 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4896288 : term191 = term235.
Proof. exact (@lem4896287 (NUMERAL 0)). Qed.
Lemma lem4896290 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4896291 : term238 = term239.
Proof. exact (@lem4896290 term121). Qed.
Lemma lem4896292 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4896293 : term240 = term241.
Proof. exact (MK_COMB (@lem4896292) (@lem4896291)). Qed.
Lemma lem4896294 : term242 = term243.
Proof. exact (MK_COMB (@lem4896293) (@lem4896288)). Qed.
Lemma lem4896295 : term243 = term244.
Proof. exact (@lem1981613 term238 term191 term208 term208). Qed.
Lemma lem4896297 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4896298 : term247 = term248.
Proof. exact (@lem4896297 term121 term121). Qed.
Lemma lem4896299 : (term249 = (BIT1 0)) = (term250 = term121).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4896300 : term250 = term121.
Proof. exact (EQ_MP (@lem4896299) (@lem940073)). Qed.
Lemma lem4896301 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4896302 : term248 = term208.
Proof. exact (MK_COMB (@lem4896301) (@lem4896300)). Qed.
Lemma lem4896303 : term247 = term208.
Proof. exact (TRANS (@lem4896298) (@lem4896302)). Qed.
Lemma lem4896305 (x : nat) : (term251 x) = term191.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem4896306 : term242 = term191.
Proof. exact (@lem4896305 term121). Qed.
Lemma lem4896307 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem4896308 : term252 = term253.
Proof. exact (MK_COMB (@lem4896307) (@lem4896306)). Qed.
Lemma lem4896309 : term244 = term235.
Proof. exact (MK_COMB (@lem4896308) (@lem4896303)). Qed.
Lemma lem4896310 : term243 = term235.
Proof. exact (TRANS (@lem4896295) (@lem4896309)). Qed.
Lemma lem4896311 : term242 = term235.
Proof. exact (TRANS (@lem4896294) (@lem4896310)). Qed.
Lemma lem4896313 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem4896314 : term235 = term191.
Proof. exact (@lem4896313 term191). Qed.
Lemma lem4896315 : term242 = term191.
Proof. exact (TRANS (@lem4896311) (@lem4896314)). Qed.
Lemma lem4896316 (_60486 : int) : (term209 _60486) = (term209 _60486).
Proof. exact (eq_refl (term209 _60486)). Qed.
Lemma lem4896317 (_60486 : int) : (term233 _60486) = (term255 _60486).
Proof. exact (MK_COMB (@lem4896316 _60486) (@lem4896315)). Qed.
Lemma lem4896318 (_60486 : int) : (term255 _60486) = (real_of_int _60486).
Proof. exact (@lem1982723 (real_of_int _60486)). Qed.
Lemma lem4896319 (_60486 : int) : (term233 _60486) = (real_of_int _60486).
Proof. exact (TRANS (@lem4896317 _60486) (@lem4896318 _60486)). Qed.
Lemma lem4896321 (_60486 : int) : (term232 _60486) = (real_of_int _60486).
Proof. exact (TRANS (@lem4896285 _60486) (@lem4896319 _60486)). Qed.
Lemma lem4896322 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4896323 (_60486 : int) : (term256 _60486) = (term257 _60486).
Proof. exact (MK_COMB (@lem4896322) (@lem4896321 _60486)). Qed.
Lemma lem4896324 : term191 = term191.
Proof. exact (eq_refl term191). Qed.
Lemma lem4896325 (_60486 : int) : (term231 _60486) = (term258 _60486).
Proof. exact (MK_COMB (@lem4896323 _60486) (@lem4896324)). Qed.
Lemma lem4896326 (_60486 : int) : (term194 _60486) = (term258 _60486).
Proof. exact (TRANS (@lem4896279 _60486) (@lem4896325 _60486)). Qed.
Lemma lem4896328 (_60486 : int) (_60485 : int) : (term186 _60485 _60486) = (term259 _60486 _60485).
Proof. exact (@lem1988287 (real_of_int _60486) (real_of_int _60485)). Qed.
Lemma lem4896334 (_60486 : int) (_60485 : int) : (term260 _60486 _60485) = (term261 _60486 _60485).
Proof. exact (@lem1982792 (real_of_int _60486) (real_of_int _60485)). Qed.
Lemma lem4896339 (_60485 : int) (_60486 : int) : (term261 _60486 _60485) = (term262 _60485 _60486).
Proof. exact (@lem1982761 (term263 _60485) (real_of_int _60486)). Qed.
Lemma lem4896341 (_60485 : int) (_60486 : int) : (term260 _60486 _60485) = (term262 _60485 _60486).
Proof. exact (TRANS (@lem4896334 _60486 _60485) (@lem4896339 _60485 _60486)). Qed.
Lemma lem4896342 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4896343 (_60485 : int) (_60486 : int) : (term264 _60486 _60485) = (term265 _60485 _60486).
Proof. exact (MK_COMB (@lem4896342) (@lem4896341 _60485 _60486)). Qed.
Lemma lem4896344 : term191 = term191.
Proof. exact (eq_refl term191). Qed.
Lemma lem4896345 (_60485 : int) (_60486 : int) : (term259 _60486 _60485) = (term266 _60485 _60486).
Proof. exact (MK_COMB (@lem4896343 _60485 _60486) (@lem4896344)). Qed.
Lemma lem4896346 (_60485 : int) (_60486 : int) : (term186 _60485 _60486) = (term266 _60485 _60486).
Proof. exact (TRANS (@lem4896328 _60486 _60485) (@lem4896345 _60485 _60486)). Qed.
Lemma lem4896347 (_60485 : int) (_60486 : int) : (term216 _60486 _60485) = (term267 _60485 _60486).
Proof. exact (@lem1988287 (real_of_int _60485) (term213 _60486)). Qed.
Lemma lem4896359 (_60486 : int) : (term213 _60486) = (term268 _60486).
Proof. exact (@lem1982755 (real_of_int _60486) term208 term208). Qed.
Lemma lem4896361 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4896362 : term208 = term269.
Proof. exact (@lem4896361 term121). Qed.
Lemma lem4896364 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4896365 : term208 = term269.
Proof. exact (@lem4896364 term121). Qed.
Lemma lem4896366 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4896367 : term270 = term271.
Proof. exact (MK_COMB (@lem4896366) (@lem4896365)). Qed.
Lemma lem4896368 : term272 = term273.
Proof. exact (MK_COMB (@lem4896367) (@lem4896362)). Qed.
Lemma lem4896369 : term274.
Proof. exact (@lem1981473 term208 term208 term208 term208 term275 term208). Qed.
Lemma lem4896371 (m : nat) (n : nat) : (term276 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4896372 : term277 = term278.
Proof. exact (@lem4896371 (NUMERAL 0) term121). Qed.
Lemma lem4896373 : term279 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4896374 (h1 : term279 = (BIT1 0)) : term278 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4896375 : (term279 = (BIT1 0)) = (term278 = True).
Proof. exact (prop_ext (fun h1 : term279 = (BIT1 0) => @lem4896374 h1) (fun h1 : term278 = True => @lem4896373)). Qed.
Lemma lem4896376 : term278 = True.
Proof. exact (EQ_MP (@lem4896375) (@lem4896373)). Qed.
Lemma lem4896377 : term277 = True.
Proof. exact (TRANS (@lem4896372) (@lem4896376)). Qed.
Lemma lem4896378 : True = term277.
Proof. exact (SYM (@lem4896377)). Qed.
Lemma lem4896379 : term277.
Proof. exact (EQ_MP (@lem4896378) (@lem0)). Qed.
Lemma lem4896380 : term280.
Proof. exact (@lem4896369 (@lem4896379)). Qed.
Lemma lem4896382 (m : nat) (n : nat) : (term276 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4896383 : term277 = term278.
Proof. exact (@lem4896382 (NUMERAL 0) term121). Qed.
Lemma lem4896384 : term279 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4896385 (h1 : term279 = (BIT1 0)) : term278 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4896386 : (term279 = (BIT1 0)) = (term278 = True).
Proof. exact (prop_ext (fun h1 : term279 = (BIT1 0) => @lem4896385 h1) (fun h1 : term278 = True => @lem4896384)). Qed.
Lemma lem4896387 : term278 = True.
Proof. exact (EQ_MP (@lem4896386) (@lem4896384)). Qed.
Lemma lem4896388 : term277 = True.
Proof. exact (TRANS (@lem4896383) (@lem4896387)). Qed.
Lemma lem4896389 : True = term277.
Proof. exact (SYM (@lem4896388)). Qed.
Lemma lem4896390 : term277.
Proof. exact (EQ_MP (@lem4896389) (@lem0)). Qed.
Lemma lem4896391 : term281.
Proof. exact (@lem4896380 (@lem4896390)). Qed.
Lemma lem4896393 (m : nat) (n : nat) : (term276 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4896394 : term277 = term278.
Proof. exact (@lem4896393 (NUMERAL 0) term121). Qed.
Lemma lem4896395 : term279 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4896396 (h1 : term279 = (BIT1 0)) : term278 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4896397 : (term279 = (BIT1 0)) = (term278 = True).
Proof. exact (prop_ext (fun h1 : term279 = (BIT1 0) => @lem4896396 h1) (fun h1 : term278 = True => @lem4896395)). Qed.
Lemma lem4896398 : term278 = True.
Proof. exact (EQ_MP (@lem4896397) (@lem4896395)). Qed.
Lemma lem4896399 : term277 = True.
Proof. exact (TRANS (@lem4896394) (@lem4896398)). Qed.
Lemma lem4896400 : True = term277.
Proof. exact (SYM (@lem4896399)). Qed.
Lemma lem4896401 : term277.
Proof. exact (EQ_MP (@lem4896400) (@lem0)). Qed.
Lemma lem4896402 : term282.
Proof. exact (@lem4896391 (@lem4896401)). Qed.
Lemma lem4896404 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4896405 : term247 = term248.
Proof. exact (@lem4896404 term121 term121). Qed.
Lemma lem4896406 : (term249 = (BIT1 0)) = (term250 = term121).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4896407 : term250 = term121.
Proof. exact (EQ_MP (@lem4896406) (@lem940073)). Qed.
Lemma lem4896408 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4896409 : term248 = term208.
Proof. exact (MK_COMB (@lem4896408) (@lem4896407)). Qed.
Lemma lem4896410 : term247 = term208.
Proof. exact (TRANS (@lem4896405) (@lem4896409)). Qed.
Lemma lem4896412 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4896413 : term247 = term248.
Proof. exact (@lem4896412 term121 term121). Qed.
Lemma lem4896414 : (term249 = (BIT1 0)) = (term250 = term121).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4896415 : term250 = term121.
Proof. exact (EQ_MP (@lem4896414) (@lem940073)). Qed.
Lemma lem4896416 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4896417 : term248 = term208.
Proof. exact (MK_COMB (@lem4896416) (@lem4896415)). Qed.
Lemma lem4896418 : term247 = term208.
Proof. exact (TRANS (@lem4896413) (@lem4896417)). Qed.
Lemma lem4896419 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4896420 : term283 = term270.
Proof. exact (MK_COMB (@lem4896419) (@lem4896418)). Qed.
Lemma lem4896421 : term284 = term272.
Proof. exact (MK_COMB (@lem4896420) (@lem4896410)). Qed.
Lemma lem4896422 : term272 = term285.
Proof. exact (@lem1367770 term121 term121). Qed.
Lemma lem4896423 : term286 = term287.
Proof. exact (@lem706885). Qed.
Lemma lem4896424 : (term286 = term287) = (term288 = term289).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term287). Qed.
Lemma lem4896425 : term288 = term289.
Proof. exact (EQ_MP (@lem4896424) (@lem4896423)). Qed.
Lemma lem4896426 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4896427 : term285 = term275.
Proof. exact (MK_COMB (@lem4896426) (@lem4896425)). Qed.
Lemma lem4896428 : term272 = term275.
Proof. exact (TRANS (@lem4896422) (@lem4896427)). Qed.
Lemma lem4896429 : term284 = term275.
Proof. exact (TRANS (@lem4896421) (@lem4896428)). Qed.
Lemma lem4896430 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4896431 : term290 = term291.
Proof. exact (MK_COMB (@lem4896430) (@lem4896429)). Qed.
Lemma lem4896432 : term208 = term208.
Proof. exact (eq_refl term208). Qed.
Lemma lem4896433 : term292 = term293.
Proof. exact (MK_COMB (@lem4896431) (@lem4896432)). Qed.
Lemma lem4896435 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4896436 : term293 = term294.
Proof. exact (@lem4896435 term289 term121). Qed.
Lemma lem4896437 : term295 = term287.
Proof. exact (@lem996237 term287). Qed.
Lemma lem4896438 : (term295 = term287) = (term296 = term289).
Proof. exact (@lem1007663 term287 (BIT1 0) term287). Qed.
Lemma lem4896439 : term296 = term289.
Proof. exact (EQ_MP (@lem4896438) (@lem4896437)). Qed.
Lemma lem4896440 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4896441 : term294 = term275.
Proof. exact (MK_COMB (@lem4896440) (@lem4896439)). Qed.
Lemma lem4896442 : term293 = term275.
Proof. exact (TRANS (@lem4896436) (@lem4896441)). Qed.
Lemma lem4896443 : term292 = term275.
Proof. exact (TRANS (@lem4896433) (@lem4896442)). Qed.
Lemma lem4896445 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4896446 : term247 = term248.
Proof. exact (@lem4896445 term121 term121). Qed.
Lemma lem4896447 : (term249 = (BIT1 0)) = (term250 = term121).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4896448 : term250 = term121.
Proof. exact (EQ_MP (@lem4896447) (@lem940073)). Qed.
Lemma lem4896449 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4896450 : term248 = term208.
Proof. exact (MK_COMB (@lem4896449) (@lem4896448)). Qed.
Lemma lem4896451 : term247 = term208.
Proof. exact (TRANS (@lem4896446) (@lem4896450)). Qed.
Lemma lem4896452 : term291 = term291.
Proof. exact (eq_refl term291). Qed.
Lemma lem4896453 : term297 = term293.
Proof. exact (MK_COMB (@lem4896452) (@lem4896451)). Qed.
Lemma lem4896455 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4896456 : term293 = term294.
Proof. exact (@lem4896455 term289 term121). Qed.
Lemma lem4896457 : term295 = term287.
Proof. exact (@lem996237 term287). Qed.
Lemma lem4896458 : (term295 = term287) = (term296 = term289).
Proof. exact (@lem1007663 term287 (BIT1 0) term287). Qed.
Lemma lem4896459 : term296 = term289.
Proof. exact (EQ_MP (@lem4896458) (@lem4896457)). Qed.
Lemma lem4896460 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4896461 : term294 = term275.
Proof. exact (MK_COMB (@lem4896460) (@lem4896459)). Qed.
Lemma lem4896462 : term293 = term275.
Proof. exact (TRANS (@lem4896456) (@lem4896461)). Qed.
Lemma lem4896463 : term297 = term275.
Proof. exact (TRANS (@lem4896453) (@lem4896462)). Qed.
Lemma lem4896464 : term275 = term297.
Proof. exact (SYM (@lem4896463)). Qed.
Lemma lem4896465 : term292 = term297.
Proof. exact (TRANS (@lem4896443) (@lem4896464)). Qed.
Lemma lem4896466 : term273 = term298.
Proof. exact (@lem4896402 (@lem4896465)). Qed.
Lemma lem4896467 : term272 = term298.
Proof. exact (TRANS (@lem4896368) (@lem4896466)). Qed.
Lemma lem4896469 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4896470 : term298 = term275.
Proof. exact (@lem4896469 term275). Qed.
Lemma lem4896471 : term272 = term275.
Proof. exact (TRANS (@lem4896467) (@lem4896470)). Qed.
Lemma lem4896472 (_60486 : int) : (term209 _60486) = (term209 _60486).
Proof. exact (eq_refl (term209 _60486)). Qed.
Lemma lem4896473 (_60486 : int) : (term268 _60486) = (term299 _60486).
Proof. exact (MK_COMB (@lem4896472 _60486) (@lem4896471)). Qed.
Lemma lem4896475 (_60486 : int) : (term213 _60486) = (term299 _60486).
Proof. exact (TRANS (@lem4896359 _60486) (@lem4896473 _60486)). Qed.
Lemma lem4896478 (_60485 : int) : (term300 _60485) = (term300 _60485).
Proof. exact (eq_refl (term300 _60485)). Qed.
Lemma lem4896479 (_60485 : int) (_60486 : int) : (term301 _60485 _60486) = (term302 _60485 _60486).
Proof. exact (MK_COMB (@lem4896478 _60485) (@lem4896475 _60486)). Qed.
Lemma lem4896480 (_60485 : int) (_60486 : int) : (term302 _60485 _60486) = (term303 _60485 _60486).
Proof. exact (@lem1982792 (real_of_int _60485) (term299 _60486)). Qed.
Lemma lem4896481 (_60486 : int) : (term304 _60486) = (term305 _60486).
Proof. exact (@lem1982781 (real_of_int _60486) term238 term275). Qed.
Lemma lem4896483 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4896484 : term275 = term298.
Proof. exact (@lem4896483 term289). Qed.
Lemma lem4896486 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4896487 : term238 = term239.
Proof. exact (@lem4896486 term121). Qed.
Lemma lem4896488 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4896489 : term240 = term241.
Proof. exact (MK_COMB (@lem4896488) (@lem4896487)). Qed.
Lemma lem4896490 : term306 = term307.
Proof. exact (MK_COMB (@lem4896489) (@lem4896484)). Qed.
Lemma lem4896491 : term307 = term308.
Proof. exact (@lem1981613 term238 term275 term208 term208). Qed.
Lemma lem4896493 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4896494 : term247 = term248.
Proof. exact (@lem4896493 term121 term121). Qed.
Lemma lem4896495 : (term249 = (BIT1 0)) = (term250 = term121).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4896496 : term250 = term121.
Proof. exact (EQ_MP (@lem4896495) (@lem940073)). Qed.
Lemma lem4896497 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4896498 : term248 = term208.
Proof. exact (MK_COMB (@lem4896497) (@lem4896496)). Qed.
Lemma lem4896499 : term247 = term208.
Proof. exact (TRANS (@lem4896494) (@lem4896498)). Qed.
Lemma lem4896501 (m : nat) (n : nat) : (term309 m n) = (term310 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4896502 : term306 = term311.
Proof. exact (@lem4896501 term121 term289). Qed.
Lemma lem4896503 : term312 = term287.
Proof. exact (@lem996238 term287). Qed.
Lemma lem4896504 : (term312 = term287) = (term313 = term289).
Proof. exact (@lem1007663 (BIT1 0) term287 term287). Qed.
Lemma lem4896505 : term313 = term289.
Proof. exact (EQ_MP (@lem4896504) (@lem4896503)). Qed.
Lemma lem4896506 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4896507 : term314 = term275.
Proof. exact (MK_COMB (@lem4896506) (@lem4896505)). Qed.
Lemma lem4896508 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4896509 : term311 = term315.
Proof. exact (MK_COMB (@lem4896508) (@lem4896507)). Qed.
Lemma lem4896510 : term306 = term315.
Proof. exact (TRANS (@lem4896502) (@lem4896509)). Qed.
Lemma lem4896511 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem4896512 : term316 = term317.
Proof. exact (MK_COMB (@lem4896511) (@lem4896510)). Qed.
Lemma lem4896513 : term308 = term318.
Proof. exact (MK_COMB (@lem4896512) (@lem4896499)). Qed.
Lemma lem4896514 : term307 = term318.
Proof. exact (TRANS (@lem4896491) (@lem4896513)). Qed.
Lemma lem4896515 : term306 = term318.
Proof. exact (TRANS (@lem4896490) (@lem4896514)). Qed.
Lemma lem4896517 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem4896518 : term318 = term315.
Proof. exact (@lem4896517 term315). Qed.
Lemma lem4896519 : term306 = term315.
Proof. exact (TRANS (@lem4896515) (@lem4896518)). Qed.
Lemma lem4896522 (_60486 : int) : (term319 _60486) = (term319 _60486).
Proof. exact (eq_refl (term319 _60486)). Qed.
Lemma lem4896523 (_60486 : int) : (term305 _60486) = (term320 _60486).
Proof. exact (MK_COMB (@lem4896522 _60486) (@lem4896519)). Qed.
Lemma lem4896524 (_60486 : int) : (term304 _60486) = (term320 _60486).
Proof. exact (TRANS (@lem4896481 _60486) (@lem4896523 _60486)). Qed.
Lemma lem4896525 (_60485 : int) : (term209 _60485) = (term209 _60485).
Proof. exact (eq_refl (term209 _60485)). Qed.
Lemma lem4896528 (_60485 : int) (_60486 : int) : (term303 _60485 _60486) = (term321 _60485 _60486).
Proof. exact (MK_COMB (@lem4896525 _60485) (@lem4896524 _60486)). Qed.
Lemma lem4896529 (_60485 : int) (_60486 : int) : (term302 _60485 _60486) = (term321 _60485 _60486).
Proof. exact (TRANS (@lem4896480 _60485 _60486) (@lem4896528 _60485 _60486)). Qed.
Lemma lem4896530 (_60485 : int) (_60486 : int) : (term301 _60485 _60486) = (term321 _60485 _60486).
Proof. exact (TRANS (@lem4896479 _60485 _60486) (@lem4896529 _60485 _60486)). Qed.
Lemma lem4896531 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4896532 (_60485 : int) (_60486 : int) : (term322 _60485 _60486) = (term323 _60485 _60486).
Proof. exact (MK_COMB (@lem4896531) (@lem4896530 _60485 _60486)). Qed.
Lemma lem4896533 : term191 = term191.
Proof. exact (eq_refl term191). Qed.
Lemma lem4896534 (_60485 : int) (_60486 : int) : (term267 _60485 _60486) = (term324 _60485 _60486).
Proof. exact (MK_COMB (@lem4896532 _60485 _60486) (@lem4896533)). Qed.
Lemma lem4896535 (_60485 : int) (_60486 : int) : (term216 _60486 _60485) = (term324 _60485 _60486).
Proof. exact (TRANS (@lem4896347 _60485 _60486) (@lem4896534 _60485 _60486)). Qed.
Lemma lem4896536 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4896537 (_60485 : int) (_60486 : int) : (term217 _60485 _60486) = (term325 _60485 _60486).
Proof. exact (MK_COMB (@lem4896536) (@lem4896346 _60485 _60486)). Qed.
Lemma lem4896538 (_60485 : int) (_60486 : int) : (term218 _60486 _60485) = (term326 _60485 _60486).
Proof. exact (MK_COMB (@lem4896537 _60485 _60486) (@lem4896535 _60485 _60486)). Qed.
Lemma lem4896540 {_112846 : Type'} (h : _112846) (t : list _112846) : (term153 _112846 h t) = (term153 _112846 h t).
Proof. exact (eq_refl (term153 _112846 h t)). Qed.
Lemma lem4896541 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) : (term219 _112846 h t _60486 _60485) = (term327 _112846 h t _60485 _60486).
Proof. exact (MK_COMB (@lem4896540 _112846 h t) (@lem4896538 _60485 _60486)). Qed.
Lemma lem4896543 (_60486 : int) (_60485 : int) : (term186 _60485 _60486) = (term259 _60486 _60485).
Proof. exact (@lem1988287 (real_of_int _60486) (real_of_int _60485)). Qed.
Lemma lem4896549 (_60486 : int) (_60485 : int) : (term260 _60486 _60485) = (term261 _60486 _60485).
Proof. exact (@lem1982792 (real_of_int _60486) (real_of_int _60485)). Qed.
Lemma lem4896554 (_60485 : int) (_60486 : int) : (term261 _60486 _60485) = (term262 _60485 _60486).
Proof. exact (@lem1982761 (term263 _60485) (real_of_int _60486)). Qed.
Lemma lem4896556 (_60485 : int) (_60486 : int) : (term260 _60486 _60485) = (term262 _60485 _60486).
Proof. exact (TRANS (@lem4896549 _60486 _60485) (@lem4896554 _60485 _60486)). Qed.
Lemma lem4896557 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4896558 (_60485 : int) (_60486 : int) : (term264 _60486 _60485) = (term265 _60485 _60486).
Proof. exact (MK_COMB (@lem4896557) (@lem4896556 _60485 _60486)). Qed.
Lemma lem4896559 : term191 = term191.
Proof. exact (eq_refl term191). Qed.
Lemma lem4896560 (_60485 : int) (_60486 : int) : (term259 _60486 _60485) = (term266 _60485 _60486).
Proof. exact (MK_COMB (@lem4896558 _60485 _60486) (@lem4896559)). Qed.
Lemma lem4896561 (_60485 : int) (_60486 : int) : (term186 _60485 _60486) = (term266 _60485 _60486).
Proof. exact (TRANS (@lem4896543 _60486 _60485) (@lem4896560 _60485 _60486)). Qed.
Lemma lem4896562 (_60485 : int) (_60486 : int) : (term222 _60486 _60485) = (term328 _60485 _60486).
Proof. exact (@lem1988287 (term210 _60485) (term213 _60486)). Qed.
Lemma lem4896574 (_60486 : int) : (term213 _60486) = (term268 _60486).
Proof. exact (@lem1982755 (real_of_int _60486) term208 term208). Qed.
Lemma lem4896576 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4896577 : term208 = term269.
Proof. exact (@lem4896576 term121). Qed.
Lemma lem4896579 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4896580 : term208 = term269.
Proof. exact (@lem4896579 term121). Qed.
Lemma lem4896581 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4896582 : term270 = term271.
Proof. exact (MK_COMB (@lem4896581) (@lem4896580)). Qed.
Lemma lem4896583 : term272 = term273.
Proof. exact (MK_COMB (@lem4896582) (@lem4896577)). Qed.
Lemma lem4896584 : term274.
Proof. exact (@lem1981473 term208 term208 term208 term208 term275 term208). Qed.
Lemma lem4896586 (m : nat) (n : nat) : (term276 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4896587 : term277 = term278.
Proof. exact (@lem4896586 (NUMERAL 0) term121). Qed.
Lemma lem4896588 : term279 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4896589 (h1 : term279 = (BIT1 0)) : term278 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4896590 : (term279 = (BIT1 0)) = (term278 = True).
Proof. exact (prop_ext (fun h1 : term279 = (BIT1 0) => @lem4896589 h1) (fun h1 : term278 = True => @lem4896588)). Qed.
Lemma lem4896591 : term278 = True.
Proof. exact (EQ_MP (@lem4896590) (@lem4896588)). Qed.
Lemma lem4896592 : term277 = True.
Proof. exact (TRANS (@lem4896587) (@lem4896591)). Qed.
Lemma lem4896593 : True = term277.
Proof. exact (SYM (@lem4896592)). Qed.
Lemma lem4896594 : term277.
Proof. exact (EQ_MP (@lem4896593) (@lem0)). Qed.
Lemma lem4896595 : term280.
Proof. exact (@lem4896584 (@lem4896594)). Qed.
Lemma lem4896597 (m : nat) (n : nat) : (term276 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4896598 : term277 = term278.
Proof. exact (@lem4896597 (NUMERAL 0) term121). Qed.
Lemma lem4896599 : term279 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4896600 (h1 : term279 = (BIT1 0)) : term278 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4896601 : (term279 = (BIT1 0)) = (term278 = True).
Proof. exact (prop_ext (fun h1 : term279 = (BIT1 0) => @lem4896600 h1) (fun h1 : term278 = True => @lem4896599)). Qed.
Lemma lem4896602 : term278 = True.
Proof. exact (EQ_MP (@lem4896601) (@lem4896599)). Qed.
Lemma lem4896603 : term277 = True.
Proof. exact (TRANS (@lem4896598) (@lem4896602)). Qed.
Lemma lem4896604 : True = term277.
Proof. exact (SYM (@lem4896603)). Qed.
Lemma lem4896605 : term277.
Proof. exact (EQ_MP (@lem4896604) (@lem0)). Qed.
Lemma lem4896606 : term281.
Proof. exact (@lem4896595 (@lem4896605)). Qed.
Lemma lem4896608 (m : nat) (n : nat) : (term276 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4896609 : term277 = term278.
Proof. exact (@lem4896608 (NUMERAL 0) term121). Qed.
Lemma lem4896610 : term279 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4896611 (h1 : term279 = (BIT1 0)) : term278 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4896612 : (term279 = (BIT1 0)) = (term278 = True).
Proof. exact (prop_ext (fun h1 : term279 = (BIT1 0) => @lem4896611 h1) (fun h1 : term278 = True => @lem4896610)). Qed.
Lemma lem4896613 : term278 = True.
Proof. exact (EQ_MP (@lem4896612) (@lem4896610)). Qed.
Lemma lem4896614 : term277 = True.
Proof. exact (TRANS (@lem4896609) (@lem4896613)). Qed.
Lemma lem4896615 : True = term277.
Proof. exact (SYM (@lem4896614)). Qed.
Lemma lem4896616 : term277.
Proof. exact (EQ_MP (@lem4896615) (@lem0)). Qed.
Lemma lem4896617 : term282.
Proof. exact (@lem4896606 (@lem4896616)). Qed.
Lemma lem4896619 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4896620 : term247 = term248.
Proof. exact (@lem4896619 term121 term121). Qed.
Lemma lem4896621 : (term249 = (BIT1 0)) = (term250 = term121).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4896622 : term250 = term121.
Proof. exact (EQ_MP (@lem4896621) (@lem940073)). Qed.
Lemma lem4896623 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4896624 : term248 = term208.
Proof. exact (MK_COMB (@lem4896623) (@lem4896622)). Qed.
Lemma lem4896625 : term247 = term208.
Proof. exact (TRANS (@lem4896620) (@lem4896624)). Qed.
Lemma lem4896627 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4896628 : term247 = term248.
Proof. exact (@lem4896627 term121 term121). Qed.
Lemma lem4896629 : (term249 = (BIT1 0)) = (term250 = term121).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4896630 : term250 = term121.
Proof. exact (EQ_MP (@lem4896629) (@lem940073)). Qed.
Lemma lem4896631 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4896632 : term248 = term208.
Proof. exact (MK_COMB (@lem4896631) (@lem4896630)). Qed.
Lemma lem4896633 : term247 = term208.
Proof. exact (TRANS (@lem4896628) (@lem4896632)). Qed.
Lemma lem4896634 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4896635 : term283 = term270.
Proof. exact (MK_COMB (@lem4896634) (@lem4896633)). Qed.
Lemma lem4896636 : term284 = term272.
Proof. exact (MK_COMB (@lem4896635) (@lem4896625)). Qed.
Lemma lem4896637 : term272 = term285.
Proof. exact (@lem1367770 term121 term121). Qed.
Lemma lem4896638 : term286 = term287.
Proof. exact (@lem706885). Qed.
Lemma lem4896639 : (term286 = term287) = (term288 = term289).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term287). Qed.
Lemma lem4896640 : term288 = term289.
Proof. exact (EQ_MP (@lem4896639) (@lem4896638)). Qed.
Lemma lem4896641 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4896642 : term285 = term275.
Proof. exact (MK_COMB (@lem4896641) (@lem4896640)). Qed.
Lemma lem4896643 : term272 = term275.
Proof. exact (TRANS (@lem4896637) (@lem4896642)). Qed.
Lemma lem4896644 : term284 = term275.
Proof. exact (TRANS (@lem4896636) (@lem4896643)). Qed.
Lemma lem4896645 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4896646 : term290 = term291.
Proof. exact (MK_COMB (@lem4896645) (@lem4896644)). Qed.
Lemma lem4896647 : term208 = term208.
Proof. exact (eq_refl term208). Qed.
Lemma lem4896648 : term292 = term293.
Proof. exact (MK_COMB (@lem4896646) (@lem4896647)). Qed.
Lemma lem4896650 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4896651 : term293 = term294.
Proof. exact (@lem4896650 term289 term121). Qed.
Lemma lem4896652 : term295 = term287.
Proof. exact (@lem996237 term287). Qed.
Lemma lem4896653 : (term295 = term287) = (term296 = term289).
Proof. exact (@lem1007663 term287 (BIT1 0) term287). Qed.
Lemma lem4896654 : term296 = term289.
Proof. exact (EQ_MP (@lem4896653) (@lem4896652)). Qed.
Lemma lem4896655 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4896656 : term294 = term275.
Proof. exact (MK_COMB (@lem4896655) (@lem4896654)). Qed.
Lemma lem4896657 : term293 = term275.
Proof. exact (TRANS (@lem4896651) (@lem4896656)). Qed.
Lemma lem4896658 : term292 = term275.
Proof. exact (TRANS (@lem4896648) (@lem4896657)). Qed.
Lemma lem4896660 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4896661 : term247 = term248.
Proof. exact (@lem4896660 term121 term121). Qed.
Lemma lem4896662 : (term249 = (BIT1 0)) = (term250 = term121).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4896663 : term250 = term121.
Proof. exact (EQ_MP (@lem4896662) (@lem940073)). Qed.
Lemma lem4896664 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4896665 : term248 = term208.
Proof. exact (MK_COMB (@lem4896664) (@lem4896663)). Qed.
Lemma lem4896666 : term247 = term208.
Proof. exact (TRANS (@lem4896661) (@lem4896665)). Qed.
Lemma lem4896667 : term291 = term291.
Proof. exact (eq_refl term291). Qed.
Lemma lem4896668 : term297 = term293.
Proof. exact (MK_COMB (@lem4896667) (@lem4896666)). Qed.
Lemma lem4896670 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4896671 : term293 = term294.
Proof. exact (@lem4896670 term289 term121). Qed.
Lemma lem4896672 : term295 = term287.
Proof. exact (@lem996237 term287). Qed.
Lemma lem4896673 : (term295 = term287) = (term296 = term289).
Proof. exact (@lem1007663 term287 (BIT1 0) term287). Qed.
Lemma lem4896674 : term296 = term289.
Proof. exact (EQ_MP (@lem4896673) (@lem4896672)). Qed.
Lemma lem4896675 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4896676 : term294 = term275.
Proof. exact (MK_COMB (@lem4896675) (@lem4896674)). Qed.
Lemma lem4896677 : term293 = term275.
Proof. exact (TRANS (@lem4896671) (@lem4896676)). Qed.
Lemma lem4896678 : term297 = term275.
Proof. exact (TRANS (@lem4896668) (@lem4896677)). Qed.
Lemma lem4896679 : term275 = term297.
Proof. exact (SYM (@lem4896678)). Qed.
Lemma lem4896680 : term292 = term297.
Proof. exact (TRANS (@lem4896658) (@lem4896679)). Qed.
Lemma lem4896681 : term273 = term298.
Proof. exact (@lem4896617 (@lem4896680)). Qed.
Lemma lem4896682 : term272 = term298.
Proof. exact (TRANS (@lem4896583) (@lem4896681)). Qed.
Lemma lem4896684 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4896685 : term298 = term275.
Proof. exact (@lem4896684 term275). Qed.
Lemma lem4896686 : term272 = term275.
Proof. exact (TRANS (@lem4896682) (@lem4896685)). Qed.
Lemma lem4896687 (_60486 : int) : (term209 _60486) = (term209 _60486).
Proof. exact (eq_refl (term209 _60486)). Qed.
Lemma lem4896688 (_60486 : int) : (term268 _60486) = (term299 _60486).
Proof. exact (MK_COMB (@lem4896687 _60486) (@lem4896686)). Qed.
Lemma lem4896690 (_60486 : int) : (term213 _60486) = (term299 _60486).
Proof. exact (TRANS (@lem4896574 _60486) (@lem4896688 _60486)). Qed.
Lemma lem4896699 (_60485 : int) : (term329 _60485) = (term329 _60485).
Proof. exact (eq_refl (term329 _60485)). Qed.
Lemma lem4896700 (_60485 : int) (_60486 : int) : (term330 _60485 _60486) = (term331 _60485 _60486).
Proof. exact (MK_COMB (@lem4896699 _60485) (@lem4896690 _60486)). Qed.
Lemma lem4896701 (_60485 : int) (_60486 : int) : (term331 _60485 _60486) = (term332 _60485 _60486).
Proof. exact (@lem1982792 (term210 _60485) (term299 _60486)). Qed.
Lemma lem4896702 (_60486 : int) : (term304 _60486) = (term305 _60486).
Proof. exact (@lem1982781 (real_of_int _60486) term238 term275). Qed.
Lemma lem4896704 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4896705 : term275 = term298.
Proof. exact (@lem4896704 term289). Qed.
Lemma lem4896707 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4896708 : term238 = term239.
Proof. exact (@lem4896707 term121). Qed.
Lemma lem4896709 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4896710 : term240 = term241.
Proof. exact (MK_COMB (@lem4896709) (@lem4896708)). Qed.
Lemma lem4896711 : term306 = term307.
Proof. exact (MK_COMB (@lem4896710) (@lem4896705)). Qed.
Lemma lem4896712 : term307 = term308.
Proof. exact (@lem1981613 term238 term275 term208 term208). Qed.
Lemma lem4896714 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4896715 : term247 = term248.
Proof. exact (@lem4896714 term121 term121). Qed.
Lemma lem4896716 : (term249 = (BIT1 0)) = (term250 = term121).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4896717 : term250 = term121.
Proof. exact (EQ_MP (@lem4896716) (@lem940073)). Qed.
Lemma lem4896718 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4896719 : term248 = term208.
Proof. exact (MK_COMB (@lem4896718) (@lem4896717)). Qed.
Lemma lem4896720 : term247 = term208.
Proof. exact (TRANS (@lem4896715) (@lem4896719)). Qed.
Lemma lem4896722 (m : nat) (n : nat) : (term309 m n) = (term310 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4896723 : term306 = term311.
Proof. exact (@lem4896722 term121 term289). Qed.
Lemma lem4896724 : term312 = term287.
Proof. exact (@lem996238 term287). Qed.
Lemma lem4896725 : (term312 = term287) = (term313 = term289).
Proof. exact (@lem1007663 (BIT1 0) term287 term287). Qed.
Lemma lem4896726 : term313 = term289.
Proof. exact (EQ_MP (@lem4896725) (@lem4896724)). Qed.
Lemma lem4896727 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4896728 : term314 = term275.
Proof. exact (MK_COMB (@lem4896727) (@lem4896726)). Qed.
Lemma lem4896729 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4896730 : term311 = term315.
Proof. exact (MK_COMB (@lem4896729) (@lem4896728)). Qed.
Lemma lem4896731 : term306 = term315.
Proof. exact (TRANS (@lem4896723) (@lem4896730)). Qed.
Lemma lem4896732 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem4896733 : term316 = term317.
Proof. exact (MK_COMB (@lem4896732) (@lem4896731)). Qed.
Lemma lem4896734 : term308 = term318.
Proof. exact (MK_COMB (@lem4896733) (@lem4896720)). Qed.
Lemma lem4896735 : term307 = term318.
Proof. exact (TRANS (@lem4896712) (@lem4896734)). Qed.
Lemma lem4896736 : term306 = term318.
Proof. exact (TRANS (@lem4896711) (@lem4896735)). Qed.
Lemma lem4896738 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem4896739 : term318 = term315.
Proof. exact (@lem4896738 term315). Qed.
Lemma lem4896740 : term306 = term315.
Proof. exact (TRANS (@lem4896736) (@lem4896739)). Qed.
Lemma lem4896743 (_60486 : int) : (term319 _60486) = (term319 _60486).
Proof. exact (eq_refl (term319 _60486)). Qed.
Lemma lem4896744 (_60486 : int) : (term305 _60486) = (term320 _60486).
Proof. exact (MK_COMB (@lem4896743 _60486) (@lem4896740)). Qed.
Lemma lem4896745 (_60486 : int) : (term304 _60486) = (term320 _60486).
Proof. exact (TRANS (@lem4896702 _60486) (@lem4896744 _60486)). Qed.
Lemma lem4896746 (_60485 : int) : (term212 _60485) = (term212 _60485).
Proof. exact (eq_refl (term212 _60485)). Qed.
Lemma lem4896747 (_60485 : int) (_60486 : int) : (term332 _60485 _60486) = (term333 _60485 _60486).
Proof. exact (MK_COMB (@lem4896746 _60485) (@lem4896745 _60486)). Qed.
Lemma lem4896748 (_60485 : int) (_60486 : int) : (term333 _60485 _60486) = (term334 _60485 _60486).
Proof. exact (@lem1982755 (real_of_int _60485) term208 (term320 _60486)). Qed.
Lemma lem4896749 (_60486 : int) : (term335 _60486) = (term336 _60486).
Proof. exact (@lem1982757 (term263 _60486) term208 term315). Qed.
Lemma lem4896751 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4896752 : term315 = term318.
Proof. exact (@lem4896751 term289). Qed.
Lemma lem4896754 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4896755 : term208 = term269.
Proof. exact (@lem4896754 term121). Qed.
Lemma lem4896756 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4896757 : term270 = term271.
Proof. exact (MK_COMB (@lem4896756) (@lem4896755)). Qed.
Lemma lem4896758 : term337 = term338.
Proof. exact (MK_COMB (@lem4896757) (@lem4896752)). Qed.
Lemma lem4896759 : term339.
Proof. exact (@lem1981473 term208 term208 term315 term208 term238 term208). Qed.
Lemma lem4896761 (m : nat) (n : nat) : (term276 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4896762 : term277 = term278.
Proof. exact (@lem4896761 (NUMERAL 0) term121). Qed.
Lemma lem4896763 : term279 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4896764 (h1 : term279 = (BIT1 0)) : term278 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4896765 : (term279 = (BIT1 0)) = (term278 = True).
Proof. exact (prop_ext (fun h1 : term279 = (BIT1 0) => @lem4896764 h1) (fun h1 : term278 = True => @lem4896763)). Qed.
Lemma lem4896766 : term278 = True.
Proof. exact (EQ_MP (@lem4896765) (@lem4896763)). Qed.
Lemma lem4896767 : term277 = True.
Proof. exact (TRANS (@lem4896762) (@lem4896766)). Qed.
Lemma lem4896768 : True = term277.
Proof. exact (SYM (@lem4896767)). Qed.
Lemma lem4896769 : term277.
Proof. exact (EQ_MP (@lem4896768) (@lem0)). Qed.
Lemma lem4896770 : term340.
Proof. exact (@lem4896759 (@lem4896769)). Qed.
Lemma lem4896772 (m : nat) (n : nat) : (term276 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4896773 : term277 = term278.
Proof. exact (@lem4896772 (NUMERAL 0) term121). Qed.
Lemma lem4896774 : term279 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4896775 (h1 : term279 = (BIT1 0)) : term278 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4896776 : (term279 = (BIT1 0)) = (term278 = True).
Proof. exact (prop_ext (fun h1 : term279 = (BIT1 0) => @lem4896775 h1) (fun h1 : term278 = True => @lem4896774)). Qed.
Lemma lem4896777 : term278 = True.
Proof. exact (EQ_MP (@lem4896776) (@lem4896774)). Qed.
Lemma lem4896778 : term277 = True.
Proof. exact (TRANS (@lem4896773) (@lem4896777)). Qed.
Lemma lem4896779 : True = term277.
Proof. exact (SYM (@lem4896778)). Qed.
Lemma lem4896780 : term277.
Proof. exact (EQ_MP (@lem4896779) (@lem0)). Qed.
Lemma lem4896781 : term341.
Proof. exact (@lem4896770 (@lem4896780)). Qed.
Lemma lem4896783 (m : nat) (n : nat) : (term276 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4896784 : term277 = term278.
Proof. exact (@lem4896783 (NUMERAL 0) term121). Qed.
Lemma lem4896785 : term279 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4896786 (h1 : term279 = (BIT1 0)) : term278 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4896787 : (term279 = (BIT1 0)) = (term278 = True).
Proof. exact (prop_ext (fun h1 : term279 = (BIT1 0) => @lem4896786 h1) (fun h1 : term278 = True => @lem4896785)). Qed.
Lemma lem4896788 : term278 = True.
Proof. exact (EQ_MP (@lem4896787) (@lem4896785)). Qed.
Lemma lem4896789 : term277 = True.
Proof. exact (TRANS (@lem4896784) (@lem4896788)). Qed.
Lemma lem4896790 : True = term277.
Proof. exact (SYM (@lem4896789)). Qed.
Lemma lem4896791 : term277.
Proof. exact (EQ_MP (@lem4896790) (@lem0)). Qed.
Lemma lem4896792 : term342.
Proof. exact (@lem4896781 (@lem4896791)). Qed.
Lemma lem4896794 (m : nat) (n : nat) : (term309 m n) = (term310 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4896795 : term343 = term344.
Proof. exact (@lem4896794 term289 term121). Qed.
Lemma lem4896796 : term295 = term287.
Proof. exact (@lem996237 term287). Qed.
Lemma lem4896797 : (term295 = term287) = (term296 = term289).
Proof. exact (@lem1007663 term287 (BIT1 0) term287). Qed.
Lemma lem4896798 : term296 = term289.
Proof. exact (EQ_MP (@lem4896797) (@lem4896796)). Qed.
Lemma lem4896799 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4896800 : term294 = term275.
Proof. exact (MK_COMB (@lem4896799) (@lem4896798)). Qed.
Lemma lem4896801 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4896802 : term344 = term315.
Proof. exact (MK_COMB (@lem4896801) (@lem4896800)). Qed.
Lemma lem4896803 : term343 = term315.
Proof. exact (TRANS (@lem4896795) (@lem4896802)). Qed.
Lemma lem4896805 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4896806 : term247 = term248.
Proof. exact (@lem4896805 term121 term121). Qed.
Lemma lem4896807 : (term249 = (BIT1 0)) = (term250 = term121).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4896808 : term250 = term121.
Proof. exact (EQ_MP (@lem4896807) (@lem940073)). Qed.
Lemma lem4896809 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4896810 : term248 = term208.
Proof. exact (MK_COMB (@lem4896809) (@lem4896808)). Qed.
Lemma lem4896811 : term247 = term208.
Proof. exact (TRANS (@lem4896806) (@lem4896810)). Qed.
Lemma lem4896812 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4896813 : term283 = term270.
Proof. exact (MK_COMB (@lem4896812) (@lem4896811)). Qed.
Lemma lem4896814 : term345 = term337.
Proof. exact (MK_COMB (@lem4896813) (@lem4896803)). Qed.
Lemma lem4896817 : term346 = term238.
Proof. exact (@lem1367771 term121 term121). Qed.
Lemma lem4896818 : term286 = term287.
Proof. exact (@lem706885). Qed.
Lemma lem4896819 : (term286 = term287) = (term288 = term289).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term287). Qed.
Lemma lem4896820 : term288 = term289.
Proof. exact (EQ_MP (@lem4896819) (@lem4896818)). Qed.
Lemma lem4896821 : term289 = term288.
Proof. exact (SYM (@lem4896820)). Qed.
Lemma lem4896822 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4896823 : term275 = term285.
Proof. exact (MK_COMB (@lem4896822) (@lem4896821)). Qed.
Lemma lem4896824 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4896825 : term315 = term347.
Proof. exact (MK_COMB (@lem4896824) (@lem4896823)). Qed.
Lemma lem4896826 : term270 = term270.
Proof. exact (eq_refl term270). Qed.
Lemma lem4896827 : term337 = term346.
Proof. exact (MK_COMB (@lem4896826) (@lem4896825)). Qed.
Lemma lem4896828 : term337 = term238.
Proof. exact (TRANS (@lem4896827) (@lem4896817)). Qed.
Lemma lem4896829 : term345 = term238.
Proof. exact (TRANS (@lem4896814) (@lem4896828)). Qed.
Lemma lem4896830 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4896831 : term348 = term240.
Proof. exact (MK_COMB (@lem4896830) (@lem4896829)). Qed.
Lemma lem4896832 : term208 = term208.
Proof. exact (eq_refl term208). Qed.
Lemma lem4896833 : term349 = term350.
Proof. exact (MK_COMB (@lem4896831) (@lem4896832)). Qed.
Lemma lem4896835 (m : nat) (n : nat) : (term309 m n) = (term310 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4896836 : term350 = term351.
Proof. exact (@lem4896835 term121 term121). Qed.
Lemma lem4896837 : (term249 = (BIT1 0)) = (term250 = term121).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4896838 : term250 = term121.
Proof. exact (EQ_MP (@lem4896837) (@lem940073)). Qed.
Lemma lem4896839 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4896840 : term248 = term208.
Proof. exact (MK_COMB (@lem4896839) (@lem4896838)). Qed.
Lemma lem4896841 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4896842 : term351 = term238.
Proof. exact (MK_COMB (@lem4896841) (@lem4896840)). Qed.
Lemma lem4896843 : term350 = term238.
Proof. exact (TRANS (@lem4896836) (@lem4896842)). Qed.
Lemma lem4896844 : term349 = term238.
Proof. exact (TRANS (@lem4896833) (@lem4896843)). Qed.
Lemma lem4896846 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4896847 : term247 = term248.
Proof. exact (@lem4896846 term121 term121). Qed.
Lemma lem4896848 : (term249 = (BIT1 0)) = (term250 = term121).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4896849 : term250 = term121.
Proof. exact (EQ_MP (@lem4896848) (@lem940073)). Qed.
Lemma lem4896850 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4896851 : term248 = term208.
Proof. exact (MK_COMB (@lem4896850) (@lem4896849)). Qed.
Lemma lem4896852 : term247 = term208.
Proof. exact (TRANS (@lem4896847) (@lem4896851)). Qed.
Lemma lem4896853 : term240 = term240.
Proof. exact (eq_refl term240). Qed.
Lemma lem4896854 : term352 = term350.
Proof. exact (MK_COMB (@lem4896853) (@lem4896852)). Qed.
Lemma lem4896856 (m : nat) (n : nat) : (term309 m n) = (term310 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4896857 : term350 = term351.
Proof. exact (@lem4896856 term121 term121). Qed.
Lemma lem4896858 : (term249 = (BIT1 0)) = (term250 = term121).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4896859 : term250 = term121.
Proof. exact (EQ_MP (@lem4896858) (@lem940073)). Qed.
Lemma lem4896860 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4896861 : term248 = term208.
Proof. exact (MK_COMB (@lem4896860) (@lem4896859)). Qed.
Lemma lem4896862 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4896863 : term351 = term238.
Proof. exact (MK_COMB (@lem4896862) (@lem4896861)). Qed.
Lemma lem4896864 : term350 = term238.
Proof. exact (TRANS (@lem4896857) (@lem4896863)). Qed.
Lemma lem4896865 : term352 = term238.
Proof. exact (TRANS (@lem4896854) (@lem4896864)). Qed.
Lemma lem4896866 : term238 = term352.
Proof. exact (SYM (@lem4896865)). Qed.
Lemma lem4896867 : term349 = term352.
Proof. exact (TRANS (@lem4896844) (@lem4896866)). Qed.
Lemma lem4896868 : term338 = term239.
Proof. exact (@lem4896792 (@lem4896867)). Qed.
Lemma lem4896869 : term337 = term239.
Proof. exact (TRANS (@lem4896758) (@lem4896868)). Qed.
Lemma lem4896871 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4896872 : term239 = term238.
Proof. exact (@lem4896871 term238). Qed.
Lemma lem4896873 : term337 = term238.
Proof. exact (TRANS (@lem4896869) (@lem4896872)). Qed.
Lemma lem4896874 (_60486 : int) : (term319 _60486) = (term319 _60486).
Proof. exact (eq_refl (term319 _60486)). Qed.
Lemma lem4896875 (_60486 : int) : (term336 _60486) = (term353 _60486).
Proof. exact (MK_COMB (@lem4896874 _60486) (@lem4896873)). Qed.
Lemma lem4896876 (_60486 : int) : (term335 _60486) = (term353 _60486).
Proof. exact (TRANS (@lem4896749 _60486) (@lem4896875 _60486)). Qed.
Lemma lem4896877 (_60485 : int) : (term209 _60485) = (term209 _60485).
Proof. exact (eq_refl (term209 _60485)). Qed.
Lemma lem4896878 (_60485 : int) (_60486 : int) : (term334 _60485 _60486) = (term354 _60485 _60486).
Proof. exact (MK_COMB (@lem4896877 _60485) (@lem4896876 _60486)). Qed.
Lemma lem4896879 (_60485 : int) (_60486 : int) : (term333 _60485 _60486) = (term354 _60485 _60486).
Proof. exact (TRANS (@lem4896748 _60485 _60486) (@lem4896878 _60485 _60486)). Qed.
Lemma lem4896880 (_60485 : int) (_60486 : int) : (term332 _60485 _60486) = (term354 _60485 _60486).
Proof. exact (TRANS (@lem4896747 _60485 _60486) (@lem4896879 _60485 _60486)). Qed.
Lemma lem4896881 (_60485 : int) (_60486 : int) : (term331 _60485 _60486) = (term354 _60485 _60486).
Proof. exact (TRANS (@lem4896701 _60485 _60486) (@lem4896880 _60485 _60486)). Qed.
Lemma lem4896882 (_60485 : int) (_60486 : int) : (term330 _60485 _60486) = (term354 _60485 _60486).
Proof. exact (TRANS (@lem4896700 _60485 _60486) (@lem4896881 _60485 _60486)). Qed.
Lemma lem4896883 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4896884 (_60485 : int) (_60486 : int) : (term355 _60485 _60486) = (term356 _60485 _60486).
Proof. exact (MK_COMB (@lem4896883) (@lem4896882 _60485 _60486)). Qed.
Lemma lem4896885 : term191 = term191.
Proof. exact (eq_refl term191). Qed.
Lemma lem4896886 (_60485 : int) (_60486 : int) : (term328 _60485 _60486) = (term357 _60485 _60486).
Proof. exact (MK_COMB (@lem4896884 _60485 _60486) (@lem4896885)). Qed.
Lemma lem4896887 (_60485 : int) (_60486 : int) : (term222 _60486 _60485) = (term357 _60485 _60486).
Proof. exact (TRANS (@lem4896562 _60485 _60486) (@lem4896886 _60485 _60486)). Qed.
Lemma lem4896888 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4896889 (_60485 : int) (_60486 : int) : (term217 _60485 _60486) = (term325 _60485 _60486).
Proof. exact (MK_COMB (@lem4896888) (@lem4896561 _60485 _60486)). Qed.
Lemma lem4896890 (_60485 : int) (_60486 : int) : (term223 _60486 _60485) = (term358 _60485 _60486).
Proof. exact (MK_COMB (@lem4896889 _60485 _60486) (@lem4896887 _60485 _60486)). Qed.
Lemma lem4896892 {_112846 : Type'} (h : _112846) (t : list _112846) : (term164 _112846 h t) = (term164 _112846 h t).
Proof. exact (eq_refl (term164 _112846 h t)). Qed.
Lemma lem4896893 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) : (term224 _112846 h t _60486 _60485) = (term359 _112846 h t _60485 _60486).
Proof. exact (MK_COMB (@lem4896892 _112846 h t) (@lem4896890 _60485 _60486)). Qed.
Lemma lem4896894 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4896895 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) : (term225 _112846 h t _60486 _60485) = (term360 _112846 h t _60485 _60486).
Proof. exact (MK_COMB (@lem4896894) (@lem4896541 _112846 h t _60485 _60486)). Qed.
Lemma lem4896896 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) : (term226 _112846 h t _60486 _60485) = (term361 _112846 h t _60485 _60486).
Proof. exact (MK_COMB (@lem4896895 _112846 h t _60485 _60486) (@lem4896893 _112846 h t _60485 _60486)). Qed.
Lemma lem4896897 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4896898 (_60486 : int) : (term227 _60486) = (term362 _60486).
Proof. exact (MK_COMB (@lem4896897) (@lem4896326 _60486)). Qed.
Lemma lem4896899 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) : (term228 _112846 h t _60486 _60485) = (term363 _112846 h t _60485 _60486).
Proof. exact (MK_COMB (@lem4896898 _60486) (@lem4896896 _112846 h t _60485 _60486)). Qed.
Lemma lem4896900 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4896901 (_60485 : int) : (term227 _60485) = (term362 _60485).
Proof. exact (MK_COMB (@lem4896900) (@lem4896278 _60485)). Qed.
Lemma lem4896902 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) : (term229 _112846 h t _60486 _60485) = (term364 _112846 h t _60485 _60486).
Proof. exact (MK_COMB (@lem4896901 _60485) (@lem4896899 _112846 h t _60485 _60486)). Qed.
Lemma lem4896909 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) : (term230 _112846 h t _60486 _60485) = (term364 _112846 h t _60485 _60486).
Proof. exact (TRANS (@lem4896230 _112846 h t _60486 _60485) (@lem4896902 _112846 h t _60485 _60486)). Qed.
Lemma lem4896950 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) : (term363 _112846 h t _60485 _60486) = (term365 _112846 h t _60485 _60486).
Proof. exact (@lem19158 (term327 _112846 h t _60485 _60486) (term258 _60486) (term359 _112846 h t _60485 _60486)). Qed.
Lemma lem4896953 (_60485 : int) : (term362 _60485) = (term362 _60485).
Proof. exact (eq_refl (term362 _60485)). Qed.
Lemma lem4896954 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) : (term364 _112846 h t _60485 _60486) = (term366 _112846 h t _60485 _60486).
Proof. exact (MK_COMB (@lem4896953 _60485) (@lem4896950 _112846 h t _60485 _60486)). Qed.
Lemma lem4896961 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) : (term366 _112846 h t _60485 _60486) = (term367 _112846 h t _60485 _60486).
Proof. exact (@lem19158 (term368 _112846 h t _60485 _60486) (term258 _60485) (term369 _112846 h t _60485 _60486)). Qed.
Lemma lem4896962 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) : (term364 _112846 h t _60485 _60486) = (term367 _112846 h t _60485 _60486).
Proof. exact (TRANS (@lem4896954 _112846 h t _60485 _60486) (@lem4896961 _112846 h t _60485 _60486)). Qed.
Lemma lem4896963 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) : (term230 _112846 h t _60486 _60485) = (term367 _112846 h t _60485 _60486).
Proof. exact (TRANS (@lem4896909 _112846 h t _60485 _60486) (@lem4896962 _112846 h t _60485 _60486)). Qed.
Lemma lem4896973 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) (h1 : term367 _112846 h t _60485 _60486) : term367 _112846 h t _60485 _60486.
Proof. exact (h1). Qed.
Lemma lem4896974 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) (h1 : term370 _112846 h t _60485 _60486) : term370 _112846 h t _60485 _60486.
Proof. exact (h1). Qed.
Lemma lem4896975 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) (h1 : term370 _112846 h t _60485 _60486) : term368 _112846 h t _60485 _60486.
Proof. exact (proj2 (@lem4896974 _112846 h t _60485 _60486 h1)). Qed.
Lemma lem4896977 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) (h1 : term370 _112846 h t _60485 _60486) : term327 _112846 h t _60485 _60486.
Proof. exact (proj2 (@lem4896975 _112846 h t _60485 _60486 h1)). Qed.
Lemma lem4896979 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) (h1 : term370 _112846 h t _60485 _60486) : term326 _60485 _60486.
Proof. exact (proj2 (@lem4896977 _112846 h t _60485 _60486 h1)). Qed.
Lemma lem4896981 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) (h1 : term370 _112846 h t _60485 _60486) : term324 _60485 _60486.
Proof. exact (proj2 (@lem4896979 _112846 h t _60485 _60486 h1)). Qed.
Lemma lem4896982 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) (h1 : term370 _112846 h t _60485 _60486) : term266 _60485 _60486.
Proof. exact (proj1 (@lem4896979 _112846 h t _60485 _60486 h1)). Qed.
Lemma lem4896984 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem4896985 : term371 = term277.
Proof. exact (@lem4896984 term191 term208). Qed.
Lemma lem4896987 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4896988 : term208 = term269.
Proof. exact (@lem4896987 term121). Qed.
Lemma lem4896990 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4896991 : term191 = term235.
Proof. exact (@lem4896990 (NUMERAL 0)). Qed.
Lemma lem4896992 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4896993 : term372 = term373.
Proof. exact (MK_COMB (@lem4896992) (@lem4896991)). Qed.
Lemma lem4896994 : term277 = term374.
Proof. exact (MK_COMB (@lem4896993) (@lem4896988)). Qed.
Lemma lem4896995 : term375.
Proof. exact (@lem1980255 term191 term208 term208 term208). Qed.
Lemma lem4896997 (m : nat) (n : nat) : (term276 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4896998 : term277 = term278.
Proof. exact (@lem4896997 (NUMERAL 0) term121). Qed.
Lemma lem4896999 : term279 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4897000 (h1 : term279 = (BIT1 0)) : term278 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4897001 : (term279 = (BIT1 0)) = (term278 = True).
Proof. exact (prop_ext (fun h1 : term279 = (BIT1 0) => @lem4897000 h1) (fun h1 : term278 = True => @lem4896999)). Qed.
Lemma lem4897002 : term278 = True.
Proof. exact (EQ_MP (@lem4897001) (@lem4896999)). Qed.
Lemma lem4897003 : term277 = True.
Proof. exact (TRANS (@lem4896998) (@lem4897002)). Qed.
Lemma lem4897004 : True = term277.
Proof. exact (SYM (@lem4897003)). Qed.
Lemma lem4897005 : term277.
Proof. exact (EQ_MP (@lem4897004) (@lem0)). Qed.
Lemma lem4897006 : term376.
Proof. exact (@lem4896995 (@lem4897005)). Qed.
Lemma lem4897008 (m : nat) (n : nat) : (term276 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4897009 : term277 = term278.
Proof. exact (@lem4897008 (NUMERAL 0) term121). Qed.
Lemma lem4897010 : term279 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4897011 (h1 : term279 = (BIT1 0)) : term278 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4897012 : (term279 = (BIT1 0)) = (term278 = True).
Proof. exact (prop_ext (fun h1 : term279 = (BIT1 0) => @lem4897011 h1) (fun h1 : term278 = True => @lem4897010)). Qed.
Lemma lem4897013 : term278 = True.
Proof. exact (EQ_MP (@lem4897012) (@lem4897010)). Qed.
Lemma lem4897014 : term277 = True.
Proof. exact (TRANS (@lem4897009) (@lem4897013)). Qed.
Lemma lem4897015 : True = term277.
Proof. exact (SYM (@lem4897014)). Qed.
Lemma lem4897016 : term277.
Proof. exact (EQ_MP (@lem4897015) (@lem0)). Qed.
Lemma lem4897017 : term374 = term377.
Proof. exact (@lem4897006 (@lem4897016)). Qed.
Lemma lem4897019 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4897020 : term247 = term248.
Proof. exact (@lem4897019 term121 term121). Qed.
Lemma lem4897021 : (term249 = (BIT1 0)) = (term250 = term121).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4897022 : term250 = term121.
Proof. exact (EQ_MP (@lem4897021) (@lem940073)). Qed.
Lemma lem4897023 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4897024 : term248 = term208.
Proof. exact (MK_COMB (@lem4897023) (@lem4897022)). Qed.
Lemma lem4897025 : term247 = term208.
Proof. exact (TRANS (@lem4897020) (@lem4897024)). Qed.
Lemma lem4897027 (x : nat) : (term378 x) = term191.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4897028 : term379 = term191.
Proof. exact (@lem4897027 term121). Qed.
Lemma lem4897029 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4897030 : term380 = term372.
Proof. exact (MK_COMB (@lem4897029) (@lem4897028)). Qed.
Lemma lem4897031 : term377 = term277.
Proof. exact (MK_COMB (@lem4897030) (@lem4897025)). Qed.
Lemma lem4897033 (m : nat) (n : nat) : (term276 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4897034 : term277 = term278.
Proof. exact (@lem4897033 (NUMERAL 0) term121). Qed.
Lemma lem4897035 : term279 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4897036 (h1 : term279 = (BIT1 0)) : term278 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4897037 : (term279 = (BIT1 0)) = (term278 = True).
Proof. exact (prop_ext (fun h1 : term279 = (BIT1 0) => @lem4897036 h1) (fun h1 : term278 = True => @lem4897035)). Qed.
Lemma lem4897038 : term278 = True.
Proof. exact (EQ_MP (@lem4897037) (@lem4897035)). Qed.
Lemma lem4897039 : term277 = True.
Proof. exact (TRANS (@lem4897034) (@lem4897038)). Qed.
Lemma lem4897040 : term377 = True.
Proof. exact (TRANS (@lem4897031) (@lem4897039)). Qed.
Lemma lem4897041 : term374 = True.
Proof. exact (TRANS (@lem4897017) (@lem4897040)). Qed.
Lemma lem4897042 : term277 = True.
Proof. exact (TRANS (@lem4896994) (@lem4897041)). Qed.
Lemma lem4897043 : term371 = True.
Proof. exact (TRANS (@lem4896985) (@lem4897042)). Qed.
Lemma lem4897044 : True = term371.
Proof. exact (SYM (@lem4897043)). Qed.
Lemma lem4897045 : term371.
Proof. exact (EQ_MP (@lem4897044) (@lem0)). Qed.
Lemma lem4897046 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) (h1 : term370 _112846 h t _60485 _60486) : term381 _60485 _60486.
Proof. exact (conj (@lem4897045) (@lem4896981 _112846 h t _60485 _60486 h1)). Qed.
Lemma lem4897048 (x : real) (y : real) : term382 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem4897049 (_60485 : int) (_60486 : int) : term383 _60485 _60486.
Proof. exact (@lem4897048 term208 (term321 _60485 _60486)). Qed.
Lemma lem4897050 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) (h1 : term370 _112846 h t _60485 _60486) : term384 _60485 _60486.
Proof. exact (@lem4897049 _60485 _60486 (@lem4897046 _112846 h t _60485 _60486 h1)). Qed.
Lemma lem4897051 (_60485 : int) (_60486 : int) : (term385 _60485 _60486) = (term321 _60485 _60486).
Proof. exact (@lem1982733 (term321 _60485 _60486)). Qed.
Lemma lem4897052 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4897053 (_60485 : int) (_60486 : int) : (term386 _60485 _60486) = (term323 _60485 _60486).
Proof. exact (MK_COMB (@lem4897052) (@lem4897051 _60485 _60486)). Qed.
Lemma lem4897054 : term191 = term191.
Proof. exact (eq_refl term191). Qed.
Lemma lem4897055 (_60485 : int) (_60486 : int) : (term384 _60485 _60486) = (term324 _60485 _60486).
Proof. exact (MK_COMB (@lem4897053 _60485 _60486) (@lem4897054)). Qed.
Lemma lem4897056 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) (h1 : term370 _112846 h t _60485 _60486) : term324 _60485 _60486.
Proof. exact (EQ_MP (@lem4897055 _60485 _60486) (@lem4897050 _112846 h t _60485 _60486 h1)). Qed.
Lemma lem4897058 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem4897059 : term371 = term277.
Proof. exact (@lem4897058 term191 term208). Qed.
Lemma lem4897061 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4897062 : term208 = term269.
Proof. exact (@lem4897061 term121). Qed.
Lemma lem4897064 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4897065 : term191 = term235.
Proof. exact (@lem4897064 (NUMERAL 0)). Qed.
Lemma lem4897066 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4897067 : term372 = term373.
Proof. exact (MK_COMB (@lem4897066) (@lem4897065)). Qed.
Lemma lem4897068 : term277 = term374.
Proof. exact (MK_COMB (@lem4897067) (@lem4897062)). Qed.
Lemma lem4897069 : term375.
Proof. exact (@lem1980255 term191 term208 term208 term208). Qed.
Lemma lem4897071 (m : nat) (n : nat) : (term276 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4897072 : term277 = term278.
Proof. exact (@lem4897071 (NUMERAL 0) term121). Qed.
Lemma lem4897073 : term279 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4897074 (h1 : term279 = (BIT1 0)) : term278 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4897075 : (term279 = (BIT1 0)) = (term278 = True).
Proof. exact (prop_ext (fun h1 : term279 = (BIT1 0) => @lem4897074 h1) (fun h1 : term278 = True => @lem4897073)). Qed.
Lemma lem4897076 : term278 = True.
Proof. exact (EQ_MP (@lem4897075) (@lem4897073)). Qed.
Lemma lem4897077 : term277 = True.
Proof. exact (TRANS (@lem4897072) (@lem4897076)). Qed.
Lemma lem4897078 : True = term277.
Proof. exact (SYM (@lem4897077)). Qed.
Lemma lem4897079 : term277.
Proof. exact (EQ_MP (@lem4897078) (@lem0)). Qed.
Lemma lem4897080 : term376.
Proof. exact (@lem4897069 (@lem4897079)). Qed.
Lemma lem4897082 (m : nat) (n : nat) : (term276 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4897083 : term277 = term278.
Proof. exact (@lem4897082 (NUMERAL 0) term121). Qed.
Lemma lem4897084 : term279 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4897085 (h1 : term279 = (BIT1 0)) : term278 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4897086 : (term279 = (BIT1 0)) = (term278 = True).
Proof. exact (prop_ext (fun h1 : term279 = (BIT1 0) => @lem4897085 h1) (fun h1 : term278 = True => @lem4897084)). Qed.
Lemma lem4897087 : term278 = True.
Proof. exact (EQ_MP (@lem4897086) (@lem4897084)). Qed.
Lemma lem4897088 : term277 = True.
Proof. exact (TRANS (@lem4897083) (@lem4897087)). Qed.
Lemma lem4897089 : True = term277.
Proof. exact (SYM (@lem4897088)). Qed.
Lemma lem4897090 : term277.
Proof. exact (EQ_MP (@lem4897089) (@lem0)). Qed.
Lemma lem4897091 : term374 = term377.
Proof. exact (@lem4897080 (@lem4897090)). Qed.
Lemma lem4897093 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4897094 : term247 = term248.
Proof. exact (@lem4897093 term121 term121). Qed.
Lemma lem4897095 : (term249 = (BIT1 0)) = (term250 = term121).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4897096 : term250 = term121.
Proof. exact (EQ_MP (@lem4897095) (@lem940073)). Qed.
Lemma lem4897097 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4897098 : term248 = term208.
Proof. exact (MK_COMB (@lem4897097) (@lem4897096)). Qed.
Lemma lem4897099 : term247 = term208.
Proof. exact (TRANS (@lem4897094) (@lem4897098)). Qed.
Lemma lem4897101 (x : nat) : (term378 x) = term191.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4897102 : term379 = term191.
Proof. exact (@lem4897101 term121). Qed.
Lemma lem4897103 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4897104 : term380 = term372.
Proof. exact (MK_COMB (@lem4897103) (@lem4897102)). Qed.
Lemma lem4897105 : term377 = term277.
Proof. exact (MK_COMB (@lem4897104) (@lem4897099)). Qed.
Lemma lem4897107 (m : nat) (n : nat) : (term276 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4897108 : term277 = term278.
Proof. exact (@lem4897107 (NUMERAL 0) term121). Qed.
Lemma lem4897109 : term279 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4897110 (h1 : term279 = (BIT1 0)) : term278 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4897111 : (term279 = (BIT1 0)) = (term278 = True).
Proof. exact (prop_ext (fun h1 : term279 = (BIT1 0) => @lem4897110 h1) (fun h1 : term278 = True => @lem4897109)). Qed.
Lemma lem4897112 : term278 = True.
Proof. exact (EQ_MP (@lem4897111) (@lem4897109)). Qed.
Lemma lem4897113 : term277 = True.
Proof. exact (TRANS (@lem4897108) (@lem4897112)). Qed.
Lemma lem4897114 : term377 = True.
Proof. exact (TRANS (@lem4897105) (@lem4897113)). Qed.
Lemma lem4897115 : term374 = True.
Proof. exact (TRANS (@lem4897091) (@lem4897114)). Qed.
Lemma lem4897116 : term277 = True.
Proof. exact (TRANS (@lem4897068) (@lem4897115)). Qed.
Lemma lem4897117 : term371 = True.
Proof. exact (TRANS (@lem4897059) (@lem4897116)). Qed.
Lemma lem4897118 : True = term371.
Proof. exact (SYM (@lem4897117)). Qed.
Lemma lem4897119 : term371.
Proof. exact (EQ_MP (@lem4897118) (@lem0)). Qed.
Lemma lem4897120 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) (h1 : term370 _112846 h t _60485 _60486) : term387 _60485 _60486.
Proof. exact (conj (@lem4897119) (@lem4896982 _112846 h t _60485 _60486 h1)). Qed.
Lemma lem4897122 (x : real) (y : real) : term382 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem4897123 (_60485 : int) (_60486 : int) : term388 _60485 _60486.
Proof. exact (@lem4897122 term208 (term262 _60485 _60486)). Qed.
Lemma lem4897124 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) (h1 : term370 _112846 h t _60485 _60486) : term389 _60485 _60486.
Proof. exact (@lem4897123 _60485 _60486 (@lem4897120 _112846 h t _60485 _60486 h1)). Qed.
Lemma lem4897125 (_60485 : int) (_60486 : int) : (term390 _60485 _60486) = (term262 _60485 _60486).
Proof. exact (@lem1982733 (term262 _60485 _60486)). Qed.
Lemma lem4897126 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4897127 (_60485 : int) (_60486 : int) : (term391 _60485 _60486) = (term265 _60485 _60486).
Proof. exact (MK_COMB (@lem4897126) (@lem4897125 _60485 _60486)). Qed.
Lemma lem4897128 : term191 = term191.
Proof. exact (eq_refl term191). Qed.
Lemma lem4897129 (_60485 : int) (_60486 : int) : (term389 _60485 _60486) = (term266 _60485 _60486).
Proof. exact (MK_COMB (@lem4897127 _60485 _60486) (@lem4897128)). Qed.
Lemma lem4897130 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) (h1 : term370 _112846 h t _60485 _60486) : term266 _60485 _60486.
Proof. exact (EQ_MP (@lem4897129 _60485 _60486) (@lem4897124 _112846 h t _60485 _60486 h1)). Qed.
Lemma lem4897131 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) (h1 : term370 _112846 h t _60485 _60486) : term326 _60485 _60486.
Proof. exact (conj (@lem4897130 _112846 h t _60485 _60486 h1) (@lem4897056 _112846 h t _60485 _60486 h1)). Qed.
Lemma lem4897133 (x : real) (y : real) : term392 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem4897134 (_60485 : int) (_60486 : int) : term393 _60485 _60486.
Proof. exact (@lem4897133 (term262 _60485 _60486) (term321 _60485 _60486)). Qed.
Lemma lem4897135 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) (h1 : term370 _112846 h t _60485 _60486) : term394 _60485 _60486.
Proof. exact (@lem4897134 _60485 _60486 (@lem4897131 _112846 h t _60485 _60486 h1)). Qed.
Lemma lem4897136 (_60485 : int) (_60486 : int) : (term395 _60485 _60486) = (term396 _60485 _60486).
Proof. exact (@lem1982753 (term263 _60485) (real_of_int _60485) (real_of_int _60486) (term320 _60486)). Qed.
Lemma lem4897137 (_60485 : int) : (term397 _60485) = (term398 _60485).
Proof. exact (@lem1982713 term238 (real_of_int _60485)). Qed.
Lemma lem4897139 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4897140 : term208 = term269.
Proof. exact (@lem4897139 term121). Qed.
Lemma lem4897142 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4897143 : term238 = term239.
Proof. exact (@lem4897142 term121). Qed.
Lemma lem4897144 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4897145 : term399 = term400.
Proof. exact (MK_COMB (@lem4897144) (@lem4897143)). Qed.
Lemma lem4897146 : term401 = term402.
Proof. exact (MK_COMB (@lem4897145) (@lem4897140)). Qed.
Lemma lem4897147 : term403.
Proof. exact (@lem1981473 term238 term208 term208 term208 term191 term208). Qed.
Lemma lem4897149 (m : nat) (n : nat) : (term276 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4897150 : term277 = term278.
Proof. exact (@lem4897149 (NUMERAL 0) term121). Qed.
Lemma lem4897151 : term279 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4897152 (h1 : term279 = (BIT1 0)) : term278 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4897153 : (term279 = (BIT1 0)) = (term278 = True).
Proof. exact (prop_ext (fun h1 : term279 = (BIT1 0) => @lem4897152 h1) (fun h1 : term278 = True => @lem4897151)). Qed.
Lemma lem4897154 : term278 = True.
Proof. exact (EQ_MP (@lem4897153) (@lem4897151)). Qed.
Lemma lem4897155 : term277 = True.
Proof. exact (TRANS (@lem4897150) (@lem4897154)). Qed.
Lemma lem4897156 : True = term277.
Proof. exact (SYM (@lem4897155)). Qed.
Lemma lem4897157 : term277.
Proof. exact (EQ_MP (@lem4897156) (@lem0)). Qed.
Lemma lem4897158 : term404.
Proof. exact (@lem4897147 (@lem4897157)). Qed.
Lemma lem4897160 (m : nat) (n : nat) : (term276 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4897161 : term277 = term278.
Proof. exact (@lem4897160 (NUMERAL 0) term121). Qed.
Lemma lem4897162 : term279 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4897163 (h1 : term279 = (BIT1 0)) : term278 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4897164 : (term279 = (BIT1 0)) = (term278 = True).
Proof. exact (prop_ext (fun h1 : term279 = (BIT1 0) => @lem4897163 h1) (fun h1 : term278 = True => @lem4897162)). Qed.
Lemma lem4897165 : term278 = True.
Proof. exact (EQ_MP (@lem4897164) (@lem4897162)). Qed.
Lemma lem4897166 : term277 = True.
Proof. exact (TRANS (@lem4897161) (@lem4897165)). Qed.
Lemma lem4897167 : True = term277.
Proof. exact (SYM (@lem4897166)). Qed.
Lemma lem4897168 : term277.
Proof. exact (EQ_MP (@lem4897167) (@lem0)). Qed.
Lemma lem4897169 : term405.
Proof. exact (@lem4897158 (@lem4897168)). Qed.
Lemma lem4897171 (m : nat) (n : nat) : (term276 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4897172 : term277 = term278.
Proof. exact (@lem4897171 (NUMERAL 0) term121). Qed.
Lemma lem4897173 : term279 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4897174 (h1 : term279 = (BIT1 0)) : term278 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4897175 : (term279 = (BIT1 0)) = (term278 = True).
Proof. exact (prop_ext (fun h1 : term279 = (BIT1 0) => @lem4897174 h1) (fun h1 : term278 = True => @lem4897173)). Qed.
Lemma lem4897176 : term278 = True.
Proof. exact (EQ_MP (@lem4897175) (@lem4897173)). Qed.
Lemma lem4897177 : term277 = True.
Proof. exact (TRANS (@lem4897172) (@lem4897176)). Qed.
Lemma lem4897178 : True = term277.
Proof. exact (SYM (@lem4897177)). Qed.
Lemma lem4897179 : term277.
Proof. exact (EQ_MP (@lem4897178) (@lem0)). Qed.
Lemma lem4897180 : term406.
Proof. exact (@lem4897169 (@lem4897179)). Qed.
Lemma lem4897182 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4897183 : term247 = term248.
Proof. exact (@lem4897182 term121 term121). Qed.
Lemma lem4897184 : (term249 = (BIT1 0)) = (term250 = term121).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4897185 : term250 = term121.
Proof. exact (EQ_MP (@lem4897184) (@lem940073)). Qed.
Lemma lem4897186 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4897187 : term248 = term208.
Proof. exact (MK_COMB (@lem4897186) (@lem4897185)). Qed.
Lemma lem4897188 : term247 = term208.
Proof. exact (TRANS (@lem4897183) (@lem4897187)). Qed.
Lemma lem4897190 (m : nat) (n : nat) : (term309 m n) = (term310 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4897191 : term350 = term351.
Proof. exact (@lem4897190 term121 term121). Qed.
Lemma lem4897192 : (term249 = (BIT1 0)) = (term250 = term121).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4897193 : term250 = term121.
Proof. exact (EQ_MP (@lem4897192) (@lem940073)). Qed.
Lemma lem4897194 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4897195 : term248 = term208.
Proof. exact (MK_COMB (@lem4897194) (@lem4897193)). Qed.
Lemma lem4897196 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4897197 : term351 = term238.
Proof. exact (MK_COMB (@lem4897196) (@lem4897195)). Qed.
Lemma lem4897198 : term350 = term238.
Proof. exact (TRANS (@lem4897191) (@lem4897197)). Qed.
Lemma lem4897199 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4897200 : term407 = term399.
Proof. exact (MK_COMB (@lem4897199) (@lem4897198)). Qed.
Lemma lem4897201 : term408 = term401.
Proof. exact (MK_COMB (@lem4897200) (@lem4897188)). Qed.
Lemma lem4897203 (m : nat) : (term409 m) = term191.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem4897204 : term401 = term191.
Proof. exact (@lem4897203 term121). Qed.
Lemma lem4897205 : term408 = term191.
Proof. exact (TRANS (@lem4897201) (@lem4897204)). Qed.
Lemma lem4897206 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4897207 : term410 = term411.
Proof. exact (MK_COMB (@lem4897206) (@lem4897205)). Qed.
Lemma lem4897208 : term208 = term208.
Proof. exact (eq_refl term208). Qed.
Lemma lem4897209 : term412 = term379.
Proof. exact (MK_COMB (@lem4897207) (@lem4897208)). Qed.
Lemma lem4897211 (x : nat) : (term378 x) = term191.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4897212 : term379 = term191.
Proof. exact (@lem4897211 term121). Qed.
Lemma lem4897213 : term412 = term191.
Proof. exact (TRANS (@lem4897209) (@lem4897212)). Qed.
Lemma lem4897215 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4897216 : term247 = term248.
Proof. exact (@lem4897215 term121 term121). Qed.
Lemma lem4897217 : (term249 = (BIT1 0)) = (term250 = term121).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4897218 : term250 = term121.
Proof. exact (EQ_MP (@lem4897217) (@lem940073)). Qed.
Lemma lem4897219 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4897220 : term248 = term208.
Proof. exact (MK_COMB (@lem4897219) (@lem4897218)). Qed.
Lemma lem4897221 : term247 = term208.
Proof. exact (TRANS (@lem4897216) (@lem4897220)). Qed.
Lemma lem4897222 : term411 = term411.
Proof. exact (eq_refl term411). Qed.
Lemma lem4897223 : term413 = term379.
Proof. exact (MK_COMB (@lem4897222) (@lem4897221)). Qed.
Lemma lem4897225 (x : nat) : (term378 x) = term191.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4897226 : term379 = term191.
Proof. exact (@lem4897225 term121). Qed.
Lemma lem4897227 : term413 = term191.
Proof. exact (TRANS (@lem4897223) (@lem4897226)). Qed.
Lemma lem4897228 : term191 = term413.
Proof. exact (SYM (@lem4897227)). Qed.
Lemma lem4897229 : term412 = term413.
Proof. exact (TRANS (@lem4897213) (@lem4897228)). Qed.
Lemma lem4897230 : term402 = term235.
Proof. exact (@lem4897180 (@lem4897229)). Qed.
Lemma lem4897231 : term401 = term235.
Proof. exact (TRANS (@lem4897146) (@lem4897230)). Qed.
Lemma lem4897233 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4897234 : term235 = term191.
Proof. exact (@lem4897233 term191). Qed.
Lemma lem4897235 : term401 = term191.
Proof. exact (TRANS (@lem4897231) (@lem4897234)). Qed.
Lemma lem4897236 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4897237 : term414 = term411.
Proof. exact (MK_COMB (@lem4897236) (@lem4897235)). Qed.
Lemma lem4897238 (_60485 : int) : (real_of_int _60485) = (real_of_int _60485).
Proof. exact (eq_refl (real_of_int _60485)). Qed.
Lemma lem4897239 (_60485 : int) : (term398 _60485) = (term415 _60485).
Proof. exact (MK_COMB (@lem4897237) (@lem4897238 _60485)). Qed.
Lemma lem4897240 (_60485 : int) : (term397 _60485) = (term415 _60485).
Proof. exact (TRANS (@lem4897137 _60485) (@lem4897239 _60485)). Qed.
Lemma lem4897241 (_60485 : int) : (term415 _60485) = term191.
Proof. exact (@lem1982719 (real_of_int _60485)). Qed.
Lemma lem4897242 (_60485 : int) : (term397 _60485) = term191.
Proof. exact (TRANS (@lem4897240 _60485) (@lem4897241 _60485)). Qed.
Lemma lem4897243 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4897244 (_60485 : int) : (term416 _60485) = term417.
Proof. exact (MK_COMB (@lem4897243) (@lem4897242 _60485)). Qed.
Lemma lem4897245 (_60486 : int) : (term418 _60486) = (term419 _60486).
Proof. exact (@lem1982763 (real_of_int _60486) (term263 _60486) term315). Qed.
Lemma lem4897246 (_60486 : int) : (term420 _60486) = (term398 _60486).
Proof. exact (@lem1982715 term238 (real_of_int _60486)). Qed.
Lemma lem4897248 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4897249 : term208 = term269.
Proof. exact (@lem4897248 term121). Qed.
Lemma lem4897251 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4897252 : term238 = term239.
Proof. exact (@lem4897251 term121). Qed.
Lemma lem4897253 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4897254 : term399 = term400.
Proof. exact (MK_COMB (@lem4897253) (@lem4897252)). Qed.
Lemma lem4897255 : term401 = term402.
Proof. exact (MK_COMB (@lem4897254) (@lem4897249)). Qed.
Lemma lem4897256 : term403.
Proof. exact (@lem1981473 term238 term208 term208 term208 term191 term208). Qed.
Lemma lem4897258 (m : nat) (n : nat) : (term276 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4897259 : term277 = term278.
Proof. exact (@lem4897258 (NUMERAL 0) term121). Qed.
Lemma lem4897260 : term279 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4897261 (h1 : term279 = (BIT1 0)) : term278 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4897262 : (term279 = (BIT1 0)) = (term278 = True).
Proof. exact (prop_ext (fun h1 : term279 = (BIT1 0) => @lem4897261 h1) (fun h1 : term278 = True => @lem4897260)). Qed.
Lemma lem4897263 : term278 = True.
Proof. exact (EQ_MP (@lem4897262) (@lem4897260)). Qed.
Lemma lem4897264 : term277 = True.
Proof. exact (TRANS (@lem4897259) (@lem4897263)). Qed.
Lemma lem4897265 : True = term277.
Proof. exact (SYM (@lem4897264)). Qed.
Lemma lem4897266 : term277.
Proof. exact (EQ_MP (@lem4897265) (@lem0)). Qed.
Lemma lem4897267 : term404.
Proof. exact (@lem4897256 (@lem4897266)). Qed.
Lemma lem4897269 (m : nat) (n : nat) : (term276 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4897270 : term277 = term278.
Proof. exact (@lem4897269 (NUMERAL 0) term121). Qed.
Lemma lem4897271 : term279 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4897272 (h1 : term279 = (BIT1 0)) : term278 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4897273 : (term279 = (BIT1 0)) = (term278 = True).
Proof. exact (prop_ext (fun h1 : term279 = (BIT1 0) => @lem4897272 h1) (fun h1 : term278 = True => @lem4897271)). Qed.
Lemma lem4897274 : term278 = True.
Proof. exact (EQ_MP (@lem4897273) (@lem4897271)). Qed.
Lemma lem4897275 : term277 = True.
Proof. exact (TRANS (@lem4897270) (@lem4897274)). Qed.
Lemma lem4897276 : True = term277.
Proof. exact (SYM (@lem4897275)). Qed.
Lemma lem4897277 : term277.
Proof. exact (EQ_MP (@lem4897276) (@lem0)). Qed.
Lemma lem4897278 : term405.
Proof. exact (@lem4897267 (@lem4897277)). Qed.
Lemma lem4897280 (m : nat) (n : nat) : (term276 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4897281 : term277 = term278.
Proof. exact (@lem4897280 (NUMERAL 0) term121). Qed.
Lemma lem4897282 : term279 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4897283 (h1 : term279 = (BIT1 0)) : term278 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4897284 : (term279 = (BIT1 0)) = (term278 = True).
Proof. exact (prop_ext (fun h1 : term279 = (BIT1 0) => @lem4897283 h1) (fun h1 : term278 = True => @lem4897282)). Qed.
Lemma lem4897285 : term278 = True.
Proof. exact (EQ_MP (@lem4897284) (@lem4897282)). Qed.
Lemma lem4897286 : term277 = True.
Proof. exact (TRANS (@lem4897281) (@lem4897285)). Qed.
Lemma lem4897287 : True = term277.
Proof. exact (SYM (@lem4897286)). Qed.
Lemma lem4897288 : term277.
Proof. exact (EQ_MP (@lem4897287) (@lem0)). Qed.
Lemma lem4897289 : term406.
Proof. exact (@lem4897278 (@lem4897288)). Qed.
Lemma lem4897291 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4897292 : term247 = term248.
Proof. exact (@lem4897291 term121 term121). Qed.
Lemma lem4897293 : (term249 = (BIT1 0)) = (term250 = term121).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4897294 : term250 = term121.
Proof. exact (EQ_MP (@lem4897293) (@lem940073)). Qed.
Lemma lem4897295 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4897296 : term248 = term208.
Proof. exact (MK_COMB (@lem4897295) (@lem4897294)). Qed.
Lemma lem4897297 : term247 = term208.
Proof. exact (TRANS (@lem4897292) (@lem4897296)). Qed.
Lemma lem4897299 (m : nat) (n : nat) : (term309 m n) = (term310 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4897300 : term350 = term351.
Proof. exact (@lem4897299 term121 term121). Qed.
Lemma lem4897301 : (term249 = (BIT1 0)) = (term250 = term121).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4897302 : term250 = term121.
Proof. exact (EQ_MP (@lem4897301) (@lem940073)). Qed.
Lemma lem4897303 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4897304 : term248 = term208.
Proof. exact (MK_COMB (@lem4897303) (@lem4897302)). Qed.
Lemma lem4897305 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4897306 : term351 = term238.
Proof. exact (MK_COMB (@lem4897305) (@lem4897304)). Qed.
Lemma lem4897307 : term350 = term238.
Proof. exact (TRANS (@lem4897300) (@lem4897306)). Qed.
Lemma lem4897308 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4897309 : term407 = term399.
Proof. exact (MK_COMB (@lem4897308) (@lem4897307)). Qed.
Lemma lem4897310 : term408 = term401.
Proof. exact (MK_COMB (@lem4897309) (@lem4897297)). Qed.
Lemma lem4897312 (m : nat) : (term409 m) = term191.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem4897313 : term401 = term191.
Proof. exact (@lem4897312 term121). Qed.
Lemma lem4897314 : term408 = term191.
Proof. exact (TRANS (@lem4897310) (@lem4897313)). Qed.
Lemma lem4897315 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4897316 : term410 = term411.
Proof. exact (MK_COMB (@lem4897315) (@lem4897314)). Qed.
Lemma lem4897317 : term208 = term208.
Proof. exact (eq_refl term208). Qed.
Lemma lem4897318 : term412 = term379.
Proof. exact (MK_COMB (@lem4897316) (@lem4897317)). Qed.
Lemma lem4897320 (x : nat) : (term378 x) = term191.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4897321 : term379 = term191.
Proof. exact (@lem4897320 term121). Qed.
Lemma lem4897322 : term412 = term191.
Proof. exact (TRANS (@lem4897318) (@lem4897321)). Qed.
Lemma lem4897324 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4897325 : term247 = term248.
Proof. exact (@lem4897324 term121 term121). Qed.
Lemma lem4897326 : (term249 = (BIT1 0)) = (term250 = term121).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4897327 : term250 = term121.
Proof. exact (EQ_MP (@lem4897326) (@lem940073)). Qed.
Lemma lem4897328 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4897329 : term248 = term208.
Proof. exact (MK_COMB (@lem4897328) (@lem4897327)). Qed.
Lemma lem4897330 : term247 = term208.
Proof. exact (TRANS (@lem4897325) (@lem4897329)). Qed.
Lemma lem4897331 : term411 = term411.
Proof. exact (eq_refl term411). Qed.
Lemma lem4897332 : term413 = term379.
Proof. exact (MK_COMB (@lem4897331) (@lem4897330)). Qed.
Lemma lem4897334 (x : nat) : (term378 x) = term191.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4897335 : term379 = term191.
Proof. exact (@lem4897334 term121). Qed.
Lemma lem4897336 : term413 = term191.
Proof. exact (TRANS (@lem4897332) (@lem4897335)). Qed.
Lemma lem4897337 : term191 = term413.
Proof. exact (SYM (@lem4897336)). Qed.
Lemma lem4897338 : term412 = term413.
Proof. exact (TRANS (@lem4897322) (@lem4897337)). Qed.
Lemma lem4897339 : term402 = term235.
Proof. exact (@lem4897289 (@lem4897338)). Qed.
Lemma lem4897340 : term401 = term235.
Proof. exact (TRANS (@lem4897255) (@lem4897339)). Qed.
Lemma lem4897342 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4897343 : term235 = term191.
Proof. exact (@lem4897342 term191). Qed.
Lemma lem4897344 : term401 = term191.
Proof. exact (TRANS (@lem4897340) (@lem4897343)). Qed.
Lemma lem4897345 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4897346 : term414 = term411.
Proof. exact (MK_COMB (@lem4897345) (@lem4897344)). Qed.
Lemma lem4897347 (_60486 : int) : (real_of_int _60486) = (real_of_int _60486).
Proof. exact (eq_refl (real_of_int _60486)). Qed.
Lemma lem4897348 (_60486 : int) : (term398 _60486) = (term415 _60486).
Proof. exact (MK_COMB (@lem4897346) (@lem4897347 _60486)). Qed.
Lemma lem4897349 (_60486 : int) : (term420 _60486) = (term415 _60486).
Proof. exact (TRANS (@lem4897246 _60486) (@lem4897348 _60486)). Qed.
Lemma lem4897350 (_60486 : int) : (term415 _60486) = term191.
Proof. exact (@lem1982719 (real_of_int _60486)). Qed.
Lemma lem4897351 (_60486 : int) : (term420 _60486) = term191.
Proof. exact (TRANS (@lem4897349 _60486) (@lem4897350 _60486)). Qed.
Lemma lem4897352 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4897353 (_60486 : int) : (term421 _60486) = term417.
Proof. exact (MK_COMB (@lem4897352) (@lem4897351 _60486)). Qed.
Lemma lem4897354 : term315 = term315.
Proof. exact (eq_refl term315). Qed.
Lemma lem4897355 (_60486 : int) : (term419 _60486) = term422.
Proof. exact (MK_COMB (@lem4897353 _60486) (@lem4897354)). Qed.
Lemma lem4897356 (_60486 : int) : (term418 _60486) = term422.
Proof. exact (TRANS (@lem4897245 _60486) (@lem4897355 _60486)). Qed.
Lemma lem4897357 : term422 = term315.
Proof. exact (@lem1982721 term315). Qed.
Lemma lem4897358 (_60486 : int) : (term418 _60486) = term315.
Proof. exact (TRANS (@lem4897356 _60486) (@lem4897357)). Qed.
Lemma lem4897359 (_60485 : int) (_60486 : int) : (term396 _60485 _60486) = term422.
Proof. exact (MK_COMB (@lem4897244 _60485) (@lem4897358 _60486)). Qed.
Lemma lem4897360 (_60485 : int) (_60486 : int) : (term395 _60485 _60486) = term422.
Proof. exact (TRANS (@lem4897136 _60485 _60486) (@lem4897359 _60485 _60486)). Qed.
Lemma lem4897361 : term422 = term315.
Proof. exact (@lem1982721 term315). Qed.
Lemma lem4897362 (_60485 : int) (_60486 : int) : (term395 _60485 _60486) = term315.
Proof. exact (TRANS (@lem4897360 _60485 _60486) (@lem4897361)). Qed.
Lemma lem4897363 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4897364 (_60485 : int) (_60486 : int) : (term423 _60485 _60486) = term424.
Proof. exact (MK_COMB (@lem4897363) (@lem4897362 _60485 _60486)). Qed.
Lemma lem4897365 : term191 = term191.
Proof. exact (eq_refl term191). Qed.
Lemma lem4897366 (_60485 : int) (_60486 : int) : (term394 _60485 _60486) = term425.
Proof. exact (MK_COMB (@lem4897364 _60485 _60486) (@lem4897365)). Qed.
Lemma lem4897367 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) (h1 : term370 _112846 h t _60485 _60486) : term425.
Proof. exact (EQ_MP (@lem4897366 _60485 _60486) (@lem4897135 _112846 h t _60485 _60486 h1)). Qed.
Lemma lem4897369 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem4897370 : term425 = term426.
Proof. exact (@lem4897369 term191 term315). Qed.
Lemma lem4897372 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4897373 : term315 = term318.
Proof. exact (@lem4897372 term289). Qed.
Lemma lem4897375 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4897376 : term191 = term235.
Proof. exact (@lem4897375 (NUMERAL 0)). Qed.
Lemma lem4897377 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4897378 : term193 = term427.
Proof. exact (MK_COMB (@lem4897377) (@lem4897376)). Qed.
Lemma lem4897379 : term426 = term428.
Proof. exact (MK_COMB (@lem4897378) (@lem4897373)). Qed.
Lemma lem4897380 : term429.
Proof. exact (@lem1980026 term191 term208 term315 term208). Qed.
Lemma lem4897382 (m : nat) (n : nat) : (term276 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4897383 : term277 = term278.
Proof. exact (@lem4897382 (NUMERAL 0) term121). Qed.
Lemma lem4897384 : term279 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4897385 (h1 : term279 = (BIT1 0)) : term278 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4897386 : (term279 = (BIT1 0)) = (term278 = True).
Proof. exact (prop_ext (fun h1 : term279 = (BIT1 0) => @lem4897385 h1) (fun h1 : term278 = True => @lem4897384)). Qed.
Lemma lem4897387 : term278 = True.
Proof. exact (EQ_MP (@lem4897386) (@lem4897384)). Qed.
Lemma lem4897388 : term277 = True.
Proof. exact (TRANS (@lem4897383) (@lem4897387)). Qed.
Lemma lem4897389 : True = term277.
Proof. exact (SYM (@lem4897388)). Qed.
Lemma lem4897390 : term277.
Proof. exact (EQ_MP (@lem4897389) (@lem0)). Qed.
Lemma lem4897391 : term430.
Proof. exact (@lem4897380 (@lem4897390)). Qed.
Lemma lem4897393 (m : nat) (n : nat) : (term276 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4897394 : term277 = term278.
Proof. exact (@lem4897393 (NUMERAL 0) term121). Qed.
Lemma lem4897395 : term279 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4897396 (h1 : term279 = (BIT1 0)) : term278 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4897397 : (term279 = (BIT1 0)) = (term278 = True).
Proof. exact (prop_ext (fun h1 : term279 = (BIT1 0) => @lem4897396 h1) (fun h1 : term278 = True => @lem4897395)). Qed.
Lemma lem4897398 : term278 = True.
Proof. exact (EQ_MP (@lem4897397) (@lem4897395)). Qed.
Lemma lem4897399 : term277 = True.
Proof. exact (TRANS (@lem4897394) (@lem4897398)). Qed.
Lemma lem4897400 : True = term277.
Proof. exact (SYM (@lem4897399)). Qed.
Lemma lem4897401 : term277.
Proof. exact (EQ_MP (@lem4897400) (@lem0)). Qed.
Lemma lem4897402 : term428 = term431.
Proof. exact (@lem4897391 (@lem4897401)). Qed.
Lemma lem4897404 (m : nat) (n : nat) : (term309 m n) = (term310 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4897405 : term343 = term344.
Proof. exact (@lem4897404 term289 term121). Qed.
Lemma lem4897406 : term295 = term287.
Proof. exact (@lem996237 term287). Qed.
Lemma lem4897407 : (term295 = term287) = (term296 = term289).
Proof. exact (@lem1007663 term287 (BIT1 0) term287). Qed.
Lemma lem4897408 : term296 = term289.
Proof. exact (EQ_MP (@lem4897407) (@lem4897406)). Qed.
Lemma lem4897409 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4897410 : term294 = term275.
Proof. exact (MK_COMB (@lem4897409) (@lem4897408)). Qed.
Lemma lem4897411 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4897412 : term344 = term315.
Proof. exact (MK_COMB (@lem4897411) (@lem4897410)). Qed.
Lemma lem4897413 : term343 = term315.
Proof. exact (TRANS (@lem4897405) (@lem4897412)). Qed.
Lemma lem4897415 (x : nat) : (term378 x) = term191.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4897416 : term379 = term191.
Proof. exact (@lem4897415 term121). Qed.
Lemma lem4897417 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4897418 : term432 = term193.
Proof. exact (MK_COMB (@lem4897417) (@lem4897416)). Qed.
Lemma lem4897419 : term431 = term426.
Proof. exact (MK_COMB (@lem4897418) (@lem4897413)). Qed.
Lemma lem4897421 (m : nat) (n : nat) : (term433 m n) = (term434 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem4897422 : term426 = term435.
Proof. exact (@lem4897421 (NUMERAL 0) term289). Qed.
Lemma lem4897423 : term436 = term287.
Proof. exact (@lem912803). Qed.
Lemma lem4897424 (h1 : term436 = term287) : (term289 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term287 h1). Qed.
Lemma lem4897425 : (term436 = term287) = ((term289 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term436 = term287 => @lem4897424 h1) (fun h1 : (term289 = (NUMERAL 0)) = False => @lem4897423)). Qed.
Lemma lem4897426 : (term289 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem4897425) (@lem4897423)). Qed.
Lemma lem4897427 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem4897428 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4897429 : term437 = (and True).
Proof. exact (MK_COMB (@lem4897428) (@lem4897427)). Qed.
Lemma lem4897430 : term435 = (True /\ False).
Proof. exact (MK_COMB (@lem4897429) (@lem4897426)). Qed.
Lemma lem4897432 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem4897433 : term435 = False.
Proof. exact (TRANS (@lem4897430) (@lem4897432)). Qed.
Lemma lem4897434 : term426 = False.
Proof. exact (TRANS (@lem4897422) (@lem4897433)). Qed.
Lemma lem4897435 : term431 = False.
Proof. exact (TRANS (@lem4897419) (@lem4897434)). Qed.
Lemma lem4897436 : term428 = False.
Proof. exact (TRANS (@lem4897402) (@lem4897435)). Qed.
Lemma lem4897437 : term426 = False.
Proof. exact (TRANS (@lem4897379) (@lem4897436)). Qed.
Lemma lem4897438 : term425 = False.
Proof. exact (TRANS (@lem4897370) (@lem4897437)). Qed.
Lemma lem4897439 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) (h1 : term370 _112846 h t _60485 _60486) : False.
Proof. exact (EQ_MP (@lem4897438) (@lem4897367 _112846 h t _60485 _60486 h1)). Qed.
Lemma lem4897440 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) (h1 : term438 _112846 h t _60485 _60486) : term438 _112846 h t _60485 _60486.
Proof. exact (h1). Qed.
Lemma lem4897441 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) (h1 : term438 _112846 h t _60485 _60486) : term369 _112846 h t _60485 _60486.
Proof. exact (proj2 (@lem4897440 _112846 h t _60485 _60486 h1)). Qed.
Lemma lem4897443 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) (h1 : term438 _112846 h t _60485 _60486) : term359 _112846 h t _60485 _60486.
Proof. exact (proj2 (@lem4897441 _112846 h t _60485 _60486 h1)). Qed.
Lemma lem4897445 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) (h1 : term438 _112846 h t _60485 _60486) : term358 _60485 _60486.
Proof. exact (proj2 (@lem4897443 _112846 h t _60485 _60486 h1)). Qed.
Lemma lem4897447 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) (h1 : term438 _112846 h t _60485 _60486) : term357 _60485 _60486.
Proof. exact (proj2 (@lem4897445 _112846 h t _60485 _60486 h1)). Qed.
Lemma lem4897448 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) (h1 : term438 _112846 h t _60485 _60486) : term266 _60485 _60486.
Proof. exact (proj1 (@lem4897445 _112846 h t _60485 _60486 h1)). Qed.
Lemma lem4897450 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem4897451 : term371 = term277.
Proof. exact (@lem4897450 term191 term208). Qed.
Lemma lem4897453 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4897454 : term208 = term269.
Proof. exact (@lem4897453 term121). Qed.
Lemma lem4897456 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4897457 : term191 = term235.
Proof. exact (@lem4897456 (NUMERAL 0)). Qed.
Lemma lem4897458 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4897459 : term372 = term373.
Proof. exact (MK_COMB (@lem4897458) (@lem4897457)). Qed.
Lemma lem4897460 : term277 = term374.
Proof. exact (MK_COMB (@lem4897459) (@lem4897454)). Qed.
Lemma lem4897461 : term375.
Proof. exact (@lem1980255 term191 term208 term208 term208). Qed.
Lemma lem4897463 (m : nat) (n : nat) : (term276 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4897464 : term277 = term278.
Proof. exact (@lem4897463 (NUMERAL 0) term121). Qed.
Lemma lem4897465 : term279 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4897466 (h1 : term279 = (BIT1 0)) : term278 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4897467 : (term279 = (BIT1 0)) = (term278 = True).
Proof. exact (prop_ext (fun h1 : term279 = (BIT1 0) => @lem4897466 h1) (fun h1 : term278 = True => @lem4897465)). Qed.
Lemma lem4897468 : term278 = True.
Proof. exact (EQ_MP (@lem4897467) (@lem4897465)). Qed.
Lemma lem4897469 : term277 = True.
Proof. exact (TRANS (@lem4897464) (@lem4897468)). Qed.
Lemma lem4897470 : True = term277.
Proof. exact (SYM (@lem4897469)). Qed.
Lemma lem4897471 : term277.
Proof. exact (EQ_MP (@lem4897470) (@lem0)). Qed.
Lemma lem4897472 : term376.
Proof. exact (@lem4897461 (@lem4897471)). Qed.
Lemma lem4897474 (m : nat) (n : nat) : (term276 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4897475 : term277 = term278.
Proof. exact (@lem4897474 (NUMERAL 0) term121). Qed.
Lemma lem4897476 : term279 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4897477 (h1 : term279 = (BIT1 0)) : term278 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4897478 : (term279 = (BIT1 0)) = (term278 = True).
Proof. exact (prop_ext (fun h1 : term279 = (BIT1 0) => @lem4897477 h1) (fun h1 : term278 = True => @lem4897476)). Qed.
Lemma lem4897479 : term278 = True.
Proof. exact (EQ_MP (@lem4897478) (@lem4897476)). Qed.
Lemma lem4897480 : term277 = True.
Proof. exact (TRANS (@lem4897475) (@lem4897479)). Qed.
Lemma lem4897481 : True = term277.
Proof. exact (SYM (@lem4897480)). Qed.
Lemma lem4897482 : term277.
Proof. exact (EQ_MP (@lem4897481) (@lem0)). Qed.
Lemma lem4897483 : term374 = term377.
Proof. exact (@lem4897472 (@lem4897482)). Qed.
Lemma lem4897485 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4897486 : term247 = term248.
Proof. exact (@lem4897485 term121 term121). Qed.
Lemma lem4897487 : (term249 = (BIT1 0)) = (term250 = term121).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4897488 : term250 = term121.
Proof. exact (EQ_MP (@lem4897487) (@lem940073)). Qed.
Lemma lem4897489 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4897490 : term248 = term208.
Proof. exact (MK_COMB (@lem4897489) (@lem4897488)). Qed.
Lemma lem4897491 : term247 = term208.
Proof. exact (TRANS (@lem4897486) (@lem4897490)). Qed.
Lemma lem4897493 (x : nat) : (term378 x) = term191.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4897494 : term379 = term191.
Proof. exact (@lem4897493 term121). Qed.
Lemma lem4897495 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4897496 : term380 = term372.
Proof. exact (MK_COMB (@lem4897495) (@lem4897494)). Qed.
Lemma lem4897497 : term377 = term277.
Proof. exact (MK_COMB (@lem4897496) (@lem4897491)). Qed.
Lemma lem4897499 (m : nat) (n : nat) : (term276 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4897500 : term277 = term278.
Proof. exact (@lem4897499 (NUMERAL 0) term121). Qed.
Lemma lem4897501 : term279 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4897502 (h1 : term279 = (BIT1 0)) : term278 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4897503 : (term279 = (BIT1 0)) = (term278 = True).
Proof. exact (prop_ext (fun h1 : term279 = (BIT1 0) => @lem4897502 h1) (fun h1 : term278 = True => @lem4897501)). Qed.
Lemma lem4897504 : term278 = True.
Proof. exact (EQ_MP (@lem4897503) (@lem4897501)). Qed.
Lemma lem4897505 : term277 = True.
Proof. exact (TRANS (@lem4897500) (@lem4897504)). Qed.
Lemma lem4897506 : term377 = True.
Proof. exact (TRANS (@lem4897497) (@lem4897505)). Qed.
Lemma lem4897507 : term374 = True.
Proof. exact (TRANS (@lem4897483) (@lem4897506)). Qed.
Lemma lem4897508 : term277 = True.
Proof. exact (TRANS (@lem4897460) (@lem4897507)). Qed.
Lemma lem4897509 : term371 = True.
Proof. exact (TRANS (@lem4897451) (@lem4897508)). Qed.
Lemma lem4897510 : True = term371.
Proof. exact (SYM (@lem4897509)). Qed.
Lemma lem4897511 : term371.
Proof. exact (EQ_MP (@lem4897510) (@lem0)). Qed.
Lemma lem4897512 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) (h1 : term438 _112846 h t _60485 _60486) : term439 _60485 _60486.
Proof. exact (conj (@lem4897511) (@lem4897447 _112846 h t _60485 _60486 h1)). Qed.
Lemma lem4897514 (x : real) (y : real) : term382 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem4897515 (_60485 : int) (_60486 : int) : term440 _60485 _60486.
Proof. exact (@lem4897514 term208 (term354 _60485 _60486)). Qed.
Lemma lem4897516 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) (h1 : term438 _112846 h t _60485 _60486) : term441 _60485 _60486.
Proof. exact (@lem4897515 _60485 _60486 (@lem4897512 _112846 h t _60485 _60486 h1)). Qed.
Lemma lem4897517 (_60485 : int) (_60486 : int) : (term442 _60485 _60486) = (term354 _60485 _60486).
Proof. exact (@lem1982733 (term354 _60485 _60486)). Qed.
Lemma lem4897518 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4897519 (_60485 : int) (_60486 : int) : (term443 _60485 _60486) = (term356 _60485 _60486).
Proof. exact (MK_COMB (@lem4897518) (@lem4897517 _60485 _60486)). Qed.
Lemma lem4897520 : term191 = term191.
Proof. exact (eq_refl term191). Qed.
Lemma lem4897521 (_60485 : int) (_60486 : int) : (term441 _60485 _60486) = (term357 _60485 _60486).
Proof. exact (MK_COMB (@lem4897519 _60485 _60486) (@lem4897520)). Qed.
Lemma lem4897522 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) (h1 : term438 _112846 h t _60485 _60486) : term357 _60485 _60486.
Proof. exact (EQ_MP (@lem4897521 _60485 _60486) (@lem4897516 _112846 h t _60485 _60486 h1)). Qed.
Lemma lem4897524 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem4897525 : term371 = term277.
Proof. exact (@lem4897524 term191 term208). Qed.
Lemma lem4897527 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4897528 : term208 = term269.
Proof. exact (@lem4897527 term121). Qed.
Lemma lem4897530 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4897531 : term191 = term235.
Proof. exact (@lem4897530 (NUMERAL 0)). Qed.
Lemma lem4897532 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4897533 : term372 = term373.
Proof. exact (MK_COMB (@lem4897532) (@lem4897531)). Qed.
Lemma lem4897534 : term277 = term374.
Proof. exact (MK_COMB (@lem4897533) (@lem4897528)). Qed.
Lemma lem4897535 : term375.
Proof. exact (@lem1980255 term191 term208 term208 term208). Qed.
Lemma lem4897537 (m : nat) (n : nat) : (term276 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4897538 : term277 = term278.
Proof. exact (@lem4897537 (NUMERAL 0) term121). Qed.
Lemma lem4897539 : term279 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4897540 (h1 : term279 = (BIT1 0)) : term278 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4897541 : (term279 = (BIT1 0)) = (term278 = True).
Proof. exact (prop_ext (fun h1 : term279 = (BIT1 0) => @lem4897540 h1) (fun h1 : term278 = True => @lem4897539)). Qed.
Lemma lem4897542 : term278 = True.
Proof. exact (EQ_MP (@lem4897541) (@lem4897539)). Qed.
Lemma lem4897543 : term277 = True.
Proof. exact (TRANS (@lem4897538) (@lem4897542)). Qed.
Lemma lem4897544 : True = term277.
Proof. exact (SYM (@lem4897543)). Qed.
Lemma lem4897545 : term277.
Proof. exact (EQ_MP (@lem4897544) (@lem0)). Qed.
Lemma lem4897546 : term376.
Proof. exact (@lem4897535 (@lem4897545)). Qed.
Lemma lem4897548 (m : nat) (n : nat) : (term276 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4897549 : term277 = term278.
Proof. exact (@lem4897548 (NUMERAL 0) term121). Qed.
Lemma lem4897550 : term279 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4897551 (h1 : term279 = (BIT1 0)) : term278 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4897552 : (term279 = (BIT1 0)) = (term278 = True).
Proof. exact (prop_ext (fun h1 : term279 = (BIT1 0) => @lem4897551 h1) (fun h1 : term278 = True => @lem4897550)). Qed.
Lemma lem4897553 : term278 = True.
Proof. exact (EQ_MP (@lem4897552) (@lem4897550)). Qed.
Lemma lem4897554 : term277 = True.
Proof. exact (TRANS (@lem4897549) (@lem4897553)). Qed.
Lemma lem4897555 : True = term277.
Proof. exact (SYM (@lem4897554)). Qed.
Lemma lem4897556 : term277.
Proof. exact (EQ_MP (@lem4897555) (@lem0)). Qed.
Lemma lem4897557 : term374 = term377.
Proof. exact (@lem4897546 (@lem4897556)). Qed.
Lemma lem4897559 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4897560 : term247 = term248.
Proof. exact (@lem4897559 term121 term121). Qed.
Lemma lem4897561 : (term249 = (BIT1 0)) = (term250 = term121).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4897562 : term250 = term121.
Proof. exact (EQ_MP (@lem4897561) (@lem940073)). Qed.
Lemma lem4897563 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4897564 : term248 = term208.
Proof. exact (MK_COMB (@lem4897563) (@lem4897562)). Qed.
Lemma lem4897565 : term247 = term208.
Proof. exact (TRANS (@lem4897560) (@lem4897564)). Qed.
Lemma lem4897567 (x : nat) : (term378 x) = term191.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4897568 : term379 = term191.
Proof. exact (@lem4897567 term121). Qed.
Lemma lem4897569 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4897570 : term380 = term372.
Proof. exact (MK_COMB (@lem4897569) (@lem4897568)). Qed.
Lemma lem4897571 : term377 = term277.
Proof. exact (MK_COMB (@lem4897570) (@lem4897565)). Qed.
Lemma lem4897573 (m : nat) (n : nat) : (term276 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4897574 : term277 = term278.
Proof. exact (@lem4897573 (NUMERAL 0) term121). Qed.
Lemma lem4897575 : term279 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4897576 (h1 : term279 = (BIT1 0)) : term278 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4897577 : (term279 = (BIT1 0)) = (term278 = True).
Proof. exact (prop_ext (fun h1 : term279 = (BIT1 0) => @lem4897576 h1) (fun h1 : term278 = True => @lem4897575)). Qed.
Lemma lem4897578 : term278 = True.
Proof. exact (EQ_MP (@lem4897577) (@lem4897575)). Qed.
Lemma lem4897579 : term277 = True.
Proof. exact (TRANS (@lem4897574) (@lem4897578)). Qed.
Lemma lem4897580 : term377 = True.
Proof. exact (TRANS (@lem4897571) (@lem4897579)). Qed.
Lemma lem4897581 : term374 = True.
Proof. exact (TRANS (@lem4897557) (@lem4897580)). Qed.
Lemma lem4897582 : term277 = True.
Proof. exact (TRANS (@lem4897534) (@lem4897581)). Qed.
Lemma lem4897583 : term371 = True.
Proof. exact (TRANS (@lem4897525) (@lem4897582)). Qed.
Lemma lem4897584 : True = term371.
Proof. exact (SYM (@lem4897583)). Qed.
Lemma lem4897585 : term371.
Proof. exact (EQ_MP (@lem4897584) (@lem0)). Qed.
Lemma lem4897586 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) (h1 : term438 _112846 h t _60485 _60486) : term387 _60485 _60486.
Proof. exact (conj (@lem4897585) (@lem4897448 _112846 h t _60485 _60486 h1)). Qed.
Lemma lem4897588 (x : real) (y : real) : term382 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem4897589 (_60485 : int) (_60486 : int) : term388 _60485 _60486.
Proof. exact (@lem4897588 term208 (term262 _60485 _60486)). Qed.
Lemma lem4897590 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) (h1 : term438 _112846 h t _60485 _60486) : term389 _60485 _60486.
Proof. exact (@lem4897589 _60485 _60486 (@lem4897586 _112846 h t _60485 _60486 h1)). Qed.
Lemma lem4897591 (_60485 : int) (_60486 : int) : (term390 _60485 _60486) = (term262 _60485 _60486).
Proof. exact (@lem1982733 (term262 _60485 _60486)). Qed.
Lemma lem4897592 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4897593 (_60485 : int) (_60486 : int) : (term391 _60485 _60486) = (term265 _60485 _60486).
Proof. exact (MK_COMB (@lem4897592) (@lem4897591 _60485 _60486)). Qed.
Lemma lem4897594 : term191 = term191.
Proof. exact (eq_refl term191). Qed.
Lemma lem4897595 (_60485 : int) (_60486 : int) : (term389 _60485 _60486) = (term266 _60485 _60486).
Proof. exact (MK_COMB (@lem4897593 _60485 _60486) (@lem4897594)). Qed.
Lemma lem4897596 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) (h1 : term438 _112846 h t _60485 _60486) : term266 _60485 _60486.
Proof. exact (EQ_MP (@lem4897595 _60485 _60486) (@lem4897590 _112846 h t _60485 _60486 h1)). Qed.
Lemma lem4897597 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) (h1 : term438 _112846 h t _60485 _60486) : term358 _60485 _60486.
Proof. exact (conj (@lem4897596 _112846 h t _60485 _60486 h1) (@lem4897522 _112846 h t _60485 _60486 h1)). Qed.
Lemma lem4897599 (x : real) (y : real) : term392 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem4897600 (_60485 : int) (_60486 : int) : term444 _60485 _60486.
Proof. exact (@lem4897599 (term262 _60485 _60486) (term354 _60485 _60486)). Qed.
Lemma lem4897601 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) (h1 : term438 _112846 h t _60485 _60486) : term445 _60485 _60486.
Proof. exact (@lem4897600 _60485 _60486 (@lem4897597 _112846 h t _60485 _60486 h1)). Qed.
Lemma lem4897602 (_60485 : int) (_60486 : int) : (term446 _60485 _60486) = (term447 _60485 _60486).
Proof. exact (@lem1982753 (term263 _60485) (real_of_int _60485) (real_of_int _60486) (term353 _60486)). Qed.
Lemma lem4897603 (_60485 : int) : (term397 _60485) = (term398 _60485).
Proof. exact (@lem1982713 term238 (real_of_int _60485)). Qed.
Lemma lem4897605 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4897606 : term208 = term269.
Proof. exact (@lem4897605 term121). Qed.
Lemma lem4897608 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4897609 : term238 = term239.
Proof. exact (@lem4897608 term121). Qed.
Lemma lem4897610 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4897611 : term399 = term400.
Proof. exact (MK_COMB (@lem4897610) (@lem4897609)). Qed.
Lemma lem4897612 : term401 = term402.
Proof. exact (MK_COMB (@lem4897611) (@lem4897606)). Qed.
Lemma lem4897613 : term403.
Proof. exact (@lem1981473 term238 term208 term208 term208 term191 term208). Qed.
Lemma lem4897615 (m : nat) (n : nat) : (term276 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4897616 : term277 = term278.
Proof. exact (@lem4897615 (NUMERAL 0) term121). Qed.
Lemma lem4897617 : term279 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4897618 (h1 : term279 = (BIT1 0)) : term278 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4897619 : (term279 = (BIT1 0)) = (term278 = True).
Proof. exact (prop_ext (fun h1 : term279 = (BIT1 0) => @lem4897618 h1) (fun h1 : term278 = True => @lem4897617)). Qed.
Lemma lem4897620 : term278 = True.
Proof. exact (EQ_MP (@lem4897619) (@lem4897617)). Qed.
Lemma lem4897621 : term277 = True.
Proof. exact (TRANS (@lem4897616) (@lem4897620)). Qed.
Lemma lem4897622 : True = term277.
Proof. exact (SYM (@lem4897621)). Qed.
Lemma lem4897623 : term277.
Proof. exact (EQ_MP (@lem4897622) (@lem0)). Qed.
Lemma lem4897624 : term404.
Proof. exact (@lem4897613 (@lem4897623)). Qed.
Lemma lem4897626 (m : nat) (n : nat) : (term276 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4897627 : term277 = term278.
Proof. exact (@lem4897626 (NUMERAL 0) term121). Qed.
Lemma lem4897628 : term279 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4897629 (h1 : term279 = (BIT1 0)) : term278 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4897630 : (term279 = (BIT1 0)) = (term278 = True).
Proof. exact (prop_ext (fun h1 : term279 = (BIT1 0) => @lem4897629 h1) (fun h1 : term278 = True => @lem4897628)). Qed.
Lemma lem4897631 : term278 = True.
Proof. exact (EQ_MP (@lem4897630) (@lem4897628)). Qed.
Lemma lem4897632 : term277 = True.
Proof. exact (TRANS (@lem4897627) (@lem4897631)). Qed.
Lemma lem4897633 : True = term277.
Proof. exact (SYM (@lem4897632)). Qed.
Lemma lem4897634 : term277.
Proof. exact (EQ_MP (@lem4897633) (@lem0)). Qed.
Lemma lem4897635 : term405.
Proof. exact (@lem4897624 (@lem4897634)). Qed.
Lemma lem4897637 (m : nat) (n : nat) : (term276 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4897638 : term277 = term278.
Proof. exact (@lem4897637 (NUMERAL 0) term121). Qed.
Lemma lem4897639 : term279 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4897640 (h1 : term279 = (BIT1 0)) : term278 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4897641 : (term279 = (BIT1 0)) = (term278 = True).
Proof. exact (prop_ext (fun h1 : term279 = (BIT1 0) => @lem4897640 h1) (fun h1 : term278 = True => @lem4897639)). Qed.
Lemma lem4897642 : term278 = True.
Proof. exact (EQ_MP (@lem4897641) (@lem4897639)). Qed.
Lemma lem4897643 : term277 = True.
Proof. exact (TRANS (@lem4897638) (@lem4897642)). Qed.
Lemma lem4897644 : True = term277.
Proof. exact (SYM (@lem4897643)). Qed.
Lemma lem4897645 : term277.
Proof. exact (EQ_MP (@lem4897644) (@lem0)). Qed.
Lemma lem4897646 : term406.
Proof. exact (@lem4897635 (@lem4897645)). Qed.
Lemma lem4897648 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4897649 : term247 = term248.
Proof. exact (@lem4897648 term121 term121). Qed.
Lemma lem4897650 : (term249 = (BIT1 0)) = (term250 = term121).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4897651 : term250 = term121.
Proof. exact (EQ_MP (@lem4897650) (@lem940073)). Qed.
Lemma lem4897652 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4897653 : term248 = term208.
Proof. exact (MK_COMB (@lem4897652) (@lem4897651)). Qed.
Lemma lem4897654 : term247 = term208.
Proof. exact (TRANS (@lem4897649) (@lem4897653)). Qed.
Lemma lem4897656 (m : nat) (n : nat) : (term309 m n) = (term310 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4897657 : term350 = term351.
Proof. exact (@lem4897656 term121 term121). Qed.
Lemma lem4897658 : (term249 = (BIT1 0)) = (term250 = term121).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4897659 : term250 = term121.
Proof. exact (EQ_MP (@lem4897658) (@lem940073)). Qed.
Lemma lem4897660 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4897661 : term248 = term208.
Proof. exact (MK_COMB (@lem4897660) (@lem4897659)). Qed.
Lemma lem4897662 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4897663 : term351 = term238.
Proof. exact (MK_COMB (@lem4897662) (@lem4897661)). Qed.
Lemma lem4897664 : term350 = term238.
Proof. exact (TRANS (@lem4897657) (@lem4897663)). Qed.
Lemma lem4897665 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4897666 : term407 = term399.
Proof. exact (MK_COMB (@lem4897665) (@lem4897664)). Qed.
Lemma lem4897667 : term408 = term401.
Proof. exact (MK_COMB (@lem4897666) (@lem4897654)). Qed.
Lemma lem4897669 (m : nat) : (term409 m) = term191.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem4897670 : term401 = term191.
Proof. exact (@lem4897669 term121). Qed.
Lemma lem4897671 : term408 = term191.
Proof. exact (TRANS (@lem4897667) (@lem4897670)). Qed.
Lemma lem4897672 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4897673 : term410 = term411.
Proof. exact (MK_COMB (@lem4897672) (@lem4897671)). Qed.
Lemma lem4897674 : term208 = term208.
Proof. exact (eq_refl term208). Qed.
Lemma lem4897675 : term412 = term379.
Proof. exact (MK_COMB (@lem4897673) (@lem4897674)). Qed.
Lemma lem4897677 (x : nat) : (term378 x) = term191.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4897678 : term379 = term191.
Proof. exact (@lem4897677 term121). Qed.
Lemma lem4897679 : term412 = term191.
Proof. exact (TRANS (@lem4897675) (@lem4897678)). Qed.
Lemma lem4897681 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4897682 : term247 = term248.
Proof. exact (@lem4897681 term121 term121). Qed.
Lemma lem4897683 : (term249 = (BIT1 0)) = (term250 = term121).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4897684 : term250 = term121.
Proof. exact (EQ_MP (@lem4897683) (@lem940073)). Qed.
Lemma lem4897685 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4897686 : term248 = term208.
Proof. exact (MK_COMB (@lem4897685) (@lem4897684)). Qed.
Lemma lem4897687 : term247 = term208.
Proof. exact (TRANS (@lem4897682) (@lem4897686)). Qed.
Lemma lem4897688 : term411 = term411.
Proof. exact (eq_refl term411). Qed.
Lemma lem4897689 : term413 = term379.
Proof. exact (MK_COMB (@lem4897688) (@lem4897687)). Qed.
Lemma lem4897691 (x : nat) : (term378 x) = term191.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4897692 : term379 = term191.
Proof. exact (@lem4897691 term121). Qed.
Lemma lem4897693 : term413 = term191.
Proof. exact (TRANS (@lem4897689) (@lem4897692)). Qed.
Lemma lem4897694 : term191 = term413.
Proof. exact (SYM (@lem4897693)). Qed.
Lemma lem4897695 : term412 = term413.
Proof. exact (TRANS (@lem4897679) (@lem4897694)). Qed.
Lemma lem4897696 : term402 = term235.
Proof. exact (@lem4897646 (@lem4897695)). Qed.
Lemma lem4897697 : term401 = term235.
Proof. exact (TRANS (@lem4897612) (@lem4897696)). Qed.
Lemma lem4897699 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4897700 : term235 = term191.
Proof. exact (@lem4897699 term191). Qed.
Lemma lem4897701 : term401 = term191.
Proof. exact (TRANS (@lem4897697) (@lem4897700)). Qed.
Lemma lem4897702 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4897703 : term414 = term411.
Proof. exact (MK_COMB (@lem4897702) (@lem4897701)). Qed.
Lemma lem4897704 (_60485 : int) : (real_of_int _60485) = (real_of_int _60485).
Proof. exact (eq_refl (real_of_int _60485)). Qed.
Lemma lem4897705 (_60485 : int) : (term398 _60485) = (term415 _60485).
Proof. exact (MK_COMB (@lem4897703) (@lem4897704 _60485)). Qed.
Lemma lem4897706 (_60485 : int) : (term397 _60485) = (term415 _60485).
Proof. exact (TRANS (@lem4897603 _60485) (@lem4897705 _60485)). Qed.
Lemma lem4897707 (_60485 : int) : (term415 _60485) = term191.
Proof. exact (@lem1982719 (real_of_int _60485)). Qed.
Lemma lem4897708 (_60485 : int) : (term397 _60485) = term191.
Proof. exact (TRANS (@lem4897706 _60485) (@lem4897707 _60485)). Qed.
Lemma lem4897709 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4897710 (_60485 : int) : (term416 _60485) = term417.
Proof. exact (MK_COMB (@lem4897709) (@lem4897708 _60485)). Qed.
Lemma lem4897711 (_60486 : int) : (term448 _60486) = (term449 _60486).
Proof. exact (@lem1982763 (real_of_int _60486) (term263 _60486) term238). Qed.
Lemma lem4897712 (_60486 : int) : (term420 _60486) = (term398 _60486).
Proof. exact (@lem1982715 term238 (real_of_int _60486)). Qed.
Lemma lem4897714 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4897715 : term208 = term269.
Proof. exact (@lem4897714 term121). Qed.
Lemma lem4897717 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4897718 : term238 = term239.
Proof. exact (@lem4897717 term121). Qed.
Lemma lem4897719 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4897720 : term399 = term400.
Proof. exact (MK_COMB (@lem4897719) (@lem4897718)). Qed.
Lemma lem4897721 : term401 = term402.
Proof. exact (MK_COMB (@lem4897720) (@lem4897715)). Qed.
Lemma lem4897722 : term403.
Proof. exact (@lem1981473 term238 term208 term208 term208 term191 term208). Qed.
Lemma lem4897724 (m : nat) (n : nat) : (term276 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4897725 : term277 = term278.
Proof. exact (@lem4897724 (NUMERAL 0) term121). Qed.
Lemma lem4897726 : term279 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4897727 (h1 : term279 = (BIT1 0)) : term278 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4897728 : (term279 = (BIT1 0)) = (term278 = True).
Proof. exact (prop_ext (fun h1 : term279 = (BIT1 0) => @lem4897727 h1) (fun h1 : term278 = True => @lem4897726)). Qed.
Lemma lem4897729 : term278 = True.
Proof. exact (EQ_MP (@lem4897728) (@lem4897726)). Qed.
Lemma lem4897730 : term277 = True.
Proof. exact (TRANS (@lem4897725) (@lem4897729)). Qed.
Lemma lem4897731 : True = term277.
Proof. exact (SYM (@lem4897730)). Qed.
Lemma lem4897732 : term277.
Proof. exact (EQ_MP (@lem4897731) (@lem0)). Qed.
Lemma lem4897733 : term404.
Proof. exact (@lem4897722 (@lem4897732)). Qed.
Lemma lem4897735 (m : nat) (n : nat) : (term276 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4897736 : term277 = term278.
Proof. exact (@lem4897735 (NUMERAL 0) term121). Qed.
Lemma lem4897737 : term279 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4897738 (h1 : term279 = (BIT1 0)) : term278 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4897739 : (term279 = (BIT1 0)) = (term278 = True).
Proof. exact (prop_ext (fun h1 : term279 = (BIT1 0) => @lem4897738 h1) (fun h1 : term278 = True => @lem4897737)). Qed.
Lemma lem4897740 : term278 = True.
Proof. exact (EQ_MP (@lem4897739) (@lem4897737)). Qed.
Lemma lem4897741 : term277 = True.
Proof. exact (TRANS (@lem4897736) (@lem4897740)). Qed.
Lemma lem4897742 : True = term277.
Proof. exact (SYM (@lem4897741)). Qed.
Lemma lem4897743 : term277.
Proof. exact (EQ_MP (@lem4897742) (@lem0)). Qed.
Lemma lem4897744 : term405.
Proof. exact (@lem4897733 (@lem4897743)). Qed.
Lemma lem4897746 (m : nat) (n : nat) : (term276 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4897747 : term277 = term278.
Proof. exact (@lem4897746 (NUMERAL 0) term121). Qed.
Lemma lem4897748 : term279 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4897749 (h1 : term279 = (BIT1 0)) : term278 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4897750 : (term279 = (BIT1 0)) = (term278 = True).
Proof. exact (prop_ext (fun h1 : term279 = (BIT1 0) => @lem4897749 h1) (fun h1 : term278 = True => @lem4897748)). Qed.
Lemma lem4897751 : term278 = True.
Proof. exact (EQ_MP (@lem4897750) (@lem4897748)). Qed.
Lemma lem4897752 : term277 = True.
Proof. exact (TRANS (@lem4897747) (@lem4897751)). Qed.
Lemma lem4897753 : True = term277.
Proof. exact (SYM (@lem4897752)). Qed.
Lemma lem4897754 : term277.
Proof. exact (EQ_MP (@lem4897753) (@lem0)). Qed.
Lemma lem4897755 : term406.
Proof. exact (@lem4897744 (@lem4897754)). Qed.
Lemma lem4897757 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4897758 : term247 = term248.
Proof. exact (@lem4897757 term121 term121). Qed.
Lemma lem4897759 : (term249 = (BIT1 0)) = (term250 = term121).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4897760 : term250 = term121.
Proof. exact (EQ_MP (@lem4897759) (@lem940073)). Qed.
Lemma lem4897761 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4897762 : term248 = term208.
Proof. exact (MK_COMB (@lem4897761) (@lem4897760)). Qed.
Lemma lem4897763 : term247 = term208.
Proof. exact (TRANS (@lem4897758) (@lem4897762)). Qed.
Lemma lem4897765 (m : nat) (n : nat) : (term309 m n) = (term310 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4897766 : term350 = term351.
Proof. exact (@lem4897765 term121 term121). Qed.
Lemma lem4897767 : (term249 = (BIT1 0)) = (term250 = term121).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4897768 : term250 = term121.
Proof. exact (EQ_MP (@lem4897767) (@lem940073)). Qed.
Lemma lem4897769 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4897770 : term248 = term208.
Proof. exact (MK_COMB (@lem4897769) (@lem4897768)). Qed.
Lemma lem4897771 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4897772 : term351 = term238.
Proof. exact (MK_COMB (@lem4897771) (@lem4897770)). Qed.
Lemma lem4897773 : term350 = term238.
Proof. exact (TRANS (@lem4897766) (@lem4897772)). Qed.
Lemma lem4897774 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4897775 : term407 = term399.
Proof. exact (MK_COMB (@lem4897774) (@lem4897773)). Qed.
Lemma lem4897776 : term408 = term401.
Proof. exact (MK_COMB (@lem4897775) (@lem4897763)). Qed.
Lemma lem4897778 (m : nat) : (term409 m) = term191.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem4897779 : term401 = term191.
Proof. exact (@lem4897778 term121). Qed.
Lemma lem4897780 : term408 = term191.
Proof. exact (TRANS (@lem4897776) (@lem4897779)). Qed.
Lemma lem4897781 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4897782 : term410 = term411.
Proof. exact (MK_COMB (@lem4897781) (@lem4897780)). Qed.
Lemma lem4897783 : term208 = term208.
Proof. exact (eq_refl term208). Qed.
Lemma lem4897784 : term412 = term379.
Proof. exact (MK_COMB (@lem4897782) (@lem4897783)). Qed.
Lemma lem4897786 (x : nat) : (term378 x) = term191.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4897787 : term379 = term191.
Proof. exact (@lem4897786 term121). Qed.
Lemma lem4897788 : term412 = term191.
Proof. exact (TRANS (@lem4897784) (@lem4897787)). Qed.
Lemma lem4897790 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4897791 : term247 = term248.
Proof. exact (@lem4897790 term121 term121). Qed.
Lemma lem4897792 : (term249 = (BIT1 0)) = (term250 = term121).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4897793 : term250 = term121.
Proof. exact (EQ_MP (@lem4897792) (@lem940073)). Qed.
Lemma lem4897794 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4897795 : term248 = term208.
Proof. exact (MK_COMB (@lem4897794) (@lem4897793)). Qed.
Lemma lem4897796 : term247 = term208.
Proof. exact (TRANS (@lem4897791) (@lem4897795)). Qed.
Lemma lem4897797 : term411 = term411.
Proof. exact (eq_refl term411). Qed.
Lemma lem4897798 : term413 = term379.
Proof. exact (MK_COMB (@lem4897797) (@lem4897796)). Qed.
Lemma lem4897800 (x : nat) : (term378 x) = term191.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4897801 : term379 = term191.
Proof. exact (@lem4897800 term121). Qed.
Lemma lem4897802 : term413 = term191.
Proof. exact (TRANS (@lem4897798) (@lem4897801)). Qed.
Lemma lem4897803 : term191 = term413.
Proof. exact (SYM (@lem4897802)). Qed.
Lemma lem4897804 : term412 = term413.
Proof. exact (TRANS (@lem4897788) (@lem4897803)). Qed.
Lemma lem4897805 : term402 = term235.
Proof. exact (@lem4897755 (@lem4897804)). Qed.
Lemma lem4897806 : term401 = term235.
Proof. exact (TRANS (@lem4897721) (@lem4897805)). Qed.
Lemma lem4897808 (x : real) : (term254 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4897809 : term235 = term191.
Proof. exact (@lem4897808 term191). Qed.
Lemma lem4897810 : term401 = term191.
Proof. exact (TRANS (@lem4897806) (@lem4897809)). Qed.
Lemma lem4897811 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4897812 : term414 = term411.
Proof. exact (MK_COMB (@lem4897811) (@lem4897810)). Qed.
Lemma lem4897813 (_60486 : int) : (real_of_int _60486) = (real_of_int _60486).
Proof. exact (eq_refl (real_of_int _60486)). Qed.
Lemma lem4897814 (_60486 : int) : (term398 _60486) = (term415 _60486).
Proof. exact (MK_COMB (@lem4897812) (@lem4897813 _60486)). Qed.
Lemma lem4897815 (_60486 : int) : (term420 _60486) = (term415 _60486).
Proof. exact (TRANS (@lem4897712 _60486) (@lem4897814 _60486)). Qed.
Lemma lem4897816 (_60486 : int) : (term415 _60486) = term191.
Proof. exact (@lem1982719 (real_of_int _60486)). Qed.
Lemma lem4897817 (_60486 : int) : (term420 _60486) = term191.
Proof. exact (TRANS (@lem4897815 _60486) (@lem4897816 _60486)). Qed.
Lemma lem4897818 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4897819 (_60486 : int) : (term421 _60486) = term417.
Proof. exact (MK_COMB (@lem4897818) (@lem4897817 _60486)). Qed.
Lemma lem4897820 : term238 = term238.
Proof. exact (eq_refl term238). Qed.
Lemma lem4897821 (_60486 : int) : (term449 _60486) = term450.
Proof. exact (MK_COMB (@lem4897819 _60486) (@lem4897820)). Qed.
Lemma lem4897822 (_60486 : int) : (term448 _60486) = term450.
Proof. exact (TRANS (@lem4897711 _60486) (@lem4897821 _60486)). Qed.
Lemma lem4897823 : term450 = term238.
Proof. exact (@lem1982721 term238). Qed.
Lemma lem4897824 (_60486 : int) : (term448 _60486) = term238.
Proof. exact (TRANS (@lem4897822 _60486) (@lem4897823)). Qed.
Lemma lem4897825 (_60485 : int) (_60486 : int) : (term447 _60485 _60486) = term450.
Proof. exact (MK_COMB (@lem4897710 _60485) (@lem4897824 _60486)). Qed.
Lemma lem4897826 (_60485 : int) (_60486 : int) : (term446 _60485 _60486) = term450.
Proof. exact (TRANS (@lem4897602 _60485 _60486) (@lem4897825 _60485 _60486)). Qed.
Lemma lem4897827 : term450 = term238.
Proof. exact (@lem1982721 term238). Qed.
Lemma lem4897828 (_60485 : int) (_60486 : int) : (term446 _60485 _60486) = term238.
Proof. exact (TRANS (@lem4897826 _60485 _60486) (@lem4897827)). Qed.
Lemma lem4897829 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4897830 (_60485 : int) (_60486 : int) : (term451 _60485 _60486) = term452.
Proof. exact (MK_COMB (@lem4897829) (@lem4897828 _60485 _60486)). Qed.
Lemma lem4897831 : term191 = term191.
Proof. exact (eq_refl term191). Qed.
Lemma lem4897832 (_60485 : int) (_60486 : int) : (term445 _60485 _60486) = term453.
Proof. exact (MK_COMB (@lem4897830 _60485 _60486) (@lem4897831)). Qed.
Lemma lem4897833 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) (h1 : term438 _112846 h t _60485 _60486) : term453.
Proof. exact (EQ_MP (@lem4897832 _60485 _60486) (@lem4897601 _112846 h t _60485 _60486 h1)). Qed.
Lemma lem4897835 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem4897836 : term453 = term454.
Proof. exact (@lem4897835 term191 term238). Qed.
Lemma lem4897838 (x : nat) : (term236 x) = (term237 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4897839 : term238 = term239.
Proof. exact (@lem4897838 term121). Qed.
Lemma lem4897841 (x : nat) : (real_of_num x) = (term234 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4897842 : term191 = term235.
Proof. exact (@lem4897841 (NUMERAL 0)). Qed.
Lemma lem4897843 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4897844 : term193 = term427.
Proof. exact (MK_COMB (@lem4897843) (@lem4897842)). Qed.
Lemma lem4897845 : term454 = term455.
Proof. exact (MK_COMB (@lem4897844) (@lem4897839)). Qed.
Lemma lem4897846 : term456.
Proof. exact (@lem1980026 term191 term208 term238 term208). Qed.
Lemma lem4897848 (m : nat) (n : nat) : (term276 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4897849 : term277 = term278.
Proof. exact (@lem4897848 (NUMERAL 0) term121). Qed.
Lemma lem4897850 : term279 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4897851 (h1 : term279 = (BIT1 0)) : term278 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4897852 : (term279 = (BIT1 0)) = (term278 = True).
Proof. exact (prop_ext (fun h1 : term279 = (BIT1 0) => @lem4897851 h1) (fun h1 : term278 = True => @lem4897850)). Qed.
Lemma lem4897853 : term278 = True.
Proof. exact (EQ_MP (@lem4897852) (@lem4897850)). Qed.
Lemma lem4897854 : term277 = True.
Proof. exact (TRANS (@lem4897849) (@lem4897853)). Qed.
Lemma lem4897855 : True = term277.
Proof. exact (SYM (@lem4897854)). Qed.
Lemma lem4897856 : term277.
Proof. exact (EQ_MP (@lem4897855) (@lem0)). Qed.
Lemma lem4897857 : term457.
Proof. exact (@lem4897846 (@lem4897856)). Qed.
Lemma lem4897859 (m : nat) (n : nat) : (term276 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4897860 : term277 = term278.
Proof. exact (@lem4897859 (NUMERAL 0) term121). Qed.
Lemma lem4897861 : term279 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4897862 (h1 : term279 = (BIT1 0)) : term278 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4897863 : (term279 = (BIT1 0)) = (term278 = True).
Proof. exact (prop_ext (fun h1 : term279 = (BIT1 0) => @lem4897862 h1) (fun h1 : term278 = True => @lem4897861)). Qed.
Lemma lem4897864 : term278 = True.
Proof. exact (EQ_MP (@lem4897863) (@lem4897861)). Qed.
Lemma lem4897865 : term277 = True.
Proof. exact (TRANS (@lem4897860) (@lem4897864)). Qed.
Lemma lem4897866 : True = term277.
Proof. exact (SYM (@lem4897865)). Qed.
Lemma lem4897867 : term277.
Proof. exact (EQ_MP (@lem4897866) (@lem0)). Qed.
Lemma lem4897868 : term455 = term458.
Proof. exact (@lem4897857 (@lem4897867)). Qed.
Lemma lem4897870 (m : nat) (n : nat) : (term309 m n) = (term310 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4897871 : term350 = term351.
Proof. exact (@lem4897870 term121 term121). Qed.
Lemma lem4897872 : (term249 = (BIT1 0)) = (term250 = term121).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4897873 : term250 = term121.
Proof. exact (EQ_MP (@lem4897872) (@lem940073)). Qed.
Lemma lem4897874 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4897875 : term248 = term208.
Proof. exact (MK_COMB (@lem4897874) (@lem4897873)). Qed.
Lemma lem4897876 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4897877 : term351 = term238.
Proof. exact (MK_COMB (@lem4897876) (@lem4897875)). Qed.
Lemma lem4897878 : term350 = term238.
Proof. exact (TRANS (@lem4897871) (@lem4897877)). Qed.
Lemma lem4897880 (x : nat) : (term378 x) = term191.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4897881 : term379 = term191.
Proof. exact (@lem4897880 term121). Qed.
Lemma lem4897882 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4897883 : term432 = term193.
Proof. exact (MK_COMB (@lem4897882) (@lem4897881)). Qed.
Lemma lem4897884 : term458 = term454.
Proof. exact (MK_COMB (@lem4897883) (@lem4897878)). Qed.
Lemma lem4897886 (m : nat) (n : nat) : (term433 m n) = (term434 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem4897887 : term454 = term459.
Proof. exact (@lem4897886 (NUMERAL 0) term121). Qed.
Lemma lem4897888 : term279 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4897889 (h1 : term279 = (BIT1 0)) : (term121 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem4897890 : (term279 = (BIT1 0)) = ((term121 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term279 = (BIT1 0) => @lem4897889 h1) (fun h1 : (term121 = (NUMERAL 0)) = False => @lem4897888)). Qed.
Lemma lem4897891 : (term121 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem4897890) (@lem4897888)). Qed.
Lemma lem4897892 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem4897893 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4897894 : term437 = (and True).
Proof. exact (MK_COMB (@lem4897893) (@lem4897892)). Qed.
Lemma lem4897895 : term459 = (True /\ False).
Proof. exact (MK_COMB (@lem4897894) (@lem4897891)). Qed.
Lemma lem4897897 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem4897898 : term459 = False.
Proof. exact (TRANS (@lem4897895) (@lem4897897)). Qed.
Lemma lem4897899 : term454 = False.
Proof. exact (TRANS (@lem4897887) (@lem4897898)). Qed.
Lemma lem4897900 : term458 = False.
Proof. exact (TRANS (@lem4897884) (@lem4897899)). Qed.
Lemma lem4897901 : term455 = False.
Proof. exact (TRANS (@lem4897868) (@lem4897900)). Qed.
Lemma lem4897902 : term454 = False.
Proof. exact (TRANS (@lem4897845) (@lem4897901)). Qed.
Lemma lem4897903 : term453 = False.
Proof. exact (TRANS (@lem4897836) (@lem4897902)). Qed.
Lemma lem4897904 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) (h1 : term438 _112846 h t _60485 _60486) : False.
Proof. exact (EQ_MP (@lem4897903) (@lem4897833 _112846 h t _60485 _60486 h1)). Qed.
Lemma lem4897905 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) (h1 : term367 _112846 h t _60485 _60486) : False.
Proof. exact (or_elim (@lem4896973 _112846 h t _60485 _60486 h1) (fun h0 : term370 _112846 h t _60485 _60486 => @lem4897439 _112846 h t _60485 _60486 h0) (fun h0 : term438 _112846 h t _60485 _60486 => @lem4897904 _112846 h t _60485 _60486 h0)). Qed.
Lemma lem4897907 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) (h1 : term367 _112846 h t _60485 _60486) : term367 _112846 h t _60485 _60486.
Proof. exact (h1). Qed.
Lemma lem4897908 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) (h1 : term367 _112846 h t _60485 _60486) : (term367 _112846 h t _60485 _60486) = False.
Proof. exact (prop_ext (fun h2 : term367 _112846 h t _60485 _60486 => @lem4897905 _112846 h t _60485 _60486 h1) (fun h2 : False => @lem4897907 _112846 h t _60485 _60486 h1)). Qed.
Lemma lem4897909 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) (h1 : term367 _112846 h t _60485 _60486) : False.
Proof. exact (EQ_MP (@lem4897908 _112846 h t _60485 _60486 h1) (@lem4897907 _112846 h t _60485 _60486 h1)). Qed.
Lemma lem4897910 {_112846 : Type'} (h : _112846) (t : list _112846) (_60486 : int) (_60485 : int) (h1 : term230 _112846 h t _60486 _60485) : term230 _112846 h t _60486 _60485.
Proof. exact (h1). Qed.
Lemma lem4897911 {_112846 : Type'} (h : _112846) (t : list _112846) (_60486 : int) (_60485 : int) (h1 : term230 _112846 h t _60486 _60485) : term367 _112846 h t _60485 _60486.
Proof. exact (EQ_MP (@lem4896963 _112846 h t _60485 _60486) (@lem4897910 _112846 h t _60486 _60485 h1)). Qed.
Lemma lem4897912 {_112846 : Type'} (h : _112846) (t : list _112846) (_60486 : int) (_60485 : int) (h1 : term230 _112846 h t _60486 _60485) : (term367 _112846 h t _60485 _60486) = False.
Proof. exact (prop_ext (fun h2 : term367 _112846 h t _60485 _60486 => @lem4897909 _112846 h t _60485 _60486 h2) (fun h2 : False => @lem4897911 _112846 h t _60486 _60485 h1)). Qed.
Lemma lem4897913 {_112846 : Type'} (h : _112846) (t : list _112846) (_60486 : int) (_60485 : int) (h1 : term230 _112846 h t _60486 _60485) : False.
Proof. exact (EQ_MP (@lem4897912 _112846 h t _60486 _60485 h1) (@lem4897911 _112846 h t _60486 _60485 h1)). Qed.
Lemma lem4897914 {_112846 : Type'} (h : _112846) (t : list _112846) (_60486 : int) (_60485 : int) : term460 _112846 h t _60486 _60485.
Proof. exact (fun h0 : term230 _112846 h t _60486 _60485 => @lem4897913 _112846 h t _60486 _60485 h0). Qed.
Lemma lem4897915 {_112846 : Type'} (h : _112846) (t : list _112846) (_60486 : int) (_60485 : int) : term461 _112846 h t _60486 _60485.
Proof. exact (@lem1386578 (term462 _112846 h t _60486 _60485)). Qed.
Lemma lem4897918 {_112846 : Type'} (h : _112846) (t : list _112846) (_60486 : int) (_60485 : int) : term462 _112846 h t _60486 _60485.
Proof. exact (@lem4897915 _112846 h t _60486 _60485 (@lem4897914 _112846 h t _60486 _60485)). Qed.
Lemma lem4897919 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) : (term229 _112846 h t _60486 _60485) = (term184 _112846 h t _60485 _60486).
Proof. exact (SYM (@lem4896148 _112846 h t _60486 _60485)). Qed.
Lemma lem4897920 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4897921 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) : (term462 _112846 h t _60486 _60485) = (term140 _112846 h t _60485 _60486).
Proof. exact (MK_COMB (@lem4897920) (@lem4897919 _112846 h t _60485 _60486)). Qed.
Lemma lem4897922 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) : term140 _112846 h t _60485 _60486.
Proof. exact (EQ_MP (@lem4897921 _112846 h t _60485 _60486) (@lem4897918 _112846 h t _60486 _60485)). Qed.
Lemma lem4897923 {_112846 : Type'} (h : _112846) (t : list _112846) (_60485 : int) (_60486 : int) : term141 _112846 h t _60485 _60486.
Proof. exact (EQ_MP (@lem4895909 _112846 h t _60485 _60486) (@lem4897922 _112846 h t _60485 _60486)). Qed.
Lemma lem4897924 {_112846 : Type'} (h : _112846) (t : list _112846) : term463 _112846 h t.
Proof. exact (@lem4897923 _112846 h t (term464 _112846 t) (term465 _112846 t)). Qed.
Lemma lem4897925 {_112846 : Type'} (h : _112846) (t : list _112846) : term466 _112846 h t.
Proof. exact (@lem4897924 _112846 h t (@lem4895905 _112846 t)). Qed.
Lemma lem4897926 {_112846 : Type'} (h : _112846) (t : list _112846) : term135 _112846 h t.
Proof. exact (@lem4897925 _112846 h t (@lem4895908 _112846 t)). Qed.
Lemma lem4897927 {_112846 : Type'} (h : _112846) (t : list _112846) : (term135 _112846 h t) = (term74 _112846 h t).
Proof. exact (SYM (@lem4895902 _112846 h t)). Qed.
Lemma lem4897928 {_112846 : Type'} (h : _112846) (t : list _112846) : term74 _112846 h t.
Proof. exact (EQ_MP (@lem4897927 _112846 h t) (@lem4897926 _112846 h t)). Qed.
Lemma lem4897929 {_112846 : Type'} (h : _112846) (t : list _112846) : (term74 _112846 h t) = ((term74 _112846 h t) = True).
Proof. exact (@lem7 (term74 _112846 h t)). Qed.
Lemma lem4897930 {_112846 : Type'} (h : _112846) (t : list _112846) : (term74 _112846 h t) = True.
Proof. exact (EQ_MP (@lem4897929 _112846 h t) (@lem4897928 _112846 h t)). Qed.
Lemma lem4897931 {_112846 : Type'} (h : _112846) (t : list _112846) : True = (term74 _112846 h t).
Proof. exact (SYM (@lem4897930 _112846 h t)). Qed.
Lemma lem4897932 {_112846 : Type'} (h : _112846) (t : list _112846) : term74 _112846 h t.
Proof. exact (EQ_MP (@lem4897931 _112846 h t) (@lem0)). Qed.
Lemma lem4897933 {_112846 : Type'} (h : _112846) (t : list _112846) (h1 : term23 _112846 t) : term58 _112846 h t.
Proof. exact (@lem4897932 _112846 h t (@lem4895409 _112846 t h1)). Qed.
Lemma lem4897934 {_112846 : Type'} (h : _112846) (t : list _112846) (h1 : term23 _112846 t) : term27 _112846 h t.
Proof. exact (EQ_MP (@lem4895548 _112846 h t) (@lem4897933 _112846 h t h1)). Qed.
Lemma lem4897935 {_112846 : Type'} : term19 _112846.
Proof. exact (EQ_MP (@lem4895425 _112846) (@lem4895621)). Qed.
Lemma lem4897936 {_112846 : Type'} (h : _112846) (t : list _112846) : term29 _112846 h t.
Proof. exact (fun h0 : term23 _112846 t => @lem4897934 _112846 h t h0). Qed.
Lemma lem4897941 {_112846 : Type'} (h : _112846) : term33 _112846 h.
Proof. exact (fun t : list _112846 => @lem4897936 _112846 h t). Qed.
Lemma lem4897946 {_112846 : Type'} : term37 _112846.
Proof. exact (fun h : _112846 => @lem4897941 _112846 h). Qed.
Lemma lem4897947 {_112846 : Type'} : term39 _112846.
Proof. exact (conj (@lem4897935 _112846) (@lem4897946 _112846)). Qed.
Lemma lem4897948 {_112846 : Type'} : term44 _112846.
Proof. exact (@lem4895408 _112846 (@lem4897947 _112846)). Qed.
