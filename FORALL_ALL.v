Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_ALL_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1100834_spec.
Require Import thm1100835_spec.
Require Import thm1100843_spec.
Require Import thm1100844_spec.
Require Import thm16445_spec.
Require Import thm16446_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17500_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm18392_spec.
Require Import thm1855_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19792_spec.
Require Import thm20230_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Lemma lem1142395 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1142396 {_26916 : Type'} (P : type1143 _26916) : term0 _26916 P.
Proof. exact (@lem1142395 _26916 P). Qed.
Lemma lem1142397 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) : term1 _26916 _26917 P.
Proof. exact (@lem1142396 _26916 (term2 _26916 _26917 P)). Qed.
Lemma lem1142398 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) : (term3 _26916 _26917 P) = ((term4 _26916 _26917 P) = (term5 _26916 _26917 P)).
Proof. exact (eq_refl (term3 _26916 _26917 P)). Qed.
Lemma lem1142399 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1142400 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) : (term6 _26916 _26917 P) = (term7 _26916 _26917 P).
Proof. exact (MK_COMB (@lem1142399) (@lem1142398 _26916 _26917 P)). Qed.
Lemma lem1142401 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term8 _26916 _26917 P t) = ((term9 _26916 _26917 P t) = (term10 _26916 _26917 P t)).
Proof. exact (eq_refl (term8 _26916 _26917 P t)). Qed.
Lemma lem1142402 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1142403 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term11 _26916 _26917 P t) = (term12 _26916 _26917 P t).
Proof. exact (MK_COMB (@lem1142402) (@lem1142401 _26916 _26917 P t)). Qed.
Lemma lem1142404 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) (t : list _26916) : (term13 _26916 _26917 P h t) = ((term14 _26916 _26917 P h t) = (term15 _26916 _26917 P h t)).
Proof. exact (eq_refl (term13 _26916 _26917 P h t)). Qed.
Lemma lem1142405 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) (t : list _26916) : (term16 _26916 _26917 P h t) = (term17 _26916 _26917 P h t).
Proof. exact (MK_COMB (@lem1142403 _26916 _26917 P t) (@lem1142404 _26916 _26917 P h t)). Qed.
Lemma lem1142406 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term18 _26916 _26917 P h) = (term19 _26916 _26917 P h).
Proof. exact (fun_ext (fun t : list _26916 => @lem1142405 _26916 _26917 P h t)). Qed.
Lemma lem1142407 {_26916 : Type'} : (@all (list _26916)) = (@all (list _26916)).
Proof. exact (eq_refl (@all (list _26916))). Qed.
Lemma lem1142408 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term20 _26916 _26917 P h) = (term21 _26916 _26917 P h).
Proof. exact (MK_COMB (@lem1142407 _26916) (@lem1142406 _26916 _26917 P h)). Qed.
Lemma lem1142409 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) : (term22 _26916 _26917 P) = (term23 _26916 _26917 P).
Proof. exact (fun_ext (fun h : _26916 => @lem1142408 _26916 _26917 P h)). Qed.
Lemma lem1142410 {_26916 : Type'} : (@all _26916) = (@all _26916).
Proof. exact (eq_refl (@all _26916)). Qed.
Lemma lem1142411 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) : (term24 _26916 _26917 P) = (term25 _26916 _26917 P).
Proof. exact (MK_COMB (@lem1142410 _26916) (@lem1142409 _26916 _26917 P)). Qed.
Lemma lem1142412 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) : (term26 _26916 _26917 P) = (term27 _26916 _26917 P).
Proof. exact (MK_COMB (@lem1142400 _26916 _26917 P) (@lem1142411 _26916 _26917 P)). Qed.
Lemma lem1142413 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1142414 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) : (term28 _26916 _26917 P) = (term29 _26916 _26917 P).
Proof. exact (MK_COMB (@lem1142413) (@lem1142412 _26916 _26917 P)). Qed.
Lemma lem1142415 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (l : list _26916) : (term8 _26916 _26917 P l) = ((term9 _26916 _26917 P l) = (term10 _26916 _26917 P l)).
Proof. exact (eq_refl (term8 _26916 _26917 P l)). Qed.
Lemma lem1142416 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) : (term30 _26916 _26917 P) = (term2 _26916 _26917 P).
Proof. exact (fun_ext (fun l : list _26916 => @lem1142415 _26916 _26917 P l)). Qed.
Lemma lem1142417 {_26916 : Type'} : (@all (list _26916)) = (@all (list _26916)).
Proof. exact (eq_refl (@all (list _26916))). Qed.
Lemma lem1142418 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) : (term31 _26916 _26917 P) = (term32 _26916 _26917 P).
Proof. exact (MK_COMB (@lem1142417 _26916) (@lem1142416 _26916 _26917 P)). Qed.
Lemma lem1142419 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) : (term1 _26916 _26917 P) = (term33 _26916 _26917 P).
Proof. exact (MK_COMB (@lem1142414 _26916 _26917 P) (@lem1142418 _26916 _26917 P)). Qed.
Lemma lem1142420 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) : term33 _26916 _26917 P.
Proof. exact (EQ_MP (@lem1142419 _26916 _26917 P) (@lem1142397 _26916 _26917 P)). Qed.
Lemma lem1142421 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) (h1 : (term9 _26916 _26917 P t) = (term10 _26916 _26917 P t)) : (term9 _26916 _26917 P t) = (term10 _26916 _26917 P t).
Proof. exact (h1). Qed.
Lemma lem1142431 {_25307 : Type'} (P : _25307 -> Prop) : (@List.Forall _25307 P (@nil _25307)) = True.
Proof. exact (EQ_MP (@lem1100835 _25307 P) (@lem1100834 _25307 P)). Qed.
Lemma lem1142432 {_26916 : Type'} (P : _26916 -> Prop) : (@List.Forall _26916 P (@nil _26916)) = True.
Proof. exact (@lem1142431 _26916 P). Qed.
Lemma lem1142433 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) : (term34 _26916 _26917 P x) = True.
Proof. exact (@lem1142432 _26916 (P x)). Qed.
Lemma lem1142434 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) : (term35 _26916 _26917 P) = (term36 _26917).
Proof. exact (fun_ext (fun x : _26917 => @lem1142433 _26916 _26917 P x)). Qed.
Lemma lem1142435 {_26917 : Type'} : (@all _26917) = (@all _26917).
Proof. exact (eq_refl (@all _26917)). Qed.
Lemma lem1142436 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) : (term4 _26916 _26917 P) = (term37 _26917).
Proof. exact (MK_COMB (@lem1142435 _26917) (@lem1142434 _26916 _26917 P)). Qed.
Lemma lem1142438 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1142439 {_26917 : Type'} (t : Prop) : (term38 _26917 t) = t.
Proof. exact (@lem1142438 _26917 t). Qed.
Lemma lem1142440 {_26917 : Type'} : (term37 _26917) = True.
Proof. exact (@lem1142439 _26917 True). Qed.
Lemma lem1142441 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) : (term4 _26916 _26917 P) = True.
Proof. exact (TRANS (@lem1142436 _26916 _26917 P) (@lem1142440 _26917)). Qed.
Lemma lem1142442 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1142443 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) : (term39 _26916 _26917 P) = (@eq Prop True).
Proof. exact (MK_COMB (@lem1142442) (@lem1142441 _26916 _26917 P)). Qed.
Lemma lem1142445 {_25307 : Type'} (P : _25307 -> Prop) : (@List.Forall _25307 P (@nil _25307)) = True.
Proof. exact (EQ_MP (@lem1100835 _25307 P) (@lem1100834 _25307 P)). Qed.
Lemma lem1142446 {_26916 : Type'} (P : _26916 -> Prop) : (@List.Forall _26916 P (@nil _26916)) = True.
Proof. exact (@lem1142445 _26916 P). Qed.
Lemma lem1142447 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) : (term5 _26916 _26917 P) = True.
Proof. exact (@lem1142446 _26916 (term40 _26916 _26917 P)). Qed.
Lemma lem1142448 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) : ((term4 _26916 _26917 P) = (term5 _26916 _26917 P)) = (True = True).
Proof. exact (MK_COMB (@lem1142443 _26916 _26917 P) (@lem1142447 _26916 _26917 P)). Qed.
Lemma lem1142450 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1142451 : (True = True) = True.
Proof. exact (@lem1142450 True). Qed.
Lemma lem1142452 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) : ((term4 _26916 _26917 P) = (term5 _26916 _26917 P)) = True.
Proof. exact (TRANS (@lem1142448 _26916 _26917 P) (@lem1142451)). Qed.
Lemma lem1142453 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) : True = ((term4 _26916 _26917 P) = (term5 _26916 _26917 P)).
Proof. exact (SYM (@lem1142452 _26916 _26917 P)). Qed.
Lemma lem1142454 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) : (term4 _26916 _26917 P) = (term5 _26916 _26917 P).
Proof. exact (EQ_MP (@lem1142453 _26916 _26917 P) (@lem0)). Qed.
Lemma lem1142464 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (t : list _25307) : (term41 _25307 P h t) = (term42 _25307 h P t).
Proof. exact (EQ_MP (@lem1100844 _25307 h P t) (@lem1100843 _25307 h P t)). Qed.
Lemma lem1142465 {_26916 : Type'} (h : _26916) (P : _26916 -> Prop) (t : list _26916) : (term41 _26916 P h t) = (term42 _26916 h P t).
Proof. exact (@lem1142464 _26916 h P t). Qed.
Lemma lem1142466 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term43 _26916 _26917 P x h t) = (term44 _26916 _26917 h P x t).
Proof. exact (@lem1142465 _26916 h (P x) t). Qed.
Lemma lem1142469 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term45 _26916 _26917 P h t) = (term46 _26916 _26917 h P t).
Proof. exact (fun_ext (fun x : _26917 => @lem1142466 _26916 _26917 h P x t)). Qed.
Lemma lem1142470 {_26917 : Type'} : (@all _26917) = (@all _26917).
Proof. exact (eq_refl (@all _26917)). Qed.
Lemma lem1142471 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term14 _26916 _26917 P h t) = (term47 _26916 _26917 h P t).
Proof. exact (MK_COMB (@lem1142470 _26917) (@lem1142469 _26916 _26917 h P t)). Qed.
Lemma lem1142476 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1142477 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term48 _26916 _26917 P h t) = (term49 _26916 _26917 h P t).
Proof. exact (MK_COMB (@lem1142476) (@lem1142471 _26916 _26917 h P t)). Qed.
Lemma lem1142479 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (t : list _25307) : (term41 _25307 P h t) = (term42 _25307 h P t).
Proof. exact (EQ_MP (@lem1100844 _25307 h P t) (@lem1100843 _25307 h P t)). Qed.
Lemma lem1142480 {_26916 : Type'} (h : _26916) (P : _26916 -> Prop) (t : list _26916) : (term41 _26916 P h t) = (term42 _26916 h P t).
Proof. exact (@lem1142479 _26916 h P t). Qed.
Lemma lem1142481 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term15 _26916 _26917 P h t) = (term50 _26916 _26917 h P t).
Proof. exact (@lem1142480 _26916 h (term40 _26916 _26917 P) t). Qed.
Lemma lem1142485 {A B : Type'} (f : A -> B) (y : A) : (term51 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1142486 {_26916 : Type'} (f : _26916 -> Prop) (y : _26916) : (term52 _26916 f y) = (f y).
Proof. exact (@lem1142485 _26916 Prop f y). Qed.
Lemma lem1142487 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term53 _26916 _26917 P h) = (term54 _26916 _26917 P h).
Proof. exact (@lem1142486 _26916 (term40 _26916 _26917 P) h). Qed.
Lemma lem1142488 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (s : _26916) : (term54 _26916 _26917 P s) = (term55 _26916 _26917 P s).
Proof. exact (eq_refl (term54 _26916 _26917 P s)). Qed.
Lemma lem1142489 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) : (term56 _26916 _26917 P) = (term40 _26916 _26917 P).
Proof. exact (fun_ext (fun s : _26916 => @lem1142488 _26916 _26917 P s)). Qed.
Lemma lem1142490 {_26916 : Type'} (h : _26916) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1142491 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term53 _26916 _26917 P h) = (term54 _26916 _26917 P h).
Proof. exact (MK_COMB (@lem1142489 _26916 _26917 P) (@lem1142490 _26916 h)). Qed.
Lemma lem1142492 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1142493 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term57 _26916 _26917 P h) = (term58 _26916 _26917 P h).
Proof. exact (MK_COMB (@lem1142492) (@lem1142491 _26916 _26917 P h)). Qed.
Lemma lem1142494 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term54 _26916 _26917 P h) = (term55 _26916 _26917 P h).
Proof. exact (eq_refl (term54 _26916 _26917 P h)). Qed.
Lemma lem1142495 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : ((term53 _26916 _26917 P h) = (term54 _26916 _26917 P h)) = ((term54 _26916 _26917 P h) = (term55 _26916 _26917 P h)).
Proof. exact (MK_COMB (@lem1142493 _26916 _26917 P h) (@lem1142494 _26916 _26917 P h)). Qed.
Lemma lem1142496 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term54 _26916 _26917 P h) = (term55 _26916 _26917 P h).
Proof. exact (EQ_MP (@lem1142495 _26916 _26917 P h) (@lem1142487 _26916 _26917 P h)). Qed.
Lemma lem1142501 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1142502 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term59 _26916 _26917 P h) = (term60 _26916 _26917 P h).
Proof. exact (MK_COMB (@lem1142501) (@lem1142496 _26916 _26917 P h)). Qed.
Lemma lem1142507 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term10 _26916 _26917 P t) = (term10 _26916 _26917 P t).
Proof. exact (eq_refl (term10 _26916 _26917 P t)). Qed.
Lemma lem1142508 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term50 _26916 _26917 h P t) = (term61 _26916 _26917 h P t).
Proof. exact (MK_COMB (@lem1142502 _26916 _26917 P h) (@lem1142507 _26916 _26917 P t)). Qed.
Lemma lem1142511 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term15 _26916 _26917 P h t) = (term61 _26916 _26917 h P t).
Proof. exact (TRANS (@lem1142481 _26916 _26917 h P t) (@lem1142508 _26916 _26917 h P t)). Qed.
Lemma lem1142512 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : ((term14 _26916 _26917 P h t) = (term15 _26916 _26917 P h t)) = ((term47 _26916 _26917 h P t) = (term61 _26916 _26917 h P t)).
Proof. exact (MK_COMB (@lem1142477 _26916 _26917 h P t) (@lem1142511 _26916 _26917 h P t)). Qed.
Lemma lem1142515 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) (t : list _26916) : ((term47 _26916 _26917 h P t) = (term61 _26916 _26917 h P t)) = ((term14 _26916 _26917 P h t) = (term15 _26916 _26917 P h t)).
Proof. exact (SYM (@lem1142512 _26916 _26917 h P t)). Qed.
Lemma lem1142517 (p : Prop) : p = (term62 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1142518 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : ((term47 _26916 _26917 h P t) = (term61 _26916 _26917 h P t)) = (term63 _26916 _26917 h P t).
Proof. exact (@lem1142517 ((term47 _26916 _26917 h P t) = (term61 _26916 _26917 h P t))). Qed.
Lemma lem1142519 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term63 _26916 _26917 h P t) = ((term47 _26916 _26917 h P t) = (term61 _26916 _26917 h P t)).
Proof. exact (SYM (@lem1142518 _26916 _26917 h P t)). Qed.
Lemma lem1142520 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term64 _26916 _26917 h P t) : term64 _26916 _26917 h P t.
Proof. exact (h1). Qed.
Lemma lem1142523 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term65 _26916 _26917 h P t) : term65 _26916 _26917 h P t.
Proof. exact (h1). Qed.
Lemma lem1142524 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : term66 _26916 _26917 h P t.
Proof. exact (fun h0 : term65 _26916 _26917 h P t => @lem1142523 _26916 _26917 h P t h0). Qed.
Lemma lem1142525 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term66 _26916 _26917 h P t) : term66 _26916 _26917 h P t.
Proof. exact (h1). Qed.
Lemma lem1142526 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term65 _26916 _26917 h P t) : term65 _26916 _26917 h P t.
Proof. exact (h1). Qed.
Lemma lem1142527 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term65 _26916 _26917 h P t) (h2 : term66 _26916 _26917 h P t) : term65 _26916 _26917 h P t.
Proof. exact (@lem1142525 _26916 _26917 h P t h2 (@lem1142526 _26916 _26917 h P t h1)). Qed.
Lemma lem1142528 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term65 _26916 _26917 h P t) : term67 _26916 _26917 h P t.
Proof. exact (fun h0 : term66 _26916 _26917 h P t => @lem1142527 _26916 _26917 h P t h1 h0). Qed.
Lemma lem1142529 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term66 _26916 _26917 h P t) : term66 _26916 _26917 h P t.
Proof. exact (h1). Qed.
Lemma lem1142530 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term65 _26916 _26917 h P t) (h2 : term66 _26916 _26917 h P t) : term65 _26916 _26917 h P t.
Proof. exact (@lem1142528 _26916 _26917 h P t h1 (@lem1142529 _26916 _26917 h P t h2)). Qed.
Lemma lem1142531 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term66 _26916 _26917 h P t) : term66 _26916 _26917 h P t.
Proof. exact (fun h0 : term65 _26916 _26917 h P t => @lem1142530 _26916 _26917 h P t h0 h1). Qed.
Lemma lem1142532 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : term68 _26916 _26917 h P t.
Proof. exact (fun h0 : term66 _26916 _26917 h P t => @lem1142531 _26916 _26917 h P t h0). Qed.
Lemma lem1142535 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : term66 _26916 _26917 h P t.
Proof. exact (@lem1142532 _26916 _26917 h P t (@lem1142524 _26916 _26917 h P t)). Qed.
Lemma lem1142536 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : term66 _26916 _26917 h P t.
Proof. exact (@lem1142535 _26916 _26917 h P t). Qed.
Lemma lem1142560 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1142561 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term63 _26916 _26917 h P t) = (term69 _26916 _26917 h P t).
Proof. exact (@lem1142560 (term64 _26916 _26917 h P t)). Qed.
Lemma lem1142563 (t : Prop) : (term70 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1142564 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term69 _26916 _26917 h P t) = ((term47 _26916 _26917 h P t) = (term61 _26916 _26917 h P t)).
Proof. exact (@lem1142563 ((term47 _26916 _26917 h P t) = (term61 _26916 _26917 h P t))). Qed.
Lemma lem1142565 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term63 _26916 _26917 h P t) = ((term47 _26916 _26917 h P t) = (term61 _26916 _26917 h P t)).
Proof. exact (TRANS (@lem1142561 _26916 _26917 h P t) (@lem1142564 _26916 _26917 h P t)). Qed.
Lemma lem1142567 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term71 A P Q) = (term72 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem1142568 {_26917 : Type'} (P : _26917 -> Prop) (Q : _26917 -> Prop) : (term71 _26917 P Q) = (term72 _26917 P Q).
Proof. exact (@lem1142567 _26917 P Q). Qed.
Lemma lem1142569 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term73 _26916 _26917 h P t) = (term74 _26916 _26917 h P t).
Proof. exact (@lem1142568 _26917 (term75 _26916 _26917 P h) (term76 _26916 _26917 P t)). Qed.
Lemma lem1142570 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (term77 _26916 _26917 P h x) = (P x h).
Proof. exact (eq_refl (term77 _26916 _26917 P h x)). Qed.
Lemma lem1142571 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1142572 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (term78 _26916 _26917 P h x) = (term79 _26916 _26917 P x h).
Proof. exact (MK_COMB (@lem1142571) (@lem1142570 _26916 _26917 P x h)). Qed.
Lemma lem1142573 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term80 _26916 _26917 P t x) = (term81 _26916 _26917 P x t).
Proof. exact (eq_refl (term80 _26916 _26917 P t x)). Qed.
Lemma lem1142574 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term82 _26916 _26917 h P t x) = (term44 _26916 _26917 h P x t).
Proof. exact (MK_COMB (@lem1142572 _26916 _26917 P x h) (@lem1142573 _26916 _26917 P x t)). Qed.
Lemma lem1142575 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term83 _26916 _26917 h P t) = (term46 _26916 _26917 h P t).
Proof. exact (fun_ext (fun x : _26917 => @lem1142574 _26916 _26917 h P x t)). Qed.
Lemma lem1142576 {_26917 : Type'} : (@all _26917) = (@all _26917).
Proof. exact (eq_refl (@all _26917)). Qed.
Lemma lem1142577 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term73 _26916 _26917 h P t) = (term47 _26916 _26917 h P t).
Proof. exact (MK_COMB (@lem1142576 _26917) (@lem1142575 _26916 _26917 h P t)). Qed.
Lemma lem1142578 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1142579 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term84 _26916 _26917 h P t) = (term49 _26916 _26917 h P t).
Proof. exact (MK_COMB (@lem1142578) (@lem1142577 _26916 _26917 h P t)). Qed.
Lemma lem1142580 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (term77 _26916 _26917 P h x) = (P x h).
Proof. exact (eq_refl (term77 _26916 _26917 P h x)). Qed.
Lemma lem1142581 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term85 _26916 _26917 P h) = (term75 _26916 _26917 P h).
Proof. exact (fun_ext (fun x : _26917 => @lem1142580 _26916 _26917 P x h)). Qed.
Lemma lem1142582 {_26917 : Type'} : (@all _26917) = (@all _26917).
Proof. exact (eq_refl (@all _26917)). Qed.
Lemma lem1142583 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term86 _26916 _26917 P h) = (term55 _26916 _26917 P h).
Proof. exact (MK_COMB (@lem1142582 _26917) (@lem1142581 _26916 _26917 P h)). Qed.
Lemma lem1142584 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1142585 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term87 _26916 _26917 P h) = (term60 _26916 _26917 P h).
Proof. exact (MK_COMB (@lem1142584) (@lem1142583 _26916 _26917 P h)). Qed.
Lemma lem1142586 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term80 _26916 _26917 P t x) = (term81 _26916 _26917 P x t).
Proof. exact (eq_refl (term80 _26916 _26917 P t x)). Qed.
Lemma lem1142587 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term88 _26916 _26917 P t) = (term76 _26916 _26917 P t).
Proof. exact (fun_ext (fun x : _26917 => @lem1142586 _26916 _26917 P x t)). Qed.
Lemma lem1142588 {_26917 : Type'} : (@all _26917) = (@all _26917).
Proof. exact (eq_refl (@all _26917)). Qed.
Lemma lem1142589 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term89 _26916 _26917 P t) = (term9 _26916 _26917 P t).
Proof. exact (MK_COMB (@lem1142588 _26917) (@lem1142587 _26916 _26917 P t)). Qed.
Lemma lem1142590 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term74 _26916 _26917 h P t) = (term90 _26916 _26917 h P t).
Proof. exact (MK_COMB (@lem1142585 _26916 _26917 P h) (@lem1142589 _26916 _26917 P t)). Qed.
Lemma lem1142591 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : ((term73 _26916 _26917 h P t) = (term74 _26916 _26917 h P t)) = ((term47 _26916 _26917 h P t) = (term90 _26916 _26917 h P t)).
Proof. exact (MK_COMB (@lem1142579 _26916 _26917 h P t) (@lem1142590 _26916 _26917 h P t)). Qed.
Lemma lem1142592 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term47 _26916 _26917 h P t) = (term90 _26916 _26917 h P t).
Proof. exact (EQ_MP (@lem1142591 _26916 _26917 h P t) (@lem1142569 _26916 _26917 h P t)). Qed.
Lemma lem1142603 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1142604 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term49 _26916 _26917 h P t) = (term91 _26916 _26917 h P t).
Proof. exact (MK_COMB (@lem1142603) (@lem1142592 _26916 _26917 h P t)). Qed.
Lemma lem1142615 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term61 _26916 _26917 h P t) = (term61 _26916 _26917 h P t).
Proof. exact (eq_refl (term61 _26916 _26917 h P t)). Qed.
Lemma lem1142616 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : ((term47 _26916 _26917 h P t) = (term61 _26916 _26917 h P t)) = ((term90 _26916 _26917 h P t) = (term61 _26916 _26917 h P t)).
Proof. exact (MK_COMB (@lem1142604 _26916 _26917 h P t) (@lem1142615 _26916 _26917 h P t)). Qed.
Lemma lem1142617 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term63 _26916 _26917 h P t) = ((term90 _26916 _26917 h P t) = (term61 _26916 _26917 h P t)).
Proof. exact (TRANS (@lem1142565 _26916 _26917 h P t) (@lem1142616 _26916 _26917 h P t)). Qed.
Lemma lem1142618 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term12 _26916 _26917 P t) = (term12 _26916 _26917 P t).
Proof. exact (eq_refl (term12 _26916 _26917 P t)). Qed.
Lemma lem1142619 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term65 _26916 _26917 h P t) = (term92 _26916 _26917 h P t).
Proof. exact (MK_COMB (@lem1142618 _26916 _26917 P t) (@lem1142617 _26916 _26917 h P t)). Qed.
Lemma lem1142622 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term93 _26916 _26917 P t) = (term94 _26916 _26917 P t).
Proof. exact (fun_ext (fun h : _26916 => @lem1142619 _26916 _26917 h P t)). Qed.
Lemma lem1142623 {_26916 : Type'} : (@all _26916) = (@all _26916).
Proof. exact (eq_refl (@all _26916)). Qed.
Lemma lem1142624 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term95 _26916 _26917 P t) = (term96 _26916 _26917 P t).
Proof. exact (MK_COMB (@lem1142623 _26916) (@lem1142622 _26916 _26917 P t)). Qed.
Lemma lem1142629 {_26916 _26917 : Type'} (t : list _26916) : (term97 _26916 _26917 t) = (term98 _26916 _26917 t).
Proof. exact (fun_ext (fun P : type1470 _26916 _26917 => @lem1142624 _26916 _26917 P t)). Qed.
Lemma lem1142630 {_26916 _26917 : Type'} : (@all (_26917 -> _26916 -> Prop)) = (@all (_26917 -> _26916 -> Prop)).
Proof. exact (eq_refl (@all (_26917 -> _26916 -> Prop))). Qed.
Lemma lem1142631 {_26916 _26917 : Type'} (t : list _26916) : (term99 _26916 _26917 t) = (term100 _26916 _26917 t).
Proof. exact (MK_COMB (@lem1142630 _26916 _26917) (@lem1142629 _26916 _26917 t)). Qed.
Lemma lem1142636 {_26916 _26917 : Type'} : (term101 _26916 _26917) = (term102 _26916 _26917).
Proof. exact (fun_ext (fun t : list _26916 => @lem1142631 _26916 _26917 t)). Qed.
Lemma lem1142637 {_26916 : Type'} : (@all (list _26916)) = (@all (list _26916)).
Proof. exact (eq_refl (@all (list _26916))). Qed.
Lemma lem1142644 {_26916 _26917 : Type'} : (term103 _26916 _26917) = (term104 _26916 _26917).
Proof. exact (MK_COMB (@lem1142637 _26916) (@lem1142636 _26916 _26917)). Qed.
Lemma lem1142645 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (h1 : _18906 = (term105 _26916 _26917)) : _18906 = (term105 _26916 _26917).
Proof. exact (h1). Qed.
Lemma lem1142646 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1142647 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (_18906 : type740 _26916 _26917) (h1 : _18906 = (term105 _26916 _26917)) : (_18906 P) = (term106 _26916 _26917 P).
Proof. exact (MK_COMB (@lem1142645 _26916 _26917 _18906 h1) (@lem1142646 _26916 _26917 P)). Qed.
Lemma lem1142648 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) : (term106 _26916 _26917 P) = (term40 _26916 _26917 P).
Proof. exact (eq_refl (term106 _26916 _26917 P)). Qed.
Lemma lem1142649 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term107 _26916 _26917 _18906 P) = (term107 _26916 _26917 _18906 P).
Proof. exact (eq_refl (term107 _26916 _26917 _18906 P)). Qed.
Lemma lem1142650 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : ((_18906 P) = (term106 _26916 _26917 P)) = ((_18906 P) = (term40 _26916 _26917 P)).
Proof. exact (MK_COMB (@lem1142649 _26916 _26917 _18906 P) (@lem1142648 _26916 _26917 P)). Qed.
Lemma lem1142651 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (_18906 : type740 _26916 _26917) (h1 : _18906 = (term105 _26916 _26917)) : (_18906 P) = (term40 _26916 _26917 P).
Proof. exact (EQ_MP (@lem1142650 _26916 _26917 _18906 P) (@lem1142647 _26916 _26917 P _18906 h1)). Qed.
Lemma lem1142653 {_26916 : Type'} (t : list _26916) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1142655 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (_18906 : type740 _26916 _26917) (h1 : _18906 = (term105 _26916 _26917)) : (term40 _26916 _26917 P) = (_18906 P).
Proof. exact (SYM (@lem1142651 _26916 _26917 P _18906 h1)). Qed.
Lemma lem1142656 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (_18906 : type740 _26916 _26917) (h1 : _18906 = (term105 _26916 _26917)) : (term40 _26916 _26917 P) = (_18906 P).
Proof. exact (@lem1142655 _26916 _26917 P _18906 h1). Qed.
Lemma lem1142657 {_26916 : Type'} : (@List.Forall _26916) = (@List.Forall _26916).
Proof. exact (eq_refl (@List.Forall _26916)). Qed.
Lemma lem1142658 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (_18906 : type740 _26916 _26917) (h1 : _18906 = (term105 _26916 _26917)) : (term108 _26916 _26917 P) = (term109 _26916 _26917 _18906 P).
Proof. exact (MK_COMB (@lem1142657 _26916) (@lem1142656 _26916 _26917 P _18906 h1)). Qed.
Lemma lem1142659 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) (_18906 : type740 _26916 _26917) (h1 : _18906 = (term105 _26916 _26917)) : (term10 _26916 _26917 P t) = (term110 _26916 _26917 _18906 P t).
Proof. exact (MK_COMB (@lem1142658 _26916 _26917 P _18906 h1) (@lem1142653 _26916 t)). Qed.
Lemma lem1142664 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (P x h) = (P x h).
Proof. exact (eq_refl (P x h)). Qed.
Lemma lem1142665 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term75 _26916 _26917 P h) = (term75 _26916 _26917 P h).
Proof. exact (fun_ext (fun x : _26917 => @lem1142664 _26916 _26917 P x h)). Qed.
Lemma lem1142666 {_26917 : Type'} : (@all _26917) = (@all _26917).
Proof. exact (eq_refl (@all _26917)). Qed.
Lemma lem1142667 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term55 _26916 _26917 P h) = (term55 _26916 _26917 P h).
Proof. exact (MK_COMB (@lem1142666 _26917) (@lem1142665 _26916 _26917 P h)). Qed.
Lemma lem1142668 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1142669 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term60 _26916 _26917 P h) = (term60 _26916 _26917 P h).
Proof. exact (MK_COMB (@lem1142668) (@lem1142667 _26916 _26917 P h)). Qed.
Lemma lem1142670 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) (_18906 : type740 _26916 _26917) (h1 : _18906 = (term105 _26916 _26917)) : (term61 _26916 _26917 h P t) = (term111 _26916 _26917 h _18906 P t).
Proof. exact (MK_COMB (@lem1142669 _26916 _26917 P h) (@lem1142659 _26916 _26917 P t _18906 h1)). Qed.
Lemma lem1142677 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term81 _26916 _26917 P x t) = (term81 _26916 _26917 P x t).
Proof. exact (eq_refl (term81 _26916 _26917 P x t)). Qed.
Lemma lem1142678 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term76 _26916 _26917 P t) = (term76 _26916 _26917 P t).
Proof. exact (fun_ext (fun x : _26917 => @lem1142677 _26916 _26917 P x t)). Qed.
Lemma lem1142679 {_26917 : Type'} : (@all _26917) = (@all _26917).
Proof. exact (eq_refl (@all _26917)). Qed.
Lemma lem1142680 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term9 _26916 _26917 P t) = (term9 _26916 _26917 P t).
Proof. exact (MK_COMB (@lem1142679 _26917) (@lem1142678 _26916 _26917 P t)). Qed.
Lemma lem1142685 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (P x h) = (P x h).
Proof. exact (eq_refl (P x h)). Qed.
Lemma lem1142686 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term75 _26916 _26917 P h) = (term75 _26916 _26917 P h).
Proof. exact (fun_ext (fun x : _26917 => @lem1142685 _26916 _26917 P x h)). Qed.
Lemma lem1142687 {_26917 : Type'} : (@all _26917) = (@all _26917).
Proof. exact (eq_refl (@all _26917)). Qed.
Lemma lem1142688 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term55 _26916 _26917 P h) = (term55 _26916 _26917 P h).
Proof. exact (MK_COMB (@lem1142687 _26917) (@lem1142686 _26916 _26917 P h)). Qed.
Lemma lem1142689 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1142690 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term60 _26916 _26917 P h) = (term60 _26916 _26917 P h).
Proof. exact (MK_COMB (@lem1142689) (@lem1142688 _26916 _26917 P h)). Qed.
Lemma lem1142691 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term90 _26916 _26917 h P t) = (term90 _26916 _26917 h P t).
Proof. exact (MK_COMB (@lem1142690 _26916 _26917 P h) (@lem1142680 _26916 _26917 P t)). Qed.
Lemma lem1142692 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1142693 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term91 _26916 _26917 h P t) = (term91 _26916 _26917 h P t).
Proof. exact (MK_COMB (@lem1142692) (@lem1142691 _26916 _26917 h P t)). Qed.
Lemma lem1142694 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) (_18906 : type740 _26916 _26917) (h1 : _18906 = (term105 _26916 _26917)) : ((term90 _26916 _26917 h P t) = (term61 _26916 _26917 h P t)) = ((term90 _26916 _26917 h P t) = (term111 _26916 _26917 h _18906 P t)).
Proof. exact (MK_COMB (@lem1142693 _26916 _26917 h P t) (@lem1142670 _26916 _26917 h P t _18906 h1)). Qed.
Lemma lem1142695 {_26916 : Type'} (t : list _26916) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1142697 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (_18906 : type740 _26916 _26917) (h1 : _18906 = (term105 _26916 _26917)) : (term40 _26916 _26917 P) = (_18906 P).
Proof. exact (SYM (@lem1142651 _26916 _26917 P _18906 h1)). Qed.
Lemma lem1142698 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (_18906 : type740 _26916 _26917) (h1 : _18906 = (term105 _26916 _26917)) : (term40 _26916 _26917 P) = (_18906 P).
Proof. exact (@lem1142697 _26916 _26917 P _18906 h1). Qed.
Lemma lem1142699 {_26916 : Type'} : (@List.Forall _26916) = (@List.Forall _26916).
Proof. exact (eq_refl (@List.Forall _26916)). Qed.
Lemma lem1142700 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (_18906 : type740 _26916 _26917) (h1 : _18906 = (term105 _26916 _26917)) : (term108 _26916 _26917 P) = (term109 _26916 _26917 _18906 P).
Proof. exact (MK_COMB (@lem1142699 _26916) (@lem1142698 _26916 _26917 P _18906 h1)). Qed.
Lemma lem1142701 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) (_18906 : type740 _26916 _26917) (h1 : _18906 = (term105 _26916 _26917)) : (term10 _26916 _26917 P t) = (term110 _26916 _26917 _18906 P t).
Proof. exact (MK_COMB (@lem1142700 _26916 _26917 P _18906 h1) (@lem1142695 _26916 t)). Qed.
Lemma lem1142708 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term81 _26916 _26917 P x t) = (term81 _26916 _26917 P x t).
Proof. exact (eq_refl (term81 _26916 _26917 P x t)). Qed.
Lemma lem1142709 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term76 _26916 _26917 P t) = (term76 _26916 _26917 P t).
Proof. exact (fun_ext (fun x : _26917 => @lem1142708 _26916 _26917 P x t)). Qed.
Lemma lem1142710 {_26917 : Type'} : (@all _26917) = (@all _26917).
Proof. exact (eq_refl (@all _26917)). Qed.
Lemma lem1142711 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term9 _26916 _26917 P t) = (term9 _26916 _26917 P t).
Proof. exact (MK_COMB (@lem1142710 _26917) (@lem1142709 _26916 _26917 P t)). Qed.
Lemma lem1142712 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1142713 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term112 _26916 _26917 P t) = (term112 _26916 _26917 P t).
Proof. exact (MK_COMB (@lem1142712) (@lem1142711 _26916 _26917 P t)). Qed.
Lemma lem1142714 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) (_18906 : type740 _26916 _26917) (h1 : _18906 = (term105 _26916 _26917)) : ((term9 _26916 _26917 P t) = (term10 _26916 _26917 P t)) = ((term9 _26916 _26917 P t) = (term110 _26916 _26917 _18906 P t)).
Proof. exact (MK_COMB (@lem1142713 _26916 _26917 P t) (@lem1142701 _26916 _26917 P t _18906 h1)). Qed.
Lemma lem1142715 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1142716 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) (_18906 : type740 _26916 _26917) (h1 : _18906 = (term105 _26916 _26917)) : (term12 _26916 _26917 P t) = (term113 _26916 _26917 _18906 P t).
Proof. exact (MK_COMB (@lem1142715) (@lem1142714 _26916 _26917 P t _18906 h1)). Qed.
Lemma lem1142717 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) (_18906 : type740 _26916 _26917) (h1 : _18906 = (term105 _26916 _26917)) : (term92 _26916 _26917 h P t) = (term114 _26916 _26917 h _18906 P t).
Proof. exact (MK_COMB (@lem1142716 _26916 _26917 P t _18906 h1) (@lem1142694 _26916 _26917 h P t _18906 h1)). Qed.
Lemma lem1142718 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) (_18906 : type740 _26916 _26917) (h1 : _18906 = (term105 _26916 _26917)) : (term94 _26916 _26917 P t) = (term115 _26916 _26917 _18906 P t).
Proof. exact (fun_ext (fun h : _26916 => @lem1142717 _26916 _26917 h P t _18906 h1)). Qed.
Lemma lem1142719 {_26916 : Type'} : (@all _26916) = (@all _26916).
Proof. exact (eq_refl (@all _26916)). Qed.
Lemma lem1142720 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) (_18906 : type740 _26916 _26917) (h1 : _18906 = (term105 _26916 _26917)) : (term96 _26916 _26917 P t) = (term116 _26916 _26917 _18906 P t).
Proof. exact (MK_COMB (@lem1142719 _26916) (@lem1142718 _26916 _26917 P t _18906 h1)). Qed.
Lemma lem1142721 {_26916 _26917 : Type'} (t : list _26916) (_18906 : type740 _26916 _26917) (h1 : _18906 = (term105 _26916 _26917)) : (term98 _26916 _26917 t) = (term117 _26916 _26917 _18906 t).
Proof. exact (fun_ext (fun P : type1470 _26916 _26917 => @lem1142720 _26916 _26917 P t _18906 h1)). Qed.
Lemma lem1142722 {_26916 _26917 : Type'} : (@all (_26917 -> _26916 -> Prop)) = (@all (_26917 -> _26916 -> Prop)).
Proof. exact (eq_refl (@all (_26917 -> _26916 -> Prop))). Qed.
Lemma lem1142723 {_26916 _26917 : Type'} (t : list _26916) (_18906 : type740 _26916 _26917) (h1 : _18906 = (term105 _26916 _26917)) : (term100 _26916 _26917 t) = (term118 _26916 _26917 _18906 t).
Proof. exact (MK_COMB (@lem1142722 _26916 _26917) (@lem1142721 _26916 _26917 t _18906 h1)). Qed.
Lemma lem1142724 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (h1 : _18906 = (term105 _26916 _26917)) : (term102 _26916 _26917) = (term119 _26916 _26917 _18906).
Proof. exact (fun_ext (fun t : list _26916 => @lem1142723 _26916 _26917 t _18906 h1)). Qed.
Lemma lem1142725 {_26916 : Type'} : (@all (list _26916)) = (@all (list _26916)).
Proof. exact (eq_refl (@all (list _26916))). Qed.
Lemma lem1142726 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (h1 : _18906 = (term105 _26916 _26917)) : (term104 _26916 _26917) = (term120 _26916 _26917 _18906).
Proof. exact (MK_COMB (@lem1142725 _26916) (@lem1142724 _26916 _26917 _18906 h1)). Qed.
Lemma lem1142727 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : term121 _26916 _26917 _18906.
Proof. exact (fun h0 : _18906 = (term105 _26916 _26917) => @lem1142726 _26916 _26917 _18906 h0). Qed.
Lemma lem1142728 {_26916 _26917 : Type'} : term122 _26916 _26917.
Proof. exact (fun _18906 : type740 _26916 _26917 => @lem1142727 _26916 _26917 _18906). Qed.
Lemma lem1142730 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) : term123 _3603 P c Q.
Proof. exact (EQ_MP (@lem20230 _3603 P c Q) (@lem0)). Qed.
Lemma lem1142731 {_26916 _26917 : Type'} (P : Prop) (c : type740 _26916 _26917) (Q : type190 _26916 _26917) : term124 _26916 _26917 P c Q.
Proof. exact (@lem1142730 (type740 _26916 _26917) P c Q). Qed.
Lemma lem1142732 {_26916 _26917 : Type'} : term125 _26916 _26917.
Proof. exact (@lem1142731 _26916 _26917 (term104 _26916 _26917) (term105 _26916 _26917) (term126 _26916 _26917)). Qed.
Lemma lem1142733 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term127 _26916 _26917 _18906) = (term120 _26916 _26917 _18906).
Proof. exact (eq_refl (term127 _26916 _26917 _18906)). Qed.
Lemma lem1142734 {_26916 _26917 : Type'} : (term128 _26916 _26917) = (term128 _26916 _26917).
Proof. exact (eq_refl (term128 _26916 _26917)). Qed.
Lemma lem1142735 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : ((term104 _26916 _26917) = (term127 _26916 _26917 _18906)) = ((term104 _26916 _26917) = (term120 _26916 _26917 _18906)).
Proof. exact (MK_COMB (@lem1142734 _26916 _26917) (@lem1142733 _26916 _26917 _18906)). Qed.
Lemma lem1142736 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term129 _26916 _26917 _18906) = (term129 _26916 _26917 _18906).
Proof. exact (eq_refl (term129 _26916 _26917 _18906)). Qed.
Lemma lem1142737 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term130 _26916 _26917 _18906) = (term121 _26916 _26917 _18906).
Proof. exact (MK_COMB (@lem1142736 _26916 _26917 _18906) (@lem1142735 _26916 _26917 _18906)). Qed.
Lemma lem1142738 {_26916 _26917 : Type'} : (term131 _26916 _26917) = (term132 _26916 _26917).
Proof. exact (fun_ext (fun _18906 : type740 _26916 _26917 => @lem1142737 _26916 _26917 _18906)). Qed.
Lemma lem1142739 {_26916 _26917 : Type'} : (@all ((_26917 -> _26916 -> Prop) -> _26916 -> Prop)) = (@all ((_26917 -> _26916 -> Prop) -> _26916 -> Prop)).
Proof. exact (eq_refl (@all ((_26917 -> _26916 -> Prop) -> _26916 -> Prop))). Qed.
Lemma lem1142740 {_26916 _26917 : Type'} : (term133 _26916 _26917) = (term122 _26916 _26917).
Proof. exact (MK_COMB (@lem1142739 _26916 _26917) (@lem1142738 _26916 _26917)). Qed.
Lemma lem1142741 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1142742 {_26916 _26917 : Type'} : (term134 _26916 _26917) = (term135 _26916 _26917).
Proof. exact (MK_COMB (@lem1142741) (@lem1142740 _26916 _26917)). Qed.
Lemma lem1142743 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term127 _26916 _26917 _18906) = (term120 _26916 _26917 _18906).
Proof. exact (eq_refl (term127 _26916 _26917 _18906)). Qed.
Lemma lem1142744 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term129 _26916 _26917 _18906) = (term129 _26916 _26917 _18906).
Proof. exact (eq_refl (term129 _26916 _26917 _18906)). Qed.
Lemma lem1142745 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term136 _26916 _26917 _18906) = (term137 _26916 _26917 _18906).
Proof. exact (MK_COMB (@lem1142744 _26916 _26917 _18906) (@lem1142743 _26916 _26917 _18906)). Qed.
Lemma lem1142746 {_26916 _26917 : Type'} : (term138 _26916 _26917) = (term139 _26916 _26917).
Proof. exact (fun_ext (fun _18906 : type740 _26916 _26917 => @lem1142745 _26916 _26917 _18906)). Qed.
Lemma lem1142747 {_26916 _26917 : Type'} : (@all ((_26917 -> _26916 -> Prop) -> _26916 -> Prop)) = (@all ((_26917 -> _26916 -> Prop) -> _26916 -> Prop)).
Proof. exact (eq_refl (@all ((_26917 -> _26916 -> Prop) -> _26916 -> Prop))). Qed.
Lemma lem1142748 {_26916 _26917 : Type'} : (term140 _26916 _26917) = (term141 _26916 _26917).
Proof. exact (MK_COMB (@lem1142747 _26916 _26917) (@lem1142746 _26916 _26917)). Qed.
Lemma lem1142749 {_26916 _26917 : Type'} : (term128 _26916 _26917) = (term128 _26916 _26917).
Proof. exact (eq_refl (term128 _26916 _26917)). Qed.
Lemma lem1142750 {_26916 _26917 : Type'} : ((term104 _26916 _26917) = (term140 _26916 _26917)) = ((term104 _26916 _26917) = (term141 _26916 _26917)).
Proof. exact (MK_COMB (@lem1142749 _26916 _26917) (@lem1142748 _26916 _26917)). Qed.
Lemma lem1142751 {_26916 _26917 : Type'} : (term125 _26916 _26917) = (term142 _26916 _26917).
Proof. exact (MK_COMB (@lem1142742 _26916 _26917) (@lem1142750 _26916 _26917)). Qed.
Lemma lem1142752 {_26916 _26917 : Type'} : term142 _26916 _26917.
Proof. exact (EQ_MP (@lem1142751 _26916 _26917) (@lem1142732 _26916 _26917)). Qed.
Lemma lem1142753 {_26916 _26917 : Type'} : (term104 _26916 _26917) = (term141 _26916 _26917).
Proof. exact (@lem1142752 _26916 _26917 (@lem1142728 _26916 _26917)). Qed.
Lemma lem1142755 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term143 _3571 _3575 t)) = (term144 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem1142756 {_26916 _26917 : Type'} (s : type740 _26916 _26917) (t : type740 _26916 _26917) : (s = (term145 _26916 _26917 t)) = (term146 _26916 _26917 s t).
Proof. exact (@lem1142755 (_26916 -> Prop) (type1470 _26916 _26917) s t). Qed.
Lemma lem1142757 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (_18906 = (term147 _26916 _26917)) = (term148 _26916 _26917 _18906).
Proof. exact (@lem1142756 _26916 _26917 _18906 (term105 _26916 _26917)). Qed.
Lemma lem1142758 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) : (term106 _26916 _26917 P) = (term40 _26916 _26917 P).
Proof. exact (eq_refl (term106 _26916 _26917 P)). Qed.
Lemma lem1142759 {_26916 _26917 : Type'} : (term147 _26916 _26917) = (term105 _26916 _26917).
Proof. exact (fun_ext (fun P : type1470 _26916 _26917 => @lem1142758 _26916 _26917 P)). Qed.
Lemma lem1142760 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (@eq ((_26917 -> _26916 -> Prop) -> _26916 -> Prop) _18906) = (@eq ((_26917 -> _26916 -> Prop) -> _26916 -> Prop) _18906).
Proof. exact (eq_refl (@eq ((_26917 -> _26916 -> Prop) -> _26916 -> Prop) _18906)). Qed.
Lemma lem1142761 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (_18906 = (term147 _26916 _26917)) = (_18906 = (term105 _26916 _26917)).
Proof. exact (MK_COMB (@lem1142760 _26916 _26917 _18906) (@lem1142759 _26916 _26917)). Qed.
Lemma lem1142762 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1142763 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term149 _26916 _26917 _18906) = (term150 _26916 _26917 _18906).
Proof. exact (MK_COMB (@lem1142762) (@lem1142761 _26916 _26917 _18906)). Qed.
Lemma lem1142764 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) : (term106 _26916 _26917 P) = (term40 _26916 _26917 P).
Proof. exact (eq_refl (term106 _26916 _26917 P)). Qed.
Lemma lem1142765 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term107 _26916 _26917 _18906 P) = (term107 _26916 _26917 _18906 P).
Proof. exact (eq_refl (term107 _26916 _26917 _18906 P)). Qed.
Lemma lem1142766 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : ((_18906 P) = (term106 _26916 _26917 P)) = ((_18906 P) = (term40 _26916 _26917 P)).
Proof. exact (MK_COMB (@lem1142765 _26916 _26917 _18906 P) (@lem1142764 _26916 _26917 P)). Qed.
Lemma lem1142767 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term151 _26916 _26917 _18906) = (term152 _26916 _26917 _18906).
Proof. exact (fun_ext (fun P : type1470 _26916 _26917 => @lem1142766 _26916 _26917 _18906 P)). Qed.
Lemma lem1142768 {_26916 _26917 : Type'} : (@all (_26917 -> _26916 -> Prop)) = (@all (_26917 -> _26916 -> Prop)).
Proof. exact (eq_refl (@all (_26917 -> _26916 -> Prop))). Qed.
Lemma lem1142769 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term148 _26916 _26917 _18906) = (term153 _26916 _26917 _18906).
Proof. exact (MK_COMB (@lem1142768 _26916 _26917) (@lem1142767 _26916 _26917 _18906)). Qed.
Lemma lem1142770 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : ((_18906 = (term147 _26916 _26917)) = (term148 _26916 _26917 _18906)) = ((_18906 = (term105 _26916 _26917)) = (term153 _26916 _26917 _18906)).
Proof. exact (MK_COMB (@lem1142763 _26916 _26917 _18906) (@lem1142769 _26916 _26917 _18906)). Qed.
Lemma lem1142771 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (_18906 = (term105 _26916 _26917)) = (term153 _26916 _26917 _18906).
Proof. exact (EQ_MP (@lem1142770 _26916 _26917 _18906) (@lem1142757 _26916 _26917 _18906)). Qed.
Lemma lem1142773 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term143 _3571 _3575 t)) = (term144 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem1142774 {_26916 : Type'} (s : _26916 -> Prop) (t : _26916 -> Prop) : (s = (term154 _26916 t)) = (term155 _26916 s t).
Proof. exact (@lem1142773 Prop _26916 s t). Qed.
Lemma lem1142775 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : ((_18906 P) = (term56 _26916 _26917 P)) = (term156 _26916 _26917 _18906 P).
Proof. exact (@lem1142774 _26916 (_18906 P) (term40 _26916 _26917 P)). Qed.
Lemma lem1142776 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (s : _26916) : (term54 _26916 _26917 P s) = (term55 _26916 _26917 P s).
Proof. exact (eq_refl (term54 _26916 _26917 P s)). Qed.
Lemma lem1142777 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) : (term56 _26916 _26917 P) = (term40 _26916 _26917 P).
Proof. exact (fun_ext (fun s : _26916 => @lem1142776 _26916 _26917 P s)). Qed.
Lemma lem1142778 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term107 _26916 _26917 _18906 P) = (term107 _26916 _26917 _18906 P).
Proof. exact (eq_refl (term107 _26916 _26917 _18906 P)). Qed.
Lemma lem1142779 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : ((_18906 P) = (term56 _26916 _26917 P)) = ((_18906 P) = (term40 _26916 _26917 P)).
Proof. exact (MK_COMB (@lem1142778 _26916 _26917 _18906 P) (@lem1142777 _26916 _26917 P)). Qed.
Lemma lem1142780 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1142781 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term157 _26916 _26917 _18906 P) = (term158 _26916 _26917 _18906 P).
Proof. exact (MK_COMB (@lem1142780) (@lem1142779 _26916 _26917 _18906 P)). Qed.
Lemma lem1142782 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (s : _26916) : (term54 _26916 _26917 P s) = (term55 _26916 _26917 P s).
Proof. exact (eq_refl (term54 _26916 _26917 P s)). Qed.
Lemma lem1142783 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (s : _26916) : (term159 _26916 _26917 _18906 P s) = (term159 _26916 _26917 _18906 P s).
Proof. exact (eq_refl (term159 _26916 _26917 _18906 P s)). Qed.
Lemma lem1142784 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (s : _26916) : ((_18906 P s) = (term54 _26916 _26917 P s)) = ((_18906 P s) = (term55 _26916 _26917 P s)).
Proof. exact (MK_COMB (@lem1142783 _26916 _26917 _18906 P s) (@lem1142782 _26916 _26917 P s)). Qed.
Lemma lem1142785 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term160 _26916 _26917 _18906 P) = (term161 _26916 _26917 _18906 P).
Proof. exact (fun_ext (fun s : _26916 => @lem1142784 _26916 _26917 _18906 P s)). Qed.
Lemma lem1142786 {_26916 : Type'} : (@all _26916) = (@all _26916).
Proof. exact (eq_refl (@all _26916)). Qed.
Lemma lem1142787 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term156 _26916 _26917 _18906 P) = (term162 _26916 _26917 _18906 P).
Proof. exact (MK_COMB (@lem1142786 _26916) (@lem1142785 _26916 _26917 _18906 P)). Qed.
Lemma lem1142788 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (((_18906 P) = (term56 _26916 _26917 P)) = (term156 _26916 _26917 _18906 P)) = (((_18906 P) = (term40 _26916 _26917 P)) = (term162 _26916 _26917 _18906 P)).
Proof. exact (MK_COMB (@lem1142781 _26916 _26917 _18906 P) (@lem1142787 _26916 _26917 _18906 P)). Qed.
Lemma lem1142789 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : ((_18906 P) = (term40 _26916 _26917 P)) = (term162 _26916 _26917 _18906 P).
Proof. exact (EQ_MP (@lem1142788 _26916 _26917 _18906 P) (@lem1142775 _26916 _26917 _18906 P)). Qed.
Lemma lem1142790 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (s : _26916) : ((_18906 P s) = (term55 _26916 _26917 P s)) = ((_18906 P s) = (term55 _26916 _26917 P s)).
Proof. exact (eq_refl ((_18906 P s) = (term55 _26916 _26917 P s))). Qed.
Lemma lem1142791 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term161 _26916 _26917 _18906 P) = (term161 _26916 _26917 _18906 P).
Proof. exact (fun_ext (fun s : _26916 => @lem1142790 _26916 _26917 _18906 P s)). Qed.
Lemma lem1142792 {_26916 : Type'} : (@all _26916) = (@all _26916).
Proof. exact (eq_refl (@all _26916)). Qed.
Lemma lem1142793 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term162 _26916 _26917 _18906 P) = (term162 _26916 _26917 _18906 P).
Proof. exact (MK_COMB (@lem1142792 _26916) (@lem1142791 _26916 _26917 _18906 P)). Qed.
Lemma lem1142794 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : ((_18906 P) = (term40 _26916 _26917 P)) = (term162 _26916 _26917 _18906 P).
Proof. exact (TRANS (@lem1142789 _26916 _26917 _18906 P) (@lem1142793 _26916 _26917 _18906 P)). Qed.
Lemma lem1142795 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term152 _26916 _26917 _18906) = (term163 _26916 _26917 _18906).
Proof. exact (fun_ext (fun P : type1470 _26916 _26917 => @lem1142794 _26916 _26917 _18906 P)). Qed.
Lemma lem1142796 {_26916 _26917 : Type'} : (@all (_26917 -> _26916 -> Prop)) = (@all (_26917 -> _26916 -> Prop)).
Proof. exact (eq_refl (@all (_26917 -> _26916 -> Prop))). Qed.
Lemma lem1142797 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term153 _26916 _26917 _18906) = (term164 _26916 _26917 _18906).
Proof. exact (MK_COMB (@lem1142796 _26916 _26917) (@lem1142795 _26916 _26917 _18906)). Qed.
Lemma lem1142798 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (_18906 = (term105 _26916 _26917)) = (term164 _26916 _26917 _18906).
Proof. exact (TRANS (@lem1142771 _26916 _26917 _18906) (@lem1142797 _26916 _26917 _18906)). Qed.
Lemma lem1142799 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1142800 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term129 _26916 _26917 _18906) = (term165 _26916 _26917 _18906).
Proof. exact (MK_COMB (@lem1142799) (@lem1142798 _26916 _26917 _18906)). Qed.
Lemma lem1142801 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term120 _26916 _26917 _18906) = (term120 _26916 _26917 _18906).
Proof. exact (eq_refl (term120 _26916 _26917 _18906)). Qed.
Lemma lem1142802 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term137 _26916 _26917 _18906) = (term166 _26916 _26917 _18906).
Proof. exact (MK_COMB (@lem1142800 _26916 _26917 _18906) (@lem1142801 _26916 _26917 _18906)). Qed.
Lemma lem1142803 {_26916 _26917 : Type'} : (term139 _26916 _26917) = (term167 _26916 _26917).
Proof. exact (fun_ext (fun _18906 : type740 _26916 _26917 => @lem1142802 _26916 _26917 _18906)). Qed.
Lemma lem1142804 {_26916 _26917 : Type'} : (@all ((_26917 -> _26916 -> Prop) -> _26916 -> Prop)) = (@all ((_26917 -> _26916 -> Prop) -> _26916 -> Prop)).
Proof. exact (eq_refl (@all ((_26917 -> _26916 -> Prop) -> _26916 -> Prop))). Qed.
Lemma lem1142805 {_26916 _26917 : Type'} : (term141 _26916 _26917) = (term168 _26916 _26917).
Proof. exact (MK_COMB (@lem1142804 _26916 _26917) (@lem1142803 _26916 _26917)). Qed.
Lemma lem1142806 {_26916 _26917 : Type'} : (term128 _26916 _26917) = (term128 _26916 _26917).
Proof. exact (eq_refl (term128 _26916 _26917)). Qed.
Lemma lem1142807 {_26916 _26917 : Type'} : ((term104 _26916 _26917) = (term141 _26916 _26917)) = ((term104 _26916 _26917) = (term168 _26916 _26917)).
Proof. exact (MK_COMB (@lem1142806 _26916 _26917) (@lem1142805 _26916 _26917)). Qed.
Lemma lem1142810 {_26916 _26917 : Type'} : (term104 _26916 _26917) = (term168 _26916 _26917).
Proof. exact (EQ_MP (@lem1142807 _26916 _26917) (@lem1142753 _26916 _26917)). Qed.
Lemma lem1142811 {_26916 _26917 : Type'} : (term103 _26916 _26917) = (term168 _26916 _26917).
Proof. exact (TRANS (@lem1142644 _26916 _26917) (@lem1142810 _26916 _26917)). Qed.
Lemma lem1142812 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term110 _26916 _26917 _18906 P t) = (term110 _26916 _26917 _18906 P t).
Proof. exact (eq_refl (term110 _26916 _26917 _18906 P t)). Qed.
Lemma lem1142813 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (P x h) = (P x h).
Proof. exact (eq_refl (P x h)). Qed.
Lemma lem1142814 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term75 _26916 _26917 P h) = (term75 _26916 _26917 P h).
Proof. exact (fun_ext (fun x : _26917 => @lem1142813 _26916 _26917 P x h)). Qed.
Lemma lem1142815 {_26917 : Type'} : (@all _26917) = (@all _26917).
Proof. exact (eq_refl (@all _26917)). Qed.
Lemma lem1142816 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term55 _26916 _26917 P h) = (term55 _26916 _26917 P h).
Proof. exact (MK_COMB (@lem1142815 _26917) (@lem1142814 _26916 _26917 P h)). Qed.
Lemma lem1142817 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1142818 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term60 _26916 _26917 P h) = (term60 _26916 _26917 P h).
Proof. exact (MK_COMB (@lem1142817) (@lem1142816 _26916 _26917 P h)). Qed.
Lemma lem1142819 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term111 _26916 _26917 h _18906 P t) = (term111 _26916 _26917 h _18906 P t).
Proof. exact (MK_COMB (@lem1142818 _26916 _26917 P h) (@lem1142812 _26916 _26917 _18906 P t)). Qed.
Lemma lem1142820 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term81 _26916 _26917 P x t) = (term81 _26916 _26917 P x t).
Proof. exact (eq_refl (term81 _26916 _26917 P x t)). Qed.
Lemma lem1142821 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term76 _26916 _26917 P t) = (term76 _26916 _26917 P t).
Proof. exact (fun_ext (fun x : _26917 => @lem1142820 _26916 _26917 P x t)). Qed.
Lemma lem1142822 {_26917 : Type'} : (@all _26917) = (@all _26917).
Proof. exact (eq_refl (@all _26917)). Qed.
Lemma lem1142823 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term9 _26916 _26917 P t) = (term9 _26916 _26917 P t).
Proof. exact (MK_COMB (@lem1142822 _26917) (@lem1142821 _26916 _26917 P t)). Qed.
Lemma lem1142824 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (P x h) = (P x h).
Proof. exact (eq_refl (P x h)). Qed.
Lemma lem1142825 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term75 _26916 _26917 P h) = (term75 _26916 _26917 P h).
Proof. exact (fun_ext (fun x : _26917 => @lem1142824 _26916 _26917 P x h)). Qed.
Lemma lem1142826 {_26917 : Type'} : (@all _26917) = (@all _26917).
Proof. exact (eq_refl (@all _26917)). Qed.
Lemma lem1142827 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term55 _26916 _26917 P h) = (term55 _26916 _26917 P h).
Proof. exact (MK_COMB (@lem1142826 _26917) (@lem1142825 _26916 _26917 P h)). Qed.
Lemma lem1142828 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1142829 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term60 _26916 _26917 P h) = (term60 _26916 _26917 P h).
Proof. exact (MK_COMB (@lem1142828) (@lem1142827 _26916 _26917 P h)). Qed.
Lemma lem1142830 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term90 _26916 _26917 h P t) = (term90 _26916 _26917 h P t).
Proof. exact (MK_COMB (@lem1142829 _26916 _26917 P h) (@lem1142823 _26916 _26917 P t)). Qed.
Lemma lem1142831 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1142832 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term91 _26916 _26917 h P t) = (term91 _26916 _26917 h P t).
Proof. exact (MK_COMB (@lem1142831) (@lem1142830 _26916 _26917 h P t)). Qed.
Lemma lem1142833 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : ((term90 _26916 _26917 h P t) = (term111 _26916 _26917 h _18906 P t)) = ((term90 _26916 _26917 h P t) = (term111 _26916 _26917 h _18906 P t)).
Proof. exact (MK_COMB (@lem1142832 _26916 _26917 h P t) (@lem1142819 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1142834 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term110 _26916 _26917 _18906 P t) = (term110 _26916 _26917 _18906 P t).
Proof. exact (eq_refl (term110 _26916 _26917 _18906 P t)). Qed.
Lemma lem1142835 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term81 _26916 _26917 P x t) = (term81 _26916 _26917 P x t).
Proof. exact (eq_refl (term81 _26916 _26917 P x t)). Qed.
Lemma lem1142836 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term76 _26916 _26917 P t) = (term76 _26916 _26917 P t).
Proof. exact (fun_ext (fun x : _26917 => @lem1142835 _26916 _26917 P x t)). Qed.
Lemma lem1142837 {_26917 : Type'} : (@all _26917) = (@all _26917).
Proof. exact (eq_refl (@all _26917)). Qed.
Lemma lem1142838 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term9 _26916 _26917 P t) = (term9 _26916 _26917 P t).
Proof. exact (MK_COMB (@lem1142837 _26917) (@lem1142836 _26916 _26917 P t)). Qed.
Lemma lem1142839 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1142840 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term112 _26916 _26917 P t) = (term112 _26916 _26917 P t).
Proof. exact (MK_COMB (@lem1142839) (@lem1142838 _26916 _26917 P t)). Qed.
Lemma lem1142841 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : ((term9 _26916 _26917 P t) = (term110 _26916 _26917 _18906 P t)) = ((term9 _26916 _26917 P t) = (term110 _26916 _26917 _18906 P t)).
Proof. exact (MK_COMB (@lem1142840 _26916 _26917 P t) (@lem1142834 _26916 _26917 _18906 P t)). Qed.
Lemma lem1142842 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1142843 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term113 _26916 _26917 _18906 P t) = (term113 _26916 _26917 _18906 P t).
Proof. exact (MK_COMB (@lem1142842) (@lem1142841 _26916 _26917 _18906 P t)). Qed.
Lemma lem1142844 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term114 _26916 _26917 h _18906 P t) = (term114 _26916 _26917 h _18906 P t).
Proof. exact (MK_COMB (@lem1142843 _26916 _26917 _18906 P t) (@lem1142833 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1142845 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term115 _26916 _26917 _18906 P t) = (term115 _26916 _26917 _18906 P t).
Proof. exact (fun_ext (fun h : _26916 => @lem1142844 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1142846 {_26916 : Type'} : (@all _26916) = (@all _26916).
Proof. exact (eq_refl (@all _26916)). Qed.
Lemma lem1142847 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term116 _26916 _26917 _18906 P t) = (term116 _26916 _26917 _18906 P t).
Proof. exact (MK_COMB (@lem1142846 _26916) (@lem1142845 _26916 _26917 _18906 P t)). Qed.
Lemma lem1142848 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (t : list _26916) : (term117 _26916 _26917 _18906 t) = (term117 _26916 _26917 _18906 t).
Proof. exact (fun_ext (fun P : type1470 _26916 _26917 => @lem1142847 _26916 _26917 _18906 P t)). Qed.
Lemma lem1142849 {_26916 _26917 : Type'} : (@all (_26917 -> _26916 -> Prop)) = (@all (_26917 -> _26916 -> Prop)).
Proof. exact (eq_refl (@all (_26917 -> _26916 -> Prop))). Qed.
Lemma lem1142850 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (t : list _26916) : (term118 _26916 _26917 _18906 t) = (term118 _26916 _26917 _18906 t).
Proof. exact (MK_COMB (@lem1142849 _26916 _26917) (@lem1142848 _26916 _26917 _18906 t)). Qed.
Lemma lem1142851 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term119 _26916 _26917 _18906) = (term119 _26916 _26917 _18906).
Proof. exact (fun_ext (fun t : list _26916 => @lem1142850 _26916 _26917 _18906 t)). Qed.
Lemma lem1142852 {_26916 : Type'} : (@all (list _26916)) = (@all (list _26916)).
Proof. exact (eq_refl (@all (list _26916))). Qed.
Lemma lem1142853 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term120 _26916 _26917 _18906) = (term120 _26916 _26917 _18906).
Proof. exact (MK_COMB (@lem1142852 _26916) (@lem1142851 _26916 _26917 _18906)). Qed.
Lemma lem1142854 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (s : _26916) : (P x s) = (P x s).
Proof. exact (eq_refl (P x s)). Qed.
Lemma lem1142855 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (s : _26916) : (term75 _26916 _26917 P s) = (term75 _26916 _26917 P s).
Proof. exact (fun_ext (fun x : _26917 => @lem1142854 _26916 _26917 P x s)). Qed.
Lemma lem1142856 {_26917 : Type'} : (@all _26917) = (@all _26917).
Proof. exact (eq_refl (@all _26917)). Qed.
Lemma lem1142857 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (s : _26916) : (term55 _26916 _26917 P s) = (term55 _26916 _26917 P s).
Proof. exact (MK_COMB (@lem1142856 _26917) (@lem1142855 _26916 _26917 P s)). Qed.
Lemma lem1142860 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (s : _26916) : (term159 _26916 _26917 _18906 P s) = (term159 _26916 _26917 _18906 P s).
Proof. exact (eq_refl (term159 _26916 _26917 _18906 P s)). Qed.
Lemma lem1142861 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (s : _26916) : ((_18906 P s) = (term55 _26916 _26917 P s)) = ((_18906 P s) = (term55 _26916 _26917 P s)).
Proof. exact (MK_COMB (@lem1142860 _26916 _26917 _18906 P s) (@lem1142857 _26916 _26917 P s)). Qed.
Lemma lem1142862 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term161 _26916 _26917 _18906 P) = (term161 _26916 _26917 _18906 P).
Proof. exact (fun_ext (fun s : _26916 => @lem1142861 _26916 _26917 _18906 P s)). Qed.
Lemma lem1142863 {_26916 : Type'} : (@all _26916) = (@all _26916).
Proof. exact (eq_refl (@all _26916)). Qed.
Lemma lem1142864 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term162 _26916 _26917 _18906 P) = (term162 _26916 _26917 _18906 P).
Proof. exact (MK_COMB (@lem1142863 _26916) (@lem1142862 _26916 _26917 _18906 P)). Qed.
Lemma lem1142865 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term163 _26916 _26917 _18906) = (term163 _26916 _26917 _18906).
Proof. exact (fun_ext (fun P : type1470 _26916 _26917 => @lem1142864 _26916 _26917 _18906 P)). Qed.
Lemma lem1142866 {_26916 _26917 : Type'} : (@all (_26917 -> _26916 -> Prop)) = (@all (_26917 -> _26916 -> Prop)).
Proof. exact (eq_refl (@all (_26917 -> _26916 -> Prop))). Qed.
Lemma lem1142867 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term164 _26916 _26917 _18906) = (term164 _26916 _26917 _18906).
Proof. exact (MK_COMB (@lem1142866 _26916 _26917) (@lem1142865 _26916 _26917 _18906)). Qed.
Lemma lem1142868 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1142869 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term165 _26916 _26917 _18906) = (term165 _26916 _26917 _18906).
Proof. exact (MK_COMB (@lem1142868) (@lem1142867 _26916 _26917 _18906)). Qed.
Lemma lem1142870 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term166 _26916 _26917 _18906) = (term166 _26916 _26917 _18906).
Proof. exact (MK_COMB (@lem1142869 _26916 _26917 _18906) (@lem1142853 _26916 _26917 _18906)). Qed.
Lemma lem1142871 {_26916 _26917 : Type'} : (term167 _26916 _26917) = (term167 _26916 _26917).
Proof. exact (fun_ext (fun _18906 : type740 _26916 _26917 => @lem1142870 _26916 _26917 _18906)). Qed.
Lemma lem1142872 {_26916 _26917 : Type'} : (@all ((_26917 -> _26916 -> Prop) -> _26916 -> Prop)) = (@all ((_26917 -> _26916 -> Prop) -> _26916 -> Prop)).
Proof. exact (eq_refl (@all ((_26917 -> _26916 -> Prop) -> _26916 -> Prop))). Qed.
Lemma lem1142873 {_26916 _26917 : Type'} : (term168 _26916 _26917) = (term168 _26916 _26917).
Proof. exact (MK_COMB (@lem1142872 _26916 _26917) (@lem1142871 _26916 _26917)). Qed.
Lemma lem1142950 {_26916 _26917 : Type'} : (term103 _26916 _26917) = (term168 _26916 _26917).
Proof. exact (TRANS (@lem1142811 _26916 _26917) (@lem1142873 _26916 _26917)). Qed.
Lemma lem1142951 {_26916 _26917 : Type'} : (term168 _26916 _26917) = (term103 _26916 _26917).
Proof. exact (SYM (@lem1142950 _26916 _26917)). Qed.
Lemma lem1142952 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (h1 : term164 _26916 _26917 _18906) : term164 _26916 _26917 _18906.
Proof. exact (h1). Qed.
Lemma lem1142953 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : (term9 _26916 _26917 P t) = (term110 _26916 _26917 _18906 P t)) : (term9 _26916 _26917 P t) = (term110 _26916 _26917 _18906 P t).
Proof. exact (h1). Qed.
Lemma lem1142955 (p : Prop) : p = (term62 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1142956 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : ((term90 _26916 _26917 h P t) = (term111 _26916 _26917 h _18906 P t)) = (term169 _26916 _26917 h _18906 P t).
Proof. exact (@lem1142955 ((term90 _26916 _26917 h P t) = (term111 _26916 _26917 h _18906 P t))). Qed.
Lemma lem1142957 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term169 _26916 _26917 h _18906 P t) = ((term90 _26916 _26917 h P t) = (term111 _26916 _26917 h _18906 P t)).
Proof. exact (SYM (@lem1142956 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1142958 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term170 _26916 _26917 h _18906 P t) : term170 _26916 _26917 h _18906 P t.
Proof. exact (h1). Qed.
Lemma lem1142962 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (s : _26916) : (P x s) = (P x s).
Proof. exact (eq_refl (P x s)). Qed.
Lemma lem1142963 {_26917 : Type'} (P : _26917 -> Prop) : (term171 _26917 P) = (term172 _26917 P).
Proof. exact (@lem18392 _26917 P). Qed.
Lemma lem1142964 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (s : _26916) : (term173 _26916 _26917 P s) = (term174 _26916 _26917 P s).
Proof. exact (@lem1142963 _26917 (term75 _26916 _26917 P s)). Qed.
Lemma lem1142965 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (s : _26916) : (term77 _26916 _26917 P s x) = (P x s).
Proof. exact (eq_refl (term77 _26916 _26917 P s x)). Qed.
Lemma lem1142966 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1142968 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (s : _26916) : (term175 _26916 _26917 P s x) = (term176 _26916 _26917 P x s).
Proof. exact (MK_COMB (@lem1142966) (@lem1142965 _26916 _26917 P x s)). Qed.
Lemma lem1142969 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (s : _26916) : (term177 _26916 _26917 P s) = (term178 _26916 _26917 P s).
Proof. exact (fun_ext (fun x : _26917 => @lem1142968 _26916 _26917 P x s)). Qed.
Lemma lem1142970 {_26917 : Type'} : (@ex _26917) = (@ex _26917).
Proof. exact (eq_refl (@ex _26917)). Qed.
Lemma lem1142971 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (s : _26916) : (term174 _26916 _26917 P s) = (term179 _26916 _26917 P s).
Proof. exact (MK_COMB (@lem1142970 _26917) (@lem1142969 _26916 _26917 P s)). Qed.
Lemma lem1142972 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (s : _26916) : (term173 _26916 _26917 P s) = (term179 _26916 _26917 P s).
Proof. exact (TRANS (@lem1142964 _26916 _26917 P s) (@lem1142971 _26916 _26917 P s)). Qed.
Lemma lem1142973 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (s : _26916) : (term75 _26916 _26917 P s) = (term75 _26916 _26917 P s).
Proof. exact (fun_ext (fun x : _26917 => @lem1142962 _26916 _26917 P x s)). Qed.
Lemma lem1142974 {_26917 : Type'} : (@all _26917) = (@all _26917).
Proof. exact (eq_refl (@all _26917)). Qed.
Lemma lem1142975 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (s : _26916) : (term55 _26916 _26917 P s) = (term55 _26916 _26917 P s).
Proof. exact (MK_COMB (@lem1142974 _26917) (@lem1142973 _26916 _26917 P s)). Qed.
Lemma lem1142977 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (s : _26916) : (term180 _26916 _26917 _18906 P s) = (term180 _26916 _26917 _18906 P s).
Proof. exact (eq_refl (term180 _26916 _26917 _18906 P s)). Qed.
Lemma lem1142978 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (s : _26916) : (term181 _26916 _26917 _18906 P s) = (term181 _26916 _26917 _18906 P s).
Proof. exact (MK_COMB (@lem1142977 _26916 _26917 _18906 P s) (@lem1142975 _26916 _26917 P s)). Qed.
Lemma lem1142980 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (s : _26916) : (term182 _26916 _26917 _18906 P s) = (term182 _26916 _26917 _18906 P s).
Proof. exact (eq_refl (term182 _26916 _26917 _18906 P s)). Qed.
Lemma lem1142981 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (s : _26916) : (term183 _26916 _26917 _18906 P s) = (term184 _26916 _26917 _18906 P s).
Proof. exact (MK_COMB (@lem1142980 _26916 _26917 _18906 P s) (@lem1142972 _26916 _26917 P s)). Qed.
Lemma lem1142982 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1142983 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (s : _26916) : (term185 _26916 _26917 _18906 P s) = (term186 _26916 _26917 _18906 P s).
Proof. exact (MK_COMB (@lem1142982) (@lem1142981 _26916 _26917 _18906 P s)). Qed.
Lemma lem1142984 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (s : _26916) : (term187 _26916 _26917 _18906 P s) = (term188 _26916 _26917 _18906 P s).
Proof. exact (MK_COMB (@lem1142983 _26916 _26917 _18906 P s) (@lem1142978 _26916 _26917 _18906 P s)). Qed.
Lemma lem1142985 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (s : _26916) : ((_18906 P s) = (term55 _26916 _26917 P s)) = (term187 _26916 _26917 _18906 P s).
Proof. exact (@lem17784 (_18906 P s) (term55 _26916 _26917 P s)). Qed.
Lemma lem1142986 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (s : _26916) : ((_18906 P s) = (term55 _26916 _26917 P s)) = (term188 _26916 _26917 _18906 P s).
Proof. exact (TRANS (@lem1142985 _26916 _26917 _18906 P s) (@lem1142984 _26916 _26917 _18906 P s)). Qed.
Lemma lem1142987 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term161 _26916 _26917 _18906 P) = (term189 _26916 _26917 _18906 P).
Proof. exact (fun_ext (fun s : _26916 => @lem1142986 _26916 _26917 _18906 P s)). Qed.
Lemma lem1142988 {_26916 : Type'} : (@all _26916) = (@all _26916).
Proof. exact (eq_refl (@all _26916)). Qed.
Lemma lem1142989 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term162 _26916 _26917 _18906 P) = (term190 _26916 _26917 _18906 P).
Proof. exact (MK_COMB (@lem1142988 _26916) (@lem1142987 _26916 _26917 _18906 P)). Qed.
Lemma lem1142990 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term163 _26916 _26917 _18906) = (term191 _26916 _26917 _18906).
Proof. exact (fun_ext (fun P : type1470 _26916 _26917 => @lem1142989 _26916 _26917 _18906 P)). Qed.
Lemma lem1142991 {_26916 _26917 : Type'} : (@all (_26917 -> _26916 -> Prop)) = (@all (_26917 -> _26916 -> Prop)).
Proof. exact (eq_refl (@all (_26917 -> _26916 -> Prop))). Qed.
Lemma lem1142992 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term164 _26916 _26917 _18906) = (term192 _26916 _26917 _18906).
Proof. exact (MK_COMB (@lem1142991 _26916 _26917) (@lem1142990 _26916 _26917 _18906)). Qed.
Lemma lem1142998 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term71 A P Q) = (term72 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1142999 {_26916 : Type'} (P : _26916 -> Prop) (Q : _26916 -> Prop) : (term71 _26916 P Q) = (term72 _26916 P Q).
Proof. exact (@lem1142998 _26916 P Q). Qed.
Lemma lem1143000 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term193 _26916 _26917 _18906 P) = (term194 _26916 _26917 _18906 P).
Proof. exact (@lem1142999 _26916 (term195 _26916 _26917 _18906 P) (term196 _26916 _26917 _18906 P)). Qed.
Lemma lem1143001 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (s : _26916) : (term197 _26916 _26917 _18906 P s) = (term184 _26916 _26917 _18906 P s).
Proof. exact (eq_refl (term197 _26916 _26917 _18906 P s)). Qed.
Lemma lem1143002 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1143003 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (s : _26916) : (term198 _26916 _26917 _18906 P s) = (term186 _26916 _26917 _18906 P s).
Proof. exact (MK_COMB (@lem1143002) (@lem1143001 _26916 _26917 _18906 P s)). Qed.
Lemma lem1143004 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (s : _26916) : (term199 _26916 _26917 _18906 P s) = (term181 _26916 _26917 _18906 P s).
Proof. exact (eq_refl (term199 _26916 _26917 _18906 P s)). Qed.
Lemma lem1143005 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (s : _26916) : (term200 _26916 _26917 _18906 P s) = (term188 _26916 _26917 _18906 P s).
Proof. exact (MK_COMB (@lem1143003 _26916 _26917 _18906 P s) (@lem1143004 _26916 _26917 _18906 P s)). Qed.
Lemma lem1143006 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term201 _26916 _26917 _18906 P) = (term189 _26916 _26917 _18906 P).
Proof. exact (fun_ext (fun s : _26916 => @lem1143005 _26916 _26917 _18906 P s)). Qed.
Lemma lem1143007 {_26916 : Type'} : (@all _26916) = (@all _26916).
Proof. exact (eq_refl (@all _26916)). Qed.
Lemma lem1143008 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term193 _26916 _26917 _18906 P) = (term190 _26916 _26917 _18906 P).
Proof. exact (MK_COMB (@lem1143007 _26916) (@lem1143006 _26916 _26917 _18906 P)). Qed.
Lemma lem1143009 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1143010 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term202 _26916 _26917 _18906 P) = (term203 _26916 _26917 _18906 P).
Proof. exact (MK_COMB (@lem1143009) (@lem1143008 _26916 _26917 _18906 P)). Qed.
Lemma lem1143011 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (s : _26916) : (term197 _26916 _26917 _18906 P s) = (term184 _26916 _26917 _18906 P s).
Proof. exact (eq_refl (term197 _26916 _26917 _18906 P s)). Qed.
Lemma lem1143012 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term204 _26916 _26917 _18906 P) = (term195 _26916 _26917 _18906 P).
Proof. exact (fun_ext (fun s : _26916 => @lem1143011 _26916 _26917 _18906 P s)). Qed.
Lemma lem1143013 {_26916 : Type'} : (@all _26916) = (@all _26916).
Proof. exact (eq_refl (@all _26916)). Qed.
Lemma lem1143014 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term205 _26916 _26917 _18906 P) = (term206 _26916 _26917 _18906 P).
Proof. exact (MK_COMB (@lem1143013 _26916) (@lem1143012 _26916 _26917 _18906 P)). Qed.
Lemma lem1143015 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1143016 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term207 _26916 _26917 _18906 P) = (term208 _26916 _26917 _18906 P).
Proof. exact (MK_COMB (@lem1143015) (@lem1143014 _26916 _26917 _18906 P)). Qed.
Lemma lem1143017 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (s : _26916) : (term199 _26916 _26917 _18906 P s) = (term181 _26916 _26917 _18906 P s).
Proof. exact (eq_refl (term199 _26916 _26917 _18906 P s)). Qed.
Lemma lem1143018 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term209 _26916 _26917 _18906 P) = (term196 _26916 _26917 _18906 P).
Proof. exact (fun_ext (fun s : _26916 => @lem1143017 _26916 _26917 _18906 P s)). Qed.
Lemma lem1143019 {_26916 : Type'} : (@all _26916) = (@all _26916).
Proof. exact (eq_refl (@all _26916)). Qed.
Lemma lem1143020 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term210 _26916 _26917 _18906 P) = (term211 _26916 _26917 _18906 P).
Proof. exact (MK_COMB (@lem1143019 _26916) (@lem1143018 _26916 _26917 _18906 P)). Qed.
Lemma lem1143021 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term194 _26916 _26917 _18906 P) = (term212 _26916 _26917 _18906 P).
Proof. exact (MK_COMB (@lem1143016 _26916 _26917 _18906 P) (@lem1143020 _26916 _26917 _18906 P)). Qed.
Lemma lem1143022 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : ((term193 _26916 _26917 _18906 P) = (term194 _26916 _26917 _18906 P)) = ((term190 _26916 _26917 _18906 P) = (term212 _26916 _26917 _18906 P)).
Proof. exact (MK_COMB (@lem1143010 _26916 _26917 _18906 P) (@lem1143021 _26916 _26917 _18906 P)). Qed.
Lemma lem1143023 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term190 _26916 _26917 _18906 P) = (term212 _26916 _26917 _18906 P).
Proof. exact (EQ_MP (@lem1143022 _26916 _26917 _18906 P) (@lem1143000 _26916 _26917 _18906 P)). Qed.
Lemma lem1143128 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term191 _26916 _26917 _18906) = (term213 _26916 _26917 _18906).
Proof. exact (fun_ext (fun P : type1470 _26916 _26917 => @lem1143023 _26916 _26917 _18906 P)). Qed.
Lemma lem1143129 {_26916 _26917 : Type'} : (@all (_26917 -> _26916 -> Prop)) = (@all (_26917 -> _26916 -> Prop)).
Proof. exact (eq_refl (@all (_26917 -> _26916 -> Prop))). Qed.
Lemma lem1143130 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term192 _26916 _26917 _18906) = (term214 _26916 _26917 _18906).
Proof. exact (MK_COMB (@lem1143129 _26916 _26917) (@lem1143128 _26916 _26917 _18906)). Qed.
Lemma lem1143132 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term71 A P Q) = (term72 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1143133 {_26916 _26917 : Type'} (P : type745 _26916 _26917) (Q : type745 _26916 _26917) : (term215 _26916 _26917 P Q) = (term216 _26916 _26917 P Q).
Proof. exact (@lem1143132 (type1470 _26916 _26917) P Q). Qed.
Lemma lem1143134 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term217 _26916 _26917 _18906) = (term218 _26916 _26917 _18906).
Proof. exact (@lem1143133 _26916 _26917 (term219 _26916 _26917 _18906) (term220 _26916 _26917 _18906)). Qed.
Lemma lem1143135 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term221 _26916 _26917 _18906 P) = (term206 _26916 _26917 _18906 P).
Proof. exact (eq_refl (term221 _26916 _26917 _18906 P)). Qed.
Lemma lem1143136 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1143137 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term222 _26916 _26917 _18906 P) = (term208 _26916 _26917 _18906 P).
Proof. exact (MK_COMB (@lem1143136) (@lem1143135 _26916 _26917 _18906 P)). Qed.
Lemma lem1143138 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term223 _26916 _26917 _18906 P) = (term211 _26916 _26917 _18906 P).
Proof. exact (eq_refl (term223 _26916 _26917 _18906 P)). Qed.
Lemma lem1143139 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term224 _26916 _26917 _18906 P) = (term212 _26916 _26917 _18906 P).
Proof. exact (MK_COMB (@lem1143137 _26916 _26917 _18906 P) (@lem1143138 _26916 _26917 _18906 P)). Qed.
Lemma lem1143140 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term225 _26916 _26917 _18906) = (term213 _26916 _26917 _18906).
Proof. exact (fun_ext (fun P : type1470 _26916 _26917 => @lem1143139 _26916 _26917 _18906 P)). Qed.
Lemma lem1143141 {_26916 _26917 : Type'} : (@all (_26917 -> _26916 -> Prop)) = (@all (_26917 -> _26916 -> Prop)).
Proof. exact (eq_refl (@all (_26917 -> _26916 -> Prop))). Qed.
Lemma lem1143142 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term217 _26916 _26917 _18906) = (term214 _26916 _26917 _18906).
Proof. exact (MK_COMB (@lem1143141 _26916 _26917) (@lem1143140 _26916 _26917 _18906)). Qed.
Lemma lem1143143 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1143144 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term226 _26916 _26917 _18906) = (term227 _26916 _26917 _18906).
Proof. exact (MK_COMB (@lem1143143) (@lem1143142 _26916 _26917 _18906)). Qed.
Lemma lem1143145 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term221 _26916 _26917 _18906 P) = (term206 _26916 _26917 _18906 P).
Proof. exact (eq_refl (term221 _26916 _26917 _18906 P)). Qed.
Lemma lem1143146 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term228 _26916 _26917 _18906) = (term219 _26916 _26917 _18906).
Proof. exact (fun_ext (fun P : type1470 _26916 _26917 => @lem1143145 _26916 _26917 _18906 P)). Qed.
Lemma lem1143147 {_26916 _26917 : Type'} : (@all (_26917 -> _26916 -> Prop)) = (@all (_26917 -> _26916 -> Prop)).
Proof. exact (eq_refl (@all (_26917 -> _26916 -> Prop))). Qed.
Lemma lem1143148 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term229 _26916 _26917 _18906) = (term230 _26916 _26917 _18906).
Proof. exact (MK_COMB (@lem1143147 _26916 _26917) (@lem1143146 _26916 _26917 _18906)). Qed.
Lemma lem1143149 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1143150 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term231 _26916 _26917 _18906) = (term232 _26916 _26917 _18906).
Proof. exact (MK_COMB (@lem1143149) (@lem1143148 _26916 _26917 _18906)). Qed.
Lemma lem1143151 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term223 _26916 _26917 _18906 P) = (term211 _26916 _26917 _18906 P).
Proof. exact (eq_refl (term223 _26916 _26917 _18906 P)). Qed.
Lemma lem1143152 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term233 _26916 _26917 _18906) = (term220 _26916 _26917 _18906).
Proof. exact (fun_ext (fun P : type1470 _26916 _26917 => @lem1143151 _26916 _26917 _18906 P)). Qed.
Lemma lem1143153 {_26916 _26917 : Type'} : (@all (_26917 -> _26916 -> Prop)) = (@all (_26917 -> _26916 -> Prop)).
Proof. exact (eq_refl (@all (_26917 -> _26916 -> Prop))). Qed.
Lemma lem1143154 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term234 _26916 _26917 _18906) = (term235 _26916 _26917 _18906).
Proof. exact (MK_COMB (@lem1143153 _26916 _26917) (@lem1143152 _26916 _26917 _18906)). Qed.
Lemma lem1143155 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term218 _26916 _26917 _18906) = (term236 _26916 _26917 _18906).
Proof. exact (MK_COMB (@lem1143150 _26916 _26917 _18906) (@lem1143154 _26916 _26917 _18906)). Qed.
Lemma lem1143156 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : ((term217 _26916 _26917 _18906) = (term218 _26916 _26917 _18906)) = ((term214 _26916 _26917 _18906) = (term236 _26916 _26917 _18906)).
Proof. exact (MK_COMB (@lem1143144 _26916 _26917 _18906) (@lem1143155 _26916 _26917 _18906)). Qed.
Lemma lem1143157 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term214 _26916 _26917 _18906) = (term236 _26916 _26917 _18906).
Proof. exact (EQ_MP (@lem1143156 _26916 _26917 _18906) (@lem1143134 _26916 _26917 _18906)). Qed.
Lemma lem1143270 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term192 _26916 _26917 _18906) = (term236 _26916 _26917 _18906).
Proof. exact (TRANS (@lem1143130 _26916 _26917 _18906) (@lem1143157 _26916 _26917 _18906)). Qed.
Lemma lem1143272 {A : Type'} (P : Prop) (Q : A -> Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1143273 {_26917 : Type'} (P : Prop) (Q : _26917 -> Prop) : (term237 _26917 P Q) = (term238 _26917 P Q).
Proof. exact (@lem1143272 _26917 P Q). Qed.
Lemma lem1143274 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (s : _26916) : (term239 _26916 _26917 _18906 P s) = (term240 _26916 _26917 _18906 P s).
Proof. exact (@lem1143273 _26917 (_18906 P s) (term178 _26916 _26917 P s)). Qed.
Lemma lem1143275 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (s : _26916) : (term241 _26916 _26917 P s x) = (term176 _26916 _26917 P x s).
Proof. exact (eq_refl (term241 _26916 _26917 P s x)). Qed.
Lemma lem1143276 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (s : _26916) : (term242 _26916 _26917 P s) = (term178 _26916 _26917 P s).
Proof. exact (fun_ext (fun x : _26917 => @lem1143275 _26916 _26917 P x s)). Qed.
Lemma lem1143277 {_26917 : Type'} : (@ex _26917) = (@ex _26917).
Proof. exact (eq_refl (@ex _26917)). Qed.
Lemma lem1143278 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (s : _26916) : (term243 _26916 _26917 P s) = (term179 _26916 _26917 P s).
Proof. exact (MK_COMB (@lem1143277 _26917) (@lem1143276 _26916 _26917 P s)). Qed.
Lemma lem1143279 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (s : _26916) : (term182 _26916 _26917 _18906 P s) = (term182 _26916 _26917 _18906 P s).
Proof. exact (eq_refl (term182 _26916 _26917 _18906 P s)). Qed.
Lemma lem1143280 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (s : _26916) : (term239 _26916 _26917 _18906 P s) = (term184 _26916 _26917 _18906 P s).
Proof. exact (MK_COMB (@lem1143279 _26916 _26917 _18906 P s) (@lem1143278 _26916 _26917 P s)). Qed.
Lemma lem1143281 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1143282 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (s : _26916) : (term244 _26916 _26917 _18906 P s) = (term245 _26916 _26917 _18906 P s).
Proof. exact (MK_COMB (@lem1143281) (@lem1143280 _26916 _26917 _18906 P s)). Qed.
Lemma lem1143283 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (s : _26916) : (term241 _26916 _26917 P s x) = (term176 _26916 _26917 P x s).
Proof. exact (eq_refl (term241 _26916 _26917 P s x)). Qed.
Lemma lem1143284 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (s : _26916) : (term182 _26916 _26917 _18906 P s) = (term182 _26916 _26917 _18906 P s).
Proof. exact (eq_refl (term182 _26916 _26917 _18906 P s)). Qed.
Lemma lem1143285 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (x : _26917) (s : _26916) : (term246 _26916 _26917 _18906 P s x) = (term247 _26916 _26917 _18906 P x s).
Proof. exact (MK_COMB (@lem1143284 _26916 _26917 _18906 P s) (@lem1143283 _26916 _26917 P x s)). Qed.
Lemma lem1143286 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (s : _26916) : (term248 _26916 _26917 _18906 P s) = (term249 _26916 _26917 _18906 P s).
Proof. exact (fun_ext (fun x : _26917 => @lem1143285 _26916 _26917 _18906 P x s)). Qed.
Lemma lem1143287 {_26917 : Type'} : (@ex _26917) = (@ex _26917).
Proof. exact (eq_refl (@ex _26917)). Qed.
Lemma lem1143288 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (s : _26916) : (term240 _26916 _26917 _18906 P s) = (term250 _26916 _26917 _18906 P s).
Proof. exact (MK_COMB (@lem1143287 _26917) (@lem1143286 _26916 _26917 _18906 P s)). Qed.
Lemma lem1143289 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (s : _26916) : ((term239 _26916 _26917 _18906 P s) = (term240 _26916 _26917 _18906 P s)) = ((term184 _26916 _26917 _18906 P s) = (term250 _26916 _26917 _18906 P s)).
Proof. exact (MK_COMB (@lem1143282 _26916 _26917 _18906 P s) (@lem1143288 _26916 _26917 _18906 P s)). Qed.
Lemma lem1143290 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (s : _26916) : (term184 _26916 _26917 _18906 P s) = (term250 _26916 _26917 _18906 P s).
Proof. exact (EQ_MP (@lem1143289 _26916 _26917 _18906 P s) (@lem1143274 _26916 _26917 _18906 P s)). Qed.
Lemma lem1143291 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term195 _26916 _26917 _18906 P) = (term251 _26916 _26917 _18906 P).
Proof. exact (fun_ext (fun s : _26916 => @lem1143290 _26916 _26917 _18906 P s)). Qed.
Lemma lem1143292 {_26916 : Type'} : (@all _26916) = (@all _26916).
Proof. exact (eq_refl (@all _26916)). Qed.
Lemma lem1143293 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term206 _26916 _26917 _18906 P) = (term252 _26916 _26917 _18906 P).
Proof. exact (MK_COMB (@lem1143292 _26916) (@lem1143291 _26916 _26917 _18906 P)). Qed.
Lemma lem1143295 {A B : Type'} (P : type1413 A B) : (term253 A B P) = (term254 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem1143296 {_26916 _26917 : Type'} (P : type1413 _26916 _26917) : (term253 _26916 _26917 P) = (term254 _26916 _26917 P).
Proof. exact (@lem1143295 _26916 _26917 P). Qed.
Lemma lem1143297 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term255 _26916 _26917 _18906 P) = (term256 _26916 _26917 _18906 P).
Proof. exact (@lem1143296 _26916 _26917 (term257 _26916 _26917 _18906 P)). Qed.
Lemma lem1143298 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (s : _26916) : (term258 _26916 _26917 _18906 P s) = (term249 _26916 _26917 _18906 P s).
Proof. exact (eq_refl (term258 _26916 _26917 _18906 P s)). Qed.
Lemma lem1143299 {_26917 : Type'} (x : _26917) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1143300 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (s : _26916) (x : _26917) : (term259 _26916 _26917 _18906 P s x) = (term260 _26916 _26917 _18906 P s x).
Proof. exact (MK_COMB (@lem1143298 _26916 _26917 _18906 P s) (@lem1143299 _26917 x)). Qed.
Lemma lem1143301 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (x : _26917) (s : _26916) : (term260 _26916 _26917 _18906 P s x) = (term247 _26916 _26917 _18906 P x s).
Proof. exact (eq_refl (term260 _26916 _26917 _18906 P s x)). Qed.
Lemma lem1143302 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (x : _26917) (s : _26916) : (term259 _26916 _26917 _18906 P s x) = (term247 _26916 _26917 _18906 P x s).
Proof. exact (TRANS (@lem1143300 _26916 _26917 _18906 P s x) (@lem1143301 _26916 _26917 _18906 P x s)). Qed.
Lemma lem1143303 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (s : _26916) : (term261 _26916 _26917 _18906 P s) = (term249 _26916 _26917 _18906 P s).
Proof. exact (fun_ext (fun x : _26917 => @lem1143302 _26916 _26917 _18906 P x s)). Qed.
Lemma lem1143304 {_26917 : Type'} : (@ex _26917) = (@ex _26917).
Proof. exact (eq_refl (@ex _26917)). Qed.
Lemma lem1143305 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (s : _26916) : (term262 _26916 _26917 _18906 P s) = (term250 _26916 _26917 _18906 P s).
Proof. exact (MK_COMB (@lem1143304 _26917) (@lem1143303 _26916 _26917 _18906 P s)). Qed.
Lemma lem1143306 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term263 _26916 _26917 _18906 P) = (term251 _26916 _26917 _18906 P).
Proof. exact (fun_ext (fun s : _26916 => @lem1143305 _26916 _26917 _18906 P s)). Qed.
Lemma lem1143307 {_26916 : Type'} : (@all _26916) = (@all _26916).
Proof. exact (eq_refl (@all _26916)). Qed.
Lemma lem1143308 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term255 _26916 _26917 _18906 P) = (term252 _26916 _26917 _18906 P).
Proof. exact (MK_COMB (@lem1143307 _26916) (@lem1143306 _26916 _26917 _18906 P)). Qed.
Lemma lem1143309 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1143310 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term264 _26916 _26917 _18906 P) = (term265 _26916 _26917 _18906 P).
Proof. exact (MK_COMB (@lem1143309) (@lem1143308 _26916 _26917 _18906 P)). Qed.
Lemma lem1143311 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (s : _26916) : (term258 _26916 _26917 _18906 P s) = (term249 _26916 _26917 _18906 P s).
Proof. exact (eq_refl (term258 _26916 _26917 _18906 P s)). Qed.
Lemma lem1143312 {_26916 _26917 : Type'} (x : _26916 -> _26917) (s : _26916) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem1143313 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (x : _26916 -> _26917) (s : _26916) : (term266 _26916 _26917 _18906 P x s) = (term267 _26916 _26917 _18906 P x s).
Proof. exact (MK_COMB (@lem1143311 _26916 _26917 _18906 P s) (@lem1143312 _26916 _26917 x s)). Qed.
Lemma lem1143314 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (x : _26916 -> _26917) (s : _26916) : (term267 _26916 _26917 _18906 P x s) = (term268 _26916 _26917 _18906 P x s).
Proof. exact (eq_refl (term267 _26916 _26917 _18906 P x s)). Qed.
Lemma lem1143315 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (x : _26916 -> _26917) (s : _26916) : (term266 _26916 _26917 _18906 P x s) = (term268 _26916 _26917 _18906 P x s).
Proof. exact (TRANS (@lem1143313 _26916 _26917 _18906 P x s) (@lem1143314 _26916 _26917 _18906 P x s)). Qed.
Lemma lem1143316 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (x : _26916 -> _26917) : (term269 _26916 _26917 _18906 P x) = (term270 _26916 _26917 _18906 P x).
Proof. exact (fun_ext (fun s : _26916 => @lem1143315 _26916 _26917 _18906 P x s)). Qed.
Lemma lem1143317 {_26916 : Type'} : (@all _26916) = (@all _26916).
Proof. exact (eq_refl (@all _26916)). Qed.
Lemma lem1143318 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (x : _26916 -> _26917) : (term271 _26916 _26917 _18906 P x) = (term272 _26916 _26917 _18906 P x).
Proof. exact (MK_COMB (@lem1143317 _26916) (@lem1143316 _26916 _26917 _18906 P x)). Qed.
Lemma lem1143319 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term273 _26916 _26917 _18906 P) = (term274 _26916 _26917 _18906 P).
Proof. exact (fun_ext (fun x : _26916 -> _26917 => @lem1143318 _26916 _26917 _18906 P x)). Qed.
Lemma lem1143320 {_26916 _26917 : Type'} : (@ex (_26916 -> _26917)) = (@ex (_26916 -> _26917)).
Proof. exact (eq_refl (@ex (_26916 -> _26917))). Qed.
Lemma lem1143321 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term256 _26916 _26917 _18906 P) = (term275 _26916 _26917 _18906 P).
Proof. exact (MK_COMB (@lem1143320 _26916 _26917) (@lem1143319 _26916 _26917 _18906 P)). Qed.
Lemma lem1143322 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : ((term255 _26916 _26917 _18906 P) = (term256 _26916 _26917 _18906 P)) = ((term252 _26916 _26917 _18906 P) = (term275 _26916 _26917 _18906 P)).
Proof. exact (MK_COMB (@lem1143310 _26916 _26917 _18906 P) (@lem1143321 _26916 _26917 _18906 P)). Qed.
Lemma lem1143323 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term252 _26916 _26917 _18906 P) = (term275 _26916 _26917 _18906 P).
Proof. exact (EQ_MP (@lem1143322 _26916 _26917 _18906 P) (@lem1143297 _26916 _26917 _18906 P)). Qed.
Lemma lem1143324 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term206 _26916 _26917 _18906 P) = (term275 _26916 _26917 _18906 P).
Proof. exact (TRANS (@lem1143293 _26916 _26917 _18906 P) (@lem1143323 _26916 _26917 _18906 P)). Qed.
Lemma lem1143325 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term219 _26916 _26917 _18906) = (term276 _26916 _26917 _18906).
Proof. exact (fun_ext (fun P : type1470 _26916 _26917 => @lem1143324 _26916 _26917 _18906 P)). Qed.
Lemma lem1143326 {_26916 _26917 : Type'} : (@all (_26917 -> _26916 -> Prop)) = (@all (_26917 -> _26916 -> Prop)).
Proof. exact (eq_refl (@all (_26917 -> _26916 -> Prop))). Qed.
Lemma lem1143327 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term230 _26916 _26917 _18906) = (term277 _26916 _26917 _18906).
Proof. exact (MK_COMB (@lem1143326 _26916 _26917) (@lem1143325 _26916 _26917 _18906)). Qed.
Lemma lem1143329 {A B : Type'} (P : type1413 A B) : (term253 A B P) = (term254 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem1143330 {_26916 _26917 : Type'} (P : type730 _26916 _26917) : (term278 _26916 _26917 P) = (term279 _26916 _26917 P).
Proof. exact (@lem1143329 (type1470 _26916 _26917) (_26916 -> _26917) P). Qed.
Lemma lem1143331 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term280 _26916 _26917 _18906) = (term281 _26916 _26917 _18906).
Proof. exact (@lem1143330 _26916 _26917 (term282 _26916 _26917 _18906)). Qed.
Lemma lem1143332 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term283 _26916 _26917 _18906 P) = (term274 _26916 _26917 _18906 P).
Proof. exact (eq_refl (term283 _26916 _26917 _18906 P)). Qed.
Lemma lem1143333 {_26916 _26917 : Type'} (x : _26916 -> _26917) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1143334 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (x : _26916 -> _26917) : (term284 _26916 _26917 _18906 P x) = (term285 _26916 _26917 _18906 P x).
Proof. exact (MK_COMB (@lem1143332 _26916 _26917 _18906 P) (@lem1143333 _26916 _26917 x)). Qed.
Lemma lem1143335 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (x : _26916 -> _26917) : (term285 _26916 _26917 _18906 P x) = (term272 _26916 _26917 _18906 P x).
Proof. exact (eq_refl (term285 _26916 _26917 _18906 P x)). Qed.
Lemma lem1143336 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (x : _26916 -> _26917) : (term284 _26916 _26917 _18906 P x) = (term272 _26916 _26917 _18906 P x).
Proof. exact (TRANS (@lem1143334 _26916 _26917 _18906 P x) (@lem1143335 _26916 _26917 _18906 P x)). Qed.
Lemma lem1143337 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term286 _26916 _26917 _18906 P) = (term274 _26916 _26917 _18906 P).
Proof. exact (fun_ext (fun x : _26916 -> _26917 => @lem1143336 _26916 _26917 _18906 P x)). Qed.
Lemma lem1143338 {_26916 _26917 : Type'} : (@ex (_26916 -> _26917)) = (@ex (_26916 -> _26917)).
Proof. exact (eq_refl (@ex (_26916 -> _26917))). Qed.
Lemma lem1143339 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term287 _26916 _26917 _18906 P) = (term275 _26916 _26917 _18906 P).
Proof. exact (MK_COMB (@lem1143338 _26916 _26917) (@lem1143337 _26916 _26917 _18906 P)). Qed.
Lemma lem1143340 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term288 _26916 _26917 _18906) = (term276 _26916 _26917 _18906).
Proof. exact (fun_ext (fun P : type1470 _26916 _26917 => @lem1143339 _26916 _26917 _18906 P)). Qed.
Lemma lem1143341 {_26916 _26917 : Type'} : (@all (_26917 -> _26916 -> Prop)) = (@all (_26917 -> _26916 -> Prop)).
Proof. exact (eq_refl (@all (_26917 -> _26916 -> Prop))). Qed.
Lemma lem1143342 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term280 _26916 _26917 _18906) = (term277 _26916 _26917 _18906).
Proof. exact (MK_COMB (@lem1143341 _26916 _26917) (@lem1143340 _26916 _26917 _18906)). Qed.
Lemma lem1143343 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1143344 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term289 _26916 _26917 _18906) = (term290 _26916 _26917 _18906).
Proof. exact (MK_COMB (@lem1143343) (@lem1143342 _26916 _26917 _18906)). Qed.
Lemma lem1143345 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term283 _26916 _26917 _18906 P) = (term274 _26916 _26917 _18906 P).
Proof. exact (eq_refl (term283 _26916 _26917 _18906 P)). Qed.
Lemma lem1143346 {_26916 _26917 : Type'} (x : type739 _26916 _26917) (P : type1470 _26916 _26917) : (x P) = (x P).
Proof. exact (eq_refl (x P)). Qed.
Lemma lem1143347 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (x : type739 _26916 _26917) (P : type1470 _26916 _26917) : (term291 _26916 _26917 _18906 x P) = (term292 _26916 _26917 _18906 x P).
Proof. exact (MK_COMB (@lem1143345 _26916 _26917 _18906 P) (@lem1143346 _26916 _26917 x P)). Qed.
Lemma lem1143348 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (x : type739 _26916 _26917) (P : type1470 _26916 _26917) : (term292 _26916 _26917 _18906 x P) = (term293 _26916 _26917 _18906 x P).
Proof. exact (eq_refl (term292 _26916 _26917 _18906 x P)). Qed.
Lemma lem1143349 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (x : type739 _26916 _26917) (P : type1470 _26916 _26917) : (term291 _26916 _26917 _18906 x P) = (term293 _26916 _26917 _18906 x P).
Proof. exact (TRANS (@lem1143347 _26916 _26917 _18906 x P) (@lem1143348 _26916 _26917 _18906 x P)). Qed.
Lemma lem1143350 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (x : type739 _26916 _26917) : (term294 _26916 _26917 _18906 x) = (term295 _26916 _26917 _18906 x).
Proof. exact (fun_ext (fun P : type1470 _26916 _26917 => @lem1143349 _26916 _26917 _18906 x P)). Qed.
Lemma lem1143351 {_26916 _26917 : Type'} : (@all (_26917 -> _26916 -> Prop)) = (@all (_26917 -> _26916 -> Prop)).
Proof. exact (eq_refl (@all (_26917 -> _26916 -> Prop))). Qed.
Lemma lem1143352 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (x : type739 _26916 _26917) : (term296 _26916 _26917 _18906 x) = (term297 _26916 _26917 _18906 x).
Proof. exact (MK_COMB (@lem1143351 _26916 _26917) (@lem1143350 _26916 _26917 _18906 x)). Qed.
Lemma lem1143353 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term298 _26916 _26917 _18906) = (term299 _26916 _26917 _18906).
Proof. exact (fun_ext (fun x : type739 _26916 _26917 => @lem1143352 _26916 _26917 _18906 x)). Qed.
Lemma lem1143354 {_26916 _26917 : Type'} : (@ex ((_26917 -> _26916 -> Prop) -> _26916 -> _26917)) = (@ex ((_26917 -> _26916 -> Prop) -> _26916 -> _26917)).
Proof. exact (eq_refl (@ex ((_26917 -> _26916 -> Prop) -> _26916 -> _26917))). Qed.
Lemma lem1143355 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term281 _26916 _26917 _18906) = (term300 _26916 _26917 _18906).
Proof. exact (MK_COMB (@lem1143354 _26916 _26917) (@lem1143353 _26916 _26917 _18906)). Qed.
Lemma lem1143356 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : ((term280 _26916 _26917 _18906) = (term281 _26916 _26917 _18906)) = ((term277 _26916 _26917 _18906) = (term300 _26916 _26917 _18906)).
Proof. exact (MK_COMB (@lem1143344 _26916 _26917 _18906) (@lem1143355 _26916 _26917 _18906)). Qed.
Lemma lem1143357 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term277 _26916 _26917 _18906) = (term300 _26916 _26917 _18906).
Proof. exact (EQ_MP (@lem1143356 _26916 _26917 _18906) (@lem1143331 _26916 _26917 _18906)). Qed.
Lemma lem1143358 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term230 _26916 _26917 _18906) = (term300 _26916 _26917 _18906).
Proof. exact (TRANS (@lem1143327 _26916 _26917 _18906) (@lem1143357 _26916 _26917 _18906)). Qed.
Lemma lem1143359 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1143360 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term232 _26916 _26917 _18906) = (term301 _26916 _26917 _18906).
Proof. exact (MK_COMB (@lem1143359) (@lem1143358 _26916 _26917 _18906)). Qed.
Lemma lem1143361 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term235 _26916 _26917 _18906) = (term235 _26916 _26917 _18906).
Proof. exact (eq_refl (term235 _26916 _26917 _18906)). Qed.
Lemma lem1143362 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term236 _26916 _26917 _18906) = (term302 _26916 _26917 _18906).
Proof. exact (MK_COMB (@lem1143360 _26916 _26917 _18906) (@lem1143361 _26916 _26917 _18906)). Qed.
Lemma lem1143364 {A : Type'} (P : A -> Prop) (Q : Prop) : (term303 A P Q) = (term304 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1143365 {_26916 _26917 : Type'} (P : type189 _26916 _26917) (Q : Prop) : (term305 _26916 _26917 P Q) = (term306 _26916 _26917 P Q).
Proof. exact (@lem1143364 (type739 _26916 _26917) P Q). Qed.
Lemma lem1143366 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term307 _26916 _26917 _18906) = (term308 _26916 _26917 _18906).
Proof. exact (@lem1143365 _26916 _26917 (term299 _26916 _26917 _18906) (term235 _26916 _26917 _18906)). Qed.
Lemma lem1143367 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (x : type739 _26916 _26917) : (term309 _26916 _26917 _18906 x) = (term297 _26916 _26917 _18906 x).
Proof. exact (eq_refl (term309 _26916 _26917 _18906 x)). Qed.
Lemma lem1143368 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term310 _26916 _26917 _18906) = (term299 _26916 _26917 _18906).
Proof. exact (fun_ext (fun x : type739 _26916 _26917 => @lem1143367 _26916 _26917 _18906 x)). Qed.
Lemma lem1143369 {_26916 _26917 : Type'} : (@ex ((_26917 -> _26916 -> Prop) -> _26916 -> _26917)) = (@ex ((_26917 -> _26916 -> Prop) -> _26916 -> _26917)).
Proof. exact (eq_refl (@ex ((_26917 -> _26916 -> Prop) -> _26916 -> _26917))). Qed.
Lemma lem1143370 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term311 _26916 _26917 _18906) = (term300 _26916 _26917 _18906).
Proof. exact (MK_COMB (@lem1143369 _26916 _26917) (@lem1143368 _26916 _26917 _18906)). Qed.
Lemma lem1143371 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1143372 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term312 _26916 _26917 _18906) = (term301 _26916 _26917 _18906).
Proof. exact (MK_COMB (@lem1143371) (@lem1143370 _26916 _26917 _18906)). Qed.
Lemma lem1143373 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term235 _26916 _26917 _18906) = (term235 _26916 _26917 _18906).
Proof. exact (eq_refl (term235 _26916 _26917 _18906)). Qed.
Lemma lem1143374 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term307 _26916 _26917 _18906) = (term302 _26916 _26917 _18906).
Proof. exact (MK_COMB (@lem1143372 _26916 _26917 _18906) (@lem1143373 _26916 _26917 _18906)). Qed.
Lemma lem1143375 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1143376 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term313 _26916 _26917 _18906) = (term314 _26916 _26917 _18906).
Proof. exact (MK_COMB (@lem1143375) (@lem1143374 _26916 _26917 _18906)). Qed.
Lemma lem1143377 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (x : type739 _26916 _26917) : (term309 _26916 _26917 _18906 x) = (term297 _26916 _26917 _18906 x).
Proof. exact (eq_refl (term309 _26916 _26917 _18906 x)). Qed.
Lemma lem1143378 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1143379 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (x : type739 _26916 _26917) : (term315 _26916 _26917 _18906 x) = (term316 _26916 _26917 _18906 x).
Proof. exact (MK_COMB (@lem1143378) (@lem1143377 _26916 _26917 _18906 x)). Qed.
Lemma lem1143380 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term235 _26916 _26917 _18906) = (term235 _26916 _26917 _18906).
Proof. exact (eq_refl (term235 _26916 _26917 _18906)). Qed.
Lemma lem1143381 {_26916 _26917 : Type'} (x : type739 _26916 _26917) (_18906 : type740 _26916 _26917) : (term317 _26916 _26917 x _18906) = (term318 _26916 _26917 x _18906).
Proof. exact (MK_COMB (@lem1143379 _26916 _26917 _18906 x) (@lem1143380 _26916 _26917 _18906)). Qed.
Lemma lem1143382 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term319 _26916 _26917 _18906) = (term320 _26916 _26917 _18906).
Proof. exact (fun_ext (fun x : type739 _26916 _26917 => @lem1143381 _26916 _26917 x _18906)). Qed.
Lemma lem1143383 {_26916 _26917 : Type'} : (@ex ((_26917 -> _26916 -> Prop) -> _26916 -> _26917)) = (@ex ((_26917 -> _26916 -> Prop) -> _26916 -> _26917)).
Proof. exact (eq_refl (@ex ((_26917 -> _26916 -> Prop) -> _26916 -> _26917))). Qed.
Lemma lem1143384 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term308 _26916 _26917 _18906) = (term321 _26916 _26917 _18906).
Proof. exact (MK_COMB (@lem1143383 _26916 _26917) (@lem1143382 _26916 _26917 _18906)). Qed.
Lemma lem1143385 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : ((term307 _26916 _26917 _18906) = (term308 _26916 _26917 _18906)) = ((term302 _26916 _26917 _18906) = (term321 _26916 _26917 _18906)).
Proof. exact (MK_COMB (@lem1143376 _26916 _26917 _18906) (@lem1143384 _26916 _26917 _18906)). Qed.
Lemma lem1143386 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term302 _26916 _26917 _18906) = (term321 _26916 _26917 _18906).
Proof. exact (EQ_MP (@lem1143385 _26916 _26917 _18906) (@lem1143366 _26916 _26917 _18906)). Qed.
Lemma lem1143387 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term236 _26916 _26917 _18906) = (term321 _26916 _26917 _18906).
Proof. exact (TRANS (@lem1143362 _26916 _26917 _18906) (@lem1143386 _26916 _26917 _18906)). Qed.
Lemma lem1143388 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term192 _26916 _26917 _18906) = (term321 _26916 _26917 _18906).
Proof. exact (TRANS (@lem1143270 _26916 _26917 _18906) (@lem1143387 _26916 _26917 _18906)). Qed.
Lemma lem1143389 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : (term164 _26916 _26917 _18906) = (term321 _26916 _26917 _18906).
Proof. exact (TRANS (@lem1142992 _26916 _26917 _18906) (@lem1143388 _26916 _26917 _18906)). Qed.
Lemma lem1143390 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (h1 : term164 _26916 _26917 _18906) : term321 _26916 _26917 _18906.
Proof. exact (EQ_MP (@lem1143389 _26916 _26917 _18906) (@lem1142952 _26916 _26917 _18906 h1)). Qed.
Lemma lem1143392 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term81 _26916 _26917 P x t) = (term81 _26916 _26917 P x t).
Proof. exact (eq_refl (term81 _26916 _26917 P x t)). Qed.
Lemma lem1143393 {_26917 : Type'} (P : _26917 -> Prop) : (term171 _26917 P) = (term172 _26917 P).
Proof. exact (@lem18392 _26917 P). Qed.
Lemma lem1143394 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term322 _26916 _26917 P t) = (term323 _26916 _26917 P t).
Proof. exact (@lem1143393 _26917 (term76 _26916 _26917 P t)). Qed.
Lemma lem1143395 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term80 _26916 _26917 P t x) = (term81 _26916 _26917 P x t).
Proof. exact (eq_refl (term80 _26916 _26917 P t x)). Qed.
Lemma lem1143396 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1143398 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term324 _26916 _26917 P t x) = (term325 _26916 _26917 P x t).
Proof. exact (MK_COMB (@lem1143396) (@lem1143395 _26916 _26917 P x t)). Qed.
Lemma lem1143399 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term326 _26916 _26917 P t) = (term327 _26916 _26917 P t).
Proof. exact (fun_ext (fun x : _26917 => @lem1143398 _26916 _26917 P x t)). Qed.
Lemma lem1143400 {_26917 : Type'} : (@ex _26917) = (@ex _26917).
Proof. exact (eq_refl (@ex _26917)). Qed.
Lemma lem1143401 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term323 _26916 _26917 P t) = (term328 _26916 _26917 P t).
Proof. exact (MK_COMB (@lem1143400 _26917) (@lem1143399 _26916 _26917 P t)). Qed.
Lemma lem1143402 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term322 _26916 _26917 P t) = (term328 _26916 _26917 P t).
Proof. exact (TRANS (@lem1143394 _26916 _26917 P t) (@lem1143401 _26916 _26917 P t)). Qed.
Lemma lem1143403 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term76 _26916 _26917 P t) = (term76 _26916 _26917 P t).
Proof. exact (fun_ext (fun x : _26917 => @lem1143392 _26916 _26917 P x t)). Qed.
Lemma lem1143404 {_26917 : Type'} : (@all _26917) = (@all _26917).
Proof. exact (eq_refl (@all _26917)). Qed.
Lemma lem1143405 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term9 _26916 _26917 P t) = (term9 _26916 _26917 P t).
Proof. exact (MK_COMB (@lem1143404 _26917) (@lem1143403 _26916 _26917 P t)). Qed.
Lemma lem1143406 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term329 _26916 _26917 _18906 P t) = (term329 _26916 _26917 _18906 P t).
Proof. exact (eq_refl (term329 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143407 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term110 _26916 _26917 _18906 P t) = (term110 _26916 _26917 _18906 P t).
Proof. exact (eq_refl (term110 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143408 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1143409 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term330 _26916 _26917 P t) = (term331 _26916 _26917 P t).
Proof. exact (MK_COMB (@lem1143408) (@lem1143402 _26916 _26917 P t)). Qed.
Lemma lem1143410 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term332 _26916 _26917 _18906 P t) = (term333 _26916 _26917 _18906 P t).
Proof. exact (MK_COMB (@lem1143409 _26916 _26917 P t) (@lem1143406 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143411 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1143412 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term334 _26916 _26917 P t) = (term334 _26916 _26917 P t).
Proof. exact (MK_COMB (@lem1143411) (@lem1143405 _26916 _26917 P t)). Qed.
Lemma lem1143413 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term335 _26916 _26917 _18906 P t) = (term335 _26916 _26917 _18906 P t).
Proof. exact (MK_COMB (@lem1143412 _26916 _26917 P t) (@lem1143407 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143414 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1143415 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term336 _26916 _26917 _18906 P t) = (term336 _26916 _26917 _18906 P t).
Proof. exact (MK_COMB (@lem1143414) (@lem1143413 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143416 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term337 _26916 _26917 _18906 P t) = (term338 _26916 _26917 _18906 P t).
Proof. exact (MK_COMB (@lem1143415 _26916 _26917 _18906 P t) (@lem1143410 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143417 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : ((term9 _26916 _26917 P t) = (term110 _26916 _26917 _18906 P t)) = (term337 _26916 _26917 _18906 P t).
Proof. exact (@lem17500 (term9 _26916 _26917 P t) (term110 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143418 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : ((term9 _26916 _26917 P t) = (term110 _26916 _26917 _18906 P t)) = (term338 _26916 _26917 _18906 P t).
Proof. exact (TRANS (@lem1143417 _26916 _26917 _18906 P t) (@lem1143416 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143429 {A : Type'} (P : A -> Prop) (Q : Prop) : (term303 A P Q) = (term304 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1143430 {_26917 : Type'} (P : _26917 -> Prop) (Q : Prop) : (term303 _26917 P Q) = (term304 _26917 P Q).
Proof. exact (@lem1143429 _26917 P Q). Qed.
Lemma lem1143431 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term339 _26916 _26917 _18906 P t) = (term340 _26916 _26917 _18906 P t).
Proof. exact (@lem1143430 _26917 (term327 _26916 _26917 P t) (term329 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143432 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term341 _26916 _26917 P t x) = (term325 _26916 _26917 P x t).
Proof. exact (eq_refl (term341 _26916 _26917 P t x)). Qed.
Lemma lem1143433 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term342 _26916 _26917 P t) = (term327 _26916 _26917 P t).
Proof. exact (fun_ext (fun x : _26917 => @lem1143432 _26916 _26917 P x t)). Qed.
Lemma lem1143434 {_26917 : Type'} : (@ex _26917) = (@ex _26917).
Proof. exact (eq_refl (@ex _26917)). Qed.
Lemma lem1143435 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term343 _26916 _26917 P t) = (term328 _26916 _26917 P t).
Proof. exact (MK_COMB (@lem1143434 _26917) (@lem1143433 _26916 _26917 P t)). Qed.
Lemma lem1143436 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1143437 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term344 _26916 _26917 P t) = (term331 _26916 _26917 P t).
Proof. exact (MK_COMB (@lem1143436) (@lem1143435 _26916 _26917 P t)). Qed.
Lemma lem1143438 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term329 _26916 _26917 _18906 P t) = (term329 _26916 _26917 _18906 P t).
Proof. exact (eq_refl (term329 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143439 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term339 _26916 _26917 _18906 P t) = (term333 _26916 _26917 _18906 P t).
Proof. exact (MK_COMB (@lem1143437 _26916 _26917 P t) (@lem1143438 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143440 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1143441 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term345 _26916 _26917 _18906 P t) = (term346 _26916 _26917 _18906 P t).
Proof. exact (MK_COMB (@lem1143440) (@lem1143439 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143442 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term341 _26916 _26917 P t x) = (term325 _26916 _26917 P x t).
Proof. exact (eq_refl (term341 _26916 _26917 P t x)). Qed.
Lemma lem1143443 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1143444 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term347 _26916 _26917 P t x) = (term348 _26916 _26917 P x t).
Proof. exact (MK_COMB (@lem1143443) (@lem1143442 _26916 _26917 P x t)). Qed.
Lemma lem1143445 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term329 _26916 _26917 _18906 P t) = (term329 _26916 _26917 _18906 P t).
Proof. exact (eq_refl (term329 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143446 {_26916 _26917 : Type'} (x : _26917) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term349 _26916 _26917 x _18906 P t) = (term350 _26916 _26917 x _18906 P t).
Proof. exact (MK_COMB (@lem1143444 _26916 _26917 P x t) (@lem1143445 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143447 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term351 _26916 _26917 _18906 P t) = (term352 _26916 _26917 _18906 P t).
Proof. exact (fun_ext (fun x : _26917 => @lem1143446 _26916 _26917 x _18906 P t)). Qed.
Lemma lem1143448 {_26917 : Type'} : (@ex _26917) = (@ex _26917).
Proof. exact (eq_refl (@ex _26917)). Qed.
Lemma lem1143449 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term340 _26916 _26917 _18906 P t) = (term353 _26916 _26917 _18906 P t).
Proof. exact (MK_COMB (@lem1143448 _26917) (@lem1143447 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143450 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : ((term339 _26916 _26917 _18906 P t) = (term340 _26916 _26917 _18906 P t)) = ((term333 _26916 _26917 _18906 P t) = (term353 _26916 _26917 _18906 P t)).
Proof. exact (MK_COMB (@lem1143441 _26916 _26917 _18906 P t) (@lem1143449 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143451 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term333 _26916 _26917 _18906 P t) = (term353 _26916 _26917 _18906 P t).
Proof. exact (EQ_MP (@lem1143450 _26916 _26917 _18906 P t) (@lem1143431 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143452 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term336 _26916 _26917 _18906 P t) = (term336 _26916 _26917 _18906 P t).
Proof. exact (eq_refl (term336 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143453 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term338 _26916 _26917 _18906 P t) = (term354 _26916 _26917 _18906 P t).
Proof. exact (MK_COMB (@lem1143452 _26916 _26917 _18906 P t) (@lem1143451 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143455 {A : Type'} (P : Prop) (Q : A -> Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1143456 {_26917 : Type'} (P : Prop) (Q : _26917 -> Prop) : (term237 _26917 P Q) = (term238 _26917 P Q).
Proof. exact (@lem1143455 _26917 P Q). Qed.
Lemma lem1143457 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term355 _26916 _26917 _18906 P t) = (term356 _26916 _26917 _18906 P t).
Proof. exact (@lem1143456 _26917 (term335 _26916 _26917 _18906 P t) (term352 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143458 {_26916 _26917 : Type'} (x : _26917) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term357 _26916 _26917 _18906 P t x) = (term350 _26916 _26917 x _18906 P t).
Proof. exact (eq_refl (term357 _26916 _26917 _18906 P t x)). Qed.
Lemma lem1143459 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term358 _26916 _26917 _18906 P t) = (term352 _26916 _26917 _18906 P t).
Proof. exact (fun_ext (fun x : _26917 => @lem1143458 _26916 _26917 x _18906 P t)). Qed.
Lemma lem1143460 {_26917 : Type'} : (@ex _26917) = (@ex _26917).
Proof. exact (eq_refl (@ex _26917)). Qed.
Lemma lem1143461 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term359 _26916 _26917 _18906 P t) = (term353 _26916 _26917 _18906 P t).
Proof. exact (MK_COMB (@lem1143460 _26917) (@lem1143459 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143462 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term336 _26916 _26917 _18906 P t) = (term336 _26916 _26917 _18906 P t).
Proof. exact (eq_refl (term336 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143463 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term355 _26916 _26917 _18906 P t) = (term354 _26916 _26917 _18906 P t).
Proof. exact (MK_COMB (@lem1143462 _26916 _26917 _18906 P t) (@lem1143461 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143464 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1143465 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term360 _26916 _26917 _18906 P t) = (term361 _26916 _26917 _18906 P t).
Proof. exact (MK_COMB (@lem1143464) (@lem1143463 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143466 {_26916 _26917 : Type'} (x : _26917) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term357 _26916 _26917 _18906 P t x) = (term350 _26916 _26917 x _18906 P t).
Proof. exact (eq_refl (term357 _26916 _26917 _18906 P t x)). Qed.
Lemma lem1143467 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term336 _26916 _26917 _18906 P t) = (term336 _26916 _26917 _18906 P t).
Proof. exact (eq_refl (term336 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143468 {_26916 _26917 : Type'} (x : _26917) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term362 _26916 _26917 _18906 P t x) = (term363 _26916 _26917 x _18906 P t).
Proof. exact (MK_COMB (@lem1143467 _26916 _26917 _18906 P t) (@lem1143466 _26916 _26917 x _18906 P t)). Qed.
Lemma lem1143469 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term364 _26916 _26917 _18906 P t) = (term365 _26916 _26917 _18906 P t).
Proof. exact (fun_ext (fun x : _26917 => @lem1143468 _26916 _26917 x _18906 P t)). Qed.
Lemma lem1143470 {_26917 : Type'} : (@ex _26917) = (@ex _26917).
Proof. exact (eq_refl (@ex _26917)). Qed.
Lemma lem1143471 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term356 _26916 _26917 _18906 P t) = (term366 _26916 _26917 _18906 P t).
Proof. exact (MK_COMB (@lem1143470 _26917) (@lem1143469 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143472 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : ((term355 _26916 _26917 _18906 P t) = (term356 _26916 _26917 _18906 P t)) = ((term354 _26916 _26917 _18906 P t) = (term366 _26916 _26917 _18906 P t)).
Proof. exact (MK_COMB (@lem1143465 _26916 _26917 _18906 P t) (@lem1143471 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143473 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term354 _26916 _26917 _18906 P t) = (term366 _26916 _26917 _18906 P t).
Proof. exact (EQ_MP (@lem1143472 _26916 _26917 _18906 P t) (@lem1143457 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143475 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term338 _26916 _26917 _18906 P t) = (term366 _26916 _26917 _18906 P t).
Proof. exact (TRANS (@lem1143453 _26916 _26917 _18906 P t) (@lem1143473 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143476 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : ((term9 _26916 _26917 P t) = (term110 _26916 _26917 _18906 P t)) = (term366 _26916 _26917 _18906 P t).
Proof. exact (TRANS (@lem1143418 _26916 _26917 _18906 P t) (@lem1143475 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143477 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : (term9 _26916 _26917 P t) = (term110 _26916 _26917 _18906 P t)) : term366 _26916 _26917 _18906 P t.
Proof. exact (EQ_MP (@lem1143476 _26916 _26917 _18906 P t) (@lem1142953 _26916 _26917 _18906 P t h1)). Qed.
Lemma lem1143479 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (P x h) = (P x h).
Proof. exact (eq_refl (P x h)). Qed.
Lemma lem1143480 {_26917 : Type'} (P : _26917 -> Prop) : (term171 _26917 P) = (term172 _26917 P).
Proof. exact (@lem18392 _26917 P). Qed.
Lemma lem1143481 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term173 _26916 _26917 P h) = (term174 _26916 _26917 P h).
Proof. exact (@lem1143480 _26917 (term75 _26916 _26917 P h)). Qed.
Lemma lem1143482 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (term77 _26916 _26917 P h x) = (P x h).
Proof. exact (eq_refl (term77 _26916 _26917 P h x)). Qed.
Lemma lem1143483 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1143485 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (term175 _26916 _26917 P h x) = (term176 _26916 _26917 P x h).
Proof. exact (MK_COMB (@lem1143483) (@lem1143482 _26916 _26917 P x h)). Qed.
Lemma lem1143486 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term177 _26916 _26917 P h) = (term178 _26916 _26917 P h).
Proof. exact (fun_ext (fun x : _26917 => @lem1143485 _26916 _26917 P x h)). Qed.
Lemma lem1143487 {_26917 : Type'} : (@ex _26917) = (@ex _26917).
Proof. exact (eq_refl (@ex _26917)). Qed.
Lemma lem1143488 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term174 _26916 _26917 P h) = (term179 _26916 _26917 P h).
Proof. exact (MK_COMB (@lem1143487 _26917) (@lem1143486 _26916 _26917 P h)). Qed.
Lemma lem1143489 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term173 _26916 _26917 P h) = (term179 _26916 _26917 P h).
Proof. exact (TRANS (@lem1143481 _26916 _26917 P h) (@lem1143488 _26916 _26917 P h)). Qed.
Lemma lem1143490 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term75 _26916 _26917 P h) = (term75 _26916 _26917 P h).
Proof. exact (fun_ext (fun x : _26917 => @lem1143479 _26916 _26917 P x h)). Qed.
Lemma lem1143491 {_26917 : Type'} : (@all _26917) = (@all _26917).
Proof. exact (eq_refl (@all _26917)). Qed.
Lemma lem1143492 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term55 _26916 _26917 P h) = (term55 _26916 _26917 P h).
Proof. exact (MK_COMB (@lem1143491 _26917) (@lem1143490 _26916 _26917 P h)). Qed.
Lemma lem1143494 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term81 _26916 _26917 P x t) = (term81 _26916 _26917 P x t).
Proof. exact (eq_refl (term81 _26916 _26917 P x t)). Qed.
Lemma lem1143495 {_26917 : Type'} (P : _26917 -> Prop) : (term171 _26917 P) = (term172 _26917 P).
Proof. exact (@lem18392 _26917 P). Qed.
Lemma lem1143496 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term322 _26916 _26917 P t) = (term323 _26916 _26917 P t).
Proof. exact (@lem1143495 _26917 (term76 _26916 _26917 P t)). Qed.
Lemma lem1143497 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term80 _26916 _26917 P t x) = (term81 _26916 _26917 P x t).
Proof. exact (eq_refl (term80 _26916 _26917 P t x)). Qed.
Lemma lem1143498 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1143500 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term324 _26916 _26917 P t x) = (term325 _26916 _26917 P x t).
Proof. exact (MK_COMB (@lem1143498) (@lem1143497 _26916 _26917 P x t)). Qed.
Lemma lem1143501 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term326 _26916 _26917 P t) = (term327 _26916 _26917 P t).
Proof. exact (fun_ext (fun x : _26917 => @lem1143500 _26916 _26917 P x t)). Qed.
Lemma lem1143502 {_26917 : Type'} : (@ex _26917) = (@ex _26917).
Proof. exact (eq_refl (@ex _26917)). Qed.
Lemma lem1143503 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term323 _26916 _26917 P t) = (term328 _26916 _26917 P t).
Proof. exact (MK_COMB (@lem1143502 _26917) (@lem1143501 _26916 _26917 P t)). Qed.
Lemma lem1143504 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term322 _26916 _26917 P t) = (term328 _26916 _26917 P t).
Proof. exact (TRANS (@lem1143496 _26916 _26917 P t) (@lem1143503 _26916 _26917 P t)). Qed.
Lemma lem1143505 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term76 _26916 _26917 P t) = (term76 _26916 _26917 P t).
Proof. exact (fun_ext (fun x : _26917 => @lem1143494 _26916 _26917 P x t)). Qed.
Lemma lem1143506 {_26917 : Type'} : (@all _26917) = (@all _26917).
Proof. exact (eq_refl (@all _26917)). Qed.
Lemma lem1143507 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term9 _26916 _26917 P t) = (term9 _26916 _26917 P t).
Proof. exact (MK_COMB (@lem1143506 _26917) (@lem1143505 _26916 _26917 P t)). Qed.
Lemma lem1143508 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1143509 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term367 _26916 _26917 P h) = (term368 _26916 _26917 P h).
Proof. exact (MK_COMB (@lem1143508) (@lem1143489 _26916 _26917 P h)). Qed.
Lemma lem1143510 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term369 _26916 _26917 h P t) = (term370 _26916 _26917 h P t).
Proof. exact (MK_COMB (@lem1143509 _26916 _26917 P h) (@lem1143504 _26916 _26917 P t)). Qed.
Lemma lem1143511 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term371 _26916 _26917 h P t) = (term369 _26916 _26917 h P t).
Proof. exact (@lem17045 (term55 _26916 _26917 P h) (term9 _26916 _26917 P t)). Qed.
Lemma lem1143512 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term371 _26916 _26917 h P t) = (term370 _26916 _26917 h P t).
Proof. exact (TRANS (@lem1143511 _26916 _26917 h P t) (@lem1143510 _26916 _26917 h P t)). Qed.
Lemma lem1143513 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1143514 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term60 _26916 _26917 P h) = (term60 _26916 _26917 P h).
Proof. exact (MK_COMB (@lem1143513) (@lem1143492 _26916 _26917 P h)). Qed.
Lemma lem1143515 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term90 _26916 _26917 h P t) = (term90 _26916 _26917 h P t).
Proof. exact (MK_COMB (@lem1143514 _26916 _26917 P h) (@lem1143507 _26916 _26917 P t)). Qed.
Lemma lem1143517 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (P x h) = (P x h).
Proof. exact (eq_refl (P x h)). Qed.
Lemma lem1143518 {_26917 : Type'} (P : _26917 -> Prop) : (term171 _26917 P) = (term172 _26917 P).
Proof. exact (@lem18392 _26917 P). Qed.
Lemma lem1143519 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term173 _26916 _26917 P h) = (term174 _26916 _26917 P h).
Proof. exact (@lem1143518 _26917 (term75 _26916 _26917 P h)). Qed.
Lemma lem1143520 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (term77 _26916 _26917 P h x) = (P x h).
Proof. exact (eq_refl (term77 _26916 _26917 P h x)). Qed.
Lemma lem1143521 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1143523 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (term175 _26916 _26917 P h x) = (term176 _26916 _26917 P x h).
Proof. exact (MK_COMB (@lem1143521) (@lem1143520 _26916 _26917 P x h)). Qed.
Lemma lem1143524 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term177 _26916 _26917 P h) = (term178 _26916 _26917 P h).
Proof. exact (fun_ext (fun x : _26917 => @lem1143523 _26916 _26917 P x h)). Qed.
Lemma lem1143525 {_26917 : Type'} : (@ex _26917) = (@ex _26917).
Proof. exact (eq_refl (@ex _26917)). Qed.
Lemma lem1143526 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term174 _26916 _26917 P h) = (term179 _26916 _26917 P h).
Proof. exact (MK_COMB (@lem1143525 _26917) (@lem1143524 _26916 _26917 P h)). Qed.
Lemma lem1143527 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term173 _26916 _26917 P h) = (term179 _26916 _26917 P h).
Proof. exact (TRANS (@lem1143519 _26916 _26917 P h) (@lem1143526 _26916 _26917 P h)). Qed.
Lemma lem1143528 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term75 _26916 _26917 P h) = (term75 _26916 _26917 P h).
Proof. exact (fun_ext (fun x : _26917 => @lem1143517 _26916 _26917 P x h)). Qed.
Lemma lem1143529 {_26917 : Type'} : (@all _26917) = (@all _26917).
Proof. exact (eq_refl (@all _26917)). Qed.
Lemma lem1143530 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term55 _26916 _26917 P h) = (term55 _26916 _26917 P h).
Proof. exact (MK_COMB (@lem1143529 _26917) (@lem1143528 _26916 _26917 P h)). Qed.
Lemma lem1143531 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term329 _26916 _26917 _18906 P t) = (term329 _26916 _26917 _18906 P t).
Proof. exact (eq_refl (term329 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143532 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term110 _26916 _26917 _18906 P t) = (term110 _26916 _26917 _18906 P t).
Proof. exact (eq_refl (term110 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143533 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1143534 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term367 _26916 _26917 P h) = (term368 _26916 _26917 P h).
Proof. exact (MK_COMB (@lem1143533) (@lem1143527 _26916 _26917 P h)). Qed.
Lemma lem1143535 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term372 _26916 _26917 h _18906 P t) = (term373 _26916 _26917 h _18906 P t).
Proof. exact (MK_COMB (@lem1143534 _26916 _26917 P h) (@lem1143531 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143536 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term374 _26916 _26917 h _18906 P t) = (term372 _26916 _26917 h _18906 P t).
Proof. exact (@lem17045 (term55 _26916 _26917 P h) (term110 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143537 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term374 _26916 _26917 h _18906 P t) = (term373 _26916 _26917 h _18906 P t).
Proof. exact (TRANS (@lem1143536 _26916 _26917 h _18906 P t) (@lem1143535 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143538 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1143539 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term60 _26916 _26917 P h) = (term60 _26916 _26917 P h).
Proof. exact (MK_COMB (@lem1143538) (@lem1143530 _26916 _26917 P h)). Qed.
Lemma lem1143540 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term111 _26916 _26917 h _18906 P t) = (term111 _26916 _26917 h _18906 P t).
Proof. exact (MK_COMB (@lem1143539 _26916 _26917 P h) (@lem1143532 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143541 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1143542 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term375 _26916 _26917 h P t) = (term376 _26916 _26917 h P t).
Proof. exact (MK_COMB (@lem1143541) (@lem1143512 _26916 _26917 h P t)). Qed.
Lemma lem1143543 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term377 _26916 _26917 h _18906 P t) = (term378 _26916 _26917 h _18906 P t).
Proof. exact (MK_COMB (@lem1143542 _26916 _26917 h P t) (@lem1143540 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143544 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1143545 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term379 _26916 _26917 h P t) = (term379 _26916 _26917 h P t).
Proof. exact (MK_COMB (@lem1143544) (@lem1143515 _26916 _26917 h P t)). Qed.
Lemma lem1143546 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term380 _26916 _26917 h _18906 P t) = (term381 _26916 _26917 h _18906 P t).
Proof. exact (MK_COMB (@lem1143545 _26916 _26917 h P t) (@lem1143537 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143547 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1143548 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term382 _26916 _26917 h _18906 P t) = (term383 _26916 _26917 h _18906 P t).
Proof. exact (MK_COMB (@lem1143547) (@lem1143546 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143549 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term384 _26916 _26917 h _18906 P t) = (term385 _26916 _26917 h _18906 P t).
Proof. exact (MK_COMB (@lem1143548 _26916 _26917 h _18906 P t) (@lem1143543 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143550 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term170 _26916 _26917 h _18906 P t) = (term384 _26916 _26917 h _18906 P t).
Proof. exact (@lem17646 (term90 _26916 _26917 h P t) (term111 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143551 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term170 _26916 _26917 h _18906 P t) = (term385 _26916 _26917 h _18906 P t).
Proof. exact (TRANS (@lem1143550 _26916 _26917 h _18906 P t) (@lem1143549 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143578 {A : Type'} (P : A -> Prop) (Q : Prop) : (term386 A P Q) = (term387 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem1143579 {_26917 : Type'} (P : _26917 -> Prop) (Q : Prop) : (term386 _26917 P Q) = (term387 _26917 P Q).
Proof. exact (@lem1143578 _26917 P Q). Qed.
Lemma lem1143580 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term388 _26916 _26917 h _18906 P t) = (term389 _26916 _26917 h _18906 P t).
Proof. exact (@lem1143579 _26917 (term178 _26916 _26917 P h) (term329 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143581 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (term241 _26916 _26917 P h x) = (term176 _26916 _26917 P x h).
Proof. exact (eq_refl (term241 _26916 _26917 P h x)). Qed.
Lemma lem1143582 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term242 _26916 _26917 P h) = (term178 _26916 _26917 P h).
Proof. exact (fun_ext (fun x : _26917 => @lem1143581 _26916 _26917 P x h)). Qed.
Lemma lem1143583 {_26917 : Type'} : (@ex _26917) = (@ex _26917).
Proof. exact (eq_refl (@ex _26917)). Qed.
Lemma lem1143584 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term243 _26916 _26917 P h) = (term179 _26916 _26917 P h).
Proof. exact (MK_COMB (@lem1143583 _26917) (@lem1143582 _26916 _26917 P h)). Qed.
Lemma lem1143585 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1143586 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term390 _26916 _26917 P h) = (term368 _26916 _26917 P h).
Proof. exact (MK_COMB (@lem1143585) (@lem1143584 _26916 _26917 P h)). Qed.
Lemma lem1143587 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term329 _26916 _26917 _18906 P t) = (term329 _26916 _26917 _18906 P t).
Proof. exact (eq_refl (term329 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143588 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term388 _26916 _26917 h _18906 P t) = (term373 _26916 _26917 h _18906 P t).
Proof. exact (MK_COMB (@lem1143586 _26916 _26917 P h) (@lem1143587 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143589 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1143590 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term391 _26916 _26917 h _18906 P t) = (term392 _26916 _26917 h _18906 P t).
Proof. exact (MK_COMB (@lem1143589) (@lem1143588 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143591 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (term241 _26916 _26917 P h x) = (term176 _26916 _26917 P x h).
Proof. exact (eq_refl (term241 _26916 _26917 P h x)). Qed.
Lemma lem1143592 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1143593 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (term393 _26916 _26917 P h x) = (term394 _26916 _26917 P x h).
Proof. exact (MK_COMB (@lem1143592) (@lem1143591 _26916 _26917 P x h)). Qed.
Lemma lem1143594 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term329 _26916 _26917 _18906 P t) = (term329 _26916 _26917 _18906 P t).
Proof. exact (eq_refl (term329 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143595 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term395 _26916 _26917 h x _18906 P t) = (term396 _26916 _26917 x h _18906 P t).
Proof. exact (MK_COMB (@lem1143593 _26916 _26917 P x h) (@lem1143594 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143596 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term397 _26916 _26917 h _18906 P t) = (term398 _26916 _26917 h _18906 P t).
Proof. exact (fun_ext (fun x : _26917 => @lem1143595 _26916 _26917 x h _18906 P t)). Qed.
Lemma lem1143597 {_26917 : Type'} : (@ex _26917) = (@ex _26917).
Proof. exact (eq_refl (@ex _26917)). Qed.
Lemma lem1143598 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term389 _26916 _26917 h _18906 P t) = (term399 _26916 _26917 h _18906 P t).
Proof. exact (MK_COMB (@lem1143597 _26917) (@lem1143596 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143599 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : ((term388 _26916 _26917 h _18906 P t) = (term389 _26916 _26917 h _18906 P t)) = ((term373 _26916 _26917 h _18906 P t) = (term399 _26916 _26917 h _18906 P t)).
Proof. exact (MK_COMB (@lem1143590 _26916 _26917 h _18906 P t) (@lem1143598 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143600 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term373 _26916 _26917 h _18906 P t) = (term399 _26916 _26917 h _18906 P t).
Proof. exact (EQ_MP (@lem1143599 _26916 _26917 h _18906 P t) (@lem1143580 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143601 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term379 _26916 _26917 h P t) = (term379 _26916 _26917 h P t).
Proof. exact (eq_refl (term379 _26916 _26917 h P t)). Qed.
Lemma lem1143602 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term381 _26916 _26917 h _18906 P t) = (term400 _26916 _26917 h _18906 P t).
Proof. exact (MK_COMB (@lem1143601 _26916 _26917 h P t) (@lem1143600 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143604 {A : Type'} (P : Prop) (Q : A -> Prop) : (term401 A P Q) = (term402 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1143605 {_26917 : Type'} (P : Prop) (Q : _26917 -> Prop) : (term401 _26917 P Q) = (term402 _26917 P Q).
Proof. exact (@lem1143604 _26917 P Q). Qed.
Lemma lem1143606 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term403 _26916 _26917 h _18906 P t) = (term404 _26916 _26917 h _18906 P t).
Proof. exact (@lem1143605 _26917 (term90 _26916 _26917 h P t) (term398 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143607 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term405 _26916 _26917 h _18906 P t x) = (term396 _26916 _26917 x h _18906 P t).
Proof. exact (eq_refl (term405 _26916 _26917 h _18906 P t x)). Qed.
Lemma lem1143608 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term406 _26916 _26917 h _18906 P t) = (term398 _26916 _26917 h _18906 P t).
Proof. exact (fun_ext (fun x : _26917 => @lem1143607 _26916 _26917 x h _18906 P t)). Qed.
Lemma lem1143609 {_26917 : Type'} : (@ex _26917) = (@ex _26917).
Proof. exact (eq_refl (@ex _26917)). Qed.
Lemma lem1143610 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term407 _26916 _26917 h _18906 P t) = (term399 _26916 _26917 h _18906 P t).
Proof. exact (MK_COMB (@lem1143609 _26917) (@lem1143608 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143611 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term379 _26916 _26917 h P t) = (term379 _26916 _26917 h P t).
Proof. exact (eq_refl (term379 _26916 _26917 h P t)). Qed.
Lemma lem1143612 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term403 _26916 _26917 h _18906 P t) = (term400 _26916 _26917 h _18906 P t).
Proof. exact (MK_COMB (@lem1143611 _26916 _26917 h P t) (@lem1143610 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143613 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1143614 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term408 _26916 _26917 h _18906 P t) = (term409 _26916 _26917 h _18906 P t).
Proof. exact (MK_COMB (@lem1143613) (@lem1143612 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143615 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term405 _26916 _26917 h _18906 P t x) = (term396 _26916 _26917 x h _18906 P t).
Proof. exact (eq_refl (term405 _26916 _26917 h _18906 P t x)). Qed.
Lemma lem1143616 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term379 _26916 _26917 h P t) = (term379 _26916 _26917 h P t).
Proof. exact (eq_refl (term379 _26916 _26917 h P t)). Qed.
Lemma lem1143617 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term410 _26916 _26917 h _18906 P t x) = (term411 _26916 _26917 x h _18906 P t).
Proof. exact (MK_COMB (@lem1143616 _26916 _26917 h P t) (@lem1143615 _26916 _26917 x h _18906 P t)). Qed.
Lemma lem1143618 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term412 _26916 _26917 h _18906 P t) = (term413 _26916 _26917 h _18906 P t).
Proof. exact (fun_ext (fun x : _26917 => @lem1143617 _26916 _26917 x h _18906 P t)). Qed.
Lemma lem1143619 {_26917 : Type'} : (@ex _26917) = (@ex _26917).
Proof. exact (eq_refl (@ex _26917)). Qed.
Lemma lem1143620 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term404 _26916 _26917 h _18906 P t) = (term414 _26916 _26917 h _18906 P t).
Proof. exact (MK_COMB (@lem1143619 _26917) (@lem1143618 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143621 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : ((term403 _26916 _26917 h _18906 P t) = (term404 _26916 _26917 h _18906 P t)) = ((term400 _26916 _26917 h _18906 P t) = (term414 _26916 _26917 h _18906 P t)).
Proof. exact (MK_COMB (@lem1143614 _26916 _26917 h _18906 P t) (@lem1143620 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143622 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term400 _26916 _26917 h _18906 P t) = (term414 _26916 _26917 h _18906 P t).
Proof. exact (EQ_MP (@lem1143621 _26916 _26917 h _18906 P t) (@lem1143606 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143623 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term381 _26916 _26917 h _18906 P t) = (term414 _26916 _26917 h _18906 P t).
Proof. exact (TRANS (@lem1143602 _26916 _26917 h _18906 P t) (@lem1143622 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143624 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1143625 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term383 _26916 _26917 h _18906 P t) = (term415 _26916 _26917 h _18906 P t).
Proof. exact (MK_COMB (@lem1143624) (@lem1143623 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143627 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term416 A P Q) = (term417 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1143628 {_26917 : Type'} (P : _26917 -> Prop) (Q : _26917 -> Prop) : (term416 _26917 P Q) = (term417 _26917 P Q).
Proof. exact (@lem1143627 _26917 P Q). Qed.
Lemma lem1143629 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term418 _26916 _26917 h P t) = (term419 _26916 _26917 h P t).
Proof. exact (@lem1143628 _26917 (term178 _26916 _26917 P h) (term327 _26916 _26917 P t)). Qed.
Lemma lem1143630 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (term241 _26916 _26917 P h x) = (term176 _26916 _26917 P x h).
Proof. exact (eq_refl (term241 _26916 _26917 P h x)). Qed.
Lemma lem1143631 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term242 _26916 _26917 P h) = (term178 _26916 _26917 P h).
Proof. exact (fun_ext (fun x : _26917 => @lem1143630 _26916 _26917 P x h)). Qed.
Lemma lem1143632 {_26917 : Type'} : (@ex _26917) = (@ex _26917).
Proof. exact (eq_refl (@ex _26917)). Qed.
Lemma lem1143633 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term243 _26916 _26917 P h) = (term179 _26916 _26917 P h).
Proof. exact (MK_COMB (@lem1143632 _26917) (@lem1143631 _26916 _26917 P h)). Qed.
Lemma lem1143634 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1143635 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term390 _26916 _26917 P h) = (term368 _26916 _26917 P h).
Proof. exact (MK_COMB (@lem1143634) (@lem1143633 _26916 _26917 P h)). Qed.
Lemma lem1143636 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term341 _26916 _26917 P t x) = (term325 _26916 _26917 P x t).
Proof. exact (eq_refl (term341 _26916 _26917 P t x)). Qed.
Lemma lem1143637 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term342 _26916 _26917 P t) = (term327 _26916 _26917 P t).
Proof. exact (fun_ext (fun x : _26917 => @lem1143636 _26916 _26917 P x t)). Qed.
Lemma lem1143638 {_26917 : Type'} : (@ex _26917) = (@ex _26917).
Proof. exact (eq_refl (@ex _26917)). Qed.
Lemma lem1143639 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term343 _26916 _26917 P t) = (term328 _26916 _26917 P t).
Proof. exact (MK_COMB (@lem1143638 _26917) (@lem1143637 _26916 _26917 P t)). Qed.
Lemma lem1143640 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term418 _26916 _26917 h P t) = (term370 _26916 _26917 h P t).
Proof. exact (MK_COMB (@lem1143635 _26916 _26917 P h) (@lem1143639 _26916 _26917 P t)). Qed.
Lemma lem1143641 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1143642 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term420 _26916 _26917 h P t) = (term421 _26916 _26917 h P t).
Proof. exact (MK_COMB (@lem1143641) (@lem1143640 _26916 _26917 h P t)). Qed.
Lemma lem1143643 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (term241 _26916 _26917 P h x) = (term176 _26916 _26917 P x h).
Proof. exact (eq_refl (term241 _26916 _26917 P h x)). Qed.
Lemma lem1143644 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1143645 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (term393 _26916 _26917 P h x) = (term394 _26916 _26917 P x h).
Proof. exact (MK_COMB (@lem1143644) (@lem1143643 _26916 _26917 P x h)). Qed.
Lemma lem1143646 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term341 _26916 _26917 P t x) = (term325 _26916 _26917 P x t).
Proof. exact (eq_refl (term341 _26916 _26917 P t x)). Qed.
Lemma lem1143647 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term422 _26916 _26917 h P t x) = (term423 _26916 _26917 h P x t).
Proof. exact (MK_COMB (@lem1143645 _26916 _26917 P x h) (@lem1143646 _26916 _26917 P x t)). Qed.
Lemma lem1143648 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term424 _26916 _26917 h P t) = (term425 _26916 _26917 h P t).
Proof. exact (fun_ext (fun x : _26917 => @lem1143647 _26916 _26917 h P x t)). Qed.
Lemma lem1143649 {_26917 : Type'} : (@ex _26917) = (@ex _26917).
Proof. exact (eq_refl (@ex _26917)). Qed.
Lemma lem1143650 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term419 _26916 _26917 h P t) = (term426 _26916 _26917 h P t).
Proof. exact (MK_COMB (@lem1143649 _26917) (@lem1143648 _26916 _26917 h P t)). Qed.
Lemma lem1143651 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : ((term418 _26916 _26917 h P t) = (term419 _26916 _26917 h P t)) = ((term370 _26916 _26917 h P t) = (term426 _26916 _26917 h P t)).
Proof. exact (MK_COMB (@lem1143642 _26916 _26917 h P t) (@lem1143650 _26916 _26917 h P t)). Qed.
Lemma lem1143652 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term370 _26916 _26917 h P t) = (term426 _26916 _26917 h P t).
Proof. exact (EQ_MP (@lem1143651 _26916 _26917 h P t) (@lem1143629 _26916 _26917 h P t)). Qed.
Lemma lem1143653 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1143654 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term376 _26916 _26917 h P t) = (term427 _26916 _26917 h P t).
Proof. exact (MK_COMB (@lem1143653) (@lem1143652 _26916 _26917 h P t)). Qed.
Lemma lem1143655 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term111 _26916 _26917 h _18906 P t) = (term111 _26916 _26917 h _18906 P t).
Proof. exact (eq_refl (term111 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143656 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term378 _26916 _26917 h _18906 P t) = (term428 _26916 _26917 h _18906 P t).
Proof. exact (MK_COMB (@lem1143654 _26916 _26917 h P t) (@lem1143655 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143658 {A : Type'} (P : A -> Prop) (Q : Prop) : (term303 A P Q) = (term304 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1143659 {_26917 : Type'} (P : _26917 -> Prop) (Q : Prop) : (term303 _26917 P Q) = (term304 _26917 P Q).
Proof. exact (@lem1143658 _26917 P Q). Qed.
Lemma lem1143660 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term429 _26916 _26917 h _18906 P t) = (term430 _26916 _26917 h _18906 P t).
Proof. exact (@lem1143659 _26917 (term425 _26916 _26917 h P t) (term111 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143661 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term431 _26916 _26917 h P t x) = (term423 _26916 _26917 h P x t).
Proof. exact (eq_refl (term431 _26916 _26917 h P t x)). Qed.
Lemma lem1143662 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term432 _26916 _26917 h P t) = (term425 _26916 _26917 h P t).
Proof. exact (fun_ext (fun x : _26917 => @lem1143661 _26916 _26917 h P x t)). Qed.
Lemma lem1143663 {_26917 : Type'} : (@ex _26917) = (@ex _26917).
Proof. exact (eq_refl (@ex _26917)). Qed.
Lemma lem1143664 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term433 _26916 _26917 h P t) = (term426 _26916 _26917 h P t).
Proof. exact (MK_COMB (@lem1143663 _26917) (@lem1143662 _26916 _26917 h P t)). Qed.
Lemma lem1143665 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1143666 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term434 _26916 _26917 h P t) = (term427 _26916 _26917 h P t).
Proof. exact (MK_COMB (@lem1143665) (@lem1143664 _26916 _26917 h P t)). Qed.
Lemma lem1143667 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term111 _26916 _26917 h _18906 P t) = (term111 _26916 _26917 h _18906 P t).
Proof. exact (eq_refl (term111 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143668 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term429 _26916 _26917 h _18906 P t) = (term428 _26916 _26917 h _18906 P t).
Proof. exact (MK_COMB (@lem1143666 _26916 _26917 h P t) (@lem1143667 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143669 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1143670 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term435 _26916 _26917 h _18906 P t) = (term436 _26916 _26917 h _18906 P t).
Proof. exact (MK_COMB (@lem1143669) (@lem1143668 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143671 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term431 _26916 _26917 h P t x) = (term423 _26916 _26917 h P x t).
Proof. exact (eq_refl (term431 _26916 _26917 h P t x)). Qed.
Lemma lem1143672 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1143673 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term437 _26916 _26917 h P t x) = (term438 _26916 _26917 h P x t).
Proof. exact (MK_COMB (@lem1143672) (@lem1143671 _26916 _26917 h P x t)). Qed.
Lemma lem1143674 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term111 _26916 _26917 h _18906 P t) = (term111 _26916 _26917 h _18906 P t).
Proof. exact (eq_refl (term111 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143675 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term439 _26916 _26917 x h _18906 P t) = (term440 _26916 _26917 x h _18906 P t).
Proof. exact (MK_COMB (@lem1143673 _26916 _26917 h P x t) (@lem1143674 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143676 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term441 _26916 _26917 h _18906 P t) = (term442 _26916 _26917 h _18906 P t).
Proof. exact (fun_ext (fun x : _26917 => @lem1143675 _26916 _26917 x h _18906 P t)). Qed.
Lemma lem1143677 {_26917 : Type'} : (@ex _26917) = (@ex _26917).
Proof. exact (eq_refl (@ex _26917)). Qed.
Lemma lem1143678 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term430 _26916 _26917 h _18906 P t) = (term443 _26916 _26917 h _18906 P t).
Proof. exact (MK_COMB (@lem1143677 _26917) (@lem1143676 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143679 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : ((term429 _26916 _26917 h _18906 P t) = (term430 _26916 _26917 h _18906 P t)) = ((term428 _26916 _26917 h _18906 P t) = (term443 _26916 _26917 h _18906 P t)).
Proof. exact (MK_COMB (@lem1143670 _26916 _26917 h _18906 P t) (@lem1143678 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143680 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term428 _26916 _26917 h _18906 P t) = (term443 _26916 _26917 h _18906 P t).
Proof. exact (EQ_MP (@lem1143679 _26916 _26917 h _18906 P t) (@lem1143660 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143681 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term378 _26916 _26917 h _18906 P t) = (term443 _26916 _26917 h _18906 P t).
Proof. exact (TRANS (@lem1143656 _26916 _26917 h _18906 P t) (@lem1143680 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143682 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term385 _26916 _26917 h _18906 P t) = (term444 _26916 _26917 h _18906 P t).
Proof. exact (MK_COMB (@lem1143625 _26916 _26917 h _18906 P t) (@lem1143681 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143684 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term416 A P Q) = (term417 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1143685 {_26917 : Type'} (P : _26917 -> Prop) (Q : _26917 -> Prop) : (term416 _26917 P Q) = (term417 _26917 P Q).
Proof. exact (@lem1143684 _26917 P Q). Qed.
Lemma lem1143686 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term445 _26916 _26917 h _18906 P t) = (term446 _26916 _26917 h _18906 P t).
Proof. exact (@lem1143685 _26917 (term413 _26916 _26917 h _18906 P t) (term442 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143687 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term447 _26916 _26917 h _18906 P t x) = (term411 _26916 _26917 x h _18906 P t).
Proof. exact (eq_refl (term447 _26916 _26917 h _18906 P t x)). Qed.
Lemma lem1143688 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term448 _26916 _26917 h _18906 P t) = (term413 _26916 _26917 h _18906 P t).
Proof. exact (fun_ext (fun x : _26917 => @lem1143687 _26916 _26917 x h _18906 P t)). Qed.
Lemma lem1143689 {_26917 : Type'} : (@ex _26917) = (@ex _26917).
Proof. exact (eq_refl (@ex _26917)). Qed.
Lemma lem1143690 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term449 _26916 _26917 h _18906 P t) = (term414 _26916 _26917 h _18906 P t).
Proof. exact (MK_COMB (@lem1143689 _26917) (@lem1143688 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143691 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1143692 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term450 _26916 _26917 h _18906 P t) = (term415 _26916 _26917 h _18906 P t).
Proof. exact (MK_COMB (@lem1143691) (@lem1143690 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143693 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term451 _26916 _26917 h _18906 P t x) = (term440 _26916 _26917 x h _18906 P t).
Proof. exact (eq_refl (term451 _26916 _26917 h _18906 P t x)). Qed.
Lemma lem1143694 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term452 _26916 _26917 h _18906 P t) = (term442 _26916 _26917 h _18906 P t).
Proof. exact (fun_ext (fun x : _26917 => @lem1143693 _26916 _26917 x h _18906 P t)). Qed.
Lemma lem1143695 {_26917 : Type'} : (@ex _26917) = (@ex _26917).
Proof. exact (eq_refl (@ex _26917)). Qed.
Lemma lem1143696 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term453 _26916 _26917 h _18906 P t) = (term443 _26916 _26917 h _18906 P t).
Proof. exact (MK_COMB (@lem1143695 _26917) (@lem1143694 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143697 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term445 _26916 _26917 h _18906 P t) = (term444 _26916 _26917 h _18906 P t).
Proof. exact (MK_COMB (@lem1143692 _26916 _26917 h _18906 P t) (@lem1143696 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143698 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1143699 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term454 _26916 _26917 h _18906 P t) = (term455 _26916 _26917 h _18906 P t).
Proof. exact (MK_COMB (@lem1143698) (@lem1143697 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143700 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term447 _26916 _26917 h _18906 P t x) = (term411 _26916 _26917 x h _18906 P t).
Proof. exact (eq_refl (term447 _26916 _26917 h _18906 P t x)). Qed.
Lemma lem1143701 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1143702 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term456 _26916 _26917 h _18906 P t x) = (term457 _26916 _26917 x h _18906 P t).
Proof. exact (MK_COMB (@lem1143701) (@lem1143700 _26916 _26917 x h _18906 P t)). Qed.
Lemma lem1143703 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term451 _26916 _26917 h _18906 P t x) = (term440 _26916 _26917 x h _18906 P t).
Proof. exact (eq_refl (term451 _26916 _26917 h _18906 P t x)). Qed.
Lemma lem1143704 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term458 _26916 _26917 h _18906 P t x) = (term459 _26916 _26917 x h _18906 P t).
Proof. exact (MK_COMB (@lem1143702 _26916 _26917 x h _18906 P t) (@lem1143703 _26916 _26917 x h _18906 P t)). Qed.
Lemma lem1143705 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term460 _26916 _26917 h _18906 P t) = (term461 _26916 _26917 h _18906 P t).
Proof. exact (fun_ext (fun x : _26917 => @lem1143704 _26916 _26917 x h _18906 P t)). Qed.
Lemma lem1143706 {_26917 : Type'} : (@ex _26917) = (@ex _26917).
Proof. exact (eq_refl (@ex _26917)). Qed.
Lemma lem1143707 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term446 _26916 _26917 h _18906 P t) = (term462 _26916 _26917 h _18906 P t).
Proof. exact (MK_COMB (@lem1143706 _26917) (@lem1143705 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143708 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : ((term445 _26916 _26917 h _18906 P t) = (term446 _26916 _26917 h _18906 P t)) = ((term444 _26916 _26917 h _18906 P t) = (term462 _26916 _26917 h _18906 P t)).
Proof. exact (MK_COMB (@lem1143699 _26916 _26917 h _18906 P t) (@lem1143707 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143709 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term444 _26916 _26917 h _18906 P t) = (term462 _26916 _26917 h _18906 P t).
Proof. exact (EQ_MP (@lem1143708 _26916 _26917 h _18906 P t) (@lem1143686 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143711 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term385 _26916 _26917 h _18906 P t) = (term462 _26916 _26917 h _18906 P t).
Proof. exact (TRANS (@lem1143682 _26916 _26917 h _18906 P t) (@lem1143709 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143712 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term170 _26916 _26917 h _18906 P t) = (term462 _26916 _26917 h _18906 P t).
Proof. exact (TRANS (@lem1143551 _26916 _26917 h _18906 P t) (@lem1143711 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143713 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term170 _26916 _26917 h _18906 P t) : term462 _26916 _26917 h _18906 P t.
Proof. exact (EQ_MP (@lem1143712 _26916 _26917 h _18906 P t) (@lem1142958 _26916 _26917 h _18906 P t h1)). Qed.
Lemma lem1143714 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term459 _26916 _26917 x h _18906 P t) : term459 _26916 _26917 x h _18906 P t.
Proof. exact (h1). Qed.
Lemma lem1143715 {_26916 _26917 : Type'} (x' : _26917) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term363 _26916 _26917 x' _18906 P t) : term363 _26916 _26917 x' _18906 P t.
Proof. exact (h1). Qed.
Lemma lem1143717 {_26916 : Type'} : (@List.Forall _26916) = (@List.Forall _26916).
Proof. exact (eq_refl (@List.Forall _26916)). Qed.
Lemma lem1143722 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1143723 {_26916 _26917 : Type'} (f : type740 _26916 _26917) (x : type1470 _26916 _26917) : (f x) = (@I ((_26917 -> _26916 -> Prop) -> _26916 -> Prop) f x).
Proof. exact (@lem1143722 (type1470 _26916 _26917) (_26916 -> Prop) f x). Qed.
Lemma lem1143725 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (_18906 P) = (@I ((_26917 -> _26916 -> Prop) -> _26916 -> Prop) _18906 P).
Proof. exact (@lem1143723 _26916 _26917 _18906 P). Qed.
Lemma lem1143726 {_26916 : Type'} (t : list _26916) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1143727 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term109 _26916 _26917 _18906 P) = (term463 _26916 _26917 _18906 P).
Proof. exact (MK_COMB (@lem1143717 _26916) (@lem1143725 _26916 _26917 _18906 P)). Qed.
Lemma lem1143728 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term110 _26916 _26917 _18906 P t) = (term464 _26916 _26917 _18906 P t).
Proof. exact (MK_COMB (@lem1143727 _26916 _26917 _18906 P) (@lem1143726 _26916 t)). Qed.
Lemma lem1143730 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1143731 {_26916 : Type'} (f : type663 _26916) (x : _26916 -> Prop) : (f x) = (@I ((_26916 -> Prop) -> (list _26916) -> Prop) f x).
Proof. exact (@lem1143730 (_26916 -> Prop) (type1143 _26916) f x). Qed.
Lemma lem1143732 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term463 _26916 _26917 _18906 P) = (term465 _26916 _26917 _18906 P).
Proof. exact (@lem1143731 _26916 (@List.Forall _26916) (@I ((_26917 -> _26916 -> Prop) -> _26916 -> Prop) _18906 P)). Qed.
Lemma lem1143733 {_26916 : Type'} (t : list _26916) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1143734 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term464 _26916 _26917 _18906 P t) = (term466 _26916 _26917 _18906 P t).
Proof. exact (MK_COMB (@lem1143732 _26916 _26917 _18906 P) (@lem1143733 _26916 t)). Qed.
Lemma lem1143736 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1143737 {_26916 : Type'} (f : type1143 _26916) (x : list _26916) : (f x) = (@I ((list _26916) -> Prop) f x).
Proof. exact (@lem1143736 (list _26916) Prop f x). Qed.
Lemma lem1143738 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term466 _26916 _26917 _18906 P t) = (term467 _26916 _26917 _18906 P t).
Proof. exact (@lem1143737 _26916 (term465 _26916 _26917 _18906 P) t). Qed.
Lemma lem1143739 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term464 _26916 _26917 _18906 P t) = (term467 _26916 _26917 _18906 P t).
Proof. exact (TRANS (@lem1143734 _26916 _26917 _18906 P t) (@lem1143738 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143740 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term110 _26916 _26917 _18906 P t) = (term467 _26916 _26917 _18906 P t).
Proof. exact (TRANS (@lem1143728 _26916 _26917 _18906 P t) (@lem1143739 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143747 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1143748 {_26916 _26917 : Type'} (f : type1470 _26916 _26917) (x : _26917) : (f x) = (@I (_26917 -> _26916 -> Prop) f x).
Proof. exact (@lem1143747 _26917 (_26916 -> Prop) f x). Qed.
Lemma lem1143749 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) : (P x) = (@I (_26917 -> _26916 -> Prop) P x).
Proof. exact (@lem1143748 _26916 _26917 P x). Qed.
Lemma lem1143750 {_26916 : Type'} (h : _26916) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1143751 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (P x h) = (@I (_26917 -> _26916 -> Prop) P x h).
Proof. exact (MK_COMB (@lem1143749 _26916 _26917 P x) (@lem1143750 _26916 h)). Qed.
Lemma lem1143753 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1143754 {_26916 : Type'} (f : _26916 -> Prop) (x : _26916) : (f x) = (@I (_26916 -> Prop) f x).
Proof. exact (@lem1143753 _26916 Prop f x). Qed.
Lemma lem1143755 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (@I (_26917 -> _26916 -> Prop) P x h) = (term468 _26916 _26917 P x h).
Proof. exact (@lem1143754 _26916 (@I (_26917 -> _26916 -> Prop) P x) h). Qed.
Lemma lem1143757 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (P x h) = (term468 _26916 _26917 P x h).
Proof. exact (TRANS (@lem1143751 _26916 _26917 P x h) (@lem1143755 _26916 _26917 P x h)). Qed.
Lemma lem1143758 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term75 _26916 _26917 P h) = (term469 _26916 _26917 P h).
Proof. exact (fun_ext (fun x : _26917 => @lem1143757 _26916 _26917 P x h)). Qed.
Lemma lem1143759 {_26917 : Type'} : (@all _26917) = (@all _26917).
Proof. exact (eq_refl (@all _26917)). Qed.
Lemma lem1143760 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term55 _26916 _26917 P h) = (term470 _26916 _26917 P h).
Proof. exact (MK_COMB (@lem1143759 _26917) (@lem1143758 _26916 _26917 P h)). Qed.
Lemma lem1143761 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1143762 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term60 _26916 _26917 P h) = (term471 _26916 _26917 P h).
Proof. exact (MK_COMB (@lem1143761) (@lem1143760 _26916 _26917 P h)). Qed.
Lemma lem1143763 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term111 _26916 _26917 h _18906 P t) = (term472 _26916 _26917 h _18906 P t).
Proof. exact (MK_COMB (@lem1143762 _26916 _26917 P h) (@lem1143740 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143764 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1143765 {_26916 : Type'} : (@List.Forall _26916) = (@List.Forall _26916).
Proof. exact (eq_refl (@List.Forall _26916)). Qed.
Lemma lem1143770 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1143771 {_26916 _26917 : Type'} (f : type1470 _26916 _26917) (x : _26917) : (f x) = (@I (_26917 -> _26916 -> Prop) f x).
Proof. exact (@lem1143770 _26917 (_26916 -> Prop) f x). Qed.
Lemma lem1143773 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) : (P x) = (@I (_26917 -> _26916 -> Prop) P x).
Proof. exact (@lem1143771 _26916 _26917 P x). Qed.
Lemma lem1143774 {_26916 : Type'} (t : list _26916) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1143775 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) : (term473 _26916 _26917 P x) = (term474 _26916 _26917 P x).
Proof. exact (MK_COMB (@lem1143765 _26916) (@lem1143773 _26916 _26917 P x)). Qed.
Lemma lem1143776 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term81 _26916 _26917 P x t) = (term475 _26916 _26917 P x t).
Proof. exact (MK_COMB (@lem1143775 _26916 _26917 P x) (@lem1143774 _26916 t)). Qed.
Lemma lem1143778 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1143779 {_26916 : Type'} (f : type663 _26916) (x : _26916 -> Prop) : (f x) = (@I ((_26916 -> Prop) -> (list _26916) -> Prop) f x).
Proof. exact (@lem1143778 (_26916 -> Prop) (type1143 _26916) f x). Qed.
Lemma lem1143780 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) : (term474 _26916 _26917 P x) = (term476 _26916 _26917 P x).
Proof. exact (@lem1143779 _26916 (@List.Forall _26916) (@I (_26917 -> _26916 -> Prop) P x)). Qed.
Lemma lem1143781 {_26916 : Type'} (t : list _26916) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1143782 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term475 _26916 _26917 P x t) = (term477 _26916 _26917 P x t).
Proof. exact (MK_COMB (@lem1143780 _26916 _26917 P x) (@lem1143781 _26916 t)). Qed.
Lemma lem1143784 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1143785 {_26916 : Type'} (f : type1143 _26916) (x : list _26916) : (f x) = (@I ((list _26916) -> Prop) f x).
Proof. exact (@lem1143784 (list _26916) Prop f x). Qed.
Lemma lem1143786 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term477 _26916 _26917 P x t) = (term478 _26916 _26917 P x t).
Proof. exact (@lem1143785 _26916 (term476 _26916 _26917 P x) t). Qed.
Lemma lem1143787 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term475 _26916 _26917 P x t) = (term478 _26916 _26917 P x t).
Proof. exact (TRANS (@lem1143782 _26916 _26917 P x t) (@lem1143786 _26916 _26917 P x t)). Qed.
Lemma lem1143788 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term81 _26916 _26917 P x t) = (term478 _26916 _26917 P x t).
Proof. exact (TRANS (@lem1143776 _26916 _26917 P x t) (@lem1143787 _26916 _26917 P x t)). Qed.
Lemma lem1143789 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term325 _26916 _26917 P x t) = (term479 _26916 _26917 P x t).
Proof. exact (MK_COMB (@lem1143764) (@lem1143788 _26916 _26917 P x t)). Qed.
Lemma lem1143790 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1143797 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1143798 {_26916 _26917 : Type'} (f : type1470 _26916 _26917) (x : _26917) : (f x) = (@I (_26917 -> _26916 -> Prop) f x).
Proof. exact (@lem1143797 _26917 (_26916 -> Prop) f x). Qed.
Lemma lem1143799 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) : (P x) = (@I (_26917 -> _26916 -> Prop) P x).
Proof. exact (@lem1143798 _26916 _26917 P x). Qed.
Lemma lem1143800 {_26916 : Type'} (h : _26916) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1143801 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (P x h) = (@I (_26917 -> _26916 -> Prop) P x h).
Proof. exact (MK_COMB (@lem1143799 _26916 _26917 P x) (@lem1143800 _26916 h)). Qed.
Lemma lem1143803 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1143804 {_26916 : Type'} (f : _26916 -> Prop) (x : _26916) : (f x) = (@I (_26916 -> Prop) f x).
Proof. exact (@lem1143803 _26916 Prop f x). Qed.
Lemma lem1143805 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (@I (_26917 -> _26916 -> Prop) P x h) = (term468 _26916 _26917 P x h).
Proof. exact (@lem1143804 _26916 (@I (_26917 -> _26916 -> Prop) P x) h). Qed.
Lemma lem1143807 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (P x h) = (term468 _26916 _26917 P x h).
Proof. exact (TRANS (@lem1143801 _26916 _26917 P x h) (@lem1143805 _26916 _26917 P x h)). Qed.
Lemma lem1143808 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (term176 _26916 _26917 P x h) = (term480 _26916 _26917 P x h).
Proof. exact (MK_COMB (@lem1143790) (@lem1143807 _26916 _26917 P x h)). Qed.
Lemma lem1143809 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1143810 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (term394 _26916 _26917 P x h) = (term481 _26916 _26917 P x h).
Proof. exact (MK_COMB (@lem1143809) (@lem1143808 _26916 _26917 P x h)). Qed.
Lemma lem1143811 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term423 _26916 _26917 h P x t) = (term482 _26916 _26917 h P x t).
Proof. exact (MK_COMB (@lem1143810 _26916 _26917 P x h) (@lem1143789 _26916 _26917 P x t)). Qed.
Lemma lem1143812 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1143813 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term438 _26916 _26917 h P x t) = (term483 _26916 _26917 h P x t).
Proof. exact (MK_COMB (@lem1143812) (@lem1143811 _26916 _26917 h P x t)). Qed.
Lemma lem1143814 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term440 _26916 _26917 x h _18906 P t) = (term484 _26916 _26917 x h _18906 P t).
Proof. exact (MK_COMB (@lem1143813 _26916 _26917 h P x t) (@lem1143763 _26916 _26917 h _18906 P t)). Qed.
Lemma lem1143815 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1143816 {_26916 : Type'} : (@List.Forall _26916) = (@List.Forall _26916).
Proof. exact (eq_refl (@List.Forall _26916)). Qed.
Lemma lem1143821 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1143822 {_26916 _26917 : Type'} (f : type740 _26916 _26917) (x : type1470 _26916 _26917) : (f x) = (@I ((_26917 -> _26916 -> Prop) -> _26916 -> Prop) f x).
Proof. exact (@lem1143821 (type1470 _26916 _26917) (_26916 -> Prop) f x). Qed.
Lemma lem1143824 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (_18906 P) = (@I ((_26917 -> _26916 -> Prop) -> _26916 -> Prop) _18906 P).
Proof. exact (@lem1143822 _26916 _26917 _18906 P). Qed.
Lemma lem1143825 {_26916 : Type'} (t : list _26916) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1143826 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term109 _26916 _26917 _18906 P) = (term463 _26916 _26917 _18906 P).
Proof. exact (MK_COMB (@lem1143816 _26916) (@lem1143824 _26916 _26917 _18906 P)). Qed.
Lemma lem1143827 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term110 _26916 _26917 _18906 P t) = (term464 _26916 _26917 _18906 P t).
Proof. exact (MK_COMB (@lem1143826 _26916 _26917 _18906 P) (@lem1143825 _26916 t)). Qed.
Lemma lem1143829 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1143830 {_26916 : Type'} (f : type663 _26916) (x : _26916 -> Prop) : (f x) = (@I ((_26916 -> Prop) -> (list _26916) -> Prop) f x).
Proof. exact (@lem1143829 (_26916 -> Prop) (type1143 _26916) f x). Qed.
Lemma lem1143831 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term463 _26916 _26917 _18906 P) = (term465 _26916 _26917 _18906 P).
Proof. exact (@lem1143830 _26916 (@List.Forall _26916) (@I ((_26917 -> _26916 -> Prop) -> _26916 -> Prop) _18906 P)). Qed.
Lemma lem1143832 {_26916 : Type'} (t : list _26916) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1143833 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term464 _26916 _26917 _18906 P t) = (term466 _26916 _26917 _18906 P t).
Proof. exact (MK_COMB (@lem1143831 _26916 _26917 _18906 P) (@lem1143832 _26916 t)). Qed.
Lemma lem1143835 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1143836 {_26916 : Type'} (f : type1143 _26916) (x : list _26916) : (f x) = (@I ((list _26916) -> Prop) f x).
Proof. exact (@lem1143835 (list _26916) Prop f x). Qed.
Lemma lem1143837 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term466 _26916 _26917 _18906 P t) = (term467 _26916 _26917 _18906 P t).
Proof. exact (@lem1143836 _26916 (term465 _26916 _26917 _18906 P) t). Qed.
Lemma lem1143838 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term464 _26916 _26917 _18906 P t) = (term467 _26916 _26917 _18906 P t).
Proof. exact (TRANS (@lem1143833 _26916 _26917 _18906 P t) (@lem1143837 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143839 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term110 _26916 _26917 _18906 P t) = (term467 _26916 _26917 _18906 P t).
Proof. exact (TRANS (@lem1143827 _26916 _26917 _18906 P t) (@lem1143838 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143840 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term329 _26916 _26917 _18906 P t) = (term485 _26916 _26917 _18906 P t).
Proof. exact (MK_COMB (@lem1143815) (@lem1143839 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143841 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1143848 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1143849 {_26916 _26917 : Type'} (f : type1470 _26916 _26917) (x : _26917) : (f x) = (@I (_26917 -> _26916 -> Prop) f x).
Proof. exact (@lem1143848 _26917 (_26916 -> Prop) f x). Qed.
Lemma lem1143850 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) : (P x) = (@I (_26917 -> _26916 -> Prop) P x).
Proof. exact (@lem1143849 _26916 _26917 P x). Qed.
Lemma lem1143851 {_26916 : Type'} (h : _26916) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1143852 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (P x h) = (@I (_26917 -> _26916 -> Prop) P x h).
Proof. exact (MK_COMB (@lem1143850 _26916 _26917 P x) (@lem1143851 _26916 h)). Qed.
Lemma lem1143854 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1143855 {_26916 : Type'} (f : _26916 -> Prop) (x : _26916) : (f x) = (@I (_26916 -> Prop) f x).
Proof. exact (@lem1143854 _26916 Prop f x). Qed.
Lemma lem1143856 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (@I (_26917 -> _26916 -> Prop) P x h) = (term468 _26916 _26917 P x h).
Proof. exact (@lem1143855 _26916 (@I (_26917 -> _26916 -> Prop) P x) h). Qed.
Lemma lem1143858 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (P x h) = (term468 _26916 _26917 P x h).
Proof. exact (TRANS (@lem1143852 _26916 _26917 P x h) (@lem1143856 _26916 _26917 P x h)). Qed.
Lemma lem1143859 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (term176 _26916 _26917 P x h) = (term480 _26916 _26917 P x h).
Proof. exact (MK_COMB (@lem1143841) (@lem1143858 _26916 _26917 P x h)). Qed.
Lemma lem1143860 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1143861 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (term394 _26916 _26917 P x h) = (term481 _26916 _26917 P x h).
Proof. exact (MK_COMB (@lem1143860) (@lem1143859 _26916 _26917 P x h)). Qed.
Lemma lem1143862 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term396 _26916 _26917 x h _18906 P t) = (term486 _26916 _26917 x h _18906 P t).
Proof. exact (MK_COMB (@lem1143861 _26916 _26917 P x h) (@lem1143840 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143863 {_26916 : Type'} : (@List.Forall _26916) = (@List.Forall _26916).
Proof. exact (eq_refl (@List.Forall _26916)). Qed.
Lemma lem1143868 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1143869 {_26916 _26917 : Type'} (f : type1470 _26916 _26917) (x : _26917) : (f x) = (@I (_26917 -> _26916 -> Prop) f x).
Proof. exact (@lem1143868 _26917 (_26916 -> Prop) f x). Qed.
Lemma lem1143871 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) : (P x) = (@I (_26917 -> _26916 -> Prop) P x).
Proof. exact (@lem1143869 _26916 _26917 P x). Qed.
Lemma lem1143872 {_26916 : Type'} (t : list _26916) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1143873 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) : (term473 _26916 _26917 P x) = (term474 _26916 _26917 P x).
Proof. exact (MK_COMB (@lem1143863 _26916) (@lem1143871 _26916 _26917 P x)). Qed.
Lemma lem1143874 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term81 _26916 _26917 P x t) = (term475 _26916 _26917 P x t).
Proof. exact (MK_COMB (@lem1143873 _26916 _26917 P x) (@lem1143872 _26916 t)). Qed.
Lemma lem1143876 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1143877 {_26916 : Type'} (f : type663 _26916) (x : _26916 -> Prop) : (f x) = (@I ((_26916 -> Prop) -> (list _26916) -> Prop) f x).
Proof. exact (@lem1143876 (_26916 -> Prop) (type1143 _26916) f x). Qed.
Lemma lem1143878 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) : (term474 _26916 _26917 P x) = (term476 _26916 _26917 P x).
Proof. exact (@lem1143877 _26916 (@List.Forall _26916) (@I (_26917 -> _26916 -> Prop) P x)). Qed.
Lemma lem1143879 {_26916 : Type'} (t : list _26916) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1143880 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term475 _26916 _26917 P x t) = (term477 _26916 _26917 P x t).
Proof. exact (MK_COMB (@lem1143878 _26916 _26917 P x) (@lem1143879 _26916 t)). Qed.
Lemma lem1143882 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1143883 {_26916 : Type'} (f : type1143 _26916) (x : list _26916) : (f x) = (@I ((list _26916) -> Prop) f x).
Proof. exact (@lem1143882 (list _26916) Prop f x). Qed.
Lemma lem1143884 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term477 _26916 _26917 P x t) = (term478 _26916 _26917 P x t).
Proof. exact (@lem1143883 _26916 (term476 _26916 _26917 P x) t). Qed.
Lemma lem1143885 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term475 _26916 _26917 P x t) = (term478 _26916 _26917 P x t).
Proof. exact (TRANS (@lem1143880 _26916 _26917 P x t) (@lem1143884 _26916 _26917 P x t)). Qed.
Lemma lem1143886 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term81 _26916 _26917 P x t) = (term478 _26916 _26917 P x t).
Proof. exact (TRANS (@lem1143874 _26916 _26917 P x t) (@lem1143885 _26916 _26917 P x t)). Qed.
Lemma lem1143887 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term76 _26916 _26917 P t) = (term487 _26916 _26917 P t).
Proof. exact (fun_ext (fun x : _26917 => @lem1143886 _26916 _26917 P x t)). Qed.
Lemma lem1143888 {_26917 : Type'} : (@all _26917) = (@all _26917).
Proof. exact (eq_refl (@all _26917)). Qed.
Lemma lem1143889 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term9 _26916 _26917 P t) = (term488 _26916 _26917 P t).
Proof. exact (MK_COMB (@lem1143888 _26917) (@lem1143887 _26916 _26917 P t)). Qed.
Lemma lem1143896 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1143897 {_26916 _26917 : Type'} (f : type1470 _26916 _26917) (x : _26917) : (f x) = (@I (_26917 -> _26916 -> Prop) f x).
Proof. exact (@lem1143896 _26917 (_26916 -> Prop) f x). Qed.
Lemma lem1143898 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) : (P x) = (@I (_26917 -> _26916 -> Prop) P x).
Proof. exact (@lem1143897 _26916 _26917 P x). Qed.
Lemma lem1143899 {_26916 : Type'} (h : _26916) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1143900 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (P x h) = (@I (_26917 -> _26916 -> Prop) P x h).
Proof. exact (MK_COMB (@lem1143898 _26916 _26917 P x) (@lem1143899 _26916 h)). Qed.
Lemma lem1143902 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1143903 {_26916 : Type'} (f : _26916 -> Prop) (x : _26916) : (f x) = (@I (_26916 -> Prop) f x).
Proof. exact (@lem1143902 _26916 Prop f x). Qed.
Lemma lem1143904 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (@I (_26917 -> _26916 -> Prop) P x h) = (term468 _26916 _26917 P x h).
Proof. exact (@lem1143903 _26916 (@I (_26917 -> _26916 -> Prop) P x) h). Qed.
Lemma lem1143906 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (P x h) = (term468 _26916 _26917 P x h).
Proof. exact (TRANS (@lem1143900 _26916 _26917 P x h) (@lem1143904 _26916 _26917 P x h)). Qed.
Lemma lem1143907 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term75 _26916 _26917 P h) = (term469 _26916 _26917 P h).
Proof. exact (fun_ext (fun x : _26917 => @lem1143906 _26916 _26917 P x h)). Qed.
Lemma lem1143908 {_26917 : Type'} : (@all _26917) = (@all _26917).
Proof. exact (eq_refl (@all _26917)). Qed.
Lemma lem1143909 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term55 _26916 _26917 P h) = (term470 _26916 _26917 P h).
Proof. exact (MK_COMB (@lem1143908 _26917) (@lem1143907 _26916 _26917 P h)). Qed.
Lemma lem1143910 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1143911 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term60 _26916 _26917 P h) = (term471 _26916 _26917 P h).
Proof. exact (MK_COMB (@lem1143910) (@lem1143909 _26916 _26917 P h)). Qed.
Lemma lem1143912 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term90 _26916 _26917 h P t) = (term489 _26916 _26917 h P t).
Proof. exact (MK_COMB (@lem1143911 _26916 _26917 P h) (@lem1143889 _26916 _26917 P t)). Qed.
Lemma lem1143913 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1143914 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term379 _26916 _26917 h P t) = (term490 _26916 _26917 h P t).
Proof. exact (MK_COMB (@lem1143913) (@lem1143912 _26916 _26917 h P t)). Qed.
Lemma lem1143915 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term411 _26916 _26917 x h _18906 P t) = (term491 _26916 _26917 x h _18906 P t).
Proof. exact (MK_COMB (@lem1143914 _26916 _26917 h P t) (@lem1143862 _26916 _26917 x h _18906 P t)). Qed.
Lemma lem1143916 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1143917 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term457 _26916 _26917 x h _18906 P t) = (term492 _26916 _26917 x h _18906 P t).
Proof. exact (MK_COMB (@lem1143916) (@lem1143915 _26916 _26917 x h _18906 P t)). Qed.
Lemma lem1143918 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term459 _26916 _26917 x h _18906 P t) = (term493 _26916 _26917 x h _18906 P t).
Proof. exact (MK_COMB (@lem1143917 _26916 _26917 x h _18906 P t) (@lem1143814 _26916 _26917 x h _18906 P t)). Qed.
Lemma lem1143919 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term459 _26916 _26917 x h _18906 P t) : term493 _26916 _26917 x h _18906 P t.
Proof. exact (EQ_MP (@lem1143918 _26916 _26917 x h _18906 P t) (@lem1143714 _26916 _26917 x h _18906 P t h1)). Qed.
Lemma lem1143920 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1143921 {_26916 : Type'} : (@List.Forall _26916) = (@List.Forall _26916).
Proof. exact (eq_refl (@List.Forall _26916)). Qed.
Lemma lem1143926 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1143927 {_26916 _26917 : Type'} (f : type740 _26916 _26917) (x : type1470 _26916 _26917) : (f x) = (@I ((_26917 -> _26916 -> Prop) -> _26916 -> Prop) f x).
Proof. exact (@lem1143926 (type1470 _26916 _26917) (_26916 -> Prop) f x). Qed.
Lemma lem1143929 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (_18906 P) = (@I ((_26917 -> _26916 -> Prop) -> _26916 -> Prop) _18906 P).
Proof. exact (@lem1143927 _26916 _26917 _18906 P). Qed.
Lemma lem1143930 {_26916 : Type'} (t : list _26916) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1143931 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term109 _26916 _26917 _18906 P) = (term463 _26916 _26917 _18906 P).
Proof. exact (MK_COMB (@lem1143921 _26916) (@lem1143929 _26916 _26917 _18906 P)). Qed.
Lemma lem1143932 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term110 _26916 _26917 _18906 P t) = (term464 _26916 _26917 _18906 P t).
Proof. exact (MK_COMB (@lem1143931 _26916 _26917 _18906 P) (@lem1143930 _26916 t)). Qed.
Lemma lem1143934 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1143935 {_26916 : Type'} (f : type663 _26916) (x : _26916 -> Prop) : (f x) = (@I ((_26916 -> Prop) -> (list _26916) -> Prop) f x).
Proof. exact (@lem1143934 (_26916 -> Prop) (type1143 _26916) f x). Qed.
Lemma lem1143936 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term463 _26916 _26917 _18906 P) = (term465 _26916 _26917 _18906 P).
Proof. exact (@lem1143935 _26916 (@List.Forall _26916) (@I ((_26917 -> _26916 -> Prop) -> _26916 -> Prop) _18906 P)). Qed.
Lemma lem1143937 {_26916 : Type'} (t : list _26916) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1143938 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term464 _26916 _26917 _18906 P t) = (term466 _26916 _26917 _18906 P t).
Proof. exact (MK_COMB (@lem1143936 _26916 _26917 _18906 P) (@lem1143937 _26916 t)). Qed.
Lemma lem1143940 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1143941 {_26916 : Type'} (f : type1143 _26916) (x : list _26916) : (f x) = (@I ((list _26916) -> Prop) f x).
Proof. exact (@lem1143940 (list _26916) Prop f x). Qed.
Lemma lem1143942 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term466 _26916 _26917 _18906 P t) = (term467 _26916 _26917 _18906 P t).
Proof. exact (@lem1143941 _26916 (term465 _26916 _26917 _18906 P) t). Qed.
Lemma lem1143943 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term464 _26916 _26917 _18906 P t) = (term467 _26916 _26917 _18906 P t).
Proof. exact (TRANS (@lem1143938 _26916 _26917 _18906 P t) (@lem1143942 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143944 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term110 _26916 _26917 _18906 P t) = (term467 _26916 _26917 _18906 P t).
Proof. exact (TRANS (@lem1143932 _26916 _26917 _18906 P t) (@lem1143943 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143945 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term329 _26916 _26917 _18906 P t) = (term485 _26916 _26917 _18906 P t).
Proof. exact (MK_COMB (@lem1143920) (@lem1143944 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143946 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1143947 {_26916 : Type'} : (@List.Forall _26916) = (@List.Forall _26916).
Proof. exact (eq_refl (@List.Forall _26916)). Qed.
Lemma lem1143952 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1143953 {_26916 _26917 : Type'} (f : type1470 _26916 _26917) (x : _26917) : (f x) = (@I (_26917 -> _26916 -> Prop) f x).
Proof. exact (@lem1143952 _26917 (_26916 -> Prop) f x). Qed.
Lemma lem1143955 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x' : _26917) : (P x') = (@I (_26917 -> _26916 -> Prop) P x').
Proof. exact (@lem1143953 _26916 _26917 P x'). Qed.
Lemma lem1143956 {_26916 : Type'} (t : list _26916) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1143957 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x' : _26917) : (term473 _26916 _26917 P x') = (term474 _26916 _26917 P x').
Proof. exact (MK_COMB (@lem1143947 _26916) (@lem1143955 _26916 _26917 P x')). Qed.
Lemma lem1143958 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x' : _26917) (t : list _26916) : (term81 _26916 _26917 P x' t) = (term475 _26916 _26917 P x' t).
Proof. exact (MK_COMB (@lem1143957 _26916 _26917 P x') (@lem1143956 _26916 t)). Qed.
Lemma lem1143960 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1143961 {_26916 : Type'} (f : type663 _26916) (x : _26916 -> Prop) : (f x) = (@I ((_26916 -> Prop) -> (list _26916) -> Prop) f x).
Proof. exact (@lem1143960 (_26916 -> Prop) (type1143 _26916) f x). Qed.
Lemma lem1143962 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x' : _26917) : (term474 _26916 _26917 P x') = (term476 _26916 _26917 P x').
Proof. exact (@lem1143961 _26916 (@List.Forall _26916) (@I (_26917 -> _26916 -> Prop) P x')). Qed.
Lemma lem1143963 {_26916 : Type'} (t : list _26916) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1143964 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x' : _26917) (t : list _26916) : (term475 _26916 _26917 P x' t) = (term477 _26916 _26917 P x' t).
Proof. exact (MK_COMB (@lem1143962 _26916 _26917 P x') (@lem1143963 _26916 t)). Qed.
Lemma lem1143966 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1143967 {_26916 : Type'} (f : type1143 _26916) (x : list _26916) : (f x) = (@I ((list _26916) -> Prop) f x).
Proof. exact (@lem1143966 (list _26916) Prop f x). Qed.
Lemma lem1143968 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x' : _26917) (t : list _26916) : (term477 _26916 _26917 P x' t) = (term478 _26916 _26917 P x' t).
Proof. exact (@lem1143967 _26916 (term476 _26916 _26917 P x') t). Qed.
Lemma lem1143969 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x' : _26917) (t : list _26916) : (term475 _26916 _26917 P x' t) = (term478 _26916 _26917 P x' t).
Proof. exact (TRANS (@lem1143964 _26916 _26917 P x' t) (@lem1143968 _26916 _26917 P x' t)). Qed.
Lemma lem1143970 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x' : _26917) (t : list _26916) : (term81 _26916 _26917 P x' t) = (term478 _26916 _26917 P x' t).
Proof. exact (TRANS (@lem1143958 _26916 _26917 P x' t) (@lem1143969 _26916 _26917 P x' t)). Qed.
Lemma lem1143971 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x' : _26917) (t : list _26916) : (term325 _26916 _26917 P x' t) = (term479 _26916 _26917 P x' t).
Proof. exact (MK_COMB (@lem1143946) (@lem1143970 _26916 _26917 P x' t)). Qed.
Lemma lem1143972 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1143973 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x' : _26917) (t : list _26916) : (term348 _26916 _26917 P x' t) = (term494 _26916 _26917 P x' t).
Proof. exact (MK_COMB (@lem1143972) (@lem1143971 _26916 _26917 P x' t)). Qed.
Lemma lem1143974 {_26916 _26917 : Type'} (x' : _26917) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term350 _26916 _26917 x' _18906 P t) = (term495 _26916 _26917 x' _18906 P t).
Proof. exact (MK_COMB (@lem1143973 _26916 _26917 P x' t) (@lem1143945 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143975 {_26916 : Type'} : (@List.Forall _26916) = (@List.Forall _26916).
Proof. exact (eq_refl (@List.Forall _26916)). Qed.
Lemma lem1143980 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1143981 {_26916 _26917 : Type'} (f : type740 _26916 _26917) (x : type1470 _26916 _26917) : (f x) = (@I ((_26917 -> _26916 -> Prop) -> _26916 -> Prop) f x).
Proof. exact (@lem1143980 (type1470 _26916 _26917) (_26916 -> Prop) f x). Qed.
Lemma lem1143983 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (_18906 P) = (@I ((_26917 -> _26916 -> Prop) -> _26916 -> Prop) _18906 P).
Proof. exact (@lem1143981 _26916 _26917 _18906 P). Qed.
Lemma lem1143984 {_26916 : Type'} (t : list _26916) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1143985 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term109 _26916 _26917 _18906 P) = (term463 _26916 _26917 _18906 P).
Proof. exact (MK_COMB (@lem1143975 _26916) (@lem1143983 _26916 _26917 _18906 P)). Qed.
Lemma lem1143986 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term110 _26916 _26917 _18906 P t) = (term464 _26916 _26917 _18906 P t).
Proof. exact (MK_COMB (@lem1143985 _26916 _26917 _18906 P) (@lem1143984 _26916 t)). Qed.
Lemma lem1143988 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1143989 {_26916 : Type'} (f : type663 _26916) (x : _26916 -> Prop) : (f x) = (@I ((_26916 -> Prop) -> (list _26916) -> Prop) f x).
Proof. exact (@lem1143988 (_26916 -> Prop) (type1143 _26916) f x). Qed.
Lemma lem1143990 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) : (term463 _26916 _26917 _18906 P) = (term465 _26916 _26917 _18906 P).
Proof. exact (@lem1143989 _26916 (@List.Forall _26916) (@I ((_26917 -> _26916 -> Prop) -> _26916 -> Prop) _18906 P)). Qed.
Lemma lem1143991 {_26916 : Type'} (t : list _26916) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1143992 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term464 _26916 _26917 _18906 P t) = (term466 _26916 _26917 _18906 P t).
Proof. exact (MK_COMB (@lem1143990 _26916 _26917 _18906 P) (@lem1143991 _26916 t)). Qed.
Lemma lem1143994 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1143995 {_26916 : Type'} (f : type1143 _26916) (x : list _26916) : (f x) = (@I ((list _26916) -> Prop) f x).
Proof. exact (@lem1143994 (list _26916) Prop f x). Qed.
Lemma lem1143996 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term466 _26916 _26917 _18906 P t) = (term467 _26916 _26917 _18906 P t).
Proof. exact (@lem1143995 _26916 (term465 _26916 _26917 _18906 P) t). Qed.
Lemma lem1143997 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term464 _26916 _26917 _18906 P t) = (term467 _26916 _26917 _18906 P t).
Proof. exact (TRANS (@lem1143992 _26916 _26917 _18906 P t) (@lem1143996 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143998 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term110 _26916 _26917 _18906 P t) = (term467 _26916 _26917 _18906 P t).
Proof. exact (TRANS (@lem1143986 _26916 _26917 _18906 P t) (@lem1143997 _26916 _26917 _18906 P t)). Qed.
Lemma lem1143999 {_26916 : Type'} : (@List.Forall _26916) = (@List.Forall _26916).
Proof. exact (eq_refl (@List.Forall _26916)). Qed.
Lemma lem1144004 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1144005 {_26916 _26917 : Type'} (f : type1470 _26916 _26917) (x : _26917) : (f x) = (@I (_26917 -> _26916 -> Prop) f x).
Proof. exact (@lem1144004 _26917 (_26916 -> Prop) f x). Qed.
Lemma lem1144007 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) : (P x) = (@I (_26917 -> _26916 -> Prop) P x).
Proof. exact (@lem1144005 _26916 _26917 P x). Qed.
Lemma lem1144008 {_26916 : Type'} (t : list _26916) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1144009 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) : (term473 _26916 _26917 P x) = (term474 _26916 _26917 P x).
Proof. exact (MK_COMB (@lem1143999 _26916) (@lem1144007 _26916 _26917 P x)). Qed.
Lemma lem1144010 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term81 _26916 _26917 P x t) = (term475 _26916 _26917 P x t).
Proof. exact (MK_COMB (@lem1144009 _26916 _26917 P x) (@lem1144008 _26916 t)). Qed.
Lemma lem1144012 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1144013 {_26916 : Type'} (f : type663 _26916) (x : _26916 -> Prop) : (f x) = (@I ((_26916 -> Prop) -> (list _26916) -> Prop) f x).
Proof. exact (@lem1144012 (_26916 -> Prop) (type1143 _26916) f x). Qed.
Lemma lem1144014 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) : (term474 _26916 _26917 P x) = (term476 _26916 _26917 P x).
Proof. exact (@lem1144013 _26916 (@List.Forall _26916) (@I (_26917 -> _26916 -> Prop) P x)). Qed.
Lemma lem1144015 {_26916 : Type'} (t : list _26916) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1144016 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term475 _26916 _26917 P x t) = (term477 _26916 _26917 P x t).
Proof. exact (MK_COMB (@lem1144014 _26916 _26917 P x) (@lem1144015 _26916 t)). Qed.
Lemma lem1144018 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1144019 {_26916 : Type'} (f : type1143 _26916) (x : list _26916) : (f x) = (@I ((list _26916) -> Prop) f x).
Proof. exact (@lem1144018 (list _26916) Prop f x). Qed.
Lemma lem1144020 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term477 _26916 _26917 P x t) = (term478 _26916 _26917 P x t).
Proof. exact (@lem1144019 _26916 (term476 _26916 _26917 P x) t). Qed.
Lemma lem1144021 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term475 _26916 _26917 P x t) = (term478 _26916 _26917 P x t).
Proof. exact (TRANS (@lem1144016 _26916 _26917 P x t) (@lem1144020 _26916 _26917 P x t)). Qed.
Lemma lem1144022 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term81 _26916 _26917 P x t) = (term478 _26916 _26917 P x t).
Proof. exact (TRANS (@lem1144010 _26916 _26917 P x t) (@lem1144021 _26916 _26917 P x t)). Qed.
Lemma lem1144023 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term76 _26916 _26917 P t) = (term487 _26916 _26917 P t).
Proof. exact (fun_ext (fun x : _26917 => @lem1144022 _26916 _26917 P x t)). Qed.
Lemma lem1144024 {_26917 : Type'} : (@all _26917) = (@all _26917).
Proof. exact (eq_refl (@all _26917)). Qed.
Lemma lem1144025 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term9 _26916 _26917 P t) = (term488 _26916 _26917 P t).
Proof. exact (MK_COMB (@lem1144024 _26917) (@lem1144023 _26916 _26917 P t)). Qed.
Lemma lem1144026 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1144027 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term334 _26916 _26917 P t) = (term496 _26916 _26917 P t).
Proof. exact (MK_COMB (@lem1144026) (@lem1144025 _26916 _26917 P t)). Qed.
Lemma lem1144028 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term335 _26916 _26917 _18906 P t) = (term497 _26916 _26917 _18906 P t).
Proof. exact (MK_COMB (@lem1144027 _26916 _26917 P t) (@lem1143998 _26916 _26917 _18906 P t)). Qed.
Lemma lem1144029 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1144030 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term336 _26916 _26917 _18906 P t) = (term498 _26916 _26917 _18906 P t).
Proof. exact (MK_COMB (@lem1144029) (@lem1144028 _26916 _26917 _18906 P t)). Qed.
Lemma lem1144031 {_26916 _26917 : Type'} (x' : _26917) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term363 _26916 _26917 x' _18906 P t) = (term499 _26916 _26917 x' _18906 P t).
Proof. exact (MK_COMB (@lem1144030 _26916 _26917 _18906 P t) (@lem1143974 _26916 _26917 x' _18906 P t)). Qed.
Lemma lem1144032 {_26916 _26917 : Type'} (x' : _26917) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term363 _26916 _26917 x' _18906 P t) : term499 _26916 _26917 x' _18906 P t.
Proof. exact (EQ_MP (@lem1144031 _26916 _26917 x' _18906 P t) (@lem1143715 _26916 _26917 x' _18906 P t h1)). Qed.
Lemma lem1144148 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term497 _26916 _26917 _18906 P t) : term497 _26916 _26917 _18906 P t.
Proof. exact (h1). Qed.
Lemma lem1144149 {_26916 _26917 : Type'} (x' : _26917) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term495 _26916 _26917 x' _18906 P t) : term495 _26916 _26917 x' _18906 P t.
Proof. exact (h1). Qed.
Lemma lem1144151 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term497 _26916 _26917 _18906 P t) : term488 _26916 _26917 P t.
Proof. exact (proj1 (@lem1144148 _26916 _26917 _18906 P t h1)). Qed.
Lemma lem1144152 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term491 _26916 _26917 x h _18906 P t) : term491 _26916 _26917 x h _18906 P t.
Proof. exact (h1). Qed.
Lemma lem1144153 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term484 _26916 _26917 x h _18906 P t) : term484 _26916 _26917 x h _18906 P t.
Proof. exact (h1). Qed.
Lemma lem1144154 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term491 _26916 _26917 x h _18906 P t) : term486 _26916 _26917 x h _18906 P t.
Proof. exact (proj2 (@lem1144152 _26916 _26917 x h _18906 P t h1)). Qed.
Lemma lem1144155 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term491 _26916 _26917 x h _18906 P t) : term489 _26916 _26917 h P t.
Proof. exact (proj1 (@lem1144152 _26916 _26917 x h _18906 P t h1)). Qed.
Lemma lem1144157 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term491 _26916 _26917 x h _18906 P t) : term470 _26916 _26917 P h.
Proof. exact (proj1 (@lem1144155 _26916 _26917 x h _18906 P t h1)). Qed.
Lemma lem1144160 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term484 _26916 _26917 x h _18906 P t) : term472 _26916 _26917 h _18906 P t.
Proof. exact (proj2 (@lem1144153 _26916 _26917 x h _18906 P t h1)). Qed.
Lemma lem1144161 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term484 _26916 _26917 x h _18906 P t) : term482 _26916 _26917 h P x t.
Proof. exact (proj1 (@lem1144153 _26916 _26917 x h _18906 P t h1)). Qed.
Lemma lem1144163 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term484 _26916 _26917 x h _18906 P t) : term470 _26916 _26917 P h.
Proof. exact (proj1 (@lem1144160 _26916 _26917 x h _18906 P t h1)). Qed.
Lemma lem1144168 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term491 _26916 _26917 x h _18906 P t) : term491 _26916 _26917 x h _18906 P t.
Proof. exact (h1). Qed.
Lemma lem1144169 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term484 _26916 _26917 x h _18906 P t) : term484 _26916 _26917 x h _18906 P t.
Proof. exact (h1). Qed.
Lemma lem1144170 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term491 _26916 _26917 x h _18906 P t) : term486 _26916 _26917 x h _18906 P t.
Proof. exact (proj2 (@lem1144168 _26916 _26917 x h _18906 P t h1)). Qed.
Lemma lem1144171 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term491 _26916 _26917 x h _18906 P t) : term489 _26916 _26917 h P t.
Proof. exact (proj1 (@lem1144168 _26916 _26917 x h _18906 P t h1)). Qed.
Lemma lem1144172 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term491 _26916 _26917 x h _18906 P t) : term488 _26916 _26917 P t.
Proof. exact (proj2 (@lem1144171 _26916 _26917 x h _18906 P t h1)). Qed.
Lemma lem1144173 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term491 _26916 _26917 x h _18906 P t) : term470 _26916 _26917 P h.
Proof. exact (proj1 (@lem1144171 _26916 _26917 x h _18906 P t h1)). Qed.
Lemma lem1144176 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term484 _26916 _26917 x h _18906 P t) : term472 _26916 _26917 h _18906 P t.
Proof. exact (proj2 (@lem1144169 _26916 _26917 x h _18906 P t h1)). Qed.
Lemma lem1144177 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term484 _26916 _26917 x h _18906 P t) : term482 _26916 _26917 h P x t.
Proof. exact (proj1 (@lem1144169 _26916 _26917 x h _18906 P t h1)). Qed.
Lemma lem1144179 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term484 _26916 _26917 x h _18906 P t) : term470 _26916 _26917 P h.
Proof. exact (proj1 (@lem1144176 _26916 _26917 x h _18906 P t h1)). Qed.
Lemma lem1144254 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (term468 _26916 _26917 P x h) = (term468 _26916 _26917 P x h).
Proof. exact (eq_refl (term468 _26916 _26917 P x h)). Qed.
Lemma lem1144255 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term469 _26916 _26917 P h) = (term469 _26916 _26917 P h).
Proof. exact (fun_ext (fun x : _26917 => @lem1144254 _26916 _26917 P x h)). Qed.
Lemma lem1144256 {_26917 : Type'} : (@all _26917) = (@all _26917).
Proof. exact (eq_refl (@all _26917)). Qed.
Lemma lem1144258 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term470 _26916 _26917 P h) = (term470 _26916 _26917 P h).
Proof. exact (MK_COMB (@lem1144256 _26917) (@lem1144255 _26916 _26917 P h)). Qed.
Lemma lem1144259 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term491 _26916 _26917 x h _18906 P t) : term470 _26916 _26917 P h.
Proof. exact (EQ_MP (@lem1144258 _26916 _26917 P h) (@lem1144157 _26916 _26917 x h _18906 P t h1)). Qed.
Lemma lem1144270 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) (h1 : term480 _26916 _26917 P x h) : term480 _26916 _26917 P x h.
Proof. exact (h1). Qed.
Lemma lem1144359 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term485 _26916 _26917 _18906 P t) : term485 _26916 _26917 _18906 P t.
Proof. exact (h1). Qed.
Lemma lem1144432 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (term468 _26916 _26917 P x h) = (term468 _26916 _26917 P x h).
Proof. exact (eq_refl (term468 _26916 _26917 P x h)). Qed.
Lemma lem1144433 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term469 _26916 _26917 P h) = (term469 _26916 _26917 P h).
Proof. exact (fun_ext (fun x : _26917 => @lem1144432 _26916 _26917 P x h)). Qed.
Lemma lem1144434 {_26917 : Type'} : (@all _26917) = (@all _26917).
Proof. exact (eq_refl (@all _26917)). Qed.
Lemma lem1144436 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term470 _26916 _26917 P h) = (term470 _26916 _26917 P h).
Proof. exact (MK_COMB (@lem1144434 _26917) (@lem1144433 _26916 _26917 P h)). Qed.
Lemma lem1144437 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term484 _26916 _26917 x h _18906 P t) : term470 _26916 _26917 P h.
Proof. exact (EQ_MP (@lem1144436 _26916 _26917 P h) (@lem1144163 _26916 _26917 x h _18906 P t h1)). Qed.
Lemma lem1144445 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) (h1 : term480 _26916 _26917 P x h) : term480 _26916 _26917 P x h.
Proof. exact (h1). Qed.
Lemma lem1144507 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term478 _26916 _26917 P x t) = (term478 _26916 _26917 P x t).
Proof. exact (eq_refl (term478 _26916 _26917 P x t)). Qed.
Lemma lem1144508 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term487 _26916 _26917 P t) = (term487 _26916 _26917 P t).
Proof. exact (fun_ext (fun x : _26917 => @lem1144507 _26916 _26917 P x t)). Qed.
Lemma lem1144509 {_26917 : Type'} : (@all _26917) = (@all _26917).
Proof. exact (eq_refl (@all _26917)). Qed.
Lemma lem1144511 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term488 _26916 _26917 P t) = (term488 _26916 _26917 P t).
Proof. exact (MK_COMB (@lem1144509 _26917) (@lem1144508 _26916 _26917 P t)). Qed.
Lemma lem1144512 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term497 _26916 _26917 _18906 P t) : term488 _26916 _26917 P t.
Proof. exact (EQ_MP (@lem1144511 _26916 _26917 P t) (@lem1144151 _26916 _26917 _18906 P t h1)). Qed.
Lemma lem1144531 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) (h1 : term479 _26916 _26917 P x t) : term479 _26916 _26917 P x t.
Proof. exact (h1). Qed.
Lemma lem1144601 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (term468 _26916 _26917 P x h) = (term468 _26916 _26917 P x h).
Proof. exact (eq_refl (term468 _26916 _26917 P x h)). Qed.
Lemma lem1144602 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term469 _26916 _26917 P h) = (term469 _26916 _26917 P h).
Proof. exact (fun_ext (fun x : _26917 => @lem1144601 _26916 _26917 P x h)). Qed.
Lemma lem1144603 {_26917 : Type'} : (@all _26917) = (@all _26917).
Proof. exact (eq_refl (@all _26917)). Qed.
Lemma lem1144605 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term470 _26916 _26917 P h) = (term470 _26916 _26917 P h).
Proof. exact (MK_COMB (@lem1144603 _26917) (@lem1144602 _26916 _26917 P h)). Qed.
Lemma lem1144606 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term491 _26916 _26917 x h _18906 P t) : term470 _26916 _26917 P h.
Proof. exact (EQ_MP (@lem1144605 _26916 _26917 P h) (@lem1144173 _26916 _26917 x h _18906 P t h1)). Qed.
Lemma lem1144617 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) (h1 : term480 _26916 _26917 P x h) : term480 _26916 _26917 P x h.
Proof. exact (h1). Qed.
Lemma lem1144694 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term478 _26916 _26917 P x t) = (term478 _26916 _26917 P x t).
Proof. exact (eq_refl (term478 _26916 _26917 P x t)). Qed.
Lemma lem1144695 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term487 _26916 _26917 P t) = (term487 _26916 _26917 P t).
Proof. exact (fun_ext (fun x : _26917 => @lem1144694 _26916 _26917 P x t)). Qed.
Lemma lem1144696 {_26917 : Type'} : (@all _26917) = (@all _26917).
Proof. exact (eq_refl (@all _26917)). Qed.
Lemma lem1144698 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term488 _26916 _26917 P t) = (term488 _26916 _26917 P t).
Proof. exact (MK_COMB (@lem1144696 _26917) (@lem1144695 _26916 _26917 P t)). Qed.
Lemma lem1144699 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term491 _26916 _26917 x h _18906 P t) : term488 _26916 _26917 P t.
Proof. exact (EQ_MP (@lem1144698 _26916 _26917 P t) (@lem1144172 _26916 _26917 x h _18906 P t h1)). Qed.
Lemma lem1144773 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (term468 _26916 _26917 P x h) = (term468 _26916 _26917 P x h).
Proof. exact (eq_refl (term468 _26916 _26917 P x h)). Qed.
Lemma lem1144774 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term469 _26916 _26917 P h) = (term469 _26916 _26917 P h).
Proof. exact (fun_ext (fun x : _26917 => @lem1144773 _26916 _26917 P x h)). Qed.
Lemma lem1144775 {_26917 : Type'} : (@all _26917) = (@all _26917).
Proof. exact (eq_refl (@all _26917)). Qed.
Lemma lem1144777 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : (term470 _26916 _26917 P h) = (term470 _26916 _26917 P h).
Proof. exact (MK_COMB (@lem1144775 _26917) (@lem1144774 _26916 _26917 P h)). Qed.
Lemma lem1144778 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term484 _26916 _26917 x h _18906 P t) : term470 _26916 _26917 P h.
Proof. exact (EQ_MP (@lem1144777 _26916 _26917 P h) (@lem1144179 _26916 _26917 x h _18906 P t h1)). Qed.
Lemma lem1144786 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) (h1 : term480 _26916 _26917 P x h) : term480 _26916 _26917 P x h.
Proof. exact (h1). Qed.
Lemma lem1144888 {_26916 _26917 : Type'} (_18913 : _26917) (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term491 _26916 _26917 x h _18906 P t) : term500 _26916 _26917 P h _18913.
Proof. exact (@lem1144259 _26916 _26917 x h _18906 P t h1 _18913). Qed.
Lemma lem1144889 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (_18913 : _26917) (h : _26916) : (term500 _26916 _26917 P h _18913) = (term468 _26916 _26917 P _18913 h).
Proof. exact (eq_refl (term500 _26916 _26917 P h _18913)). Qed.
Lemma lem1144936 {_26916 _26917 : Type'} (_18929 : _26917) (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term484 _26916 _26917 x h _18906 P t) : term500 _26916 _26917 P h _18929.
Proof. exact (@lem1144437 _26916 _26917 x h _18906 P t h1 _18929). Qed.
Lemma lem1144937 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (_18929 : _26917) (h : _26916) : (term500 _26916 _26917 P h _18929) = (term468 _26916 _26917 P _18929 h).
Proof. exact (eq_refl (term500 _26916 _26917 P h _18929)). Qed.
Lemma lem1144954 {_26916 _26917 : Type'} (_18935 : _26917) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term497 _26916 _26917 _18906 P t) : term501 _26916 _26917 P t _18935.
Proof. exact (@lem1144512 _26916 _26917 _18906 P t h1 _18935). Qed.
Lemma lem1144955 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (_18935 : _26917) (t : list _26916) : (term501 _26916 _26917 P t _18935) = (term478 _26916 _26917 P _18935 t).
Proof. exact (eq_refl (term501 _26916 _26917 P t _18935)). Qed.
Lemma lem1144975 {_26916 _26917 : Type'} (_18942 : _26917) (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term491 _26916 _26917 x h _18906 P t) : term500 _26916 _26917 P h _18942.
Proof. exact (@lem1144606 _26916 _26917 x h _18906 P t h1 _18942). Qed.
Lemma lem1144976 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (_18942 : _26917) (h : _26916) : (term500 _26916 _26917 P h _18942) = (term468 _26916 _26917 P _18942 h).
Proof. exact (eq_refl (term500 _26916 _26917 P h _18942)). Qed.
Lemma lem1144999 {_26916 _26917 : Type'} (_18950 : _26917) (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term491 _26916 _26917 x h _18906 P t) : term501 _26916 _26917 P t _18950.
Proof. exact (@lem1144699 _26916 _26917 x h _18906 P t h1 _18950). Qed.
Lemma lem1145000 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (_18950 : _26917) (t : list _26916) : (term501 _26916 _26917 P t _18950) = (term478 _26916 _26917 P _18950 t).
Proof. exact (eq_refl (term501 _26916 _26917 P t _18950)). Qed.
Lemma lem1145017 {_26916 _26917 : Type'} (_18956 : _26917) (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term484 _26916 _26917 x h _18906 P t) : term500 _26916 _26917 P h _18956.
Proof. exact (@lem1144778 _26916 _26917 x h _18906 P t h1 _18956). Qed.
Lemma lem1145018 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (_18956 : _26917) (h : _26916) : (term500 _26916 _26917 P h _18956) = (term468 _26916 _26917 P _18956 h).
Proof. exact (eq_refl (term500 _26916 _26917 P h _18956)). Qed.
Lemma lem1145059 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) (h1 : term480 _26916 _26917 P x h) : term480 _26916 _26917 P x h.
Proof. exact (h1). Qed.
Lemma lem1145081 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term485 _26916 _26917 _18906 P t) : term485 _26916 _26917 _18906 P t.
Proof. exact (h1). Qed.
Lemma lem1145103 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) (h1 : term480 _26916 _26917 P x h) : term480 _26916 _26917 P x h.
Proof. exact (h1). Qed.
Lemma lem1145125 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) (h1 : term479 _26916 _26917 P x t) : term479 _26916 _26917 P x t.
Proof. exact (h1). Qed.
Lemma lem1145147 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) (h1 : term480 _26916 _26917 P x h) : term480 _26916 _26917 P x h.
Proof. exact (h1). Qed.
Lemma lem1145161 {_26916 _26917 : Type'} (x' : _26917) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term495 _26916 _26917 x' _18906 P t) : term479 _26916 _26917 P x' t.
Proof. exact (proj1 (@lem1144149 _26916 _26917 x' _18906 P t h1)). Qed.
Lemma lem1145191 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) (h1 : term480 _26916 _26917 P x h) : term480 _26916 _26917 P x h.
Proof. exact (h1). Qed.
Lemma lem1145207 {_26916 _26917 : Type'} (x' : _26917) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term495 _26916 _26917 x' _18906 P t) : term485 _26916 _26917 _18906 P t.
Proof. exact (proj2 (@lem1144149 _26916 _26917 x' _18906 P t h1)). Qed.
Lemma lem1145215 {_26916 _26917 : Type'} (_18913 : _26917) (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term491 _26916 _26917 x h _18906 P t) : term468 _26916 _26917 P _18913 h.
Proof. exact (EQ_MP (@lem1144889 _26916 _26917 P _18913 h) (@lem1144888 _26916 _26917 _18913 x h _18906 P t h1)). Qed.
Lemma lem1145216 {_26916 _26917 : Type'} (_18913 : _26917) (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term491 _26916 _26917 x h _18906 P t) : term468 _26916 _26917 P _18913 h.
Proof. exact (@lem1145215 _26916 _26917 _18913 x h _18906 P t h1). Qed.
Lemma lem1145217 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term491 _26916 _26917 x h _18906 P t) : term468 _26916 _26917 P x h.
Proof. exact (@lem1145216 _26916 _26917 x x h _18906 P t h1). Qed.
Lemma lem1145218 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term491 _26916 _26917 x h _18906 P t) : term502 _26916 _26917 P x h.
Proof. exact (fun h0 : term480 _26916 _26917 P x h => @lem1145217 _26916 _26917 x h _18906 P t h1). Qed.
Lemma lem1145220 (p : Prop) : (term503 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1145221 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (term502 _26916 _26917 P x h) = (term468 _26916 _26917 P x h).
Proof. exact (@lem1145220 (term468 _26916 _26917 P x h)). Qed.
Lemma lem1145222 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term491 _26916 _26917 x h _18906 P t) : term468 _26916 _26917 P x h.
Proof. exact (EQ_MP (@lem1145221 _26916 _26917 P x h) (@lem1145218 _26916 _26917 x h _18906 P t h1)). Qed.
Lemma lem1145225 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1145227 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (term480 _26916 _26917 P x h) = (term504 _26916 _26917 P x h).
Proof. exact (@lem1145225 (term468 _26916 _26917 P x h)). Qed.
Lemma lem1145230 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) (h1 : term480 _26916 _26917 P x h) : term504 _26916 _26917 P x h.
Proof. exact (EQ_MP (@lem1145227 _26916 _26917 P x h) (@lem1145059 _26916 _26917 P x h h1)). Qed.
Lemma lem1145233 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term480 _26916 _26917 P x h) (h2 : term491 _26916 _26917 x h _18906 P t) : False.
Proof. exact (@lem1145230 _26916 _26917 P x h h1 (@lem1145222 _26916 _26917 x h _18906 P t h2)). Qed.
Lemma lem1145234 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term480 _26916 _26917 P x h) (h2 : term491 _26916 _26917 x h _18906 P t) : term505.
Proof. exact (fun h0 : ~ False => @lem1145233 _26916 _26917 x h _18906 P t h1 h2). Qed.
Lemma lem1145236 (p : Prop) : (term503 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1145237 : term505 = False.
Proof. exact (@lem1145236 False). Qed.
Lemma lem1145238 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term480 _26916 _26917 P x h) (h2 : term491 _26916 _26917 x h _18906 P t) : False.
Proof. exact (EQ_MP (@lem1145237) (@lem1145234 _26916 _26917 x h _18906 P t h1 h2)). Qed.
Lemma lem1145240 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term497 _26916 _26917 _18906 P t) : term467 _26916 _26917 _18906 P t.
Proof. exact (proj2 (@lem1144148 _26916 _26917 _18906 P t h1)). Qed.
Lemma lem1145241 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term497 _26916 _26917 _18906 P t) : term506 _26916 _26917 _18906 P t.
Proof. exact (fun h0 : term485 _26916 _26917 _18906 P t => @lem1145240 _26916 _26917 _18906 P t h1). Qed.
Lemma lem1145243 (p : Prop) : (term503 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1145244 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term506 _26916 _26917 _18906 P t) = (term467 _26916 _26917 _18906 P t).
Proof. exact (@lem1145243 (term467 _26916 _26917 _18906 P t)). Qed.
Lemma lem1145245 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term497 _26916 _26917 _18906 P t) : term467 _26916 _26917 _18906 P t.
Proof. exact (EQ_MP (@lem1145244 _26916 _26917 _18906 P t) (@lem1145241 _26916 _26917 _18906 P t h1)). Qed.
Lemma lem1145248 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1145250 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term485 _26916 _26917 _18906 P t) = (term507 _26916 _26917 _18906 P t).
Proof. exact (@lem1145248 (term467 _26916 _26917 _18906 P t)). Qed.
Lemma lem1145253 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term485 _26916 _26917 _18906 P t) : term507 _26916 _26917 _18906 P t.
Proof. exact (EQ_MP (@lem1145250 _26916 _26917 _18906 P t) (@lem1145081 _26916 _26917 _18906 P t h1)). Qed.
Lemma lem1145256 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term485 _26916 _26917 _18906 P t) (h2 : term497 _26916 _26917 _18906 P t) : False.
Proof. exact (@lem1145253 _26916 _26917 _18906 P t h1 (@lem1145245 _26916 _26917 _18906 P t h2)). Qed.
Lemma lem1145257 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term485 _26916 _26917 _18906 P t) (h2 : term497 _26916 _26917 _18906 P t) : term505.
Proof. exact (fun h0 : ~ False => @lem1145256 _26916 _26917 _18906 P t h1 h2). Qed.
Lemma lem1145259 (p : Prop) : (term503 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1145260 : term505 = False.
Proof. exact (@lem1145259 False). Qed.
Lemma lem1145261 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term485 _26916 _26917 _18906 P t) (h2 : term497 _26916 _26917 _18906 P t) : False.
Proof. exact (EQ_MP (@lem1145260) (@lem1145257 _26916 _26917 _18906 P t h1 h2)). Qed.
Lemma lem1145263 {_26916 _26917 : Type'} (_18929 : _26917) (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term484 _26916 _26917 x h _18906 P t) : term468 _26916 _26917 P _18929 h.
Proof. exact (EQ_MP (@lem1144937 _26916 _26917 P _18929 h) (@lem1144936 _26916 _26917 _18929 x h _18906 P t h1)). Qed.
Lemma lem1145264 {_26916 _26917 : Type'} (_18929 : _26917) (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term484 _26916 _26917 x h _18906 P t) : term468 _26916 _26917 P _18929 h.
Proof. exact (@lem1145263 _26916 _26917 _18929 x h _18906 P t h1). Qed.
Lemma lem1145265 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term484 _26916 _26917 x h _18906 P t) : term468 _26916 _26917 P x h.
Proof. exact (@lem1145264 _26916 _26917 x x h _18906 P t h1). Qed.
Lemma lem1145266 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term484 _26916 _26917 x h _18906 P t) : term502 _26916 _26917 P x h.
Proof. exact (fun h0 : term480 _26916 _26917 P x h => @lem1145265 _26916 _26917 x h _18906 P t h1). Qed.
Lemma lem1145268 (p : Prop) : (term503 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1145269 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (term502 _26916 _26917 P x h) = (term468 _26916 _26917 P x h).
Proof. exact (@lem1145268 (term468 _26916 _26917 P x h)). Qed.
Lemma lem1145270 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term484 _26916 _26917 x h _18906 P t) : term468 _26916 _26917 P x h.
Proof. exact (EQ_MP (@lem1145269 _26916 _26917 P x h) (@lem1145266 _26916 _26917 x h _18906 P t h1)). Qed.
Lemma lem1145273 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1145275 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (term480 _26916 _26917 P x h) = (term504 _26916 _26917 P x h).
Proof. exact (@lem1145273 (term468 _26916 _26917 P x h)). Qed.
Lemma lem1145278 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) (h1 : term480 _26916 _26917 P x h) : term504 _26916 _26917 P x h.
Proof. exact (EQ_MP (@lem1145275 _26916 _26917 P x h) (@lem1145103 _26916 _26917 P x h h1)). Qed.
Lemma lem1145281 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term480 _26916 _26917 P x h) (h2 : term484 _26916 _26917 x h _18906 P t) : False.
Proof. exact (@lem1145278 _26916 _26917 P x h h1 (@lem1145270 _26916 _26917 x h _18906 P t h2)). Qed.
Lemma lem1145282 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term480 _26916 _26917 P x h) (h2 : term484 _26916 _26917 x h _18906 P t) : term505.
Proof. exact (fun h0 : ~ False => @lem1145281 _26916 _26917 x h _18906 P t h1 h2). Qed.
Lemma lem1145284 (p : Prop) : (term503 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1145285 : term505 = False.
Proof. exact (@lem1145284 False). Qed.
Lemma lem1145286 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term480 _26916 _26917 P x h) (h2 : term484 _26916 _26917 x h _18906 P t) : False.
Proof. exact (EQ_MP (@lem1145285) (@lem1145282 _26916 _26917 x h _18906 P t h1 h2)). Qed.
Lemma lem1145288 {_26916 _26917 : Type'} (_18935 : _26917) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term497 _26916 _26917 _18906 P t) : term478 _26916 _26917 P _18935 t.
Proof. exact (EQ_MP (@lem1144955 _26916 _26917 P _18935 t) (@lem1144954 _26916 _26917 _18935 _18906 P t h1)). Qed.
Lemma lem1145289 {_26916 _26917 : Type'} (_18935 : _26917) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term497 _26916 _26917 _18906 P t) : term478 _26916 _26917 P _18935 t.
Proof. exact (@lem1145288 _26916 _26917 _18935 _18906 P t h1). Qed.
Lemma lem1145290 {_26916 _26917 : Type'} (x : _26917) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term497 _26916 _26917 _18906 P t) : term478 _26916 _26917 P x t.
Proof. exact (@lem1145289 _26916 _26917 x _18906 P t h1). Qed.
Lemma lem1145291 {_26916 _26917 : Type'} (x : _26917) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term497 _26916 _26917 _18906 P t) : term508 _26916 _26917 P x t.
Proof. exact (fun h0 : term479 _26916 _26917 P x t => @lem1145290 _26916 _26917 x _18906 P t h1). Qed.
Lemma lem1145293 (p : Prop) : (term503 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1145294 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term508 _26916 _26917 P x t) = (term478 _26916 _26917 P x t).
Proof. exact (@lem1145293 (term478 _26916 _26917 P x t)). Qed.
Lemma lem1145295 {_26916 _26917 : Type'} (x : _26917) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term497 _26916 _26917 _18906 P t) : term478 _26916 _26917 P x t.
Proof. exact (EQ_MP (@lem1145294 _26916 _26917 P x t) (@lem1145291 _26916 _26917 x _18906 P t h1)). Qed.
Lemma lem1145298 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1145300 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) : (term479 _26916 _26917 P x t) = (term509 _26916 _26917 P x t).
Proof. exact (@lem1145298 (term478 _26916 _26917 P x t)). Qed.
Lemma lem1145303 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (t : list _26916) (h1 : term479 _26916 _26917 P x t) : term509 _26916 _26917 P x t.
Proof. exact (EQ_MP (@lem1145300 _26916 _26917 P x t) (@lem1145125 _26916 _26917 P x t h1)). Qed.
Lemma lem1145306 {_26916 _26917 : Type'} (x : _26917) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term479 _26916 _26917 P x t) (h2 : term497 _26916 _26917 _18906 P t) : False.
Proof. exact (@lem1145303 _26916 _26917 P x t h1 (@lem1145295 _26916 _26917 x _18906 P t h2)). Qed.
Lemma lem1145307 {_26916 _26917 : Type'} (x : _26917) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term479 _26916 _26917 P x t) (h2 : term497 _26916 _26917 _18906 P t) : term505.
Proof. exact (fun h0 : ~ False => @lem1145306 _26916 _26917 x _18906 P t h1 h2). Qed.
Lemma lem1145309 (p : Prop) : (term503 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1145310 : term505 = False.
Proof. exact (@lem1145309 False). Qed.
Lemma lem1145311 {_26916 _26917 : Type'} (x : _26917) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term479 _26916 _26917 P x t) (h2 : term497 _26916 _26917 _18906 P t) : False.
Proof. exact (EQ_MP (@lem1145310) (@lem1145307 _26916 _26917 x _18906 P t h1 h2)). Qed.
Lemma lem1145313 {_26916 _26917 : Type'} (_18942 : _26917) (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term491 _26916 _26917 x h _18906 P t) : term468 _26916 _26917 P _18942 h.
Proof. exact (EQ_MP (@lem1144976 _26916 _26917 P _18942 h) (@lem1144975 _26916 _26917 _18942 x h _18906 P t h1)). Qed.
Lemma lem1145314 {_26916 _26917 : Type'} (_18942 : _26917) (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term491 _26916 _26917 x h _18906 P t) : term468 _26916 _26917 P _18942 h.
Proof. exact (@lem1145313 _26916 _26917 _18942 x h _18906 P t h1). Qed.
Lemma lem1145315 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term491 _26916 _26917 x h _18906 P t) : term468 _26916 _26917 P x h.
Proof. exact (@lem1145314 _26916 _26917 x x h _18906 P t h1). Qed.
Lemma lem1145316 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term491 _26916 _26917 x h _18906 P t) : term502 _26916 _26917 P x h.
Proof. exact (fun h0 : term480 _26916 _26917 P x h => @lem1145315 _26916 _26917 x h _18906 P t h1). Qed.
Lemma lem1145318 (p : Prop) : (term503 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1145319 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (term502 _26916 _26917 P x h) = (term468 _26916 _26917 P x h).
Proof. exact (@lem1145318 (term468 _26916 _26917 P x h)). Qed.
Lemma lem1145320 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term491 _26916 _26917 x h _18906 P t) : term468 _26916 _26917 P x h.
Proof. exact (EQ_MP (@lem1145319 _26916 _26917 P x h) (@lem1145316 _26916 _26917 x h _18906 P t h1)). Qed.
Lemma lem1145323 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1145325 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (term480 _26916 _26917 P x h) = (term504 _26916 _26917 P x h).
Proof. exact (@lem1145323 (term468 _26916 _26917 P x h)). Qed.
Lemma lem1145328 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) (h1 : term480 _26916 _26917 P x h) : term504 _26916 _26917 P x h.
Proof. exact (EQ_MP (@lem1145325 _26916 _26917 P x h) (@lem1145147 _26916 _26917 P x h h1)). Qed.
Lemma lem1145331 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term480 _26916 _26917 P x h) (h2 : term491 _26916 _26917 x h _18906 P t) : False.
Proof. exact (@lem1145328 _26916 _26917 P x h h1 (@lem1145320 _26916 _26917 x h _18906 P t h2)). Qed.
Lemma lem1145332 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term480 _26916 _26917 P x h) (h2 : term491 _26916 _26917 x h _18906 P t) : term505.
Proof. exact (fun h0 : ~ False => @lem1145331 _26916 _26917 x h _18906 P t h1 h2). Qed.
Lemma lem1145334 (p : Prop) : (term503 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1145335 : term505 = False.
Proof. exact (@lem1145334 False). Qed.
Lemma lem1145336 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term480 _26916 _26917 P x h) (h2 : term491 _26916 _26917 x h _18906 P t) : False.
Proof. exact (EQ_MP (@lem1145335) (@lem1145332 _26916 _26917 x h _18906 P t h1 h2)). Qed.
Lemma lem1145338 {_26916 _26917 : Type'} (_18950 : _26917) (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term491 _26916 _26917 x h _18906 P t) : term478 _26916 _26917 P _18950 t.
Proof. exact (EQ_MP (@lem1145000 _26916 _26917 P _18950 t) (@lem1144999 _26916 _26917 _18950 x h _18906 P t h1)). Qed.
Lemma lem1145339 {_26916 _26917 : Type'} (_18950 : _26917) (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term491 _26916 _26917 x h _18906 P t) : term478 _26916 _26917 P _18950 t.
Proof. exact (@lem1145338 _26916 _26917 _18950 x h _18906 P t h1). Qed.
Lemma lem1145340 {_26916 _26917 : Type'} (x' : _26917) (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term491 _26916 _26917 x h _18906 P t) : term478 _26916 _26917 P x' t.
Proof. exact (@lem1145339 _26916 _26917 x' x h _18906 P t h1). Qed.
Lemma lem1145341 {_26916 _26917 : Type'} (x' : _26917) (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term491 _26916 _26917 x h _18906 P t) : term508 _26916 _26917 P x' t.
Proof. exact (fun h0 : term479 _26916 _26917 P x' t => @lem1145340 _26916 _26917 x' x h _18906 P t h1). Qed.
Lemma lem1145343 (p : Prop) : (term503 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1145344 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x' : _26917) (t : list _26916) : (term508 _26916 _26917 P x' t) = (term478 _26916 _26917 P x' t).
Proof. exact (@lem1145343 (term478 _26916 _26917 P x' t)). Qed.
Lemma lem1145345 {_26916 _26917 : Type'} (x' : _26917) (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term491 _26916 _26917 x h _18906 P t) : term478 _26916 _26917 P x' t.
Proof. exact (EQ_MP (@lem1145344 _26916 _26917 P x' t) (@lem1145341 _26916 _26917 x' x h _18906 P t h1)). Qed.
Lemma lem1145348 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1145350 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x' : _26917) (t : list _26916) : (term479 _26916 _26917 P x' t) = (term509 _26916 _26917 P x' t).
Proof. exact (@lem1145348 (term478 _26916 _26917 P x' t)). Qed.
Lemma lem1145353 {_26916 _26917 : Type'} (x' : _26917) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term495 _26916 _26917 x' _18906 P t) : term509 _26916 _26917 P x' t.
Proof. exact (EQ_MP (@lem1145350 _26916 _26917 P x' t) (@lem1145161 _26916 _26917 x' _18906 P t h1)). Qed.
Lemma lem1145356 {_26916 _26917 : Type'} (x' : _26917) (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term495 _26916 _26917 x' _18906 P t) (h2 : term491 _26916 _26917 x h _18906 P t) : False.
Proof. exact (@lem1145353 _26916 _26917 x' _18906 P t h1 (@lem1145345 _26916 _26917 x' x h _18906 P t h2)). Qed.
Lemma lem1145357 {_26916 _26917 : Type'} (x' : _26917) (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term495 _26916 _26917 x' _18906 P t) (h2 : term491 _26916 _26917 x h _18906 P t) : term505.
Proof. exact (fun h0 : ~ False => @lem1145356 _26916 _26917 x' x h _18906 P t h1 h2). Qed.
Lemma lem1145359 (p : Prop) : (term503 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1145360 : term505 = False.
Proof. exact (@lem1145359 False). Qed.
Lemma lem1145361 {_26916 _26917 : Type'} (x' : _26917) (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term495 _26916 _26917 x' _18906 P t) (h2 : term491 _26916 _26917 x h _18906 P t) : False.
Proof. exact (EQ_MP (@lem1145360) (@lem1145357 _26916 _26917 x' x h _18906 P t h1 h2)). Qed.
Lemma lem1145363 {_26916 _26917 : Type'} (_18956 : _26917) (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term484 _26916 _26917 x h _18906 P t) : term468 _26916 _26917 P _18956 h.
Proof. exact (EQ_MP (@lem1145018 _26916 _26917 P _18956 h) (@lem1145017 _26916 _26917 _18956 x h _18906 P t h1)). Qed.
Lemma lem1145364 {_26916 _26917 : Type'} (_18956 : _26917) (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term484 _26916 _26917 x h _18906 P t) : term468 _26916 _26917 P _18956 h.
Proof. exact (@lem1145363 _26916 _26917 _18956 x h _18906 P t h1). Qed.
Lemma lem1145365 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term484 _26916 _26917 x h _18906 P t) : term468 _26916 _26917 P x h.
Proof. exact (@lem1145364 _26916 _26917 x x h _18906 P t h1). Qed.
Lemma lem1145366 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term484 _26916 _26917 x h _18906 P t) : term502 _26916 _26917 P x h.
Proof. exact (fun h0 : term480 _26916 _26917 P x h => @lem1145365 _26916 _26917 x h _18906 P t h1). Qed.
Lemma lem1145368 (p : Prop) : (term503 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1145369 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (term502 _26916 _26917 P x h) = (term468 _26916 _26917 P x h).
Proof. exact (@lem1145368 (term468 _26916 _26917 P x h)). Qed.
Lemma lem1145370 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term484 _26916 _26917 x h _18906 P t) : term468 _26916 _26917 P x h.
Proof. exact (EQ_MP (@lem1145369 _26916 _26917 P x h) (@lem1145366 _26916 _26917 x h _18906 P t h1)). Qed.
Lemma lem1145373 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1145375 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) : (term480 _26916 _26917 P x h) = (term504 _26916 _26917 P x h).
Proof. exact (@lem1145373 (term468 _26916 _26917 P x h)). Qed.
Lemma lem1145378 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (x : _26917) (h : _26916) (h1 : term480 _26916 _26917 P x h) : term504 _26916 _26917 P x h.
Proof. exact (EQ_MP (@lem1145375 _26916 _26917 P x h) (@lem1145191 _26916 _26917 P x h h1)). Qed.
Lemma lem1145381 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term480 _26916 _26917 P x h) (h2 : term484 _26916 _26917 x h _18906 P t) : False.
Proof. exact (@lem1145378 _26916 _26917 P x h h1 (@lem1145370 _26916 _26917 x h _18906 P t h2)). Qed.
Lemma lem1145382 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term480 _26916 _26917 P x h) (h2 : term484 _26916 _26917 x h _18906 P t) : term505.
Proof. exact (fun h0 : ~ False => @lem1145381 _26916 _26917 x h _18906 P t h1 h2). Qed.
Lemma lem1145384 (p : Prop) : (term503 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1145385 : term505 = False.
Proof. exact (@lem1145384 False). Qed.
Lemma lem1145386 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term480 _26916 _26917 P x h) (h2 : term484 _26916 _26917 x h _18906 P t) : False.
Proof. exact (EQ_MP (@lem1145385) (@lem1145382 _26916 _26917 x h _18906 P t h1 h2)). Qed.
Lemma lem1145388 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term484 _26916 _26917 x h _18906 P t) : term467 _26916 _26917 _18906 P t.
Proof. exact (proj2 (@lem1144176 _26916 _26917 x h _18906 P t h1)). Qed.
Lemma lem1145389 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term484 _26916 _26917 x h _18906 P t) : term506 _26916 _26917 _18906 P t.
Proof. exact (fun h0 : term485 _26916 _26917 _18906 P t => @lem1145388 _26916 _26917 x h _18906 P t h1). Qed.
Lemma lem1145391 (p : Prop) : (term503 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1145392 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term506 _26916 _26917 _18906 P t) = (term467 _26916 _26917 _18906 P t).
Proof. exact (@lem1145391 (term467 _26916 _26917 _18906 P t)). Qed.
Lemma lem1145393 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term484 _26916 _26917 x h _18906 P t) : term467 _26916 _26917 _18906 P t.
Proof. exact (EQ_MP (@lem1145392 _26916 _26917 _18906 P t) (@lem1145389 _26916 _26917 x h _18906 P t h1)). Qed.
Lemma lem1145396 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1145398 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) : (term485 _26916 _26917 _18906 P t) = (term507 _26916 _26917 _18906 P t).
Proof. exact (@lem1145396 (term467 _26916 _26917 _18906 P t)). Qed.
Lemma lem1145401 {_26916 _26917 : Type'} (x' : _26917) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term495 _26916 _26917 x' _18906 P t) : term507 _26916 _26917 _18906 P t.
Proof. exact (EQ_MP (@lem1145398 _26916 _26917 _18906 P t) (@lem1145207 _26916 _26917 x' _18906 P t h1)). Qed.
Lemma lem1145404 {_26916 _26917 : Type'} (x' : _26917) (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term495 _26916 _26917 x' _18906 P t) (h2 : term484 _26916 _26917 x h _18906 P t) : False.
Proof. exact (@lem1145401 _26916 _26917 x' _18906 P t h1 (@lem1145393 _26916 _26917 x h _18906 P t h2)). Qed.
Lemma lem1145405 {_26916 _26917 : Type'} (x' : _26917) (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term495 _26916 _26917 x' _18906 P t) (h2 : term484 _26916 _26917 x h _18906 P t) : term505.
Proof. exact (fun h0 : ~ False => @lem1145404 _26916 _26917 x' x h _18906 P t h1 h2). Qed.
Lemma lem1145407 (p : Prop) : (term503 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1145408 : term505 = False.
Proof. exact (@lem1145407 False). Qed.
Lemma lem1145409 {_26916 _26917 : Type'} (x' : _26917) (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term495 _26916 _26917 x' _18906 P t) (h2 : term484 _26916 _26917 x h _18906 P t) : False.
Proof. exact (EQ_MP (@lem1145408) (@lem1145405 _26916 _26917 x' x h _18906 P t h1 h2)). Qed.
Lemma lem1145410 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term480 _26916 _26917 P x h) (h2 : term484 _26916 _26917 x h _18906 P t) : (term480 _26916 _26917 P x h) = False.
Proof. exact (prop_ext (fun h3 : term480 _26916 _26917 P x h => @lem1145386 _26916 _26917 x h _18906 P t h1 h2) (fun h3 : False => @lem1145191 _26916 _26917 P x h h1)). Qed.
Lemma lem1145411 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term480 _26916 _26917 P x h) (h2 : term484 _26916 _26917 x h _18906 P t) : False.
Proof. exact (EQ_MP (@lem1145410 _26916 _26917 x h _18906 P t h1 h2) (@lem1145191 _26916 _26917 P x h h1)). Qed.
Lemma lem1145412 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term480 _26916 _26917 P x h) (h2 : term491 _26916 _26917 x h _18906 P t) : (term480 _26916 _26917 P x h) = False.
Proof. exact (prop_ext (fun h3 : term480 _26916 _26917 P x h => @lem1145336 _26916 _26917 x h _18906 P t h1 h2) (fun h3 : False => @lem1145147 _26916 _26917 P x h h1)). Qed.
Lemma lem1145413 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term480 _26916 _26917 P x h) (h2 : term491 _26916 _26917 x h _18906 P t) : False.
Proof. exact (EQ_MP (@lem1145412 _26916 _26917 x h _18906 P t h1 h2) (@lem1145147 _26916 _26917 P x h h1)). Qed.
Lemma lem1145414 {_26916 _26917 : Type'} (x : _26917) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term479 _26916 _26917 P x t) (h2 : term497 _26916 _26917 _18906 P t) : (term479 _26916 _26917 P x t) = False.
Proof. exact (prop_ext (fun h3 : term479 _26916 _26917 P x t => @lem1145311 _26916 _26917 x _18906 P t h1 h2) (fun h3 : False => @lem1145125 _26916 _26917 P x t h1)). Qed.
Lemma lem1145415 {_26916 _26917 : Type'} (x : _26917) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term479 _26916 _26917 P x t) (h2 : term497 _26916 _26917 _18906 P t) : False.
Proof. exact (EQ_MP (@lem1145414 _26916 _26917 x _18906 P t h1 h2) (@lem1145125 _26916 _26917 P x t h1)). Qed.
Lemma lem1145416 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term480 _26916 _26917 P x h) (h2 : term484 _26916 _26917 x h _18906 P t) : (term480 _26916 _26917 P x h) = False.
Proof. exact (prop_ext (fun h3 : term480 _26916 _26917 P x h => @lem1145286 _26916 _26917 x h _18906 P t h1 h2) (fun h3 : False => @lem1145103 _26916 _26917 P x h h1)). Qed.
Lemma lem1145417 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term480 _26916 _26917 P x h) (h2 : term484 _26916 _26917 x h _18906 P t) : False.
Proof. exact (EQ_MP (@lem1145416 _26916 _26917 x h _18906 P t h1 h2) (@lem1145103 _26916 _26917 P x h h1)). Qed.
Lemma lem1145418 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term485 _26916 _26917 _18906 P t) (h2 : term497 _26916 _26917 _18906 P t) : (term485 _26916 _26917 _18906 P t) = False.
Proof. exact (prop_ext (fun h3 : term485 _26916 _26917 _18906 P t => @lem1145261 _26916 _26917 _18906 P t h1 h2) (fun h3 : False => @lem1145081 _26916 _26917 _18906 P t h1)). Qed.
Lemma lem1145419 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term485 _26916 _26917 _18906 P t) (h2 : term497 _26916 _26917 _18906 P t) : False.
Proof. exact (EQ_MP (@lem1145418 _26916 _26917 _18906 P t h1 h2) (@lem1145081 _26916 _26917 _18906 P t h1)). Qed.
Lemma lem1145420 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term480 _26916 _26917 P x h) (h2 : term491 _26916 _26917 x h _18906 P t) : (term480 _26916 _26917 P x h) = False.
Proof. exact (prop_ext (fun h3 : term480 _26916 _26917 P x h => @lem1145238 _26916 _26917 x h _18906 P t h1 h2) (fun h3 : False => @lem1145059 _26916 _26917 P x h h1)). Qed.
Lemma lem1145421 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term480 _26916 _26917 P x h) (h2 : term491 _26916 _26917 x h _18906 P t) : False.
Proof. exact (EQ_MP (@lem1145420 _26916 _26917 x h _18906 P t h1 h2) (@lem1145059 _26916 _26917 P x h h1)). Qed.
Lemma lem1145422 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term480 _26916 _26917 P x h) (h2 : term484 _26916 _26917 x h _18906 P t) : (term480 _26916 _26917 P x h) = False.
Proof. exact (prop_ext (fun h3 : term480 _26916 _26917 P x h => @lem1145411 _26916 _26917 x h _18906 P t h1 h2) (fun h3 : False => @lem1144786 _26916 _26917 P x h h1)). Qed.
Lemma lem1145423 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term480 _26916 _26917 P x h) (h2 : term484 _26916 _26917 x h _18906 P t) : False.
Proof. exact (EQ_MP (@lem1145422 _26916 _26917 x h _18906 P t h1 h2) (@lem1144786 _26916 _26917 P x h h1)). Qed.
Lemma lem1145424 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term480 _26916 _26917 P x h) (h2 : term491 _26916 _26917 x h _18906 P t) : (term480 _26916 _26917 P x h) = False.
Proof. exact (prop_ext (fun h3 : term480 _26916 _26917 P x h => @lem1145413 _26916 _26917 x h _18906 P t h1 h2) (fun h3 : False => @lem1144617 _26916 _26917 P x h h1)). Qed.
Lemma lem1145425 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term480 _26916 _26917 P x h) (h2 : term491 _26916 _26917 x h _18906 P t) : False.
Proof. exact (EQ_MP (@lem1145424 _26916 _26917 x h _18906 P t h1 h2) (@lem1144617 _26916 _26917 P x h h1)). Qed.
Lemma lem1145426 {_26916 _26917 : Type'} (x : _26917) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term479 _26916 _26917 P x t) (h2 : term497 _26916 _26917 _18906 P t) : (term479 _26916 _26917 P x t) = False.
Proof. exact (prop_ext (fun h3 : term479 _26916 _26917 P x t => @lem1145415 _26916 _26917 x _18906 P t h1 h2) (fun h3 : False => @lem1144531 _26916 _26917 P x t h1)). Qed.
Lemma lem1145427 {_26916 _26917 : Type'} (x : _26917) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term479 _26916 _26917 P x t) (h2 : term497 _26916 _26917 _18906 P t) : False.
Proof. exact (EQ_MP (@lem1145426 _26916 _26917 x _18906 P t h1 h2) (@lem1144531 _26916 _26917 P x t h1)). Qed.
Lemma lem1145428 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term480 _26916 _26917 P x h) (h2 : term484 _26916 _26917 x h _18906 P t) : (term480 _26916 _26917 P x h) = False.
Proof. exact (prop_ext (fun h3 : term480 _26916 _26917 P x h => @lem1145417 _26916 _26917 x h _18906 P t h1 h2) (fun h3 : False => @lem1144445 _26916 _26917 P x h h1)). Qed.
Lemma lem1145429 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term480 _26916 _26917 P x h) (h2 : term484 _26916 _26917 x h _18906 P t) : False.
Proof. exact (EQ_MP (@lem1145428 _26916 _26917 x h _18906 P t h1 h2) (@lem1144445 _26916 _26917 P x h h1)). Qed.
Lemma lem1145430 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term485 _26916 _26917 _18906 P t) (h2 : term497 _26916 _26917 _18906 P t) : (term485 _26916 _26917 _18906 P t) = False.
Proof. exact (prop_ext (fun h3 : term485 _26916 _26917 _18906 P t => @lem1145419 _26916 _26917 _18906 P t h1 h2) (fun h3 : False => @lem1144359 _26916 _26917 _18906 P t h1)). Qed.
Lemma lem1145431 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term485 _26916 _26917 _18906 P t) (h2 : term497 _26916 _26917 _18906 P t) : False.
Proof. exact (EQ_MP (@lem1145430 _26916 _26917 _18906 P t h1 h2) (@lem1144359 _26916 _26917 _18906 P t h1)). Qed.
Lemma lem1145432 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term480 _26916 _26917 P x h) (h2 : term491 _26916 _26917 x h _18906 P t) : (term480 _26916 _26917 P x h) = False.
Proof. exact (prop_ext (fun h3 : term480 _26916 _26917 P x h => @lem1145421 _26916 _26917 x h _18906 P t h1 h2) (fun h3 : False => @lem1144270 _26916 _26917 P x h h1)). Qed.
Lemma lem1145433 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term480 _26916 _26917 P x h) (h2 : term491 _26916 _26917 x h _18906 P t) : False.
Proof. exact (EQ_MP (@lem1145432 _26916 _26917 x h _18906 P t h1 h2) (@lem1144270 _26916 _26917 P x h h1)). Qed.
Lemma lem1145434 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term480 _26916 _26917 P x h) (h2 : term484 _26916 _26917 x h _18906 P t) : (term480 _26916 _26917 P x h) = False.
Proof. exact (prop_ext (fun h3 : term480 _26916 _26917 P x h => @lem1145423 _26916 _26917 x h _18906 P t h1 h2) (fun h3 : False => @lem1144786 _26916 _26917 P x h h1)). Qed.
Lemma lem1145435 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term480 _26916 _26917 P x h) (h2 : term484 _26916 _26917 x h _18906 P t) : False.
Proof. exact (EQ_MP (@lem1145434 _26916 _26917 x h _18906 P t h1 h2) (@lem1144786 _26916 _26917 P x h h1)). Qed.
Lemma lem1145436 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term480 _26916 _26917 P x h) (h2 : term491 _26916 _26917 x h _18906 P t) : (term480 _26916 _26917 P x h) = False.
Proof. exact (prop_ext (fun h3 : term480 _26916 _26917 P x h => @lem1145425 _26916 _26917 x h _18906 P t h1 h2) (fun h3 : False => @lem1144617 _26916 _26917 P x h h1)). Qed.
Lemma lem1145437 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term480 _26916 _26917 P x h) (h2 : term491 _26916 _26917 x h _18906 P t) : False.
Proof. exact (EQ_MP (@lem1145436 _26916 _26917 x h _18906 P t h1 h2) (@lem1144617 _26916 _26917 P x h h1)). Qed.
Lemma lem1145438 {_26916 _26917 : Type'} (x : _26917) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term479 _26916 _26917 P x t) (h2 : term497 _26916 _26917 _18906 P t) : (term479 _26916 _26917 P x t) = False.
Proof. exact (prop_ext (fun h3 : term479 _26916 _26917 P x t => @lem1145427 _26916 _26917 x _18906 P t h1 h2) (fun h3 : False => @lem1144531 _26916 _26917 P x t h1)). Qed.
Lemma lem1145439 {_26916 _26917 : Type'} (x : _26917) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term479 _26916 _26917 P x t) (h2 : term497 _26916 _26917 _18906 P t) : False.
Proof. exact (EQ_MP (@lem1145438 _26916 _26917 x _18906 P t h1 h2) (@lem1144531 _26916 _26917 P x t h1)). Qed.
Lemma lem1145440 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term480 _26916 _26917 P x h) (h2 : term484 _26916 _26917 x h _18906 P t) : (term480 _26916 _26917 P x h) = False.
Proof. exact (prop_ext (fun h3 : term480 _26916 _26917 P x h => @lem1145429 _26916 _26917 x h _18906 P t h1 h2) (fun h3 : False => @lem1144445 _26916 _26917 P x h h1)). Qed.
Lemma lem1145441 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term480 _26916 _26917 P x h) (h2 : term484 _26916 _26917 x h _18906 P t) : False.
Proof. exact (EQ_MP (@lem1145440 _26916 _26917 x h _18906 P t h1 h2) (@lem1144445 _26916 _26917 P x h h1)). Qed.
Lemma lem1145442 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term485 _26916 _26917 _18906 P t) (h2 : term497 _26916 _26917 _18906 P t) : (term485 _26916 _26917 _18906 P t) = False.
Proof. exact (prop_ext (fun h3 : term485 _26916 _26917 _18906 P t => @lem1145431 _26916 _26917 _18906 P t h1 h2) (fun h3 : False => @lem1144359 _26916 _26917 _18906 P t h1)). Qed.
Lemma lem1145443 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term485 _26916 _26917 _18906 P t) (h2 : term497 _26916 _26917 _18906 P t) : False.
Proof. exact (EQ_MP (@lem1145442 _26916 _26917 _18906 P t h1 h2) (@lem1144359 _26916 _26917 _18906 P t h1)). Qed.
Lemma lem1145444 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term480 _26916 _26917 P x h) (h2 : term491 _26916 _26917 x h _18906 P t) : (term480 _26916 _26917 P x h) = False.
Proof. exact (prop_ext (fun h3 : term480 _26916 _26917 P x h => @lem1145433 _26916 _26917 x h _18906 P t h1 h2) (fun h3 : False => @lem1144270 _26916 _26917 P x h h1)). Qed.
Lemma lem1145445 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term480 _26916 _26917 P x h) (h2 : term491 _26916 _26917 x h _18906 P t) : False.
Proof. exact (EQ_MP (@lem1145444 _26916 _26917 x h _18906 P t h1 h2) (@lem1144270 _26916 _26917 P x h h1)). Qed.
Lemma lem1145446 {_26916 _26917 : Type'} (x' : _26917) (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term495 _26916 _26917 x' _18906 P t) (h2 : term484 _26916 _26917 x h _18906 P t) : False.
Proof. exact (or_elim (@lem1144177 _26916 _26917 x h _18906 P t h2) (fun h0 : term480 _26916 _26917 P x h => @lem1145435 _26916 _26917 x h _18906 P t h0 h2) (fun h0 : term479 _26916 _26917 P x t => @lem1145409 _26916 _26917 x' x h _18906 P t h1 h2)). Qed.
Lemma lem1145447 {_26916 _26917 : Type'} (x' : _26917) (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term495 _26916 _26917 x' _18906 P t) (h2 : term491 _26916 _26917 x h _18906 P t) : False.
Proof. exact (or_elim (@lem1144170 _26916 _26917 x h _18906 P t h2) (fun h0 : term480 _26916 _26917 P x h => @lem1145437 _26916 _26917 x h _18906 P t h0 h2) (fun h0 : term485 _26916 _26917 _18906 P t => @lem1145361 _26916 _26917 x' x h _18906 P t h1 h2)). Qed.
Lemma lem1145448 {_26916 _26917 : Type'} (x' : _26917) (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term495 _26916 _26917 x' _18906 P t) (h2 : term459 _26916 _26917 x h _18906 P t) : False.
Proof. exact (or_elim (@lem1143919 _26916 _26917 x h _18906 P t h2) (fun h0 : term491 _26916 _26917 x h _18906 P t => @lem1145447 _26916 _26917 x' x h _18906 P t h1 h0) (fun h0 : term484 _26916 _26917 x h _18906 P t => @lem1145446 _26916 _26917 x' x h _18906 P t h1 h0)). Qed.
Lemma lem1145449 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term497 _26916 _26917 _18906 P t) (h2 : term484 _26916 _26917 x h _18906 P t) : False.
Proof. exact (or_elim (@lem1144161 _26916 _26917 x h _18906 P t h2) (fun h0 : term480 _26916 _26917 P x h => @lem1145441 _26916 _26917 x h _18906 P t h0 h2) (fun h0 : term479 _26916 _26917 P x t => @lem1145439 _26916 _26917 x _18906 P t h0 h1)). Qed.
Lemma lem1145450 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term497 _26916 _26917 _18906 P t) (h2 : term491 _26916 _26917 x h _18906 P t) : False.
Proof. exact (or_elim (@lem1144154 _26916 _26917 x h _18906 P t h2) (fun h0 : term480 _26916 _26917 P x h => @lem1145445 _26916 _26917 x h _18906 P t h0 h2) (fun h0 : term485 _26916 _26917 _18906 P t => @lem1145443 _26916 _26917 _18906 P t h0 h1)). Qed.
Lemma lem1145451 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term497 _26916 _26917 _18906 P t) (h2 : term459 _26916 _26917 x h _18906 P t) : False.
Proof. exact (or_elim (@lem1143919 _26916 _26917 x h _18906 P t h2) (fun h0 : term491 _26916 _26917 x h _18906 P t => @lem1145450 _26916 _26917 x h _18906 P t h1 h0) (fun h0 : term484 _26916 _26917 x h _18906 P t => @lem1145449 _26916 _26917 x h _18906 P t h1 h0)). Qed.
Lemma lem1145452 {_26916 _26917 : Type'} (x' : _26917) (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term363 _26916 _26917 x' _18906 P t) (h2 : term459 _26916 _26917 x h _18906 P t) : False.
Proof. exact (or_elim (@lem1144032 _26916 _26917 x' _18906 P t h1) (fun h0 : term497 _26916 _26917 _18906 P t => @lem1145451 _26916 _26917 x h _18906 P t h0 h2) (fun h0 : term495 _26916 _26917 x' _18906 P t => @lem1145448 _26916 _26917 x' x h _18906 P t h0 h2)). Qed.
Lemma lem1145453 {_26916 _26917 : Type'} (x' : _26917) (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term164 _26916 _26917 _18906) (h2 : term363 _26916 _26917 x' _18906 P t) (h3 : term459 _26916 _26917 x h _18906 P t) : False.
Proof. exact (ex_elim (@lem1143390 _26916 _26917 _18906 h1) (fun x'' : type739 _26916 _26917 => fun h0 : term320 _26916 _26917 _18906 x'' => @lem1145452 _26916 _26917 x' x h _18906 P t h2 h3)). Qed.
Lemma lem1145454 {_26916 _26917 : Type'} (x : _26917) (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term164 _26916 _26917 _18906) (h2 : (term9 _26916 _26917 P t) = (term110 _26916 _26917 _18906 P t)) (h3 : term459 _26916 _26917 x h _18906 P t) : False.
Proof. exact (ex_elim (@lem1143477 _26916 _26917 _18906 P t h2) (fun x' : _26917 => fun h0 : term365 _26916 _26917 _18906 P t x' => @lem1145453 _26916 _26917 x' x h _18906 P t h1 h0 h3)). Qed.
Lemma lem1145455 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term164 _26916 _26917 _18906) (h2 : term170 _26916 _26917 h _18906 P t) (h3 : (term9 _26916 _26917 P t) = (term110 _26916 _26917 _18906 P t)) : False.
Proof. exact (ex_elim (@lem1143713 _26916 _26917 h _18906 P t h2) (fun x : _26917 => fun h0 : term461 _26916 _26917 h _18906 P t x => @lem1145454 _26916 _26917 x h _18906 P t h1 h3 h0)). Qed.
Lemma lem1145456 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term164 _26916 _26917 _18906) (h2 : term170 _26916 _26917 h _18906 P t) (h3 : (term9 _26916 _26917 P t) = (term110 _26916 _26917 _18906 P t)) : (term170 _26916 _26917 h _18906 P t) = False.
Proof. exact (prop_ext (fun h4 : term170 _26916 _26917 h _18906 P t => @lem1145455 _26916 _26917 h _18906 P t h1 h2 h3) (fun h4 : False => @lem1142958 _26916 _26917 h _18906 P t h2)). Qed.
Lemma lem1145457 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term164 _26916 _26917 _18906) (h2 : term170 _26916 _26917 h _18906 P t) (h3 : (term9 _26916 _26917 P t) = (term110 _26916 _26917 _18906 P t)) : False.
Proof. exact (EQ_MP (@lem1145456 _26916 _26917 h _18906 P t h1 h2 h3) (@lem1142958 _26916 _26917 h _18906 P t h2)). Qed.
Lemma lem1145458 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term164 _26916 _26917 _18906) (h2 : (term9 _26916 _26917 P t) = (term110 _26916 _26917 _18906 P t)) : term169 _26916 _26917 h _18906 P t.
Proof. exact (fun h0 : term170 _26916 _26917 h _18906 P t => @lem1145457 _26916 _26917 h _18906 P t h1 h0 h2). Qed.
Lemma lem1145459 {_26916 _26917 : Type'} (h : _26916) (_18906 : type740 _26916 _26917) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term164 _26916 _26917 _18906) (h2 : (term9 _26916 _26917 P t) = (term110 _26916 _26917 _18906 P t)) : (term90 _26916 _26917 h P t) = (term111 _26916 _26917 h _18906 P t).
Proof. exact (EQ_MP (@lem1142957 _26916 _26917 h _18906 P t) (@lem1145458 _26916 _26917 h _18906 P t h1 h2)). Qed.
Lemma lem1145460 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) (_18906 : type740 _26916 _26917) (h1 : term164 _26916 _26917 _18906) : term114 _26916 _26917 h _18906 P t.
Proof. exact (fun h0 : (term9 _26916 _26917 P t) = (term110 _26916 _26917 _18906 P t) => @lem1145459 _26916 _26917 h _18906 P t h1 h0). Qed.
Lemma lem1145465 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) (_18906 : type740 _26916 _26917) (h1 : term164 _26916 _26917 _18906) : term116 _26916 _26917 _18906 P t.
Proof. exact (fun h : _26916 => @lem1145460 _26916 _26917 h P t _18906 h1). Qed.
Lemma lem1145470 {_26916 _26917 : Type'} (t : list _26916) (_18906 : type740 _26916 _26917) (h1 : term164 _26916 _26917 _18906) : term118 _26916 _26917 _18906 t.
Proof. exact (fun P : type1470 _26916 _26917 => @lem1145465 _26916 _26917 P t _18906 h1). Qed.
Lemma lem1145475 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) (h1 : term164 _26916 _26917 _18906) : term120 _26916 _26917 _18906.
Proof. exact (fun t : list _26916 => @lem1145470 _26916 _26917 t _18906 h1). Qed.
Lemma lem1145476 {_26916 _26917 : Type'} (_18906 : type740 _26916 _26917) : term166 _26916 _26917 _18906.
Proof. exact (fun h0 : term164 _26916 _26917 _18906 => @lem1145475 _26916 _26917 _18906 h0). Qed.
Lemma lem1145481 {_26916 _26917 : Type'} : term168 _26916 _26917.
Proof. exact (fun _18906 : type740 _26916 _26917 => @lem1145476 _26916 _26917 _18906). Qed.
Lemma lem1145482 {_26916 _26917 : Type'} : term103 _26916 _26917.
Proof. exact (EQ_MP (@lem1142951 _26916 _26917) (@lem1145481 _26916 _26917)). Qed.
Lemma lem1145483 {_26916 _26917 : Type'} (t : list _26916) : term510 _26916 _26917 t.
Proof. exact (@lem1145482 _26916 _26917 t). Qed.
Lemma lem1145484 {_26916 _26917 : Type'} (t : list _26916) : (term510 _26916 _26917 t) = (term99 _26916 _26917 t).
Proof. exact (eq_refl (term510 _26916 _26917 t)). Qed.
Lemma lem1145485 {_26916 _26917 : Type'} (t : list _26916) : term99 _26916 _26917 t.
Proof. exact (EQ_MP (@lem1145484 _26916 _26917 t) (@lem1145483 _26916 _26917 t)). Qed.
Lemma lem1145486 {_26916 _26917 : Type'} (t : list _26916) (P : type1470 _26916 _26917) : term511 _26916 _26917 t P.
Proof. exact (@lem1145485 _26916 _26917 t P). Qed.
Lemma lem1145487 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : (term511 _26916 _26917 t P) = (term95 _26916 _26917 P t).
Proof. exact (eq_refl (term511 _26916 _26917 t P)). Qed.
Lemma lem1145488 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) : term95 _26916 _26917 P t.
Proof. exact (EQ_MP (@lem1145487 _26916 _26917 P t) (@lem1145486 _26916 _26917 t P)). Qed.
Lemma lem1145489 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (t : list _26916) (h : _26916) : term512 _26916 _26917 P t h.
Proof. exact (@lem1145488 _26916 _26917 P t h). Qed.
Lemma lem1145490 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : (term512 _26916 _26917 P t h) = (term65 _26916 _26917 h P t).
Proof. exact (eq_refl (term512 _26916 _26917 P t h)). Qed.
Lemma lem1145491 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : term65 _26916 _26917 h P t.
Proof. exact (EQ_MP (@lem1145490 _26916 _26917 h P t) (@lem1145489 _26916 _26917 P t h)). Qed.
Lemma lem1145493 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) : term65 _26916 _26917 h P t.
Proof. exact (@lem1142536 _26916 _26917 h P t (@lem1145491 _26916 _26917 h P t)). Qed.
Lemma lem1145494 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) (h1 : (term9 _26916 _26917 P t) = (term10 _26916 _26917 P t)) : term63 _26916 _26917 h P t.
Proof. exact (@lem1145493 _26916 _26917 h P t (@lem1142421 _26916 _26917 P t h1)). Qed.
Lemma lem1145495 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term64 _26916 _26917 h P t) (h2 : (term9 _26916 _26917 P t) = (term10 _26916 _26917 P t)) : False.
Proof. exact (@lem1145494 _26916 _26917 h P t h2 (@lem1142520 _26916 _26917 h P t h1)). Qed.
Lemma lem1145496 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term64 _26916 _26917 h P t) (h2 : (term9 _26916 _26917 P t) = (term10 _26916 _26917 P t)) : (term64 _26916 _26917 h P t) = False.
Proof. exact (prop_ext (fun h3 : term64 _26916 _26917 h P t => @lem1145495 _26916 _26917 h P t h1 h2) (fun h3 : False => @lem1142520 _26916 _26917 h P t h1)). Qed.
Lemma lem1145497 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) (h1 : term64 _26916 _26917 h P t) (h2 : (term9 _26916 _26917 P t) = (term10 _26916 _26917 P t)) : False.
Proof. exact (EQ_MP (@lem1145496 _26916 _26917 h P t h1 h2) (@lem1142520 _26916 _26917 h P t h1)). Qed.
Lemma lem1145498 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) (h1 : (term9 _26916 _26917 P t) = (term10 _26916 _26917 P t)) : term63 _26916 _26917 h P t.
Proof. exact (fun h0 : term64 _26916 _26917 h P t => @lem1145497 _26916 _26917 h P t h0 h1). Qed.
Lemma lem1145499 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) (h1 : (term9 _26916 _26917 P t) = (term10 _26916 _26917 P t)) : (term47 _26916 _26917 h P t) = (term61 _26916 _26917 h P t).
Proof. exact (EQ_MP (@lem1142519 _26916 _26917 h P t) (@lem1145498 _26916 _26917 h P t h1)). Qed.
Lemma lem1145500 {_26916 _26917 : Type'} (h : _26916) (P : type1470 _26916 _26917) (t : list _26916) (h1 : (term9 _26916 _26917 P t) = (term10 _26916 _26917 P t)) : (term14 _26916 _26917 P h t) = (term15 _26916 _26917 P h t).
Proof. exact (EQ_MP (@lem1142515 _26916 _26917 P h t) (@lem1145499 _26916 _26917 h P t h1)). Qed.
Lemma lem1145501 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) (t : list _26916) : term17 _26916 _26917 P h t.
Proof. exact (fun h0 : (term9 _26916 _26917 P t) = (term10 _26916 _26917 P t) => @lem1145500 _26916 _26917 h P t h0). Qed.
Lemma lem1145506 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) (h : _26916) : term21 _26916 _26917 P h.
Proof. exact (fun t : list _26916 => @lem1145501 _26916 _26917 P h t). Qed.
Lemma lem1145511 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) : term25 _26916 _26917 P.
Proof. exact (fun h : _26916 => @lem1145506 _26916 _26917 P h). Qed.
Lemma lem1145512 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) : term27 _26916 _26917 P.
Proof. exact (conj (@lem1142454 _26916 _26917 P) (@lem1145511 _26916 _26917 P)). Qed.
Lemma lem1145513 {_26916 _26917 : Type'} (P : type1470 _26916 _26917) : term32 _26916 _26917 P.
Proof. exact (@lem1142420 _26916 _26917 P (@lem1145512 _26916 _26917 P)). Qed.
Lemma lem1145518 {_26916 _26917 : Type'} : term513 _26916 _26917.
Proof. exact (fun P : type1470 _26916 _26917 => @lem1145513 _26916 _26917 P). Qed.
