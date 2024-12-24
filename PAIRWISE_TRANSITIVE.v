Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PAIRWISE_TRANSITIVE_term_abbrevs.
Require Import ALL_IMP_spec.
Require Import BOOL_CASES_AX_spec.
Require Import CONJ_ASSOC_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1100843_spec.
Require Import thm1100844_spec.
Require Import thm1110681_spec.
Require Import thm1110682_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem1235506 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1235507 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1235508 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1235507 t1) (@lem1235506 t1)). Qed.
Lemma lem1235509 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1235508 t1 t2). Qed.
Lemma lem1235510 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1235511 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1235510 t1 t2) (@lem1235509 t1 t2)). Qed.
Lemma lem1235512 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1235511 t1 t2 t3). Qed.
Lemma lem1235513 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1235514 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1235513 t1 t2 t3) (@lem1235512 t1 t2 t3)). Qed.
Lemma lem1235515 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1235514 t1 t2 t3)). Qed.
Lemma lem1235529 (p : Prop) (q : Prop) (r : Prop) : (term7 p q r) = (term8 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem1235530 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (l : list _26340) : (term9 _26340 P Q l) = (term10 _26340 P Q l).
Proof. exact (@lem1235529 (term11 _26340 l P Q) (@List.Forall _26340 P l) (@List.Forall _26340 Q l)). Qed.
Lemma lem1235538 (p : Prop) (q : Prop) (r : Prop) : (term7 p q r) = (term8 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem1235539 {_26340 : Type'} (l : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (x : _26340) : (term12 _26340 l P Q x) = (term13 _26340 l P Q x).
Proof. exact (@lem1235538 (@List.In _26340 x l) (P x) (Q x)). Qed.
Lemma lem1235544 {_26340 : Type'} (l : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term14 _26340 l P Q) = (term15 _26340 l P Q).
Proof. exact (fun_ext (fun x : _26340 => @lem1235539 _26340 l P Q x)). Qed.
Lemma lem1235545 {_26340 : Type'} : (@all _26340) = (@all _26340).
Proof. exact (eq_refl (@all _26340)). Qed.
Lemma lem1235546 {_26340 : Type'} (l : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term11 _26340 l P Q) = (term16 _26340 l P Q).
Proof. exact (MK_COMB (@lem1235545 _26340) (@lem1235544 _26340 l P Q)). Qed.
Lemma lem1235551 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1235552 {_26340 : Type'} (l : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term17 _26340 l P Q) = (term18 _26340 l P Q).
Proof. exact (MK_COMB (@lem1235551) (@lem1235546 _26340 l P Q)). Qed.
Lemma lem1235555 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (l : list _26340) : (term19 _26340 P Q l) = (term19 _26340 P Q l).
Proof. exact (eq_refl (term19 _26340 P Q l)). Qed.
Lemma lem1235556 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (l : list _26340) : (term10 _26340 P Q l) = (term20 _26340 P Q l).
Proof. exact (MK_COMB (@lem1235552 _26340 l P Q) (@lem1235555 _26340 P Q l)). Qed.
Lemma lem1235559 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (l : list _26340) : (term9 _26340 P Q l) = (term20 _26340 P Q l).
Proof. exact (TRANS (@lem1235530 _26340 P Q l) (@lem1235556 _26340 P Q l)). Qed.
Lemma lem1235560 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term21 _26340 P Q) = (term22 _26340 P Q).
Proof. exact (fun_ext (fun l : list _26340 => @lem1235559 _26340 P Q l)). Qed.
Lemma lem1235561 {_26340 : Type'} : (@all (list _26340)) = (@all (list _26340)).
Proof. exact (eq_refl (@all (list _26340))). Qed.
Lemma lem1235562 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term23 _26340 P Q) = (term24 _26340 P Q).
Proof. exact (MK_COMB (@lem1235561 _26340) (@lem1235560 _26340 P Q)). Qed.
Lemma lem1235567 {_26340 : Type'} (P : _26340 -> Prop) : (term25 _26340 P) = (term26 _26340 P).
Proof. exact (fun_ext (fun Q : _26340 -> Prop => @lem1235562 _26340 P Q)). Qed.
Lemma lem1235568 {_26340 : Type'} : (@all (_26340 -> Prop)) = (@all (_26340 -> Prop)).
Proof. exact (eq_refl (@all (_26340 -> Prop))). Qed.
Lemma lem1235569 {_26340 : Type'} (P : _26340 -> Prop) : (term27 _26340 P) = (term28 _26340 P).
Proof. exact (MK_COMB (@lem1235568 _26340) (@lem1235567 _26340 P)). Qed.
Lemma lem1235574 {_26340 : Type'} : (term29 _26340) = (term30 _26340).
Proof. exact (fun_ext (fun P : _26340 -> Prop => @lem1235569 _26340 P)). Qed.
Lemma lem1235575 {_26340 : Type'} : (@all (_26340 -> Prop)) = (@all (_26340 -> Prop)).
Proof. exact (eq_refl (@all (_26340 -> Prop))). Qed.
Lemma lem1235576 {_26340 : Type'} : (term31 _26340) = (term32 _26340).
Proof. exact (MK_COMB (@lem1235575 _26340) (@lem1235574 _26340)). Qed.
Lemma lem1235581 {_26340 : Type'} : term32 _26340.
Proof. exact (EQ_MP (@lem1235576 _26340) (@lem1123316 _26340)). Qed.
Lemma lem1235582 {_26340 : Type'} (h1 : term32 _26340) : term32 _26340.
Proof. exact (h1). Qed.
Lemma lem1235583 {_26340 : Type'} (P : _26340 -> Prop) (h1 : term32 _26340) : term33 _26340 P.
Proof. exact (@lem1235582 _26340 h1 P). Qed.
Lemma lem1235584 {_26340 : Type'} (P : _26340 -> Prop) : (term33 _26340 P) = (term28 _26340 P).
Proof. exact (eq_refl (term33 _26340 P)). Qed.
Lemma lem1235585 {_26340 : Type'} (P : _26340 -> Prop) (h1 : term32 _26340) : term28 _26340 P.
Proof. exact (EQ_MP (@lem1235584 _26340 P) (@lem1235583 _26340 P h1)). Qed.
Lemma lem1235586 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (h1 : term32 _26340) : term34 _26340 P Q.
Proof. exact (@lem1235585 _26340 P h1 Q). Qed.
Lemma lem1235587 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term34 _26340 P Q) = (term24 _26340 P Q).
Proof. exact (eq_refl (term34 _26340 P Q)). Qed.
Lemma lem1235588 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (h1 : term32 _26340) : term24 _26340 P Q.
Proof. exact (EQ_MP (@lem1235587 _26340 P Q) (@lem1235586 _26340 P Q h1)). Qed.
Lemma lem1235589 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (l : list _26340) (h1 : term32 _26340) : term35 _26340 P Q l.
Proof. exact (@lem1235588 _26340 P Q h1 l). Qed.
Lemma lem1235590 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (l : list _26340) : (term35 _26340 P Q l) = (term20 _26340 P Q l).
Proof. exact (eq_refl (term35 _26340 P Q l)). Qed.
Lemma lem1235591 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (l : list _26340) (h1 : term32 _26340) : term20 _26340 P Q l.
Proof. exact (EQ_MP (@lem1235590 _26340 P Q l) (@lem1235589 _26340 P Q l h1)). Qed.
Lemma lem1235592 {_26340 : Type'} (l : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (h1 : term16 _26340 l P Q) : term16 _26340 l P Q.
Proof. exact (h1). Qed.
Lemma lem1235593 {_26340 : Type'} (l : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (h1 : term16 _26340 l P Q) (h2 : term32 _26340) : term19 _26340 P Q l.
Proof. exact (@lem1235591 _26340 P Q l h2 (@lem1235592 _26340 l P Q h1)). Qed.
Lemma lem1235594 {_26340 : Type'} (l : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (h1 : term16 _26340 l P Q) : term36 _26340 P Q l.
Proof. exact (fun h0 : term32 _26340 => @lem1235593 _26340 l P Q h1 h0). Qed.
Lemma lem1235595 {_26340 : Type'} (h1 : term32 _26340) : term32 _26340.
Proof. exact (h1). Qed.
Lemma lem1235596 {_26340 : Type'} (l : list _26340) (P : _26340 -> Prop) (Q : _26340 -> Prop) (h1 : term16 _26340 l P Q) (h2 : term32 _26340) : term19 _26340 P Q l.
Proof. exact (@lem1235594 _26340 l P Q h1 (@lem1235595 _26340 h2)). Qed.
Lemma lem1235597 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (l : list _26340) (h1 : term32 _26340) : term20 _26340 P Q l.
Proof. exact (fun h0 : term16 _26340 l P Q => @lem1235596 _26340 l P Q h0 h1). Qed.
Lemma lem1235598 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (h1 : term32 _26340) : term24 _26340 P Q.
Proof. exact (fun l : list _26340 => @lem1235597 _26340 P Q l h1). Qed.
Lemma lem1235599 {_26340 : Type'} (P : _26340 -> Prop) (h1 : term32 _26340) : term28 _26340 P.
Proof. exact (fun Q : _26340 -> Prop => @lem1235598 _26340 P Q h1). Qed.
Lemma lem1235600 {_26340 : Type'} (h1 : term32 _26340) : term32 _26340.
Proof. exact (fun P : _26340 -> Prop => @lem1235599 _26340 P h1). Qed.
Lemma lem1235601 {_26340 : Type'} : term37 _26340.
Proof. exact (fun h0 : term32 _26340 => @lem1235600 _26340 h0). Qed.
Lemma lem1235602 {_26340 : Type'} : term32 _26340.
Proof. exact (@lem1235601 _26340 (@lem1235581 _26340)). Qed.
Lemma lem1235603 {_26340 : Type'} (P : _26340 -> Prop) : term33 _26340 P.
Proof. exact (@lem1235602 _26340 P). Qed.
Lemma lem1235604 {_26340 : Type'} (P : _26340 -> Prop) : (term33 _26340 P) = (term28 _26340 P).
Proof. exact (eq_refl (term33 _26340 P)). Qed.
Lemma lem1235605 {_26340 : Type'} (P : _26340 -> Prop) : term28 _26340 P.
Proof. exact (EQ_MP (@lem1235604 _26340 P) (@lem1235603 _26340 P)). Qed.
Lemma lem1235606 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) : term34 _26340 P Q.
Proof. exact (@lem1235605 _26340 P Q). Qed.
Lemma lem1235607 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) : (term34 _26340 P Q) = (term24 _26340 P Q).
Proof. exact (eq_refl (term34 _26340 P Q)). Qed.
Lemma lem1235608 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) : term24 _26340 P Q.
Proof. exact (EQ_MP (@lem1235607 _26340 P Q) (@lem1235606 _26340 P Q)). Qed.
Lemma lem1235609 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (l : list _26340) : term35 _26340 P Q l.
Proof. exact (@lem1235608 _26340 P Q l). Qed.
Lemma lem1235610 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (l : list _26340) : (term35 _26340 P Q l) = (term20 _26340 P Q l).
Proof. exact (eq_refl (term35 _26340 P Q l)). Qed.
Lemma lem1235634 (p : Prop) : term38 p.
Proof. exact (@lem9851 p). Qed.
Lemma lem1235635 (p : Prop) : (term38 p) = (term39 p).
Proof. exact (eq_refl (term38 p)). Qed.
Lemma lem1235636 (p : Prop) : term39 p.
Proof. exact (EQ_MP (@lem1235635 p) (@lem1235634 p)). Qed.
Lemma lem1235637 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem1235638 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem1235661 (s : Prop) (r : Prop) (q : Prop) : (term40 s r q) = (term40 s r q).
Proof. exact (eq_refl (term40 s r q)). Qed.
Lemma lem1235662 (s : Prop) (r : Prop) (q : Prop) (p : Prop) (h1 : p = True) : (term41 s r q p) = (term42 s r q).
Proof. exact (MK_COMB (@lem1235661 s r q) (@lem1235637 p h1)). Qed.
Lemma lem1235663 (s : Prop) (r : Prop) (q : Prop) : (term42 s r q) = (((term43 q r s) = (term44 r s)) = (term45 s r q)).
Proof. exact (eq_refl (term42 s r q)). Qed.
Lemma lem1235664 (s : Prop) (r : Prop) (q : Prop) (p : Prop) : (term46 s r q p) = (term46 s r q p).
Proof. exact (eq_refl (term46 s r q p)). Qed.
Lemma lem1235665 (p : Prop) (s : Prop) (r : Prop) (q : Prop) : ((term41 s r q p) = (term42 s r q)) = ((term41 s r q p) = (((term43 q r s) = (term44 r s)) = (term45 s r q))).
Proof. exact (MK_COMB (@lem1235664 s r q p) (@lem1235663 s r q)). Qed.
Lemma lem1235666 (p : Prop) (s : Prop) (r : Prop) (q : Prop) : (term41 s r q p) = (((term47 p q r s) = (term48 p r s)) = (term49 p s r q)).
Proof. exact (eq_refl (term41 s r q p)). Qed.
Lemma lem1235667 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1235668 (p : Prop) (s : Prop) (r : Prop) (q : Prop) : (term46 s r q p) = (term50 p s r q).
Proof. exact (MK_COMB (@lem1235667) (@lem1235666 p s r q)). Qed.
Lemma lem1235669 (s : Prop) (r : Prop) (q : Prop) : (((term43 q r s) = (term44 r s)) = (term45 s r q)) = (((term43 q r s) = (term44 r s)) = (term45 s r q)).
Proof. exact (eq_refl (((term43 q r s) = (term44 r s)) = (term45 s r q))). Qed.
Lemma lem1235670 (p : Prop) (s : Prop) (r : Prop) (q : Prop) : ((term41 s r q p) = (((term43 q r s) = (term44 r s)) = (term45 s r q))) = ((((term47 p q r s) = (term48 p r s)) = (term49 p s r q)) = (((term43 q r s) = (term44 r s)) = (term45 s r q))).
Proof. exact (MK_COMB (@lem1235668 p s r q) (@lem1235669 s r q)). Qed.
Lemma lem1235671 (p : Prop) (s : Prop) (r : Prop) (q : Prop) : ((term41 s r q p) = (term42 s r q)) = ((((term47 p q r s) = (term48 p r s)) = (term49 p s r q)) = (((term43 q r s) = (term44 r s)) = (term45 s r q))).
Proof. exact (TRANS (@lem1235665 p s r q) (@lem1235670 p s r q)). Qed.
Lemma lem1235672 (s : Prop) (r : Prop) (q : Prop) (p : Prop) (h1 : p = True) : (((term47 p q r s) = (term48 p r s)) = (term49 p s r q)) = (((term43 q r s) = (term44 r s)) = (term45 s r q)).
Proof. exact (EQ_MP (@lem1235671 p s r q) (@lem1235662 s r q p h1)). Qed.
Lemma lem1235673 (s : Prop) (r : Prop) (q : Prop) (p : Prop) (h1 : p = True) : (((term43 q r s) = (term44 r s)) = (term45 s r q)) = (((term47 p q r s) = (term48 p r s)) = (term49 p s r q)).
Proof. exact (SYM (@lem1235672 s r q p h1)). Qed.
Lemma lem1235674 (s : Prop) (r : Prop) (q : Prop) : (term40 s r q) = (term40 s r q).
Proof. exact (eq_refl (term40 s r q)). Qed.
Lemma lem1235675 (s : Prop) (r : Prop) (q : Prop) (p : Prop) (h1 : p = False) : (term41 s r q p) = (term51 s r q).
Proof. exact (MK_COMB (@lem1235674 s r q) (@lem1235638 p h1)). Qed.
Lemma lem1235676 (s : Prop) (r : Prop) (q : Prop) : (term51 s r q) = (((term52 q r s) = (term53 r s)) = (term54 s r q)).
Proof. exact (eq_refl (term51 s r q)). Qed.
Lemma lem1235677 (s : Prop) (r : Prop) (q : Prop) (p : Prop) : (term46 s r q p) = (term46 s r q p).
Proof. exact (eq_refl (term46 s r q p)). Qed.
Lemma lem1235678 (p : Prop) (s : Prop) (r : Prop) (q : Prop) : ((term41 s r q p) = (term51 s r q)) = ((term41 s r q p) = (((term52 q r s) = (term53 r s)) = (term54 s r q))).
Proof. exact (MK_COMB (@lem1235677 s r q p) (@lem1235676 s r q)). Qed.
Lemma lem1235679 (p : Prop) (s : Prop) (r : Prop) (q : Prop) : (term41 s r q p) = (((term47 p q r s) = (term48 p r s)) = (term49 p s r q)).
Proof. exact (eq_refl (term41 s r q p)). Qed.
Lemma lem1235680 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1235681 (p : Prop) (s : Prop) (r : Prop) (q : Prop) : (term46 s r q p) = (term50 p s r q).
Proof. exact (MK_COMB (@lem1235680) (@lem1235679 p s r q)). Qed.
Lemma lem1235682 (s : Prop) (r : Prop) (q : Prop) : (((term52 q r s) = (term53 r s)) = (term54 s r q)) = (((term52 q r s) = (term53 r s)) = (term54 s r q)).
Proof. exact (eq_refl (((term52 q r s) = (term53 r s)) = (term54 s r q))). Qed.
Lemma lem1235683 (p : Prop) (s : Prop) (r : Prop) (q : Prop) : ((term41 s r q p) = (((term52 q r s) = (term53 r s)) = (term54 s r q))) = ((((term47 p q r s) = (term48 p r s)) = (term49 p s r q)) = (((term52 q r s) = (term53 r s)) = (term54 s r q))).
Proof. exact (MK_COMB (@lem1235681 p s r q) (@lem1235682 s r q)). Qed.
Lemma lem1235684 (p : Prop) (s : Prop) (r : Prop) (q : Prop) : ((term41 s r q p) = (term51 s r q)) = ((((term47 p q r s) = (term48 p r s)) = (term49 p s r q)) = (((term52 q r s) = (term53 r s)) = (term54 s r q))).
Proof. exact (TRANS (@lem1235678 p s r q) (@lem1235683 p s r q)). Qed.
Lemma lem1235685 (s : Prop) (r : Prop) (q : Prop) (p : Prop) (h1 : p = False) : (((term47 p q r s) = (term48 p r s)) = (term49 p s r q)) = (((term52 q r s) = (term53 r s)) = (term54 s r q)).
Proof. exact (EQ_MP (@lem1235684 p s r q) (@lem1235675 s r q p h1)). Qed.
Lemma lem1235686 (s : Prop) (r : Prop) (q : Prop) (p : Prop) (h1 : p = False) : (((term52 q r s) = (term53 r s)) = (term54 s r q)) = (((term47 p q r s) = (term48 p r s)) = (term49 p s r q)).
Proof. exact (SYM (@lem1235685 s r q p h1)). Qed.
Lemma lem1235692 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1235693 (q : Prop) (r : Prop) (s : Prop) : (term43 q r s) = (term48 q r s).
Proof. exact (@lem1235692 (term48 q r s)). Qed.
Lemma lem1235698 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1235699 (q : Prop) (r : Prop) (s : Prop) : (term55 q r s) = (term56 q r s).
Proof. exact (MK_COMB (@lem1235698) (@lem1235693 q r s)). Qed.
Lemma lem1235701 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1235702 (r : Prop) (s : Prop) : (term44 r s) = (r /\ s).
Proof. exact (@lem1235701 (r /\ s)). Qed.
Lemma lem1235705 (q : Prop) (r : Prop) (s : Prop) : ((term43 q r s) = (term44 r s)) = ((term48 q r s) = (r /\ s)).
Proof. exact (MK_COMB (@lem1235699 q r s) (@lem1235702 r s)). Qed.
Lemma lem1235708 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1235709 (q : Prop) (r : Prop) (s : Prop) : (term57 q r s) = (term58 q r s).
Proof. exact (MK_COMB (@lem1235708) (@lem1235705 q r s)). Qed.
Lemma lem1235713 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1235714 (s : Prop) : (True /\ s) = s.
Proof. exact (@lem1235713 s). Qed.
Lemma lem1235715 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1235716 (s : Prop) : (term59 s) = (imp s).
Proof. exact (MK_COMB (@lem1235715) (@lem1235714 s)). Qed.
Lemma lem1235719 (r : Prop) (q : Prop) : (r -> q) = (r -> q).
Proof. exact (eq_refl (r -> q)). Qed.
Lemma lem1235720 (s : Prop) (r : Prop) (q : Prop) : (term45 s r q) = (term8 s r q).
Proof. exact (MK_COMB (@lem1235716 s) (@lem1235719 r q)). Qed.
Lemma lem1235723 (s : Prop) (r : Prop) (q : Prop) : (((term43 q r s) = (term44 r s)) = (term45 s r q)) = (((term48 q r s) = (r /\ s)) = (term8 s r q)).
Proof. exact (MK_COMB (@lem1235709 q r s) (@lem1235720 s r q)). Qed.
Lemma lem1235726 (s : Prop) (r : Prop) (q : Prop) : (((term48 q r s) = (r /\ s)) = (term8 s r q)) = (((term43 q r s) = (term44 r s)) = (term45 s r q)).
Proof. exact (SYM (@lem1235723 s r q)). Qed.
Lemma lem1235727 (q : Prop) : term38 q.
Proof. exact (@lem9851 q). Qed.
Lemma lem1235728 (q : Prop) : (term38 q) = (term39 q).
Proof. exact (eq_refl (term38 q)). Qed.
Lemma lem1235729 (q : Prop) : term39 q.
Proof. exact (EQ_MP (@lem1235728 q) (@lem1235727 q)). Qed.
Lemma lem1235730 (q : Prop) (h1 : q = True) : q = True.
Proof. exact (h1). Qed.
Lemma lem1235731 (q : Prop) (h1 : q = False) : q = False.
Proof. exact (h1). Qed.
Lemma lem1235748 (s : Prop) (r : Prop) : (term60 s r) = (term60 s r).
Proof. exact (eq_refl (term60 s r)). Qed.
Lemma lem1235749 (s : Prop) (r : Prop) (q : Prop) (h1 : q = True) : (term61 s r q) = (term62 s r).
Proof. exact (MK_COMB (@lem1235748 s r) (@lem1235730 q h1)). Qed.
Lemma lem1235750 (s : Prop) (r : Prop) : (term62 s r) = (((term44 r s) = (r /\ s)) = (term63 s r)).
Proof. exact (eq_refl (term62 s r)). Qed.
Lemma lem1235751 (s : Prop) (r : Prop) (q : Prop) : (term64 s r q) = (term64 s r q).
Proof. exact (eq_refl (term64 s r q)). Qed.
Lemma lem1235752 (q : Prop) (s : Prop) (r : Prop) : ((term61 s r q) = (term62 s r)) = ((term61 s r q) = (((term44 r s) = (r /\ s)) = (term63 s r))).
Proof. exact (MK_COMB (@lem1235751 s r q) (@lem1235750 s r)). Qed.
Lemma lem1235753 (s : Prop) (r : Prop) (q : Prop) : (term61 s r q) = (((term48 q r s) = (r /\ s)) = (term8 s r q)).
Proof. exact (eq_refl (term61 s r q)). Qed.
Lemma lem1235754 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1235755 (s : Prop) (r : Prop) (q : Prop) : (term64 s r q) = (term65 s r q).
Proof. exact (MK_COMB (@lem1235754) (@lem1235753 s r q)). Qed.
Lemma lem1235756 (s : Prop) (r : Prop) : (((term44 r s) = (r /\ s)) = (term63 s r)) = (((term44 r s) = (r /\ s)) = (term63 s r)).
Proof. exact (eq_refl (((term44 r s) = (r /\ s)) = (term63 s r))). Qed.
Lemma lem1235757 (q : Prop) (s : Prop) (r : Prop) : ((term61 s r q) = (((term44 r s) = (r /\ s)) = (term63 s r))) = ((((term48 q r s) = (r /\ s)) = (term8 s r q)) = (((term44 r s) = (r /\ s)) = (term63 s r))).
Proof. exact (MK_COMB (@lem1235755 s r q) (@lem1235756 s r)). Qed.
Lemma lem1235758 (q : Prop) (s : Prop) (r : Prop) : ((term61 s r q) = (term62 s r)) = ((((term48 q r s) = (r /\ s)) = (term8 s r q)) = (((term44 r s) = (r /\ s)) = (term63 s r))).
Proof. exact (TRANS (@lem1235752 q s r) (@lem1235757 q s r)). Qed.
Lemma lem1235759 (s : Prop) (r : Prop) (q : Prop) (h1 : q = True) : (((term48 q r s) = (r /\ s)) = (term8 s r q)) = (((term44 r s) = (r /\ s)) = (term63 s r)).
Proof. exact (EQ_MP (@lem1235758 q s r) (@lem1235749 s r q h1)). Qed.
Lemma lem1235760 (s : Prop) (r : Prop) (q : Prop) (h1 : q = True) : (((term44 r s) = (r /\ s)) = (term63 s r)) = (((term48 q r s) = (r /\ s)) = (term8 s r q)).
Proof. exact (SYM (@lem1235759 s r q h1)). Qed.
Lemma lem1235761 (s : Prop) (r : Prop) : (term60 s r) = (term60 s r).
Proof. exact (eq_refl (term60 s r)). Qed.
Lemma lem1235762 (s : Prop) (r : Prop) (q : Prop) (h1 : q = False) : (term61 s r q) = (term66 s r).
Proof. exact (MK_COMB (@lem1235761 s r) (@lem1235731 q h1)). Qed.
Lemma lem1235763 (s : Prop) (r : Prop) : (term66 s r) = (((term53 r s) = (r /\ s)) = (term67 s r)).
Proof. exact (eq_refl (term66 s r)). Qed.
Lemma lem1235764 (s : Prop) (r : Prop) (q : Prop) : (term64 s r q) = (term64 s r q).
Proof. exact (eq_refl (term64 s r q)). Qed.
Lemma lem1235765 (q : Prop) (s : Prop) (r : Prop) : ((term61 s r q) = (term66 s r)) = ((term61 s r q) = (((term53 r s) = (r /\ s)) = (term67 s r))).
Proof. exact (MK_COMB (@lem1235764 s r q) (@lem1235763 s r)). Qed.
Lemma lem1235766 (s : Prop) (r : Prop) (q : Prop) : (term61 s r q) = (((term48 q r s) = (r /\ s)) = (term8 s r q)).
Proof. exact (eq_refl (term61 s r q)). Qed.
Lemma lem1235767 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1235768 (s : Prop) (r : Prop) (q : Prop) : (term64 s r q) = (term65 s r q).
Proof. exact (MK_COMB (@lem1235767) (@lem1235766 s r q)). Qed.
Lemma lem1235769 (s : Prop) (r : Prop) : (((term53 r s) = (r /\ s)) = (term67 s r)) = (((term53 r s) = (r /\ s)) = (term67 s r)).
Proof. exact (eq_refl (((term53 r s) = (r /\ s)) = (term67 s r))). Qed.
Lemma lem1235770 (q : Prop) (s : Prop) (r : Prop) : ((term61 s r q) = (((term53 r s) = (r /\ s)) = (term67 s r))) = ((((term48 q r s) = (r /\ s)) = (term8 s r q)) = (((term53 r s) = (r /\ s)) = (term67 s r))).
Proof. exact (MK_COMB (@lem1235768 s r q) (@lem1235769 s r)). Qed.
Lemma lem1235771 (q : Prop) (s : Prop) (r : Prop) : ((term61 s r q) = (term66 s r)) = ((((term48 q r s) = (r /\ s)) = (term8 s r q)) = (((term53 r s) = (r /\ s)) = (term67 s r))).
Proof. exact (TRANS (@lem1235765 q s r) (@lem1235770 q s r)). Qed.
Lemma lem1235772 (s : Prop) (r : Prop) (q : Prop) (h1 : q = False) : (((term48 q r s) = (r /\ s)) = (term8 s r q)) = (((term53 r s) = (r /\ s)) = (term67 s r)).
Proof. exact (EQ_MP (@lem1235771 q s r) (@lem1235762 s r q h1)). Qed.
Lemma lem1235773 (s : Prop) (r : Prop) (q : Prop) (h1 : q = False) : (((term53 r s) = (r /\ s)) = (term67 s r)) = (((term48 q r s) = (r /\ s)) = (term8 s r q)).
Proof. exact (SYM (@lem1235772 s r q h1)). Qed.
Lemma lem1235779 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1235780 (r : Prop) (s : Prop) : (term44 r s) = (r /\ s).
Proof. exact (@lem1235779 (r /\ s)). Qed.
Lemma lem1235783 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1235784 (r : Prop) (s : Prop) : (term68 r s) = (term69 r s).
Proof. exact (MK_COMB (@lem1235783) (@lem1235780 r s)). Qed.
Lemma lem1235787 (r : Prop) (s : Prop) : (r /\ s) = (r /\ s).
Proof. exact (eq_refl (r /\ s)). Qed.
Lemma lem1235788 (r : Prop) (s : Prop) : ((term44 r s) = (r /\ s)) = ((r /\ s) = (r /\ s)).
Proof. exact (MK_COMB (@lem1235784 r s) (@lem1235787 r s)). Qed.
Lemma lem1235790 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1235791 (x : Prop) : (x = x) = True.
Proof. exact (@lem1235790 Prop x). Qed.
Lemma lem1235792 (r : Prop) (s : Prop) : ((r /\ s) = (r /\ s)) = True.
Proof. exact (@lem1235791 (r /\ s)). Qed.
Lemma lem1235793 (r : Prop) (s : Prop) : ((term44 r s) = (r /\ s)) = True.
Proof. exact (TRANS (@lem1235788 r s) (@lem1235792 r s)). Qed.
Lemma lem1235794 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1235795 (r : Prop) (s : Prop) : (term70 r s) = (@eq Prop True).
Proof. exact (MK_COMB (@lem1235794) (@lem1235793 r s)). Qed.
Lemma lem1235799 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1235800 (r : Prop) : (r -> True) = True.
Proof. exact (@lem1235799 r). Qed.
Lemma lem1235801 (s : Prop) : (imp s) = (imp s).
Proof. exact (eq_refl (imp s)). Qed.
Lemma lem1235802 (r : Prop) (s : Prop) : (term63 s r) = (s -> True).
Proof. exact (MK_COMB (@lem1235801 s) (@lem1235800 r)). Qed.
Lemma lem1235804 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1235805 (s : Prop) : (s -> True) = True.
Proof. exact (@lem1235804 s). Qed.
Lemma lem1235806 (s : Prop) (r : Prop) : (term63 s r) = True.
Proof. exact (TRANS (@lem1235802 r s) (@lem1235805 s)). Qed.
Lemma lem1235807 (s : Prop) (r : Prop) : (((term44 r s) = (r /\ s)) = (term63 s r)) = (True = True).
Proof. exact (MK_COMB (@lem1235795 r s) (@lem1235806 s r)). Qed.
Lemma lem1235809 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1235810 : (True = True) = True.
Proof. exact (@lem1235809 True). Qed.
Lemma lem1235811 (s : Prop) (r : Prop) : (((term44 r s) = (r /\ s)) = (term63 s r)) = True.
Proof. exact (TRANS (@lem1235807 s r) (@lem1235810)). Qed.
Lemma lem1235812 (s : Prop) (r : Prop) : True = (((term44 r s) = (r /\ s)) = (term63 s r)).
Proof. exact (SYM (@lem1235811 s r)). Qed.
Lemma lem1235813 (s : Prop) (r : Prop) : ((term44 r s) = (r /\ s)) = (term63 s r).
Proof. exact (EQ_MP (@lem1235812 s r) (@lem0)). Qed.
Lemma lem1235819 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1235820 (r : Prop) (s : Prop) : (term53 r s) = False.
Proof. exact (@lem1235819 (r /\ s)). Qed.
Lemma lem1235821 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1235822 (r : Prop) (s : Prop) : (term71 r s) = (@eq Prop False).
Proof. exact (MK_COMB (@lem1235821) (@lem1235820 r s)). Qed.
Lemma lem1235825 (r : Prop) (s : Prop) : (r /\ s) = (r /\ s).
Proof. exact (eq_refl (r /\ s)). Qed.
Lemma lem1235826 (r : Prop) (s : Prop) : ((term53 r s) = (r /\ s)) = (False = (r /\ s)).
Proof. exact (MK_COMB (@lem1235822 r s) (@lem1235825 r s)). Qed.
Lemma lem1235828 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1235829 (r : Prop) (s : Prop) : (False = (r /\ s)) = (term72 r s).
Proof. exact (@lem1235828 (r /\ s)). Qed.
Lemma lem1235832 (r : Prop) (s : Prop) : ((term53 r s) = (r /\ s)) = (term72 r s).
Proof. exact (TRANS (@lem1235826 r s) (@lem1235829 r s)). Qed.
Lemma lem1235833 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1235834 (r : Prop) (s : Prop) : (term73 r s) = (term74 r s).
Proof. exact (MK_COMB (@lem1235833) (@lem1235832 r s)). Qed.
Lemma lem1235838 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1235839 (r : Prop) : (r -> False) = (~ r).
Proof. exact (@lem1235838 r). Qed.
Lemma lem1235840 (s : Prop) : (imp s) = (imp s).
Proof. exact (eq_refl (imp s)). Qed.
Lemma lem1235841 (s : Prop) (r : Prop) : (term67 s r) = (term75 s r).
Proof. exact (MK_COMB (@lem1235840 s) (@lem1235839 r)). Qed.
Lemma lem1235844 (s : Prop) (r : Prop) : (((term53 r s) = (r /\ s)) = (term67 s r)) = ((term72 r s) = (term75 s r)).
Proof. exact (MK_COMB (@lem1235834 r s) (@lem1235841 s r)). Qed.
Lemma lem1235847 (s : Prop) (r : Prop) : ((term72 r s) = (term75 s r)) = (((term53 r s) = (r /\ s)) = (term67 s r)).
Proof. exact (SYM (@lem1235844 s r)). Qed.
Lemma lem1235848 (r : Prop) : term38 r.
Proof. exact (@lem9851 r). Qed.
Lemma lem1235849 (r : Prop) : (term38 r) = (term39 r).
Proof. exact (eq_refl (term38 r)). Qed.
Lemma lem1235850 (r : Prop) : term39 r.
Proof. exact (EQ_MP (@lem1235849 r) (@lem1235848 r)). Qed.
Lemma lem1235851 (r : Prop) (h1 : r = True) : r = True.
Proof. exact (h1). Qed.
Lemma lem1235852 (r : Prop) (h1 : r = False) : r = False.
Proof. exact (h1). Qed.
Lemma lem1235861 (s : Prop) : (term76 s) = (term76 s).
Proof. exact (eq_refl (term76 s)). Qed.
Lemma lem1235862 (s : Prop) (r : Prop) (h1 : r = True) : (term77 s r) = (term78 s).
Proof. exact (MK_COMB (@lem1235861 s) (@lem1235851 r h1)). Qed.
Lemma lem1235863 (s : Prop) : (term78 s) = ((term79 s) = (term80 s)).
Proof. exact (eq_refl (term78 s)). Qed.
Lemma lem1235864 (s : Prop) (r : Prop) : (term81 s r) = (term81 s r).
Proof. exact (eq_refl (term81 s r)). Qed.
Lemma lem1235865 (r : Prop) (s : Prop) : ((term77 s r) = (term78 s)) = ((term77 s r) = ((term79 s) = (term80 s))).
Proof. exact (MK_COMB (@lem1235864 s r) (@lem1235863 s)). Qed.
Lemma lem1235866 (s : Prop) (r : Prop) : (term77 s r) = ((term72 r s) = (term75 s r)).
Proof. exact (eq_refl (term77 s r)). Qed.
Lemma lem1235867 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1235868 (s : Prop) (r : Prop) : (term81 s r) = (term82 s r).
Proof. exact (MK_COMB (@lem1235867) (@lem1235866 s r)). Qed.
Lemma lem1235869 (s : Prop) : ((term79 s) = (term80 s)) = ((term79 s) = (term80 s)).
Proof. exact (eq_refl ((term79 s) = (term80 s))). Qed.
Lemma lem1235870 (r : Prop) (s : Prop) : ((term77 s r) = ((term79 s) = (term80 s))) = (((term72 r s) = (term75 s r)) = ((term79 s) = (term80 s))).
Proof. exact (MK_COMB (@lem1235868 s r) (@lem1235869 s)). Qed.
Lemma lem1235871 (r : Prop) (s : Prop) : ((term77 s r) = (term78 s)) = (((term72 r s) = (term75 s r)) = ((term79 s) = (term80 s))).
Proof. exact (TRANS (@lem1235865 r s) (@lem1235870 r s)). Qed.
Lemma lem1235872 (s : Prop) (r : Prop) (h1 : r = True) : ((term72 r s) = (term75 s r)) = ((term79 s) = (term80 s)).
Proof. exact (EQ_MP (@lem1235871 r s) (@lem1235862 s r h1)). Qed.
Lemma lem1235873 (s : Prop) (r : Prop) (h1 : r = True) : ((term79 s) = (term80 s)) = ((term72 r s) = (term75 s r)).
Proof. exact (SYM (@lem1235872 s r h1)). Qed.
Lemma lem1235874 (s : Prop) : (term76 s) = (term76 s).
Proof. exact (eq_refl (term76 s)). Qed.
Lemma lem1235875 (s : Prop) (r : Prop) (h1 : r = False) : (term77 s r) = (term83 s).
Proof. exact (MK_COMB (@lem1235874 s) (@lem1235852 r h1)). Qed.
Lemma lem1235876 (s : Prop) : (term83 s) = ((term84 s) = (term85 s)).
Proof. exact (eq_refl (term83 s)). Qed.
Lemma lem1235877 (s : Prop) (r : Prop) : (term81 s r) = (term81 s r).
Proof. exact (eq_refl (term81 s r)). Qed.
Lemma lem1235878 (r : Prop) (s : Prop) : ((term77 s r) = (term83 s)) = ((term77 s r) = ((term84 s) = (term85 s))).
Proof. exact (MK_COMB (@lem1235877 s r) (@lem1235876 s)). Qed.
Lemma lem1235879 (s : Prop) (r : Prop) : (term77 s r) = ((term72 r s) = (term75 s r)).
Proof. exact (eq_refl (term77 s r)). Qed.
Lemma lem1235880 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1235881 (s : Prop) (r : Prop) : (term81 s r) = (term82 s r).
Proof. exact (MK_COMB (@lem1235880) (@lem1235879 s r)). Qed.
Lemma lem1235882 (s : Prop) : ((term84 s) = (term85 s)) = ((term84 s) = (term85 s)).
Proof. exact (eq_refl ((term84 s) = (term85 s))). Qed.
Lemma lem1235883 (r : Prop) (s : Prop) : ((term77 s r) = ((term84 s) = (term85 s))) = (((term72 r s) = (term75 s r)) = ((term84 s) = (term85 s))).
Proof. exact (MK_COMB (@lem1235881 s r) (@lem1235882 s)). Qed.
Lemma lem1235884 (r : Prop) (s : Prop) : ((term77 s r) = (term83 s)) = (((term72 r s) = (term75 s r)) = ((term84 s) = (term85 s))).
Proof. exact (TRANS (@lem1235878 r s) (@lem1235883 r s)). Qed.
Lemma lem1235885 (s : Prop) (r : Prop) (h1 : r = False) : ((term72 r s) = (term75 s r)) = ((term84 s) = (term85 s)).
Proof. exact (EQ_MP (@lem1235884 r s) (@lem1235875 s r h1)). Qed.
Lemma lem1235886 (s : Prop) (r : Prop) (h1 : r = False) : ((term84 s) = (term85 s)) = ((term72 r s) = (term75 s r)).
Proof. exact (SYM (@lem1235885 s r h1)). Qed.
Lemma lem1235890 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1235891 (s : Prop) : (True /\ s) = s.
Proof. exact (@lem1235890 s). Qed.
Lemma lem1235892 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1235893 (s : Prop) : (term79 s) = (~ s).
Proof. exact (MK_COMB (@lem1235892) (@lem1235891 s)). Qed.
Lemma lem1235894 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1235895 (s : Prop) : (term86 s) = (term87 s).
Proof. exact (MK_COMB (@lem1235894) (@lem1235893 s)). Qed.
Lemma lem1235899 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1235900 (s : Prop) : (imp s) = (imp s).
Proof. exact (eq_refl (imp s)). Qed.
Lemma lem1235901 (s : Prop) : (term80 s) = (s -> False).
Proof. exact (MK_COMB (@lem1235900 s) (@lem1235899)). Qed.
Lemma lem1235903 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1235904 (s : Prop) : (s -> False) = (~ s).
Proof. exact (@lem1235903 s). Qed.
Lemma lem1235905 (s : Prop) : (term80 s) = (~ s).
Proof. exact (TRANS (@lem1235901 s) (@lem1235904 s)). Qed.
Lemma lem1235906 (s : Prop) : ((term79 s) = (term80 s)) = ((~ s) = (~ s)).
Proof. exact (MK_COMB (@lem1235895 s) (@lem1235905 s)). Qed.
Lemma lem1235908 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1235909 (x : Prop) : (x = x) = True.
Proof. exact (@lem1235908 Prop x). Qed.
Lemma lem1235910 (s : Prop) : ((~ s) = (~ s)) = True.
Proof. exact (@lem1235909 (~ s)). Qed.
Lemma lem1235911 (s : Prop) : ((term79 s) = (term80 s)) = True.
Proof. exact (TRANS (@lem1235906 s) (@lem1235910 s)). Qed.
Lemma lem1235912 (s : Prop) : True = ((term79 s) = (term80 s)).
Proof. exact (SYM (@lem1235911 s)). Qed.
Lemma lem1235913 (s : Prop) : (term79 s) = (term80 s).
Proof. exact (EQ_MP (@lem1235912 s) (@lem0)). Qed.
Lemma lem1235917 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1235918 (s : Prop) : (False /\ s) = False.
Proof. exact (@lem1235917 s). Qed.
Lemma lem1235919 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1235920 (s : Prop) : (term84 s) = (~ False).
Proof. exact (MK_COMB (@lem1235919) (@lem1235918 s)). Qed.
Lemma lem1235922 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1235923 (s : Prop) : (term84 s) = True.
Proof. exact (TRANS (@lem1235920 s) (@lem1235922)). Qed.
Lemma lem1235924 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1235925 (s : Prop) : (term88 s) = (@eq Prop True).
Proof. exact (MK_COMB (@lem1235924) (@lem1235923 s)). Qed.
Lemma lem1235929 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1235930 (s : Prop) : (imp s) = (imp s).
Proof. exact (eq_refl (imp s)). Qed.
Lemma lem1235931 (s : Prop) : (term85 s) = (s -> True).
Proof. exact (MK_COMB (@lem1235930 s) (@lem1235929)). Qed.
Lemma lem1235933 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1235934 (s : Prop) : (s -> True) = True.
Proof. exact (@lem1235933 s). Qed.
Lemma lem1235935 (s : Prop) : (term85 s) = True.
Proof. exact (TRANS (@lem1235931 s) (@lem1235934 s)). Qed.
Lemma lem1235936 (s : Prop) : ((term84 s) = (term85 s)) = (True = True).
Proof. exact (MK_COMB (@lem1235925 s) (@lem1235935 s)). Qed.
Lemma lem1235938 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1235939 : (True = True) = True.
Proof. exact (@lem1235938 True). Qed.
Lemma lem1235940 (s : Prop) : ((term84 s) = (term85 s)) = True.
Proof. exact (TRANS (@lem1235936 s) (@lem1235939)). Qed.
Lemma lem1235941 (s : Prop) : True = ((term84 s) = (term85 s)).
Proof. exact (SYM (@lem1235940 s)). Qed.
Lemma lem1235942 (s : Prop) : (term84 s) = (term85 s).
Proof. exact (EQ_MP (@lem1235941 s) (@lem0)). Qed.
Lemma lem1235943 (s : Prop) (r : Prop) (h1 : r = False) : (term72 r s) = (term75 s r).
Proof. exact (EQ_MP (@lem1235886 s r h1) (@lem1235942 s)). Qed.
Lemma lem1235944 (s : Prop) (r : Prop) (h1 : r = True) : (term72 r s) = (term75 s r).
Proof. exact (EQ_MP (@lem1235873 s r h1) (@lem1235913 s)). Qed.
Lemma lem1235946 (s : Prop) (r : Prop) : (term72 r s) = (term75 s r).
Proof. exact (or_elim (@lem1235850 r) (fun h0 : r = True => @lem1235944 s r h0) (fun h0 : r = False => @lem1235943 s r h0)). Qed.
Lemma lem1235947 (s : Prop) (r : Prop) : ((term53 r s) = (r /\ s)) = (term67 s r).
Proof. exact (EQ_MP (@lem1235847 s r) (@lem1235946 s r)). Qed.
Lemma lem1235948 (s : Prop) (r : Prop) (q : Prop) (h1 : q = False) : ((term48 q r s) = (r /\ s)) = (term8 s r q).
Proof. exact (EQ_MP (@lem1235773 s r q h1) (@lem1235947 s r)). Qed.
Lemma lem1235949 (s : Prop) (r : Prop) (q : Prop) (h1 : q = True) : ((term48 q r s) = (r /\ s)) = (term8 s r q).
Proof. exact (EQ_MP (@lem1235760 s r q h1) (@lem1235813 s r)). Qed.
Lemma lem1235951 (s : Prop) (r : Prop) (q : Prop) : ((term48 q r s) = (r /\ s)) = (term8 s r q).
Proof. exact (or_elim (@lem1235729 q) (fun h0 : q = True => @lem1235949 s r q h0) (fun h0 : q = False => @lem1235948 s r q h0)). Qed.
Lemma lem1235952 (s : Prop) (r : Prop) (q : Prop) : ((term43 q r s) = (term44 r s)) = (term45 s r q).
Proof. exact (EQ_MP (@lem1235726 s r q) (@lem1235951 s r q)). Qed.
Lemma lem1235958 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1235959 (q : Prop) (r : Prop) (s : Prop) : (term52 q r s) = False.
Proof. exact (@lem1235958 (term48 q r s)). Qed.
Lemma lem1235960 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1235961 (q : Prop) (r : Prop) (s : Prop) : (term89 q r s) = (@eq Prop False).
Proof. exact (MK_COMB (@lem1235960) (@lem1235959 q r s)). Qed.
Lemma lem1235963 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1235964 (r : Prop) (s : Prop) : (term53 r s) = False.
Proof. exact (@lem1235963 (r /\ s)). Qed.
Lemma lem1235965 (q : Prop) (r : Prop) (s : Prop) : ((term52 q r s) = (term53 r s)) = (False = False).
Proof. exact (MK_COMB (@lem1235961 q r s) (@lem1235964 r s)). Qed.
Lemma lem1235967 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1235968 : (False = False) = (~ False).
Proof. exact (@lem1235967 False). Qed.
Lemma lem1235970 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1235971 : (False = False) = True.
Proof. exact (TRANS (@lem1235968) (@lem1235970)). Qed.
Lemma lem1235972 (q : Prop) (r : Prop) (s : Prop) : ((term52 q r s) = (term53 r s)) = True.
Proof. exact (TRANS (@lem1235965 q r s) (@lem1235971)). Qed.
Lemma lem1235973 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1235974 (q : Prop) (r : Prop) (s : Prop) : (term90 q r s) = (@eq Prop True).
Proof. exact (MK_COMB (@lem1235973) (@lem1235972 q r s)). Qed.
Lemma lem1235978 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1235979 (s : Prop) : (False /\ s) = False.
Proof. exact (@lem1235978 s). Qed.
Lemma lem1235980 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1235981 (s : Prop) : (term91 s) = (imp False).
Proof. exact (MK_COMB (@lem1235980) (@lem1235979 s)). Qed.
Lemma lem1235984 (r : Prop) (q : Prop) : (r -> q) = (r -> q).
Proof. exact (eq_refl (r -> q)). Qed.
Lemma lem1235985 (s : Prop) (r : Prop) (q : Prop) : (term54 s r q) = (term92 r q).
Proof. exact (MK_COMB (@lem1235981 s) (@lem1235984 r q)). Qed.
Lemma lem1235987 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1235988 (r : Prop) (q : Prop) : (term92 r q) = True.
Proof. exact (@lem1235987 (r -> q)). Qed.
Lemma lem1235989 (s : Prop) (r : Prop) (q : Prop) : (term54 s r q) = True.
Proof. exact (TRANS (@lem1235985 s r q) (@lem1235988 r q)). Qed.
Lemma lem1235990 (s : Prop) (r : Prop) (q : Prop) : (((term52 q r s) = (term53 r s)) = (term54 s r q)) = (True = True).
Proof. exact (MK_COMB (@lem1235974 q r s) (@lem1235989 s r q)). Qed.
Lemma lem1235992 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1235993 : (True = True) = True.
Proof. exact (@lem1235992 True). Qed.
Lemma lem1235994 (s : Prop) (r : Prop) (q : Prop) : (((term52 q r s) = (term53 r s)) = (term54 s r q)) = True.
Proof. exact (TRANS (@lem1235990 s r q) (@lem1235993)). Qed.
Lemma lem1235995 (s : Prop) (r : Prop) (q : Prop) : True = (((term52 q r s) = (term53 r s)) = (term54 s r q)).
Proof. exact (SYM (@lem1235994 s r q)). Qed.
Lemma lem1235996 (s : Prop) (r : Prop) (q : Prop) : ((term52 q r s) = (term53 r s)) = (term54 s r q).
Proof. exact (EQ_MP (@lem1235995 s r q) (@lem0)). Qed.
Lemma lem1235997 (s : Prop) (r : Prop) (q : Prop) (p : Prop) (h1 : p = False) : ((term47 p q r s) = (term48 p r s)) = (term49 p s r q).
Proof. exact (EQ_MP (@lem1235686 s r q p h1) (@lem1235996 s r q)). Qed.
Lemma lem1235998 (s : Prop) (r : Prop) (q : Prop) (p : Prop) (h1 : p = True) : ((term47 p q r s) = (term48 p r s)) = (term49 p s r q).
Proof. exact (EQ_MP (@lem1235673 s r q p h1) (@lem1235952 s r q)). Qed.
Lemma lem1236005 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term48 t1 t2 t3) = (term93 t1 t2 t3)) : (term48 t1 t2 t3) = (term93 t1 t2 t3).
Proof. exact (h1). Qed.
Lemma lem1236006 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term48 t1 t2 t3) = (term93 t1 t2 t3)) : (term93 t1 t2 t3) = (term48 t1 t2 t3).
Proof. exact (SYM (@lem1236005 t1 t2 t3 h1)). Qed.
Lemma lem1236007 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term93 t1 t2 t3) = (term48 t1 t2 t3)) : (term93 t1 t2 t3) = (term48 t1 t2 t3).
Proof. exact (h1). Qed.
Lemma lem1236008 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term93 t1 t2 t3) = (term48 t1 t2 t3)) : (term48 t1 t2 t3) = (term93 t1 t2 t3).
Proof. exact (SYM (@lem1236007 t1 t2 t3 h1)). Qed.
Lemma lem1236009 (t1 : Prop) (t2 : Prop) (t3 : Prop) : ((term48 t1 t2 t3) = (term93 t1 t2 t3)) = ((term93 t1 t2 t3) = (term48 t1 t2 t3)).
Proof. exact (prop_ext (fun h1 : (term48 t1 t2 t3) = (term93 t1 t2 t3) => @lem1236006 t1 t2 t3 h1) (fun h1 : (term93 t1 t2 t3) = (term48 t1 t2 t3) => @lem1236008 t1 t2 t3 h1)). Qed.
Lemma lem1236010 (t1 : Prop) (t2 : Prop) : (term94 t1 t2) = (term95 t1 t2).
Proof. exact (fun_ext (fun t3 : Prop => @lem1236009 t1 t2 t3)). Qed.
Lemma lem1236011 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem1236012 (t1 : Prop) (t2 : Prop) : (term96 t1 t2) = (term97 t1 t2).
Proof. exact (MK_COMB (@lem1236011) (@lem1236010 t1 t2)). Qed.
Lemma lem1236013 (t1 : Prop) : (term98 t1) = (term99 t1).
Proof. exact (fun_ext (fun t2 : Prop => @lem1236012 t1 t2)). Qed.
Lemma lem1236014 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem1236015 (t1 : Prop) : (term100 t1) = (term101 t1).
Proof. exact (MK_COMB (@lem1236014) (@lem1236013 t1)). Qed.
Lemma lem1236016 : term102 = term103.
Proof. exact (fun_ext (fun t1 : Prop => @lem1236015 t1)). Qed.
Lemma lem1236017 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem1236018 : term104 = term105.
Proof. exact (MK_COMB (@lem1236017) (@lem1236016)). Qed.
Lemma lem1236019 : term105.
Proof. exact (EQ_MP (@lem1236018) (@lem512)). Qed.
Lemma lem1236020 (t1 : Prop) : term106 t1.
Proof. exact (@lem1236019 t1). Qed.
Lemma lem1236021 (t1 : Prop) : (term106 t1) = (term101 t1).
Proof. exact (eq_refl (term106 t1)). Qed.
Lemma lem1236022 (t1 : Prop) : term101 t1.
Proof. exact (EQ_MP (@lem1236021 t1) (@lem1236020 t1)). Qed.
Lemma lem1236023 (t1 : Prop) (t2 : Prop) : term107 t1 t2.
Proof. exact (@lem1236022 t1 t2). Qed.
Lemma lem1236024 (t1 : Prop) (t2 : Prop) : (term107 t1 t2) = (term97 t1 t2).
Proof. exact (eq_refl (term107 t1 t2)). Qed.
Lemma lem1236025 (t1 : Prop) (t2 : Prop) : term97 t1 t2.
Proof. exact (EQ_MP (@lem1236024 t1 t2) (@lem1236023 t1 t2)). Qed.
Lemma lem1236026 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term108 t1 t2 t3.
Proof. exact (@lem1236025 t1 t2 t3). Qed.
Lemma lem1236027 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term108 t1 t2 t3) = ((term93 t1 t2 t3) = (term48 t1 t2 t3)).
Proof. exact (eq_refl (term108 t1 t2 t3)). Qed.
Lemma lem1236033 {A : Type'} (R : type1402 A) (h1 : term109 A R) : term109 A R.
Proof. exact (h1). Qed.
Lemma lem1236037 {A : Type'} (h : A) (r : type1402 A) (t : list A) : (term110 A r h t) = (term111 A h r t).
Proof. exact (EQ_MP (@lem1110682 A h r t) (@lem1110681 A h r t)). Qed.
Lemma lem1236038 {A : Type'} (h : A) (r : type1402 A) (t : list A) : (term110 A r h t) = (term111 A h r t).
Proof. exact (@lem1236037 A h r t). Qed.
Lemma lem1236039 {A : Type'} (x : A) (R : type1402 A) (y : A) (l : list A) : (term112 A R x y l) = (term113 A x R y l).
Proof. exact (@lem1236038 A x R (@cons A y l)). Qed.
Lemma lem1236043 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (t : list _25307) : (term114 _25307 P h t) = (term115 _25307 h P t).
Proof. exact (EQ_MP (@lem1100844 _25307 h P t) (@lem1100843 _25307 h P t)). Qed.
Lemma lem1236044 {A : Type'} (h : A) (P : A -> Prop) (t : list A) : (term114 A P h t) = (term115 A h P t).
Proof. exact (@lem1236043 A h P t). Qed.
Lemma lem1236045 {A : Type'} (y : A) (R : type1402 A) (x : A) (l : list A) : (term116 A R x y l) = (term117 A y R x l).
Proof. exact (@lem1236044 A y (R x) l). Qed.
Lemma lem1236048 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1236049 {A : Type'} (y : A) (R : type1402 A) (x : A) (l : list A) : (term118 A R x y l) = (term119 A y R x l).
Proof. exact (MK_COMB (@lem1236048) (@lem1236045 A y R x l)). Qed.
Lemma lem1236051 {A : Type'} (h : A) (r : type1402 A) (t : list A) : (term110 A r h t) = (term111 A h r t).
Proof. exact (EQ_MP (@lem1110682 A h r t) (@lem1110681 A h r t)). Qed.
Lemma lem1236052 {A : Type'} (h : A) (r : type1402 A) (t : list A) : (term110 A r h t) = (term111 A h r t).
Proof. exact (@lem1236051 A h r t). Qed.
Lemma lem1236053 {A : Type'} (y : A) (R : type1402 A) (l : list A) : (term110 A R y l) = (term111 A y R l).
Proof. exact (@lem1236052 A y R l). Qed.
Lemma lem1236056 {A : Type'} (x : A) (y : A) (R : type1402 A) (l : list A) : (term113 A x R y l) = (term120 A x y R l).
Proof. exact (MK_COMB (@lem1236049 A y R x l) (@lem1236053 A y R l)). Qed.
Lemma lem1236058 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term93 t1 t2 t3) = (term48 t1 t2 t3).
Proof. exact (EQ_MP (@lem1236027 t1 t2 t3) (@lem1236026 t1 t2 t3)). Qed.
Lemma lem1236059 {A : Type'} (x : A) (y : A) (R : type1402 A) (l : list A) : (term120 A x y R l) = (term121 A x y R l).
Proof. exact (@lem1236058 (R x y) (term122 A R x l) (term111 A y R l)). Qed.
Lemma lem1236066 {A : Type'} (x : A) (y : A) (R : type1402 A) (l : list A) : (term113 A x R y l) = (term121 A x y R l).
Proof. exact (TRANS (@lem1236056 A x y R l) (@lem1236059 A x y R l)). Qed.
Lemma lem1236067 {A : Type'} (x : A) (y : A) (R : type1402 A) (l : list A) : (term112 A R x y l) = (term121 A x y R l).
Proof. exact (TRANS (@lem1236039 A x R y l) (@lem1236066 A x y R l)). Qed.
Lemma lem1236068 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1236069 {A : Type'} (x : A) (y : A) (R : type1402 A) (l : list A) : (term123 A R x y l) = (term124 A x y R l).
Proof. exact (MK_COMB (@lem1236068) (@lem1236067 A x y R l)). Qed.
Lemma lem1236073 {A : Type'} (h : A) (r : type1402 A) (t : list A) : (term110 A r h t) = (term111 A h r t).
Proof. exact (EQ_MP (@lem1110682 A h r t) (@lem1110681 A h r t)). Qed.
Lemma lem1236074 {A : Type'} (h : A) (r : type1402 A) (t : list A) : (term110 A r h t) = (term111 A h r t).
Proof. exact (@lem1236073 A h r t). Qed.
Lemma lem1236075 {A : Type'} (y : A) (R : type1402 A) (l : list A) : (term110 A R y l) = (term111 A y R l).
Proof. exact (@lem1236074 A y R l). Qed.
Lemma lem1236078 {A : Type'} (R : type1402 A) (x : A) (y : A) : (term125 A R x y) = (term125 A R x y).
Proof. exact (eq_refl (term125 A R x y)). Qed.
Lemma lem1236079 {A : Type'} (x : A) (y : A) (R : type1402 A) (l : list A) : (term126 A x R y l) = (term127 A x y R l).
Proof. exact (MK_COMB (@lem1236078 A R x y) (@lem1236075 A y R l)). Qed.
Lemma lem1236082 {A : Type'} (x : A) (y : A) (R : type1402 A) (l : list A) : ((term112 A R x y l) = (term126 A x R y l)) = ((term121 A x y R l) = (term127 A x y R l)).
Proof. exact (MK_COMB (@lem1236069 A x y R l) (@lem1236079 A x y R l)). Qed.
Lemma lem1236084 (p : Prop) (s : Prop) (r : Prop) (q : Prop) : ((term47 p q r s) = (term48 p r s)) = (term49 p s r q).
Proof. exact (or_elim (@lem1235636 p) (fun h0 : p = True => @lem1235998 s r q p h0) (fun h0 : p = False => @lem1235997 s r q p h0)). Qed.
Lemma lem1236085 {A : Type'} (y : A) (R : type1402 A) (x : A) (l : list A) : ((term121 A x y R l) = (term127 A x y R l)) = (term128 A y R x l).
Proof. exact (@lem1236084 (R x y) (@List.ForallOrdPairs A R l) (term122 A R y l) (term122 A R x l)). Qed.
Lemma lem1236092 {A : Type'} (y : A) (R : type1402 A) (x : A) (l : list A) : ((term112 A R x y l) = (term126 A x R y l)) = (term128 A y R x l).
Proof. exact (TRANS (@lem1236082 A x y R l) (@lem1236085 A y R x l)). Qed.
Lemma lem1236093 {A : Type'} (x : A) (R : type1402 A) (y : A) (l : list A) : (term128 A y R x l) = ((term112 A R x y l) = (term126 A x R y l)).
Proof. exact (SYM (@lem1236092 A y R x l)). Qed.
Lemma lem1236094 {A : Type'} (x : A) (y : A) (R : type1402 A) (l : list A) (h1 : term129 A x y R l) : term129 A x y R l.
Proof. exact (h1). Qed.
Lemma lem1236095 {A : Type'} (R : type1402 A) (l : list A) (h1 : @List.ForallOrdPairs A R l) : @List.ForallOrdPairs A R l.
Proof. exact (h1). Qed.
Lemma lem1236096 {A : Type'} (R : type1402 A) (x : A) (y : A) (h1 : R x y) : R x y.
Proof. exact (h1). Qed.
Lemma lem1236098 {_26340 : Type'} (P : _26340 -> Prop) (Q : _26340 -> Prop) (l : list _26340) : term20 _26340 P Q l.
Proof. exact (EQ_MP (@lem1235610 _26340 P Q l) (@lem1235609 _26340 P Q l)). Qed.
Lemma lem1236099 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (l : list A) : term20 A P Q l.
Proof. exact (@lem1236098 A P Q l). Qed.
Lemma lem1236100 {A : Type'} (y : A) (R : type1402 A) (x : A) (l : list A) : term130 A y R x l.
Proof. exact (@lem1236099 A (R y) (R x) l). Qed.
Lemma lem1236102 (p : Prop) : p = (term131 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1236103 {A : Type'} (l : list A) (y : A) (R : type1402 A) (x : A) : (term132 A l y R x) = (term133 A l y R x).
Proof. exact (@lem1236102 (term132 A l y R x)). Qed.
Lemma lem1236104 {A : Type'} (l : list A) (y : A) (R : type1402 A) (x : A) : (term133 A l y R x) = (term132 A l y R x).
Proof. exact (SYM (@lem1236103 A l y R x)). Qed.
Lemma lem1236105 {A : Type'} (l : list A) (y : A) (R : type1402 A) (x : A) (h1 : term134 A l y R x) : term134 A l y R x.
Proof. exact (h1). Qed.
Lemma lem1236108 {A : Type'} (l : list A) (y : A) (R : type1402 A) (x : A) (h1 : term135 A l y R x) : term135 A l y R x.
Proof. exact (h1). Qed.
Lemma lem1236109 {A : Type'} (l : list A) (y : A) (R : type1402 A) (x : A) : term136 A l y R x.
Proof. exact (fun h0 : term135 A l y R x => @lem1236108 A l y R x h0). Qed.
Lemma lem1236110 {A : Type'} (l : list A) (y : A) (R : type1402 A) (x : A) (h1 : term136 A l y R x) : term136 A l y R x.
Proof. exact (h1). Qed.
Lemma lem1236111 {A : Type'} (l : list A) (y : A) (R : type1402 A) (x : A) (h1 : term135 A l y R x) : term135 A l y R x.
Proof. exact (h1). Qed.
Lemma lem1236112 {A : Type'} (l : list A) (y : A) (R : type1402 A) (x : A) (h1 : term135 A l y R x) (h2 : term136 A l y R x) : term135 A l y R x.
Proof. exact (@lem1236110 A l y R x h2 (@lem1236111 A l y R x h1)). Qed.
Lemma lem1236113 {A : Type'} (l : list A) (y : A) (R : type1402 A) (x : A) (h1 : term135 A l y R x) : term137 A l y R x.
Proof. exact (fun h0 : term136 A l y R x => @lem1236112 A l y R x h1 h0). Qed.
Lemma lem1236114 {A : Type'} (l : list A) (y : A) (R : type1402 A) (x : A) (h1 : term136 A l y R x) : term136 A l y R x.
Proof. exact (h1). Qed.
Lemma lem1236115 {A : Type'} (l : list A) (y : A) (R : type1402 A) (x : A) (h1 : term135 A l y R x) (h2 : term136 A l y R x) : term135 A l y R x.
Proof. exact (@lem1236113 A l y R x h1 (@lem1236114 A l y R x h2)). Qed.
Lemma lem1236116 {A : Type'} (l : list A) (y : A) (R : type1402 A) (x : A) (h1 : term136 A l y R x) : term136 A l y R x.
Proof. exact (fun h0 : term135 A l y R x => @lem1236115 A l y R x h0 h1). Qed.
Lemma lem1236117 {A : Type'} (l : list A) (y : A) (R : type1402 A) (x : A) : term138 A l y R x.
Proof. exact (fun h0 : term136 A l y R x => @lem1236116 A l y R x h0). Qed.
Lemma lem1236120 {A : Type'} (l : list A) (y : A) (R : type1402 A) (x : A) : term136 A l y R x.
Proof. exact (@lem1236117 A l y R x (@lem1236109 A l y R x)). Qed.
Lemma lem1236121 {A : Type'} (l : list A) (y : A) (R : type1402 A) (x : A) : term136 A l y R x.
Proof. exact (@lem1236120 A l y R x). Qed.
Lemma lem1236161 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1236162 {A : Type'} (l : list A) (y : A) (R : type1402 A) (x : A) : (term133 A l y R x) = (term139 A l y R x).
Proof. exact (@lem1236161 (term134 A l y R x)). Qed.
Lemma lem1236164 (t : Prop) : (term140 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1236165 {A : Type'} (l : list A) (y : A) (R : type1402 A) (x : A) : (term139 A l y R x) = (term132 A l y R x).
Proof. exact (@lem1236164 (term132 A l y R x)). Qed.
Lemma lem1236170 {A : Type'} (l : list A) (y : A) (R : type1402 A) (x : A) : (term133 A l y R x) = (term132 A l y R x).
Proof. exact (TRANS (@lem1236162 A l y R x) (@lem1236165 A l y R x)). Qed.
Lemma lem1236175 {A : Type'} (R : type1402 A) (l : list A) : (term141 A R l) = (term141 A R l).
Proof. exact (eq_refl (term141 A R l)). Qed.
Lemma lem1236176 {A : Type'} (l : list A) (y : A) (R : type1402 A) (x : A) : (term142 A l y R x) = (term143 A l y R x).
Proof. exact (MK_COMB (@lem1236175 A R l) (@lem1236170 A l y R x)). Qed.
Lemma lem1236179 {A : Type'} (R : type1402 A) (x : A) (y : A) : (term144 A R x y) = (term144 A R x y).
Proof. exact (eq_refl (term144 A R x y)). Qed.
Lemma lem1236180 {A : Type'} (l : list A) (y : A) (R : type1402 A) (x : A) : (term145 A l y R x) = (term146 A l y R x).
Proof. exact (MK_COMB (@lem1236179 A R x y) (@lem1236176 A l y R x)). Qed.
Lemma lem1236183 {A : Type'} (R : type1402 A) : (term147 A R) = (term147 A R).
Proof. exact (eq_refl (term147 A R)). Qed.
Lemma lem1236184 {A : Type'} (l : list A) (y : A) (R : type1402 A) (x : A) : (term135 A l y R x) = (term148 A l y R x).
Proof. exact (MK_COMB (@lem1236183 A R) (@lem1236180 A l y R x)). Qed.
Lemma lem1236187 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term149 A y R x) = (term150 A y R x).
Proof. exact (fun_ext (fun l : list A => @lem1236184 A l y R x)). Qed.
Lemma lem1236188 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1236189 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term151 A y R x) = (term152 A y R x).
Proof. exact (MK_COMB (@lem1236188 A) (@lem1236187 A y R x)). Qed.
Lemma lem1236194 {A : Type'} (R : type1402 A) (x : A) : (term153 A R x) = (term154 A R x).
Proof. exact (fun_ext (fun y : A => @lem1236189 A y R x)). Qed.
Lemma lem1236195 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1236196 {A : Type'} (R : type1402 A) (x : A) : (term155 A R x) = (term156 A R x).
Proof. exact (MK_COMB (@lem1236195 A) (@lem1236194 A R x)). Qed.
Lemma lem1236201 {A : Type'} (x : A) : (term157 A x) = (term158 A x).
Proof. exact (fun_ext (fun R : type1402 A => @lem1236196 A R x)). Qed.
Lemma lem1236202 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem1236203 {A : Type'} (x : A) : (term159 A x) = (term160 A x).
Proof. exact (MK_COMB (@lem1236202 A) (@lem1236201 A x)). Qed.
Lemma lem1236208 {A : Type'} : (term161 A) = (term162 A).
Proof. exact (fun_ext (fun x : A => @lem1236203 A x)). Qed.
Lemma lem1236209 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1236218 {A : Type'} : (term163 A) = (term164 A).
Proof. exact (MK_COMB (@lem1236209 A) (@lem1236208 A)). Qed.
Lemma lem1236227 {A : Type'} (l : list A) (y : A) (R : type1402 A) (x : A) (x' : A) : (term165 A l y R x x') = (term165 A l y R x x').
Proof. exact (eq_refl (term165 A l y R x x')). Qed.
Lemma lem1236228 {A : Type'} (l : list A) (y : A) (R : type1402 A) (x : A) : (term166 A l y R x) = (term166 A l y R x).
Proof. exact (fun_ext (fun x' : A => @lem1236227 A l y R x x')). Qed.
Lemma lem1236229 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1236230 {A : Type'} (l : list A) (y : A) (R : type1402 A) (x : A) : (term132 A l y R x) = (term132 A l y R x).
Proof. exact (MK_COMB (@lem1236229 A) (@lem1236228 A l y R x)). Qed.
Lemma lem1236233 {A : Type'} (R : type1402 A) (l : list A) : (term141 A R l) = (term141 A R l).
Proof. exact (eq_refl (term141 A R l)). Qed.
Lemma lem1236234 {A : Type'} (l : list A) (y : A) (R : type1402 A) (x : A) : (term143 A l y R x) = (term143 A l y R x).
Proof. exact (MK_COMB (@lem1236233 A R l) (@lem1236230 A l y R x)). Qed.
Lemma lem1236237 {A : Type'} (R : type1402 A) (x : A) (y : A) : (term144 A R x y) = (term144 A R x y).
Proof. exact (eq_refl (term144 A R x y)). Qed.
Lemma lem1236238 {A : Type'} (l : list A) (y : A) (R : type1402 A) (x : A) : (term146 A l y R x) = (term146 A l y R x).
Proof. exact (MK_COMB (@lem1236237 A R x y) (@lem1236234 A l y R x)). Qed.
Lemma lem1236247 {A : Type'} (y : A) (R : type1402 A) (x : A) (z : A) : (term167 A y R x z) = (term167 A y R x z).
Proof. exact (eq_refl (term167 A y R x z)). Qed.
Lemma lem1236248 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term168 A y R x) = (term168 A y R x).
Proof. exact (fun_ext (fun z : A => @lem1236247 A y R x z)). Qed.
Lemma lem1236249 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1236250 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term169 A y R x) = (term169 A y R x).
Proof. exact (MK_COMB (@lem1236249 A) (@lem1236248 A y R x)). Qed.
Lemma lem1236251 {A : Type'} (R : type1402 A) (x : A) : (term170 A R x) = (term170 A R x).
Proof. exact (fun_ext (fun y : A => @lem1236250 A y R x)). Qed.
Lemma lem1236252 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1236253 {A : Type'} (R : type1402 A) (x : A) : (term171 A R x) = (term171 A R x).
Proof. exact (MK_COMB (@lem1236252 A) (@lem1236251 A R x)). Qed.
Lemma lem1236254 {A : Type'} (R : type1402 A) : (term172 A R) = (term172 A R).
Proof. exact (fun_ext (fun x : A => @lem1236253 A R x)). Qed.
Lemma lem1236255 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1236256 {A : Type'} (R : type1402 A) : (term109 A R) = (term109 A R).
Proof. exact (MK_COMB (@lem1236255 A) (@lem1236254 A R)). Qed.
Lemma lem1236257 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1236258 {A : Type'} (R : type1402 A) : (term147 A R) = (term147 A R).
Proof. exact (MK_COMB (@lem1236257) (@lem1236256 A R)). Qed.
Lemma lem1236259 {A : Type'} (l : list A) (y : A) (R : type1402 A) (x : A) : (term148 A l y R x) = (term148 A l y R x).
Proof. exact (MK_COMB (@lem1236258 A R) (@lem1236238 A l y R x)). Qed.
Lemma lem1236260 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term150 A y R x) = (term150 A y R x).
Proof. exact (fun_ext (fun l : list A => @lem1236259 A l y R x)). Qed.
Lemma lem1236261 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1236262 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term152 A y R x) = (term152 A y R x).
Proof. exact (MK_COMB (@lem1236261 A) (@lem1236260 A y R x)). Qed.
Lemma lem1236263 {A : Type'} (R : type1402 A) (x : A) : (term154 A R x) = (term154 A R x).
Proof. exact (fun_ext (fun y : A => @lem1236262 A y R x)). Qed.
Lemma lem1236264 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1236265 {A : Type'} (R : type1402 A) (x : A) : (term156 A R x) = (term156 A R x).
Proof. exact (MK_COMB (@lem1236264 A) (@lem1236263 A R x)). Qed.
Lemma lem1236266 {A : Type'} (x : A) : (term158 A x) = (term158 A x).
Proof. exact (fun_ext (fun R : type1402 A => @lem1236265 A R x)). Qed.
Lemma lem1236267 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem1236268 {A : Type'} (x : A) : (term160 A x) = (term160 A x).
Proof. exact (MK_COMB (@lem1236267 A) (@lem1236266 A x)). Qed.
Lemma lem1236269 {A : Type'} : (term162 A) = (term162 A).
Proof. exact (fun_ext (fun x : A => @lem1236268 A x)). Qed.
Lemma lem1236270 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1236271 {A : Type'} : (term164 A) = (term164 A).
Proof. exact (MK_COMB (@lem1236270 A) (@lem1236269 A)). Qed.
Lemma lem1236336 {A : Type'} : (term163 A) = (term164 A).
Proof. exact (TRANS (@lem1236218 A) (@lem1236271 A)). Qed.
Lemma lem1236337 {A : Type'} : (term164 A) = (term163 A).
Proof. exact (SYM (@lem1236336 A)). Qed.
Lemma lem1236338 {A : Type'} (R : type1402 A) (h1 : term109 A R) : term109 A R.
Proof. exact (h1). Qed.
Lemma lem1236344 (p : Prop) : p = (term131 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1236345 {A : Type'} (R : type1402 A) (x : A) (x' : A) : (R x x') = (term173 A R x x').
Proof. exact (@lem1236344 (R x x')). Qed.
Lemma lem1236346 {A : Type'} (R : type1402 A) (x : A) (x' : A) : (term173 A R x x') = (R x x').
Proof. exact (SYM (@lem1236345 A R x x')). Qed.
Lemma lem1236347 {A : Type'} (R : type1402 A) (x : A) (x' : A) (h1 : term174 A R x x') : term174 A R x x'.
Proof. exact (h1). Qed.
Lemma lem1236354 {A : Type'} (x : A) (R : type1402 A) (y : A) (z : A) : (term175 A x R y z) = (term176 A x R y z).
Proof. exact (@lem17045 (R x y) (R y z)). Qed.
Lemma lem1236355 {A : Type'} (R : type1402 A) (x : A) (z : A) : (R x z) = (R x z).
Proof. exact (eq_refl (R x z)). Qed.
Lemma lem1236356 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1236357 {A : Type'} (x : A) (R : type1402 A) (y : A) (z : A) : (term177 A x R y z) = (term178 A x R y z).
Proof. exact (MK_COMB (@lem1236356) (@lem1236354 A x R y z)). Qed.
Lemma lem1236358 {A : Type'} (y : A) (R : type1402 A) (x : A) (z : A) : (term179 A y R x z) = (term180 A y R x z).
Proof. exact (MK_COMB (@lem1236357 A x R y z) (@lem1236355 A R x z)). Qed.
Lemma lem1236359 {A : Type'} (y : A) (R : type1402 A) (x : A) (z : A) : (term167 A y R x z) = (term179 A y R x z).
Proof. exact (@lem17265 (term181 A x R y z) (R x z)). Qed.
Lemma lem1236360 {A : Type'} (y : A) (R : type1402 A) (x : A) (z : A) : (term167 A y R x z) = (term180 A y R x z).
Proof. exact (TRANS (@lem1236359 A y R x z) (@lem1236358 A y R x z)). Qed.
Lemma lem1236361 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term168 A y R x) = (term182 A y R x).
Proof. exact (fun_ext (fun z : A => @lem1236360 A y R x z)). Qed.
Lemma lem1236362 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1236363 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term169 A y R x) = (term183 A y R x).
Proof. exact (MK_COMB (@lem1236362 A) (@lem1236361 A y R x)). Qed.
Lemma lem1236364 {A : Type'} (R : type1402 A) (x : A) : (term170 A R x) = (term184 A R x).
Proof. exact (fun_ext (fun y : A => @lem1236363 A y R x)). Qed.
Lemma lem1236365 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1236366 {A : Type'} (R : type1402 A) (x : A) : (term171 A R x) = (term185 A R x).
Proof. exact (MK_COMB (@lem1236365 A) (@lem1236364 A R x)). Qed.
Lemma lem1236367 {A : Type'} (R : type1402 A) : (term172 A R) = (term186 A R).
Proof. exact (fun_ext (fun x : A => @lem1236366 A R x)). Qed.
Lemma lem1236368 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1236429 {A : Type'} (R : type1402 A) : (term109 A R) = (term187 A R).
Proof. exact (MK_COMB (@lem1236368 A) (@lem1236367 A R)). Qed.
Lemma lem1236430 {A : Type'} (R : type1402 A) (h1 : term109 A R) : term187 A R.
Proof. exact (EQ_MP (@lem1236429 A R) (@lem1236338 A R h1)). Qed.
Lemma lem1236436 {A : Type'} (R : type1402 A) (x : A) (y : A) (h1 : R x y) : R x y.
Proof. exact (h1). Qed.
Lemma lem1236454 {A : Type'} (R : type1402 A) (y : A) (x' : A) (h1 : R y x') : R y x'.
Proof. exact (h1). Qed.
Lemma lem1236460 {A : Type'} (R : type1402 A) (x : A) (x' : A) (h1 : term174 A R x x') : term174 A R x x'.
Proof. exact (h1). Qed.
Lemma lem1236467 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1236468 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem1236467 A (A -> Prop) f x). Qed.
Lemma lem1236469 {A : Type'} (R : type1402 A) (x : A) : (R x) = (@I (A -> A -> Prop) R x).
Proof. exact (@lem1236468 A R x). Qed.
Lemma lem1236470 {A : Type'} (z : A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1236471 {A : Type'} (R : type1402 A) (x : A) (z : A) : (R x z) = (@I (A -> A -> Prop) R x z).
Proof. exact (MK_COMB (@lem1236469 A R x) (@lem1236470 A z)). Qed.
Lemma lem1236473 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1236474 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem1236473 A Prop f x). Qed.
Lemma lem1236475 {A : Type'} (R : type1402 A) (x : A) (z : A) : (@I (A -> A -> Prop) R x z) = (term188 A R x z).
Proof. exact (@lem1236474 A (@I (A -> A -> Prop) R x) z). Qed.
Lemma lem1236477 {A : Type'} (R : type1402 A) (x : A) (z : A) : (R x z) = (term188 A R x z).
Proof. exact (TRANS (@lem1236471 A R x z) (@lem1236475 A R x z)). Qed.
Lemma lem1236478 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1236485 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1236486 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem1236485 A (A -> Prop) f x). Qed.
Lemma lem1236487 {A : Type'} (R : type1402 A) (y : A) : (R y) = (@I (A -> A -> Prop) R y).
Proof. exact (@lem1236486 A R y). Qed.
Lemma lem1236488 {A : Type'} (z : A) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1236489 {A : Type'} (R : type1402 A) (y : A) (z : A) : (R y z) = (@I (A -> A -> Prop) R y z).
Proof. exact (MK_COMB (@lem1236487 A R y) (@lem1236488 A z)). Qed.
Lemma lem1236491 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1236492 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem1236491 A Prop f x). Qed.
Lemma lem1236493 {A : Type'} (R : type1402 A) (y : A) (z : A) : (@I (A -> A -> Prop) R y z) = (term188 A R y z).
Proof. exact (@lem1236492 A (@I (A -> A -> Prop) R y) z). Qed.
Lemma lem1236495 {A : Type'} (R : type1402 A) (y : A) (z : A) : (R y z) = (term188 A R y z).
Proof. exact (TRANS (@lem1236489 A R y z) (@lem1236493 A R y z)). Qed.
Lemma lem1236496 {A : Type'} (R : type1402 A) (y : A) (z : A) : (term174 A R y z) = (term189 A R y z).
Proof. exact (MK_COMB (@lem1236478) (@lem1236495 A R y z)). Qed.
Lemma lem1236497 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1236504 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1236505 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem1236504 A (A -> Prop) f x). Qed.
Lemma lem1236506 {A : Type'} (R : type1402 A) (x : A) : (R x) = (@I (A -> A -> Prop) R x).
Proof. exact (@lem1236505 A R x). Qed.
Lemma lem1236507 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1236508 {A : Type'} (R : type1402 A) (x : A) (y : A) : (R x y) = (@I (A -> A -> Prop) R x y).
Proof. exact (MK_COMB (@lem1236506 A R x) (@lem1236507 A y)). Qed.
Lemma lem1236510 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1236511 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem1236510 A Prop f x). Qed.
Lemma lem1236512 {A : Type'} (R : type1402 A) (x : A) (y : A) : (@I (A -> A -> Prop) R x y) = (term188 A R x y).
Proof. exact (@lem1236511 A (@I (A -> A -> Prop) R x) y). Qed.
Lemma lem1236514 {A : Type'} (R : type1402 A) (x : A) (y : A) : (R x y) = (term188 A R x y).
Proof. exact (TRANS (@lem1236508 A R x y) (@lem1236512 A R x y)). Qed.
Lemma lem1236515 {A : Type'} (R : type1402 A) (x : A) (y : A) : (term174 A R x y) = (term189 A R x y).
Proof. exact (MK_COMB (@lem1236497) (@lem1236514 A R x y)). Qed.
Lemma lem1236516 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1236517 {A : Type'} (R : type1402 A) (x : A) (y : A) : (term190 A R x y) = (term191 A R x y).
Proof. exact (MK_COMB (@lem1236516) (@lem1236515 A R x y)). Qed.
Lemma lem1236518 {A : Type'} (x : A) (R : type1402 A) (y : A) (z : A) : (term176 A x R y z) = (term192 A x R y z).
Proof. exact (MK_COMB (@lem1236517 A R x y) (@lem1236496 A R y z)). Qed.
Lemma lem1236519 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1236520 {A : Type'} (x : A) (R : type1402 A) (y : A) (z : A) : (term178 A x R y z) = (term193 A x R y z).
Proof. exact (MK_COMB (@lem1236519) (@lem1236518 A x R y z)). Qed.
Lemma lem1236521 {A : Type'} (y : A) (R : type1402 A) (x : A) (z : A) : (term180 A y R x z) = (term194 A y R x z).
Proof. exact (MK_COMB (@lem1236520 A x R y z) (@lem1236477 A R x z)). Qed.
Lemma lem1236522 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term182 A y R x) = (term195 A y R x).
Proof. exact (fun_ext (fun z : A => @lem1236521 A y R x z)). Qed.
Lemma lem1236523 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1236524 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term183 A y R x) = (term196 A y R x).
Proof. exact (MK_COMB (@lem1236523 A) (@lem1236522 A y R x)). Qed.
Lemma lem1236525 {A : Type'} (R : type1402 A) (x : A) : (term184 A R x) = (term197 A R x).
Proof. exact (fun_ext (fun y : A => @lem1236524 A y R x)). Qed.
Lemma lem1236526 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1236527 {A : Type'} (R : type1402 A) (x : A) : (term185 A R x) = (term198 A R x).
Proof. exact (MK_COMB (@lem1236526 A) (@lem1236525 A R x)). Qed.
Lemma lem1236528 {A : Type'} (R : type1402 A) : (term186 A R) = (term199 A R).
Proof. exact (fun_ext (fun x : A => @lem1236527 A R x)). Qed.
Lemma lem1236529 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1236530 {A : Type'} (R : type1402 A) : (term187 A R) = (term200 A R).
Proof. exact (MK_COMB (@lem1236529 A) (@lem1236528 A R)). Qed.
Lemma lem1236531 {A : Type'} (R : type1402 A) (h1 : term109 A R) : term200 A R.
Proof. exact (EQ_MP (@lem1236530 A R) (@lem1236430 A R h1)). Qed.
Lemma lem1236538 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1236539 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem1236538 A (A -> Prop) f x). Qed.
Lemma lem1236540 {A : Type'} (R : type1402 A) (x : A) : (R x) = (@I (A -> A -> Prop) R x).
Proof. exact (@lem1236539 A R x). Qed.
Lemma lem1236541 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1236542 {A : Type'} (R : type1402 A) (x : A) (y : A) : (R x y) = (@I (A -> A -> Prop) R x y).
Proof. exact (MK_COMB (@lem1236540 A R x) (@lem1236541 A y)). Qed.
Lemma lem1236544 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1236545 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem1236544 A Prop f x). Qed.
Lemma lem1236546 {A : Type'} (R : type1402 A) (x : A) (y : A) : (@I (A -> A -> Prop) R x y) = (term188 A R x y).
Proof. exact (@lem1236545 A (@I (A -> A -> Prop) R x) y). Qed.
Lemma lem1236548 {A : Type'} (R : type1402 A) (x : A) (y : A) : (R x y) = (term188 A R x y).
Proof. exact (TRANS (@lem1236542 A R x y) (@lem1236546 A R x y)). Qed.
Lemma lem1236568 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1236569 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem1236568 A (A -> Prop) f x). Qed.
Lemma lem1236570 {A : Type'} (R : type1402 A) (y : A) : (R y) = (@I (A -> A -> Prop) R y).
Proof. exact (@lem1236569 A R y). Qed.
Lemma lem1236571 {A : Type'} (x' : A) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem1236572 {A : Type'} (R : type1402 A) (y : A) (x' : A) : (R y x') = (@I (A -> A -> Prop) R y x').
Proof. exact (MK_COMB (@lem1236570 A R y) (@lem1236571 A x')). Qed.
Lemma lem1236574 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1236575 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem1236574 A Prop f x). Qed.
Lemma lem1236576 {A : Type'} (R : type1402 A) (y : A) (x' : A) : (@I (A -> A -> Prop) R y x') = (term188 A R y x').
Proof. exact (@lem1236575 A (@I (A -> A -> Prop) R y) x'). Qed.
Lemma lem1236578 {A : Type'} (R : type1402 A) (y : A) (x' : A) : (R y x') = (term188 A R y x').
Proof. exact (TRANS (@lem1236572 A R y x') (@lem1236576 A R y x')). Qed.
Lemma lem1236580 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1236587 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1236588 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem1236587 A (A -> Prop) f x). Qed.
Lemma lem1236589 {A : Type'} (R : type1402 A) (x : A) : (R x) = (@I (A -> A -> Prop) R x).
Proof. exact (@lem1236588 A R x). Qed.
Lemma lem1236590 {A : Type'} (x' : A) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem1236591 {A : Type'} (R : type1402 A) (x : A) (x' : A) : (R x x') = (@I (A -> A -> Prop) R x x').
Proof. exact (MK_COMB (@lem1236589 A R x) (@lem1236590 A x')). Qed.
Lemma lem1236593 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1236594 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem1236593 A Prop f x). Qed.
Lemma lem1236595 {A : Type'} (R : type1402 A) (x : A) (x' : A) : (@I (A -> A -> Prop) R x x') = (term188 A R x x').
Proof. exact (@lem1236594 A (@I (A -> A -> Prop) R x) x'). Qed.
Lemma lem1236597 {A : Type'} (R : type1402 A) (x : A) (x' : A) : (R x x') = (term188 A R x x').
Proof. exact (TRANS (@lem1236591 A R x x') (@lem1236595 A R x x')). Qed.
Lemma lem1236598 {A : Type'} (R : type1402 A) (x : A) (x' : A) : (term174 A R x x') = (term189 A R x x').
Proof. exact (MK_COMB (@lem1236580) (@lem1236597 A R x x')). Qed.
Lemma lem1236613 {A : Type'} (y : A) (R : type1402 A) (x : A) (z : A) : (term194 A y R x z) = (term194 A y R x z).
Proof. exact (eq_refl (term194 A y R x z)). Qed.
Lemma lem1236614 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term195 A y R x) = (term195 A y R x).
Proof. exact (fun_ext (fun z : A => @lem1236613 A y R x z)). Qed.
Lemma lem1236615 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1236616 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term196 A y R x) = (term196 A y R x).
Proof. exact (MK_COMB (@lem1236615 A) (@lem1236614 A y R x)). Qed.
Lemma lem1236617 {A : Type'} (R : type1402 A) (x : A) : (term197 A R x) = (term197 A R x).
Proof. exact (fun_ext (fun y : A => @lem1236616 A y R x)). Qed.
Lemma lem1236618 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1236619 {A : Type'} (R : type1402 A) (x : A) : (term198 A R x) = (term198 A R x).
Proof. exact (MK_COMB (@lem1236618 A) (@lem1236617 A R x)). Qed.
Lemma lem1236620 {A : Type'} (R : type1402 A) : (term199 A R) = (term199 A R).
Proof. exact (fun_ext (fun x : A => @lem1236619 A R x)). Qed.
Lemma lem1236621 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1236623 {A : Type'} (R : type1402 A) : (term200 A R) = (term200 A R).
Proof. exact (MK_COMB (@lem1236621 A) (@lem1236620 A R)). Qed.
Lemma lem1236624 {A : Type'} (R : type1402 A) (h1 : term109 A R) : term200 A R.
Proof. exact (EQ_MP (@lem1236623 A R) (@lem1236531 A R h1)). Qed.
Lemma lem1236645 {A : Type'} (_22675 : A) (R : type1402 A) (h1 : term109 A R) : term201 A R _22675.
Proof. exact (@lem1236624 A R h1 _22675). Qed.
Lemma lem1236646 {A : Type'} (R : type1402 A) (_22675 : A) : (term201 A R _22675) = (term198 A R _22675).
Proof. exact (eq_refl (term201 A R _22675)). Qed.
Lemma lem1236647 {A : Type'} (_22675 : A) (R : type1402 A) (h1 : term109 A R) : term198 A R _22675.
Proof. exact (EQ_MP (@lem1236646 A R _22675) (@lem1236645 A _22675 R h1)). Qed.
Lemma lem1236648 {A : Type'} (_22675 : A) (_22676 : A) (R : type1402 A) (h1 : term109 A R) : term202 A R _22675 _22676.
Proof. exact (@lem1236647 A _22675 R h1 _22676). Qed.
Lemma lem1236649 {A : Type'} (_22676 : A) (R : type1402 A) (_22675 : A) : (term202 A R _22675 _22676) = (term196 A _22676 R _22675).
Proof. exact (eq_refl (term202 A R _22675 _22676)). Qed.
Lemma lem1236650 {A : Type'} (_22676 : A) (_22675 : A) (R : type1402 A) (h1 : term109 A R) : term196 A _22676 R _22675.
Proof. exact (EQ_MP (@lem1236649 A _22676 R _22675) (@lem1236648 A _22675 _22676 R h1)). Qed.
Lemma lem1236651 {A : Type'} (_22676 : A) (_22675 : A) (_22677 : A) (R : type1402 A) (h1 : term109 A R) : term203 A _22676 R _22675 _22677.
Proof. exact (@lem1236650 A _22676 _22675 R h1 _22677). Qed.
Lemma lem1236652 {A : Type'} (_22676 : A) (R : type1402 A) (_22675 : A) (_22677 : A) : (term203 A _22676 R _22675 _22677) = (term194 A _22676 R _22675 _22677).
Proof. exact (eq_refl (term203 A _22676 R _22675 _22677)). Qed.
Lemma lem1236653 {A : Type'} (_22676 : A) (_22675 : A) (_22677 : A) (R : type1402 A) (h1 : term109 A R) : term194 A _22676 R _22675 _22677.
Proof. exact (EQ_MP (@lem1236652 A _22676 R _22675 _22677) (@lem1236651 A _22676 _22675 _22677 R h1)). Qed.
Lemma lem1236664 {A : Type'} (_22676 : A) (R : type1402 A) (_22675 : A) (_22677 : A) : (term194 A _22676 R _22675 _22677) = (term204 A _22676 R _22675 _22677).
Proof. exact (@lem1235515 (term189 A R _22675 _22676) (term189 A R _22676 _22677) (term188 A R _22675 _22677)). Qed.
Lemma lem1236665 {A : Type'} (_22676 : A) (_22675 : A) (_22677 : A) (R : type1402 A) (h1 : term109 A R) : term204 A _22676 R _22675 _22677.
Proof. exact (EQ_MP (@lem1236664 A _22676 R _22675 _22677) (@lem1236653 A _22676 _22675 _22677 R h1)). Qed.
Lemma lem1236675 {A : Type'} (R : type1402 A) (x : A) (x' : A) (h1 : term174 A R x x') : term189 A R x x'.
Proof. exact (EQ_MP (@lem1236598 A R x x') (@lem1236460 A R x x' h1)). Qed.
Lemma lem1236677 {A : Type'} (R : type1402 A) (x : A) (y : A) (h1 : R x y) : term188 A R x y.
Proof. exact (EQ_MP (@lem1236548 A R x y) (@lem1236436 A R x y h1)). Qed.
Lemma lem1236678 {A : Type'} (R : type1402 A) (x : A) (y : A) (h1 : R x y) : term205 A R x y.
Proof. exact (fun h0 : term189 A R x y => @lem1236677 A R x y h1). Qed.
Lemma lem1236680 (p : Prop) : (term206 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1236681 {A : Type'} (R : type1402 A) (x : A) (y : A) : (term205 A R x y) = (term188 A R x y).
Proof. exact (@lem1236680 (term188 A R x y)). Qed.
Lemma lem1236682 {A : Type'} (R : type1402 A) (x : A) (y : A) (h1 : R x y) : term188 A R x y.
Proof. exact (EQ_MP (@lem1236681 A R x y) (@lem1236678 A R x y h1)). Qed.
Lemma lem1236684 {A : Type'} (R : type1402 A) (y : A) (x' : A) (h1 : R y x') : term188 A R y x'.
Proof. exact (EQ_MP (@lem1236578 A R y x') (@lem1236454 A R y x' h1)). Qed.
Lemma lem1236685 {A : Type'} (R : type1402 A) (y : A) (x' : A) (h1 : R y x') : term205 A R y x'.
Proof. exact (fun h0 : term189 A R y x' => @lem1236684 A R y x' h1). Qed.
Lemma lem1236687 (p : Prop) : (term206 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1236688 {A : Type'} (R : type1402 A) (y : A) (x' : A) : (term205 A R y x') = (term188 A R y x').
Proof. exact (@lem1236687 (term188 A R y x')). Qed.
Lemma lem1236689 {A : Type'} (R : type1402 A) (y : A) (x' : A) (h1 : R y x') : term188 A R y x'.
Proof. exact (EQ_MP (@lem1236688 A R y x') (@lem1236685 A R y x' h1)). Qed.
Lemma lem1236705 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1236706 {A : Type'} (_22675 : A) (R : type1402 A) (_22676 : A) (_22677 : A) : (term207 A _22676 R _22675 _22677) = (term208 A _22675 R _22676 _22677).
Proof. exact (@lem1236705 (term188 A R _22675 _22677) (term189 A R _22676 _22677)). Qed.
Lemma lem1236712 {A : Type'} (R : type1402 A) (_22675 : A) (_22676 : A) : (term191 A R _22675 _22676) = (term191 A R _22675 _22676).
Proof. exact (eq_refl (term191 A R _22675 _22676)). Qed.
Lemma lem1236713 {A : Type'} (_22675 : A) (R : type1402 A) (_22676 : A) (_22677 : A) : (term204 A _22676 R _22675 _22677) = (term209 A _22675 R _22676 _22677).
Proof. exact (MK_COMB (@lem1236712 A R _22675 _22676) (@lem1236706 A _22675 R _22676 _22677)). Qed.
Lemma lem1236717 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1236718 {A : Type'} (_22675 : A) (R : type1402 A) (_22676 : A) (_22677 : A) : (term209 A _22675 R _22676 _22677) = (term210 A _22675 R _22676 _22677).
Proof. exact (@lem1236717 (term188 A R _22675 _22677) (term189 A R _22675 _22676) (term189 A R _22676 _22677)). Qed.
Lemma lem1236734 {A : Type'} (_22675 : A) (R : type1402 A) (_22676 : A) (_22677 : A) : (term204 A _22676 R _22675 _22677) = (term210 A _22675 R _22676 _22677).
Proof. exact (TRANS (@lem1236713 A _22675 R _22676 _22677) (@lem1236718 A _22675 R _22676 _22677)). Qed.
Lemma lem1236735 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1236736 {A : Type'} (_22675 : A) (R : type1402 A) (_22676 : A) (_22677 : A) : (term211 A _22676 R _22675 _22677) = (term212 A _22675 R _22676 _22677).
Proof. exact (MK_COMB (@lem1236735) (@lem1236734 A _22675 R _22676 _22677)). Qed.
Lemma lem1236752 {A : Type'} (_22675 : A) (R : type1402 A) (_22676 : A) (_22677 : A) : (term210 A _22675 R _22676 _22677) = (term210 A _22675 R _22676 _22677).
Proof. exact (eq_refl (term210 A _22675 R _22676 _22677)). Qed.
Lemma lem1236753 {A : Type'} (_22675 : A) (R : type1402 A) (_22676 : A) (_22677 : A) : ((term204 A _22676 R _22675 _22677) = (term210 A _22675 R _22676 _22677)) = ((term210 A _22675 R _22676 _22677) = (term210 A _22675 R _22676 _22677)).
Proof. exact (MK_COMB (@lem1236736 A _22675 R _22676 _22677) (@lem1236752 A _22675 R _22676 _22677)). Qed.
Lemma lem1236755 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1236756 (x : Prop) : (x = x) = True.
Proof. exact (@lem1236755 Prop x). Qed.
Lemma lem1236757 {A : Type'} (_22675 : A) (R : type1402 A) (_22676 : A) (_22677 : A) : ((term210 A _22675 R _22676 _22677) = (term210 A _22675 R _22676 _22677)) = True.
Proof. exact (@lem1236756 (term210 A _22675 R _22676 _22677)). Qed.
Lemma lem1236758 {A : Type'} (_22675 : A) (R : type1402 A) (_22676 : A) (_22677 : A) : ((term204 A _22676 R _22675 _22677) = (term210 A _22675 R _22676 _22677)) = True.
Proof. exact (TRANS (@lem1236753 A _22675 R _22676 _22677) (@lem1236757 A _22675 R _22676 _22677)). Qed.
Lemma lem1236759 {A : Type'} (_22675 : A) (R : type1402 A) (_22676 : A) (_22677 : A) : True = ((term204 A _22676 R _22675 _22677) = (term210 A _22675 R _22676 _22677)).
Proof. exact (SYM (@lem1236758 A _22675 R _22676 _22677)). Qed.
Lemma lem1236760 {A : Type'} (_22675 : A) (R : type1402 A) (_22676 : A) (_22677 : A) : (term204 A _22676 R _22675 _22677) = (term210 A _22675 R _22676 _22677).
Proof. exact (EQ_MP (@lem1236759 A _22675 R _22676 _22677) (@lem0)). Qed.
Lemma lem1236761 {A : Type'} (_22675 : A) (_22676 : A) (_22677 : A) (R : type1402 A) (h1 : term109 A R) : term210 A _22675 R _22676 _22677.
Proof. exact (EQ_MP (@lem1236760 A _22675 R _22676 _22677) (@lem1236665 A _22676 _22675 _22677 R h1)). Qed.
Lemma lem1236763 (b : Prop) (a : Prop) : (a \/ b) = (term213 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1236764 {A : Type'} (_22676 : A) (R : type1402 A) (_22675 : A) (_22677 : A) : (term210 A _22675 R _22676 _22677) = (term214 A _22676 R _22675 _22677).
Proof. exact (@lem1236763 (term192 A _22675 R _22676 _22677) (term188 A R _22675 _22677)). Qed.
Lemma lem1236766 (a : Prop) (b : Prop) : (term215 a b) = (term216 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1236767 {A : Type'} (_22675 : A) (R : type1402 A) (_22676 : A) (_22677 : A) : (term217 A _22675 R _22676 _22677) = (term218 A _22675 R _22676 _22677).
Proof. exact (@lem1236766 (term189 A R _22675 _22676) (term189 A R _22676 _22677)). Qed.
Lemma lem1236769 (a : Prop) : (term140 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1236770 {A : Type'} (R : type1402 A) (_22675 : A) (_22676 : A) : (term219 A R _22675 _22676) = (term188 A R _22675 _22676).
Proof. exact (@lem1236769 (term188 A R _22675 _22676)). Qed.
Lemma lem1236771 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1236772 {A : Type'} (R : type1402 A) (_22675 : A) (_22676 : A) : (term220 A R _22675 _22676) = (term221 A R _22675 _22676).
Proof. exact (MK_COMB (@lem1236771) (@lem1236770 A R _22675 _22676)). Qed.
Lemma lem1236774 (a : Prop) : (term140 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1236775 {A : Type'} (R : type1402 A) (_22676 : A) (_22677 : A) : (term219 A R _22676 _22677) = (term188 A R _22676 _22677).
Proof. exact (@lem1236774 (term188 A R _22676 _22677)). Qed.
Lemma lem1236776 {A : Type'} (_22675 : A) (R : type1402 A) (_22676 : A) (_22677 : A) : (term218 A _22675 R _22676 _22677) = (term222 A _22675 R _22676 _22677).
Proof. exact (MK_COMB (@lem1236772 A R _22675 _22676) (@lem1236775 A R _22676 _22677)). Qed.
Lemma lem1236777 {A : Type'} (_22675 : A) (R : type1402 A) (_22676 : A) (_22677 : A) : (term217 A _22675 R _22676 _22677) = (term222 A _22675 R _22676 _22677).
Proof. exact (TRANS (@lem1236767 A _22675 R _22676 _22677) (@lem1236776 A _22675 R _22676 _22677)). Qed.
Lemma lem1236778 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1236779 {A : Type'} (_22675 : A) (R : type1402 A) (_22676 : A) (_22677 : A) : (term223 A _22675 R _22676 _22677) = (term224 A _22675 R _22676 _22677).
Proof. exact (MK_COMB (@lem1236778) (@lem1236777 A _22675 R _22676 _22677)). Qed.
Lemma lem1236780 {A : Type'} (R : type1402 A) (_22675 : A) (_22677 : A) : (term188 A R _22675 _22677) = (term188 A R _22675 _22677).
Proof. exact (eq_refl (term188 A R _22675 _22677)). Qed.
Lemma lem1236781 {A : Type'} (_22676 : A) (R : type1402 A) (_22675 : A) (_22677 : A) : (term214 A _22676 R _22675 _22677) = (term225 A _22676 R _22675 _22677).
Proof. exact (MK_COMB (@lem1236779 A _22675 R _22676 _22677) (@lem1236780 A R _22675 _22677)). Qed.
Lemma lem1236782 {A : Type'} (_22676 : A) (R : type1402 A) (_22675 : A) (_22677 : A) : (term210 A _22675 R _22676 _22677) = (term225 A _22676 R _22675 _22677).
Proof. exact (TRANS (@lem1236764 A _22676 R _22675 _22677) (@lem1236781 A _22676 R _22675 _22677)). Qed.
Lemma lem1236784 {A : Type'} (x : A) (R : type1402 A) (y : A) (x' : A) (h1 : R x y) (h2 : R y x') : term222 A x R y x'.
Proof. exact (conj (@lem1236682 A R x y h1) (@lem1236689 A R y x' h2)). Qed.
Lemma lem1236786 {A : Type'} (_22676 : A) (_22675 : A) (_22677 : A) (R : type1402 A) (h1 : term109 A R) : term225 A _22676 R _22675 _22677.
Proof. exact (EQ_MP (@lem1236782 A _22676 R _22675 _22677) (@lem1236761 A _22675 _22676 _22677 R h1)). Qed.
Lemma lem1236787 {A : Type'} (_22676 : A) (_22675 : A) (_22677 : A) (R : type1402 A) (h1 : term109 A R) : term225 A _22676 R _22675 _22677.
Proof. exact (@lem1236786 A _22676 _22675 _22677 R h1). Qed.
Lemma lem1236788 {A : Type'} (y : A) (x : A) (x' : A) (R : type1402 A) (h1 : term109 A R) : term225 A y R x x'.
Proof. exact (@lem1236787 A y x x' R h1). Qed.
Lemma lem1236791 {A : Type'} (x : A) (R : type1402 A) (y : A) (x' : A) (h1 : term109 A R) (h2 : R x y) (h3 : R y x') : term188 A R x x'.
Proof. exact (@lem1236788 A y x x' R h1 (@lem1236784 A x R y x' h2 h3)). Qed.
Lemma lem1236792 {A : Type'} (x : A) (R : type1402 A) (y : A) (x' : A) (h1 : term109 A R) (h2 : R x y) (h3 : R y x') : term205 A R x x'.
Proof. exact (fun h0 : term189 A R x x' => @lem1236791 A x R y x' h1 h2 h3). Qed.
Lemma lem1236794 (p : Prop) : (term206 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1236795 {A : Type'} (R : type1402 A) (x : A) (x' : A) : (term205 A R x x') = (term188 A R x x').
Proof. exact (@lem1236794 (term188 A R x x')). Qed.
Lemma lem1236796 {A : Type'} (x : A) (R : type1402 A) (y : A) (x' : A) (h1 : term109 A R) (h2 : R x y) (h3 : R y x') : term188 A R x x'.
Proof. exact (EQ_MP (@lem1236795 A R x x') (@lem1236792 A x R y x' h1 h2 h3)). Qed.
Lemma lem1236799 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1236801 {A : Type'} (R : type1402 A) (x : A) (x' : A) : (term189 A R x x') = (term226 A R x x').
Proof. exact (@lem1236799 (term188 A R x x')). Qed.
Lemma lem1236804 {A : Type'} (R : type1402 A) (x : A) (x' : A) (h1 : term174 A R x x') : term226 A R x x'.
Proof. exact (EQ_MP (@lem1236801 A R x x') (@lem1236675 A R x x' h1)). Qed.
Lemma lem1236807 {A : Type'} (x : A) (R : type1402 A) (y : A) (x' : A) (h1 : term109 A R) (h2 : term174 A R x x') (h3 : R x y) (h4 : R y x') : False.
Proof. exact (@lem1236804 A R x x' h2 (@lem1236796 A x R y x' h1 h3 h4)). Qed.
Lemma lem1236808 {A : Type'} (x : A) (R : type1402 A) (y : A) (x' : A) (h1 : term109 A R) (h2 : term174 A R x x') (h3 : R x y) (h4 : R y x') : term227.
Proof. exact (fun h0 : ~ False => @lem1236807 A x R y x' h1 h2 h3 h4). Qed.
Lemma lem1236810 (p : Prop) : (term206 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1236811 : term227 = False.
Proof. exact (@lem1236810 False). Qed.
Lemma lem1236812 {A : Type'} (x : A) (R : type1402 A) (y : A) (x' : A) (h1 : term109 A R) (h2 : term174 A R x x') (h3 : R x y) (h4 : R y x') : False.
Proof. exact (EQ_MP (@lem1236811) (@lem1236808 A x R y x' h1 h2 h3 h4)). Qed.
Lemma lem1236813 {A : Type'} (x : A) (R : type1402 A) (y : A) (x' : A) (h1 : term109 A R) (h2 : term174 A R x x') (h3 : R x y) (h4 : R y x') : (term174 A R x x') = False.
Proof. exact (prop_ext (fun h5 : term174 A R x x' => @lem1236812 A x R y x' h1 h2 h3 h4) (fun h5 : False => @lem1236460 A R x x' h2)). Qed.
Lemma lem1236814 {A : Type'} (x : A) (R : type1402 A) (y : A) (x' : A) (h1 : term109 A R) (h2 : term174 A R x x') (h3 : R x y) (h4 : R y x') : False.
Proof. exact (EQ_MP (@lem1236813 A x R y x' h1 h2 h3 h4) (@lem1236460 A R x x' h2)). Qed.
Lemma lem1236815 {A : Type'} (x : A) (R : type1402 A) (y : A) (x' : A) (h1 : term109 A R) (h2 : term174 A R x x') (h3 : R x y) (h4 : R y x') : (R y x') = False.
Proof. exact (prop_ext (fun h5 : R y x' => @lem1236814 A x R y x' h1 h2 h3 h4) (fun h5 : False => @lem1236454 A R y x' h4)). Qed.
Lemma lem1236816 {A : Type'} (x : A) (R : type1402 A) (y : A) (x' : A) (h1 : term109 A R) (h2 : term174 A R x x') (h3 : R x y) (h4 : R y x') : False.
Proof. exact (EQ_MP (@lem1236815 A x R y x' h1 h2 h3 h4) (@lem1236454 A R y x' h4)). Qed.
Lemma lem1236817 {A : Type'} (x : A) (R : type1402 A) (y : A) (x' : A) (h1 : term109 A R) (h2 : term174 A R x x') (h3 : R x y) (h4 : R y x') : (R x y) = False.
Proof. exact (prop_ext (fun h5 : R x y => @lem1236816 A x R y x' h1 h2 h3 h4) (fun h5 : False => @lem1236436 A R x y h3)). Qed.
Lemma lem1236818 {A : Type'} (x : A) (R : type1402 A) (y : A) (x' : A) (h1 : term109 A R) (h2 : term174 A R x x') (h3 : R x y) (h4 : R y x') : False.
Proof. exact (EQ_MP (@lem1236817 A x R y x' h1 h2 h3 h4) (@lem1236436 A R x y h3)). Qed.
Lemma lem1236819 {A : Type'} (x : A) (R : type1402 A) (y : A) (x' : A) (h1 : term109 A R) (h2 : term174 A R x x') (h3 : R x y) (h4 : R y x') : (term174 A R x x') = False.
Proof. exact (prop_ext (fun h5 : term174 A R x x' => @lem1236818 A x R y x' h1 h2 h3 h4) (fun h5 : False => @lem1236347 A R x x' h2)). Qed.
Lemma lem1236820 {A : Type'} (x : A) (R : type1402 A) (y : A) (x' : A) (h1 : term109 A R) (h2 : term174 A R x x') (h3 : R x y) (h4 : R y x') : False.
Proof. exact (EQ_MP (@lem1236819 A x R y x' h1 h2 h3 h4) (@lem1236347 A R x x' h2)). Qed.
Lemma lem1236821 {A : Type'} (x : A) (R : type1402 A) (y : A) (x' : A) (h1 : term109 A R) (h2 : R x y) (h3 : R y x') : term173 A R x x'.
Proof. exact (fun h0 : term174 A R x x' => @lem1236820 A x R y x' h1 h0 h2 h3). Qed.
Lemma lem1236822 {A : Type'} (x : A) (R : type1402 A) (y : A) (x' : A) (h1 : term109 A R) (h2 : R x y) (h3 : R y x') : R x x'.
Proof. exact (EQ_MP (@lem1236346 A R x x') (@lem1236821 A x R y x' h1 h2 h3)). Qed.
Lemma lem1236823 {A : Type'} (x' : A) (R : type1402 A) (x : A) (y : A) (h1 : term109 A R) (h2 : R x y) : term228 A y R x x'.
Proof. exact (fun h0 : R y x' => @lem1236822 A x R y x' h1 h2 h0). Qed.
Lemma lem1236824 {A : Type'} (l : list A) (x' : A) (R : type1402 A) (x : A) (y : A) (h1 : term109 A R) (h2 : R x y) : term165 A l y R x x'.
Proof. exact (fun h0 : @List.In A x' l => @lem1236823 A x' R x y h1 h2). Qed.
Lemma lem1236829 {A : Type'} (l : list A) (R : type1402 A) (x : A) (y : A) (h1 : term109 A R) (h2 : R x y) : term132 A l y R x.
Proof. exact (fun x' : A => @lem1236824 A l x' R x y h1 h2). Qed.
Lemma lem1236830 {A : Type'} (l : list A) (R : type1402 A) (x : A) (y : A) (h1 : term109 A R) (h2 : R x y) : term143 A l y R x.
Proof. exact (fun h0 : @List.ForallOrdPairs A R l => @lem1236829 A l R x y h1 h2). Qed.
Lemma lem1236831 {A : Type'} (l : list A) (y : A) (x : A) (R : type1402 A) (h1 : term109 A R) : term146 A l y R x.
Proof. exact (fun h0 : R x y => @lem1236830 A l R x y h1 h0). Qed.
Lemma lem1236832 {A : Type'} (l : list A) (y : A) (R : type1402 A) (x : A) : term148 A l y R x.
Proof. exact (fun h0 : term109 A R => @lem1236831 A l y x R h0). Qed.
Lemma lem1236837 {A : Type'} (y : A) (R : type1402 A) (x : A) : term152 A y R x.
Proof. exact (fun l : list A => @lem1236832 A l y R x). Qed.
Lemma lem1236842 {A : Type'} (R : type1402 A) (x : A) : term156 A R x.
Proof. exact (fun y : A => @lem1236837 A y R x). Qed.
Lemma lem1236847 {A : Type'} (x : A) : term160 A x.
Proof. exact (fun R : type1402 A => @lem1236842 A R x). Qed.
Lemma lem1236852 {A : Type'} : term164 A.
Proof. exact (fun x : A => @lem1236847 A x). Qed.
Lemma lem1236853 {A : Type'} : term163 A.
Proof. exact (EQ_MP (@lem1236337 A) (@lem1236852 A)). Qed.
Lemma lem1236854 {A : Type'} (x : A) : term229 A x.
Proof. exact (@lem1236853 A x). Qed.
Lemma lem1236855 {A : Type'} (x : A) : (term229 A x) = (term159 A x).
Proof. exact (eq_refl (term229 A x)). Qed.
Lemma lem1236856 {A : Type'} (x : A) : term159 A x.
Proof. exact (EQ_MP (@lem1236855 A x) (@lem1236854 A x)). Qed.
Lemma lem1236857 {A : Type'} (x : A) (R : type1402 A) : term230 A x R.
Proof. exact (@lem1236856 A x R). Qed.
Lemma lem1236858 {A : Type'} (R : type1402 A) (x : A) : (term230 A x R) = (term155 A R x).
Proof. exact (eq_refl (term230 A x R)). Qed.
Lemma lem1236859 {A : Type'} (R : type1402 A) (x : A) : term155 A R x.
Proof. exact (EQ_MP (@lem1236858 A R x) (@lem1236857 A x R)). Qed.
Lemma lem1236860 {A : Type'} (R : type1402 A) (x : A) (y : A) : term231 A R x y.
Proof. exact (@lem1236859 A R x y). Qed.
Lemma lem1236861 {A : Type'} (y : A) (R : type1402 A) (x : A) : (term231 A R x y) = (term151 A y R x).
Proof. exact (eq_refl (term231 A R x y)). Qed.
Lemma lem1236862 {A : Type'} (y : A) (R : type1402 A) (x : A) : term151 A y R x.
Proof. exact (EQ_MP (@lem1236861 A y R x) (@lem1236860 A R x y)). Qed.
Lemma lem1236863 {A : Type'} (y : A) (R : type1402 A) (x : A) (l : list A) : term232 A y R x l.
Proof. exact (@lem1236862 A y R x l). Qed.
Lemma lem1236864 {A : Type'} (l : list A) (y : A) (R : type1402 A) (x : A) : (term232 A y R x l) = (term135 A l y R x).
Proof. exact (eq_refl (term232 A y R x l)). Qed.
Lemma lem1236865 {A : Type'} (l : list A) (y : A) (R : type1402 A) (x : A) : term135 A l y R x.
Proof. exact (EQ_MP (@lem1236864 A l y R x) (@lem1236863 A y R x l)). Qed.
Lemma lem1236867 {A : Type'} (l : list A) (y : A) (R : type1402 A) (x : A) : term135 A l y R x.
Proof. exact (@lem1236121 A l y R x (@lem1236865 A l y R x)). Qed.
Lemma lem1236868 {A : Type'} (l : list A) (y : A) (x : A) (R : type1402 A) (h1 : term109 A R) : term145 A l y R x.
Proof. exact (@lem1236867 A l y R x (@lem1236033 A R h1)). Qed.
Lemma lem1236869 {A : Type'} (l : list A) (R : type1402 A) (x : A) (y : A) (h1 : term109 A R) (h2 : R x y) : term142 A l y R x.
Proof. exact (@lem1236868 A l y x R h1 (@lem1236096 A R x y h2)). Qed.
Lemma lem1236870 {A : Type'} (l : list A) (R : type1402 A) (x : A) (y : A) (h1 : term109 A R) (h2 : @List.ForallOrdPairs A R l) (h3 : R x y) : term133 A l y R x.
Proof. exact (@lem1236869 A l R x y h1 h3 (@lem1236095 A R l h2)). Qed.
Lemma lem1236871 {A : Type'} (l : list A) (R : type1402 A) (x : A) (y : A) (h1 : term109 A R) (h2 : term134 A l y R x) (h3 : @List.ForallOrdPairs A R l) (h4 : R x y) : False.
Proof. exact (@lem1236870 A l R x y h1 h3 h4 (@lem1236105 A l y R x h2)). Qed.
Lemma lem1236872 {A : Type'} (l : list A) (R : type1402 A) (x : A) (y : A) (h1 : term109 A R) (h2 : term134 A l y R x) (h3 : @List.ForallOrdPairs A R l) (h4 : R x y) : (term134 A l y R x) = False.
Proof. exact (prop_ext (fun h5 : term134 A l y R x => @lem1236871 A l R x y h1 h2 h3 h4) (fun h5 : False => @lem1236105 A l y R x h2)). Qed.
Lemma lem1236873 {A : Type'} (l : list A) (R : type1402 A) (x : A) (y : A) (h1 : term109 A R) (h2 : term134 A l y R x) (h3 : @List.ForallOrdPairs A R l) (h4 : R x y) : False.
Proof. exact (EQ_MP (@lem1236872 A l R x y h1 h2 h3 h4) (@lem1236105 A l y R x h2)). Qed.
Lemma lem1236874 {A : Type'} (l : list A) (R : type1402 A) (x : A) (y : A) (h1 : term109 A R) (h2 : @List.ForallOrdPairs A R l) (h3 : R x y) : term133 A l y R x.
Proof. exact (fun h0 : term134 A l y R x => @lem1236873 A l R x y h1 h0 h2 h3). Qed.
Lemma lem1236875 {A : Type'} (l : list A) (R : type1402 A) (x : A) (y : A) (h1 : term109 A R) (h2 : @List.ForallOrdPairs A R l) (h3 : R x y) : term132 A l y R x.
Proof. exact (EQ_MP (@lem1236104 A l y R x) (@lem1236874 A l R x y h1 h2 h3)). Qed.
Lemma lem1236876 {A : Type'} (l : list A) (R : type1402 A) (x : A) (y : A) (h1 : term109 A R) (h2 : @List.ForallOrdPairs A R l) (h3 : R x y) : term233 A y R x l.
Proof. exact (@lem1236100 A y R x l (@lem1236875 A l R x y h1 h2 h3)). Qed.
Lemma lem1236877 {A : Type'} (x : A) (y : A) (R : type1402 A) (l : list A) (h1 : term129 A x y R l) : @List.ForallOrdPairs A R l.
Proof. exact (proj2 (@lem1236094 A x y R l h1)). Qed.
Lemma lem1236878 {A : Type'} (x : A) (y : A) (R : type1402 A) (l : list A) (h1 : term129 A x y R l) : R x y.
Proof. exact (proj1 (@lem1236094 A x y R l h1)). Qed.
Lemma lem1236879 {A : Type'} (l : list A) (R : type1402 A) (x : A) (y : A) (h1 : term109 A R) (h2 : @List.ForallOrdPairs A R l) (h3 : R x y) : (@List.ForallOrdPairs A R l) = (term233 A y R x l).
Proof. exact (prop_ext (fun h4 : @List.ForallOrdPairs A R l => @lem1236876 A l R x y h1 h2 h3) (fun h4 : term233 A y R x l => @lem1236095 A R l h2)). Qed.
Lemma lem1236880 {A : Type'} (l : list A) (R : type1402 A) (x : A) (y : A) (h1 : term109 A R) (h2 : @List.ForallOrdPairs A R l) (h3 : R x y) : term233 A y R x l.
Proof. exact (EQ_MP (@lem1236879 A l R x y h1 h2 h3) (@lem1236095 A R l h2)). Qed.
Lemma lem1236881 {A : Type'} (l : list A) (R : type1402 A) (x : A) (y : A) (h1 : term109 A R) (h2 : @List.ForallOrdPairs A R l) (h3 : R x y) : (R x y) = (term233 A y R x l).
Proof. exact (prop_ext (fun h4 : R x y => @lem1236880 A l R x y h1 h2 h3) (fun h4 : term233 A y R x l => @lem1236096 A R x y h3)). Qed.
Lemma lem1236882 {A : Type'} (l : list A) (R : type1402 A) (x : A) (y : A) (h1 : term109 A R) (h2 : @List.ForallOrdPairs A R l) (h3 : R x y) : term233 A y R x l.
Proof. exact (EQ_MP (@lem1236881 A l R x y h1 h2 h3) (@lem1236096 A R x y h3)). Qed.
Lemma lem1236883 {A : Type'} (l : list A) (R : type1402 A) (x : A) (y : A) (h1 : term109 A R) (h2 : term129 A x y R l) (h3 : R x y) : (@List.ForallOrdPairs A R l) = (term233 A y R x l).
Proof. exact (prop_ext (fun h4 : @List.ForallOrdPairs A R l => @lem1236882 A l R x y h1 h4 h3) (fun h4 : term233 A y R x l => @lem1236877 A x y R l h2)). Qed.
Lemma lem1236884 {A : Type'} (l : list A) (R : type1402 A) (x : A) (y : A) (h1 : term109 A R) (h2 : term129 A x y R l) (h3 : R x y) : term233 A y R x l.
Proof. exact (EQ_MP (@lem1236883 A l R x y h1 h2 h3) (@lem1236877 A x y R l h2)). Qed.
Lemma lem1236885 {A : Type'} (x : A) (y : A) (R : type1402 A) (l : list A) (h1 : term109 A R) (h2 : term129 A x y R l) : (R x y) = (term233 A y R x l).
Proof. exact (prop_ext (fun h3 : R x y => @lem1236884 A l R x y h1 h2 h3) (fun h3 : term233 A y R x l => @lem1236878 A x y R l h2)). Qed.
Lemma lem1236886 {A : Type'} (x : A) (y : A) (R : type1402 A) (l : list A) (h1 : term109 A R) (h2 : term129 A x y R l) : term233 A y R x l.
Proof. exact (EQ_MP (@lem1236885 A x y R l h1 h2) (@lem1236878 A x y R l h2)). Qed.
Lemma lem1236887 {A : Type'} (y : A) (x : A) (l : list A) (R : type1402 A) (h1 : term109 A R) : term128 A y R x l.
Proof. exact (fun h0 : term129 A x y R l => @lem1236886 A x y R l h1 h0). Qed.
Lemma lem1236888 {A : Type'} (x : A) (y : A) (l : list A) (R : type1402 A) (h1 : term109 A R) : (term112 A R x y l) = (term126 A x R y l).
Proof. exact (EQ_MP (@lem1236093 A x R y l) (@lem1236887 A y x l R h1)). Qed.
Lemma lem1236889 {A : Type'} (x : A) (y : A) (l : list A) (R : type1402 A) (h1 : term109 A R) : (term109 A R) = ((term112 A R x y l) = (term126 A x R y l)).
Proof. exact (prop_ext (fun h2 : term109 A R => @lem1236888 A x y l R h1) (fun h2 : (term112 A R x y l) = (term126 A x R y l) => @lem1236033 A R h1)). Qed.
Lemma lem1236890 {A : Type'} (x : A) (y : A) (l : list A) (R : type1402 A) (h1 : term109 A R) : (term112 A R x y l) = (term126 A x R y l).
Proof. exact (EQ_MP (@lem1236889 A x y l R h1) (@lem1236033 A R h1)). Qed.
Lemma lem1236891 {A : Type'} (x : A) (R : type1402 A) (y : A) (l : list A) : term234 A x R y l.
Proof. exact (fun h0 : term109 A R => @lem1236890 A x y l R h0). Qed.
Lemma lem1236896 {A : Type'} (x : A) (R : type1402 A) (y : A) : term235 A x R y.
Proof. exact (fun l : list A => @lem1236891 A x R y l). Qed.
Lemma lem1236901 {A : Type'} (x : A) (R : type1402 A) : term236 A x R.
Proof. exact (fun y : A => @lem1236896 A x R y). Qed.
Lemma lem1236906 {A : Type'} (R : type1402 A) : term237 A R.
Proof. exact (fun x : A => @lem1236901 A x R). Qed.
Lemma lem1236911 {A : Type'} : term238 A.
Proof. exact (fun R : type1402 A => @lem1236906 A R). Qed.
