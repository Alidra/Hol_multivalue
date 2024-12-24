Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3892933_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import HAS_SIZE_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16445_spec.
Require Import thm16446_spec.
Require Import thm16457_spec.
Require Import thm16458_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
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
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Lemma lem3888989 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3888990 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3888991 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3888990 t1) (@lem3888989 t1)). Qed.
Lemma lem3888992 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3888991 t1 t2). Qed.
Lemma lem3888993 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3888994 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3888993 t1 t2) (@lem3888992 t1 t2)). Qed.
Lemma lem3888995 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3888994 t1 t2 t3). Qed.
Lemma lem3888996 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3888997 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3888996 t1 t2 t3) (@lem3888995 t1 t2 t3)). Qed.
Lemma lem3888998 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3888997 t1 t2 t3)). Qed.
Lemma lem3889012 {_100499 : Type'} (s : _100499 -> Prop) : (term7 _100499 s) = (s = (@EMPTY _100499)).
Proof. exact (proj1 (@lem3887954 _100499 (@el nat) s)). Qed.
Lemma lem3889013 {_100607 : Type'} (s : _100607 -> Prop) : (term7 _100607 s) = (s = (@EMPTY _100607)).
Proof. exact (@lem3889012 _100607 s). Qed.
Lemma lem3889016 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3889017 {_100607 : Type'} (s : _100607 -> Prop) : (term8 _100607 s) = (term9 _100607 s).
Proof. exact (MK_COMB (@lem3889016) (@lem3889013 _100607 s)). Qed.
Lemma lem3889018 {_100607 : Type'} (P : type686 _100607) (s : _100607 -> Prop) : (P s) = (P s).
Proof. exact (eq_refl (P s)). Qed.
Lemma lem3889019 {_100607 : Type'} (P : type686 _100607) (s : _100607 -> Prop) : (term10 _100607 P s) = (term11 _100607 P s).
Proof. exact (MK_COMB (@lem3889017 _100607 s) (@lem3889018 _100607 P s)). Qed.
Lemma lem3889022 {_100607 : Type'} (P : type686 _100607) : (term12 _100607 P) = (term13 _100607 P).
Proof. exact (fun_ext (fun s : _100607 -> Prop => @lem3889019 _100607 P s)). Qed.
Lemma lem3889023 {_100607 : Type'} : (@ex (_100607 -> Prop)) = (@ex (_100607 -> Prop)).
Proof. exact (eq_refl (@ex (_100607 -> Prop))). Qed.
Lemma lem3889024 {_100607 : Type'} (P : type686 _100607) : (term14 _100607 P) = (term15 _100607 P).
Proof. exact (MK_COMB (@lem3889023 _100607) (@lem3889022 _100607 P)). Qed.
Lemma lem3889029 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3889030 {_100607 : Type'} (P : type686 _100607) : (term16 _100607 P) = (term17 _100607 P).
Proof. exact (MK_COMB (@lem3889029) (@lem3889024 _100607 P)). Qed.
Lemma lem3889031 {_100607 : Type'} (P : type686 _100607) : (P (@EMPTY _100607)) = (P (@EMPTY _100607)).
Proof. exact (eq_refl (P (@EMPTY _100607))). Qed.
Lemma lem3889032 {_100607 : Type'} (P : type686 _100607) : ((term14 _100607 P) = (P (@EMPTY _100607))) = ((term15 _100607 P) = (P (@EMPTY _100607))).
Proof. exact (MK_COMB (@lem3889030 _100607 P) (@lem3889031 _100607 P)). Qed.
Lemma lem3889035 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3889036 {_100607 : Type'} (P : type686 _100607) : (term18 _100607 P) = (term19 _100607 P).
Proof. exact (MK_COMB (@lem3889035) (@lem3889032 _100607 P)). Qed.
Lemma lem3889046 {_100499 : Type'} (n : nat) (s : _100499 -> Prop) : (term20 _100499 s n) = (term21 _100499 n s).
Proof. exact (proj2 (@lem3887954 _100499 n s)). Qed.
Lemma lem3889047 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) : (term20 _100607 s n) = (term21 _100607 n s).
Proof. exact (@lem3889046 _100607 n s). Qed.
Lemma lem3889062 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3889063 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) : (term22 _100607 s n) = (term23 _100607 n s).
Proof. exact (MK_COMB (@lem3889062) (@lem3889047 _100607 n s)). Qed.
Lemma lem3889064 {_100607 : Type'} (P : type686 _100607) (s : _100607 -> Prop) : (P s) = (P s).
Proof. exact (eq_refl (P s)). Qed.
Lemma lem3889065 {_100607 : Type'} (n : nat) (P : type686 _100607) (s : _100607 -> Prop) : (term24 _100607 n P s) = (term25 _100607 n P s).
Proof. exact (MK_COMB (@lem3889063 _100607 n s) (@lem3889064 _100607 P s)). Qed.
Lemma lem3889068 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term26 _100607 n P) = (term27 _100607 n P).
Proof. exact (fun_ext (fun s : _100607 -> Prop => @lem3889065 _100607 n P s)). Qed.
Lemma lem3889069 {_100607 : Type'} : (@ex (_100607 -> Prop)) = (@ex (_100607 -> Prop)).
Proof. exact (eq_refl (@ex (_100607 -> Prop))). Qed.
Lemma lem3889070 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term28 _100607 n P) = (term29 _100607 n P).
Proof. exact (MK_COMB (@lem3889069 _100607) (@lem3889068 _100607 n P)). Qed.
Lemma lem3889075 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3889076 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term30 _100607 n P) = (term31 _100607 n P).
Proof. exact (MK_COMB (@lem3889075) (@lem3889070 _100607 n P)). Qed.
Lemma lem3889089 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term32 _100607 n P) = (term32 _100607 n P).
Proof. exact (eq_refl (term32 _100607 n P)). Qed.
Lemma lem3889090 {_100607 : Type'} (n : nat) (P : type686 _100607) : ((term28 _100607 n P) = (term32 _100607 n P)) = ((term29 _100607 n P) = (term32 _100607 n P)).
Proof. exact (MK_COMB (@lem3889076 _100607 n P) (@lem3889089 _100607 n P)). Qed.
Lemma lem3889093 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term33 _100607 n P) = (term34 _100607 n P).
Proof. exact (MK_COMB (@lem3889036 _100607 P) (@lem3889090 _100607 n P)). Qed.
Lemma lem3889096 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term34 _100607 n P) = (term33 _100607 n P).
Proof. exact (SYM (@lem3889093 _100607 n P)). Qed.
Lemma lem3889098 (p : Prop) : p = (term35 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3889099 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term34 _100607 n P) = (term36 _100607 n P).
Proof. exact (@lem3889098 (term34 _100607 n P)). Qed.
Lemma lem3889100 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term36 _100607 n P) = (term34 _100607 n P).
Proof. exact (SYM (@lem3889099 _100607 n P)). Qed.
Lemma lem3889101 {_100607 : Type'} (n : nat) (P : type686 _100607) (h1 : term37 _100607 n P) : term37 _100607 n P.
Proof. exact (h1). Qed.
Lemma lem3889104 {_100607 : Type'} (n : nat) (P : type686 _100607) (h1 : term36 _100607 n P) : term36 _100607 n P.
Proof. exact (h1). Qed.
Lemma lem3889105 {_100607 : Type'} (n : nat) (P : type686 _100607) : term38 _100607 n P.
Proof. exact (fun h0 : term36 _100607 n P => @lem3889104 _100607 n P h0). Qed.
Lemma lem3889106 {_100607 : Type'} (n : nat) (P : type686 _100607) (h1 : term38 _100607 n P) : term38 _100607 n P.
Proof. exact (h1). Qed.
Lemma lem3889107 {_100607 : Type'} (n : nat) (P : type686 _100607) (h1 : term36 _100607 n P) : term36 _100607 n P.
Proof. exact (h1). Qed.
Lemma lem3889108 {_100607 : Type'} (n : nat) (P : type686 _100607) (h1 : term36 _100607 n P) (h2 : term38 _100607 n P) : term36 _100607 n P.
Proof. exact (@lem3889106 _100607 n P h2 (@lem3889107 _100607 n P h1)). Qed.
Lemma lem3889109 {_100607 : Type'} (n : nat) (P : type686 _100607) (h1 : term36 _100607 n P) : term39 _100607 n P.
Proof. exact (fun h0 : term38 _100607 n P => @lem3889108 _100607 n P h1 h0). Qed.
Lemma lem3889110 {_100607 : Type'} (n : nat) (P : type686 _100607) (h1 : term38 _100607 n P) : term38 _100607 n P.
Proof. exact (h1). Qed.
Lemma lem3889111 {_100607 : Type'} (n : nat) (P : type686 _100607) (h1 : term36 _100607 n P) (h2 : term38 _100607 n P) : term36 _100607 n P.
Proof. exact (@lem3889109 _100607 n P h1 (@lem3889110 _100607 n P h2)). Qed.
Lemma lem3889112 {_100607 : Type'} (n : nat) (P : type686 _100607) (h1 : term38 _100607 n P) : term38 _100607 n P.
Proof. exact (fun h0 : term36 _100607 n P => @lem3889111 _100607 n P h0 h1). Qed.
Lemma lem3889113 {_100607 : Type'} (n : nat) (P : type686 _100607) : term40 _100607 n P.
Proof. exact (fun h0 : term38 _100607 n P => @lem3889112 _100607 n P h0). Qed.
Lemma lem3889116 {_100607 : Type'} (n : nat) (P : type686 _100607) : term38 _100607 n P.
Proof. exact (@lem3889113 _100607 n P (@lem3889105 _100607 n P)). Qed.
Lemma lem3889117 {_100607 : Type'} (n : nat) (P : type686 _100607) : term38 _100607 n P.
Proof. exact (@lem3889116 _100607 n P). Qed.
Lemma lem3889127 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3889128 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term36 _100607 n P) = (term41 _100607 n P).
Proof. exact (@lem3889127 (term37 _100607 n P)). Qed.
Lemma lem3889130 (t : Prop) : (term42 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3889131 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term41 _100607 n P) = (term34 _100607 n P).
Proof. exact (@lem3889130 (term34 _100607 n P)). Qed.
Lemma lem3889134 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term36 _100607 n P) = (term34 _100607 n P).
Proof. exact (TRANS (@lem3889128 _100607 n P) (@lem3889131 _100607 n P)). Qed.
Lemma lem3889315 {_100607 : Type'} (P : type686 _100607) : (term43 _100607 P) = (term44 _100607 P).
Proof. exact (fun_ext (fun n : nat => @lem3889134 _100607 n P)). Qed.
Lemma lem3889316 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3889317 {_100607 : Type'} (P : type686 _100607) : (term45 _100607 P) = (term46 _100607 P).
Proof. exact (MK_COMB (@lem3889316) (@lem3889315 _100607 P)). Qed.
Lemma lem3889319 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term47 A P Q) = (term48 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem3889320 (P : nat -> Prop) (Q : nat -> Prop) : (term49 P Q) = (term50 P Q).
Proof. exact (@lem3889319 nat P Q). Qed.
Lemma lem3889321 {_100607 : Type'} (P : type686 _100607) : (term51 _100607 P) = (term52 _100607 P).
Proof. exact (@lem3889320 (term53 _100607 P) (term54 _100607 P)). Qed.
Lemma lem3889322 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term55 _100607 P n) = ((term15 _100607 P) = (P (@EMPTY _100607))).
Proof. exact (eq_refl (term55 _100607 P n)). Qed.
Lemma lem3889323 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3889324 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term56 _100607 P n) = (term19 _100607 P).
Proof. exact (MK_COMB (@lem3889323) (@lem3889322 _100607 n P)). Qed.
Lemma lem3889325 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term57 _100607 P n) = ((term29 _100607 n P) = (term32 _100607 n P)).
Proof. exact (eq_refl (term57 _100607 P n)). Qed.
Lemma lem3889326 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term58 _100607 P n) = (term34 _100607 n P).
Proof. exact (MK_COMB (@lem3889324 _100607 n P) (@lem3889325 _100607 n P)). Qed.
Lemma lem3889327 {_100607 : Type'} (P : type686 _100607) : (term59 _100607 P) = (term44 _100607 P).
Proof. exact (fun_ext (fun n : nat => @lem3889326 _100607 n P)). Qed.
Lemma lem3889328 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3889329 {_100607 : Type'} (P : type686 _100607) : (term51 _100607 P) = (term46 _100607 P).
Proof. exact (MK_COMB (@lem3889328) (@lem3889327 _100607 P)). Qed.
Lemma lem3889330 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3889331 {_100607 : Type'} (P : type686 _100607) : (term60 _100607 P) = (term61 _100607 P).
Proof. exact (MK_COMB (@lem3889330) (@lem3889329 _100607 P)). Qed.
Lemma lem3889332 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term55 _100607 P n) = ((term15 _100607 P) = (P (@EMPTY _100607))).
Proof. exact (eq_refl (term55 _100607 P n)). Qed.
Lemma lem3889333 {_100607 : Type'} (P : type686 _100607) : (term62 _100607 P) = (term53 _100607 P).
Proof. exact (fun_ext (fun n : nat => @lem3889332 _100607 n P)). Qed.
Lemma lem3889334 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3889335 {_100607 : Type'} (P : type686 _100607) : (term63 _100607 P) = (term64 _100607 P).
Proof. exact (MK_COMB (@lem3889334) (@lem3889333 _100607 P)). Qed.
Lemma lem3889336 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3889337 {_100607 : Type'} (P : type686 _100607) : (term65 _100607 P) = (term66 _100607 P).
Proof. exact (MK_COMB (@lem3889336) (@lem3889335 _100607 P)). Qed.
Lemma lem3889338 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term57 _100607 P n) = ((term29 _100607 n P) = (term32 _100607 n P)).
Proof. exact (eq_refl (term57 _100607 P n)). Qed.
Lemma lem3889339 {_100607 : Type'} (P : type686 _100607) : (term67 _100607 P) = (term54 _100607 P).
Proof. exact (fun_ext (fun n : nat => @lem3889338 _100607 n P)). Qed.
Lemma lem3889340 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3889341 {_100607 : Type'} (P : type686 _100607) : (term68 _100607 P) = (term69 _100607 P).
Proof. exact (MK_COMB (@lem3889340) (@lem3889339 _100607 P)). Qed.
Lemma lem3889342 {_100607 : Type'} (P : type686 _100607) : (term52 _100607 P) = (term70 _100607 P).
Proof. exact (MK_COMB (@lem3889337 _100607 P) (@lem3889341 _100607 P)). Qed.
Lemma lem3889343 {_100607 : Type'} (P : type686 _100607) : ((term51 _100607 P) = (term52 _100607 P)) = ((term46 _100607 P) = (term70 _100607 P)).
Proof. exact (MK_COMB (@lem3889331 _100607 P) (@lem3889342 _100607 P)). Qed.
Lemma lem3889344 {_100607 : Type'} (P : type686 _100607) : (term46 _100607 P) = (term70 _100607 P).
Proof. exact (EQ_MP (@lem3889343 _100607 P) (@lem3889321 _100607 P)). Qed.
Lemma lem3889348 {A : Type'} (t : Prop) : (term71 A t) = t.
Proof. exact (EQ_MP (@lem16458 A t) (@lem16457 A t)). Qed.
Lemma lem3889349 (t : Prop) : (term72 t) = t.
Proof. exact (@lem3889348 nat t). Qed.
Lemma lem3889350 {_100607 : Type'} (P : type686 _100607) : (term64 _100607 P) = ((term15 _100607 P) = (P (@EMPTY _100607))).
Proof. exact (@lem3889349 ((term15 _100607 P) = (P (@EMPTY _100607)))). Qed.
Lemma lem3889385 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3889386 {_100607 : Type'} (P : type686 _100607) : (term66 _100607 P) = (term19 _100607 P).
Proof. exact (MK_COMB (@lem3889385) (@lem3889350 _100607 P)). Qed.
Lemma lem3889537 {_100607 : Type'} (P : type686 _100607) : (term69 _100607 P) = (term69 _100607 P).
Proof. exact (eq_refl (term69 _100607 P)). Qed.
Lemma lem3889538 {_100607 : Type'} (P : type686 _100607) : (term70 _100607 P) = (term73 _100607 P).
Proof. exact (MK_COMB (@lem3889386 _100607 P) (@lem3889537 _100607 P)). Qed.
Lemma lem3889541 {_100607 : Type'} (P : type686 _100607) : (term46 _100607 P) = (term73 _100607 P).
Proof. exact (TRANS (@lem3889344 _100607 P) (@lem3889538 _100607 P)). Qed.
Lemma lem3889542 {_100607 : Type'} (P : type686 _100607) : (term45 _100607 P) = (term73 _100607 P).
Proof. exact (TRANS (@lem3889317 _100607 P) (@lem3889541 _100607 P)). Qed.
Lemma lem3889543 {_100607 : Type'} : (term74 _100607) = (term75 _100607).
Proof. exact (fun_ext (fun P : type686 _100607 => @lem3889542 _100607 P)). Qed.
Lemma lem3889544 {_100607 : Type'} : (@all ((_100607 -> Prop) -> Prop)) = (@all ((_100607 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_100607 -> Prop) -> Prop))). Qed.
Lemma lem3889545 {_100607 : Type'} : (term76 _100607) = (term77 _100607).
Proof. exact (MK_COMB (@lem3889544 _100607) (@lem3889543 _100607)). Qed.
Lemma lem3889547 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term47 A P Q) = (term48 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem3889548 {_100607 : Type'} (P : type180 _100607) (Q : type180 _100607) : (term78 _100607 P Q) = (term79 _100607 P Q).
Proof. exact (@lem3889547 (type686 _100607) P Q). Qed.
Lemma lem3889549 {_100607 : Type'} : (term80 _100607) = (term81 _100607).
Proof. exact (@lem3889548 _100607 (term82 _100607) (term83 _100607)). Qed.
Lemma lem3889550 {_100607 : Type'} (P : type686 _100607) : (term84 _100607 P) = ((term15 _100607 P) = (P (@EMPTY _100607))).
Proof. exact (eq_refl (term84 _100607 P)). Qed.
Lemma lem3889551 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3889552 {_100607 : Type'} (P : type686 _100607) : (term85 _100607 P) = (term19 _100607 P).
Proof. exact (MK_COMB (@lem3889551) (@lem3889550 _100607 P)). Qed.
Lemma lem3889553 {_100607 : Type'} (P : type686 _100607) : (term86 _100607 P) = (term69 _100607 P).
Proof. exact (eq_refl (term86 _100607 P)). Qed.
Lemma lem3889554 {_100607 : Type'} (P : type686 _100607) : (term87 _100607 P) = (term73 _100607 P).
Proof. exact (MK_COMB (@lem3889552 _100607 P) (@lem3889553 _100607 P)). Qed.
Lemma lem3889555 {_100607 : Type'} : (term88 _100607) = (term75 _100607).
Proof. exact (fun_ext (fun P : type686 _100607 => @lem3889554 _100607 P)). Qed.
Lemma lem3889556 {_100607 : Type'} : (@all ((_100607 -> Prop) -> Prop)) = (@all ((_100607 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_100607 -> Prop) -> Prop))). Qed.
Lemma lem3889557 {_100607 : Type'} : (term80 _100607) = (term77 _100607).
Proof. exact (MK_COMB (@lem3889556 _100607) (@lem3889555 _100607)). Qed.
Lemma lem3889558 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3889559 {_100607 : Type'} : (term89 _100607) = (term90 _100607).
Proof. exact (MK_COMB (@lem3889558) (@lem3889557 _100607)). Qed.
Lemma lem3889560 {_100607 : Type'} (P : type686 _100607) : (term84 _100607 P) = ((term15 _100607 P) = (P (@EMPTY _100607))).
Proof. exact (eq_refl (term84 _100607 P)). Qed.
Lemma lem3889561 {_100607 : Type'} : (term91 _100607) = (term82 _100607).
Proof. exact (fun_ext (fun P : type686 _100607 => @lem3889560 _100607 P)). Qed.
Lemma lem3889562 {_100607 : Type'} : (@all ((_100607 -> Prop) -> Prop)) = (@all ((_100607 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_100607 -> Prop) -> Prop))). Qed.
Lemma lem3889563 {_100607 : Type'} : (term92 _100607) = (term93 _100607).
Proof. exact (MK_COMB (@lem3889562 _100607) (@lem3889561 _100607)). Qed.
Lemma lem3889564 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3889565 {_100607 : Type'} : (term94 _100607) = (term95 _100607).
Proof. exact (MK_COMB (@lem3889564) (@lem3889563 _100607)). Qed.
Lemma lem3889566 {_100607 : Type'} (P : type686 _100607) : (term86 _100607 P) = (term69 _100607 P).
Proof. exact (eq_refl (term86 _100607 P)). Qed.
Lemma lem3889567 {_100607 : Type'} : (term96 _100607) = (term83 _100607).
Proof. exact (fun_ext (fun P : type686 _100607 => @lem3889566 _100607 P)). Qed.
Lemma lem3889568 {_100607 : Type'} : (@all ((_100607 -> Prop) -> Prop)) = (@all ((_100607 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_100607 -> Prop) -> Prop))). Qed.
Lemma lem3889569 {_100607 : Type'} : (term97 _100607) = (term98 _100607).
Proof. exact (MK_COMB (@lem3889568 _100607) (@lem3889567 _100607)). Qed.
Lemma lem3889570 {_100607 : Type'} : (term81 _100607) = (term99 _100607).
Proof. exact (MK_COMB (@lem3889565 _100607) (@lem3889569 _100607)). Qed.
Lemma lem3889571 {_100607 : Type'} : ((term80 _100607) = (term81 _100607)) = ((term77 _100607) = (term99 _100607)).
Proof. exact (MK_COMB (@lem3889559 _100607) (@lem3889570 _100607)). Qed.
Lemma lem3889572 {_100607 : Type'} : (term77 _100607) = (term99 _100607).
Proof. exact (EQ_MP (@lem3889571 _100607) (@lem3889549 _100607)). Qed.
Lemma lem3889771 {_100607 : Type'} : (term76 _100607) = (term99 _100607).
Proof. exact (TRANS (@lem3889545 _100607) (@lem3889572 _100607)). Qed.
Lemma lem3889782 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) (s : _100607 -> Prop) : (term100 _100607 n P a s) = (term100 _100607 n P a s).
Proof. exact (eq_refl (term100 _100607 n P a s)). Qed.
Lemma lem3889783 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) : (term101 _100607 n P a) = (term101 _100607 n P a).
Proof. exact (fun_ext (fun s : _100607 -> Prop => @lem3889782 _100607 n P a s)). Qed.
Lemma lem3889784 {_100607 : Type'} : (@ex (_100607 -> Prop)) = (@ex (_100607 -> Prop)).
Proof. exact (eq_refl (@ex (_100607 -> Prop))). Qed.
Lemma lem3889785 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) : (term102 _100607 n P a) = (term102 _100607 n P a).
Proof. exact (MK_COMB (@lem3889784 _100607) (@lem3889783 _100607 n P a)). Qed.
Lemma lem3889786 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term103 _100607 n P) = (term103 _100607 n P).
Proof. exact (fun_ext (fun a : _100607 => @lem3889785 _100607 n P a)). Qed.
Lemma lem3889787 {_100607 : Type'} : (@ex _100607) = (@ex _100607).
Proof. exact (eq_refl (@ex _100607)). Qed.
Lemma lem3889788 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term32 _100607 n P) = (term32 _100607 n P).
Proof. exact (MK_COMB (@lem3889787 _100607) (@lem3889786 _100607 n P)). Qed.
Lemma lem3889789 {_100607 : Type'} (P : type686 _100607) (s : _100607 -> Prop) : (P s) = (P s).
Proof. exact (eq_refl (P s)). Qed.
Lemma lem3889800 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) (a : _100607) (t : _100607 -> Prop) : (term104 _100607 n s a t) = (term104 _100607 n s a t).
Proof. exact (eq_refl (term104 _100607 n s a t)). Qed.
Lemma lem3889801 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) (a : _100607) : (term105 _100607 n s a) = (term105 _100607 n s a).
Proof. exact (fun_ext (fun t : _100607 -> Prop => @lem3889800 _100607 n s a t)). Qed.
Lemma lem3889802 {_100607 : Type'} : (@ex (_100607 -> Prop)) = (@ex (_100607 -> Prop)).
Proof. exact (eq_refl (@ex (_100607 -> Prop))). Qed.
Lemma lem3889803 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) (a : _100607) : (term106 _100607 n s a) = (term106 _100607 n s a).
Proof. exact (MK_COMB (@lem3889802 _100607) (@lem3889801 _100607 n s a)). Qed.
Lemma lem3889804 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) : (term107 _100607 n s) = (term107 _100607 n s).
Proof. exact (fun_ext (fun a : _100607 => @lem3889803 _100607 n s a)). Qed.
Lemma lem3889805 {_100607 : Type'} : (@ex _100607) = (@ex _100607).
Proof. exact (eq_refl (@ex _100607)). Qed.
Lemma lem3889806 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) : (term21 _100607 n s) = (term21 _100607 n s).
Proof. exact (MK_COMB (@lem3889805 _100607) (@lem3889804 _100607 n s)). Qed.
Lemma lem3889807 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3889808 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) : (term23 _100607 n s) = (term23 _100607 n s).
Proof. exact (MK_COMB (@lem3889807) (@lem3889806 _100607 n s)). Qed.
Lemma lem3889809 {_100607 : Type'} (n : nat) (P : type686 _100607) (s : _100607 -> Prop) : (term25 _100607 n P s) = (term25 _100607 n P s).
Proof. exact (MK_COMB (@lem3889808 _100607 n s) (@lem3889789 _100607 P s)). Qed.
Lemma lem3889810 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term27 _100607 n P) = (term27 _100607 n P).
Proof. exact (fun_ext (fun s : _100607 -> Prop => @lem3889809 _100607 n P s)). Qed.
Lemma lem3889811 {_100607 : Type'} : (@ex (_100607 -> Prop)) = (@ex (_100607 -> Prop)).
Proof. exact (eq_refl (@ex (_100607 -> Prop))). Qed.
Lemma lem3889812 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term29 _100607 n P) = (term29 _100607 n P).
Proof. exact (MK_COMB (@lem3889811 _100607) (@lem3889810 _100607 n P)). Qed.
Lemma lem3889813 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3889814 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term31 _100607 n P) = (term31 _100607 n P).
Proof. exact (MK_COMB (@lem3889813) (@lem3889812 _100607 n P)). Qed.
Lemma lem3889815 {_100607 : Type'} (n : nat) (P : type686 _100607) : ((term29 _100607 n P) = (term32 _100607 n P)) = ((term29 _100607 n P) = (term32 _100607 n P)).
Proof. exact (MK_COMB (@lem3889814 _100607 n P) (@lem3889788 _100607 n P)). Qed.
Lemma lem3889816 {_100607 : Type'} (P : type686 _100607) : (term54 _100607 P) = (term54 _100607 P).
Proof. exact (fun_ext (fun n : nat => @lem3889815 _100607 n P)). Qed.
Lemma lem3889817 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3889818 {_100607 : Type'} (P : type686 _100607) : (term69 _100607 P) = (term69 _100607 P).
Proof. exact (MK_COMB (@lem3889817) (@lem3889816 _100607 P)). Qed.
Lemma lem3889819 {_100607 : Type'} : (term83 _100607) = (term83 _100607).
Proof. exact (fun_ext (fun P : type686 _100607 => @lem3889818 _100607 P)). Qed.
Lemma lem3889820 {_100607 : Type'} : (@all ((_100607 -> Prop) -> Prop)) = (@all ((_100607 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_100607 -> Prop) -> Prop))). Qed.
Lemma lem3889821 {_100607 : Type'} : (term98 _100607) = (term98 _100607).
Proof. exact (MK_COMB (@lem3889820 _100607) (@lem3889819 _100607)). Qed.
Lemma lem3889822 {_100607 : Type'} (P : type686 _100607) : (P (@EMPTY _100607)) = (P (@EMPTY _100607)).
Proof. exact (eq_refl (P (@EMPTY _100607))). Qed.
Lemma lem3889827 {_100607 : Type'} (P : type686 _100607) (s : _100607 -> Prop) : (term11 _100607 P s) = (term11 _100607 P s).
Proof. exact (eq_refl (term11 _100607 P s)). Qed.
Lemma lem3889828 {_100607 : Type'} (P : type686 _100607) : (term13 _100607 P) = (term13 _100607 P).
Proof. exact (fun_ext (fun s : _100607 -> Prop => @lem3889827 _100607 P s)). Qed.
Lemma lem3889829 {_100607 : Type'} : (@ex (_100607 -> Prop)) = (@ex (_100607 -> Prop)).
Proof. exact (eq_refl (@ex (_100607 -> Prop))). Qed.
Lemma lem3889830 {_100607 : Type'} (P : type686 _100607) : (term15 _100607 P) = (term15 _100607 P).
Proof. exact (MK_COMB (@lem3889829 _100607) (@lem3889828 _100607 P)). Qed.
Lemma lem3889831 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3889832 {_100607 : Type'} (P : type686 _100607) : (term17 _100607 P) = (term17 _100607 P).
Proof. exact (MK_COMB (@lem3889831) (@lem3889830 _100607 P)). Qed.
Lemma lem3889833 {_100607 : Type'} (P : type686 _100607) : ((term15 _100607 P) = (P (@EMPTY _100607))) = ((term15 _100607 P) = (P (@EMPTY _100607))).
Proof. exact (MK_COMB (@lem3889832 _100607 P) (@lem3889822 _100607 P)). Qed.
Lemma lem3889834 {_100607 : Type'} : (term82 _100607) = (term82 _100607).
Proof. exact (fun_ext (fun P : type686 _100607 => @lem3889833 _100607 P)). Qed.
Lemma lem3889835 {_100607 : Type'} : (@all ((_100607 -> Prop) -> Prop)) = (@all ((_100607 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_100607 -> Prop) -> Prop))). Qed.
Lemma lem3889836 {_100607 : Type'} : (term93 _100607) = (term93 _100607).
Proof. exact (MK_COMB (@lem3889835 _100607) (@lem3889834 _100607)). Qed.
Lemma lem3889837 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3889838 {_100607 : Type'} : (term95 _100607) = (term95 _100607).
Proof. exact (MK_COMB (@lem3889837) (@lem3889836 _100607)). Qed.
Lemma lem3889839 {_100607 : Type'} : (term99 _100607) = (term99 _100607).
Proof. exact (MK_COMB (@lem3889838 _100607) (@lem3889821 _100607)). Qed.
Lemma lem3889910 {_100607 : Type'} : (term76 _100607) = (term99 _100607).
Proof. exact (TRANS (@lem3889771 _100607) (@lem3889839 _100607)). Qed.
Lemma lem3889911 {_100607 : Type'} : (term99 _100607) = (term76 _100607).
Proof. exact (SYM (@lem3889910 _100607)). Qed.
Lemma lem3889913 (p : Prop) : p = (term35 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3889914 {_100607 : Type'} : (term99 _100607) = (term108 _100607).
Proof. exact (@lem3889913 (term99 _100607)). Qed.
Lemma lem3889915 {_100607 : Type'} : (term108 _100607) = (term99 _100607).
Proof. exact (SYM (@lem3889914 _100607)). Qed.
Lemma lem3889916 {_100607 : Type'} (h1 : term109 _100607) : term109 _100607.
Proof. exact (h1). Qed.
Lemma lem3889925 {_100607 : Type'} (P : type686 _100607) (s : _100607 -> Prop) : (term110 _100607 P s) = (term111 _100607 P s).
Proof. exact (@lem17045 (s = (@EMPTY _100607)) (P s)). Qed.
Lemma lem3889928 {_100607 : Type'} (P : type686 _100607) (s : _100607 -> Prop) : (term11 _100607 P s) = (term11 _100607 P s).
Proof. exact (eq_refl (term11 _100607 P s)). Qed.
Lemma lem3889929 {_100607 : Type'} (P : type686 _100607) : (term112 _100607 P) = (term113 _100607 P).
Proof. exact (@lem18394 (_100607 -> Prop) P). Qed.
Lemma lem3889930 {_100607 : Type'} (P : type686 _100607) : (term114 _100607 P) = (term115 _100607 P).
Proof. exact (@lem3889929 _100607 (term13 _100607 P)). Qed.
Lemma lem3889931 {_100607 : Type'} (P : type686 _100607) (s : _100607 -> Prop) : (term116 _100607 P s) = (term11 _100607 P s).
Proof. exact (eq_refl (term116 _100607 P s)). Qed.
Lemma lem3889932 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3889933 {_100607 : Type'} (P : type686 _100607) (s : _100607 -> Prop) : (term117 _100607 P s) = (term110 _100607 P s).
Proof. exact (MK_COMB (@lem3889932) (@lem3889931 _100607 P s)). Qed.
Lemma lem3889934 {_100607 : Type'} (P : type686 _100607) (s : _100607 -> Prop) : (term117 _100607 P s) = (term111 _100607 P s).
Proof. exact (TRANS (@lem3889933 _100607 P s) (@lem3889925 _100607 P s)). Qed.
Lemma lem3889935 {_100607 : Type'} (P : type686 _100607) : (term118 _100607 P) = (term119 _100607 P).
Proof. exact (fun_ext (fun s : _100607 -> Prop => @lem3889934 _100607 P s)). Qed.
Lemma lem3889936 {_100607 : Type'} : (@all (_100607 -> Prop)) = (@all (_100607 -> Prop)).
Proof. exact (eq_refl (@all (_100607 -> Prop))). Qed.
Lemma lem3889937 {_100607 : Type'} (P : type686 _100607) : (term115 _100607 P) = (term120 _100607 P).
Proof. exact (MK_COMB (@lem3889936 _100607) (@lem3889935 _100607 P)). Qed.
Lemma lem3889938 {_100607 : Type'} (P : type686 _100607) : (term114 _100607 P) = (term120 _100607 P).
Proof. exact (TRANS (@lem3889930 _100607 P) (@lem3889937 _100607 P)). Qed.
Lemma lem3889939 {_100607 : Type'} (P : type686 _100607) : (term13 _100607 P) = (term13 _100607 P).
Proof. exact (fun_ext (fun s : _100607 -> Prop => @lem3889928 _100607 P s)). Qed.
Lemma lem3889940 {_100607 : Type'} : (@ex (_100607 -> Prop)) = (@ex (_100607 -> Prop)).
Proof. exact (eq_refl (@ex (_100607 -> Prop))). Qed.
Lemma lem3889941 {_100607 : Type'} (P : type686 _100607) : (term15 _100607 P) = (term15 _100607 P).
Proof. exact (MK_COMB (@lem3889940 _100607) (@lem3889939 _100607 P)). Qed.
Lemma lem3889942 {_100607 : Type'} (P : type686 _100607) : (term121 _100607 P) = (term121 _100607 P).
Proof. exact (eq_refl (term121 _100607 P)). Qed.
Lemma lem3889943 {_100607 : Type'} (P : type686 _100607) : (P (@EMPTY _100607)) = (P (@EMPTY _100607)).
Proof. exact (eq_refl (P (@EMPTY _100607))). Qed.
Lemma lem3889944 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3889945 {_100607 : Type'} (P : type686 _100607) : (term122 _100607 P) = (term123 _100607 P).
Proof. exact (MK_COMB (@lem3889944) (@lem3889938 _100607 P)). Qed.
Lemma lem3889946 {_100607 : Type'} (P : type686 _100607) : (term124 _100607 P) = (term125 _100607 P).
Proof. exact (MK_COMB (@lem3889945 _100607 P) (@lem3889943 _100607 P)). Qed.
Lemma lem3889947 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3889948 {_100607 : Type'} (P : type686 _100607) : (term126 _100607 P) = (term126 _100607 P).
Proof. exact (MK_COMB (@lem3889947) (@lem3889941 _100607 P)). Qed.
Lemma lem3889949 {_100607 : Type'} (P : type686 _100607) : (term127 _100607 P) = (term127 _100607 P).
Proof. exact (MK_COMB (@lem3889948 _100607 P) (@lem3889942 _100607 P)). Qed.
Lemma lem3889950 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3889951 {_100607 : Type'} (P : type686 _100607) : (term128 _100607 P) = (term128 _100607 P).
Proof. exact (MK_COMB (@lem3889950) (@lem3889949 _100607 P)). Qed.
Lemma lem3889952 {_100607 : Type'} (P : type686 _100607) : (term129 _100607 P) = (term130 _100607 P).
Proof. exact (MK_COMB (@lem3889951 _100607 P) (@lem3889946 _100607 P)). Qed.
Lemma lem3889953 {_100607 : Type'} (P : type686 _100607) : (term131 _100607 P) = (term129 _100607 P).
Proof. exact (@lem17646 (term15 _100607 P) (P (@EMPTY _100607))). Qed.
Lemma lem3889954 {_100607 : Type'} (P : type686 _100607) : (term131 _100607 P) = (term130 _100607 P).
Proof. exact (TRANS (@lem3889953 _100607 P) (@lem3889952 _100607 P)). Qed.
Lemma lem3889955 {_100607 : Type'} (P : type180 _100607) : (term132 _100607 P) = (term133 _100607 P).
Proof. exact (@lem18392 (type686 _100607) P). Qed.
Lemma lem3889956 {_100607 : Type'} : (term134 _100607) = (term135 _100607).
Proof. exact (@lem3889955 _100607 (term82 _100607)). Qed.
Lemma lem3889957 {_100607 : Type'} (P : type686 _100607) : (term84 _100607 P) = ((term15 _100607 P) = (P (@EMPTY _100607))).
Proof. exact (eq_refl (term84 _100607 P)). Qed.
Lemma lem3889958 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3889959 {_100607 : Type'} (P : type686 _100607) : (term136 _100607 P) = (term131 _100607 P).
Proof. exact (MK_COMB (@lem3889958) (@lem3889957 _100607 P)). Qed.
Lemma lem3889960 {_100607 : Type'} (P : type686 _100607) : (term136 _100607 P) = (term130 _100607 P).
Proof. exact (TRANS (@lem3889959 _100607 P) (@lem3889954 _100607 P)). Qed.
Lemma lem3889961 {_100607 : Type'} : (term137 _100607) = (term138 _100607).
Proof. exact (fun_ext (fun P : type686 _100607 => @lem3889960 _100607 P)). Qed.
Lemma lem3889962 {_100607 : Type'} : (@ex ((_100607 -> Prop) -> Prop)) = (@ex ((_100607 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_100607 -> Prop) -> Prop))). Qed.
Lemma lem3889963 {_100607 : Type'} : (term135 _100607) = (term139 _100607).
Proof. exact (MK_COMB (@lem3889962 _100607) (@lem3889961 _100607)). Qed.
Lemma lem3889964 {_100607 : Type'} : (term134 _100607) = (term139 _100607).
Proof. exact (TRANS (@lem3889956 _100607) (@lem3889963 _100607)). Qed.
Lemma lem3889970 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) : (term140 _100607 a t) = (@IN _100607 a t).
Proof. exact (@lem16933 (@IN _100607 a t)). Qed.
Lemma lem3889971 {_100607 : Type'} (s : _100607 -> Prop) (a : _100607) (t : _100607 -> Prop) : (term141 _100607 s a t) = (term141 _100607 s a t).
Proof. exact (eq_refl (term141 _100607 s a t)). Qed.
Lemma lem3889973 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3889974 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) : (term142 _100607 a t) = (term143 _100607 a t).
Proof. exact (MK_COMB (@lem3889973) (@lem3889970 _100607 a t)). Qed.
Lemma lem3889975 {_100607 : Type'} (s : _100607 -> Prop) (a : _100607) (t : _100607 -> Prop) : (term144 _100607 s a t) = (term145 _100607 s a t).
Proof. exact (MK_COMB (@lem3889974 _100607 a t) (@lem3889971 _100607 s a t)). Qed.
Lemma lem3889976 {_100607 : Type'} (s : _100607 -> Prop) (a : _100607) (t : _100607 -> Prop) : (term146 _100607 s a t) = (term144 _100607 s a t).
Proof. exact (@lem17045 (term147 _100607 a t) (s = (@INSERT _100607 a t))). Qed.
Lemma lem3889977 {_100607 : Type'} (s : _100607 -> Prop) (a : _100607) (t : _100607 -> Prop) : (term146 _100607 s a t) = (term145 _100607 s a t).
Proof. exact (TRANS (@lem3889976 _100607 s a t) (@lem3889975 _100607 s a t)). Qed.
Lemma lem3889982 {_100607 : Type'} (t : _100607 -> Prop) (n : nat) : (term148 _100607 t n) = (term148 _100607 t n).
Proof. exact (eq_refl (term148 _100607 t n)). Qed.
Lemma lem3889983 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) (a : _100607) (t : _100607 -> Prop) : (term149 _100607 n s a t) = (term150 _100607 n s a t).
Proof. exact (MK_COMB (@lem3889982 _100607 t n) (@lem3889977 _100607 s a t)). Qed.
Lemma lem3889984 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) (a : _100607) (t : _100607 -> Prop) : (term151 _100607 n s a t) = (term149 _100607 n s a t).
Proof. exact (@lem17045 (@HAS_SIZE _100607 t n) (term152 _100607 s a t)). Qed.
Lemma lem3889985 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) (a : _100607) (t : _100607 -> Prop) : (term151 _100607 n s a t) = (term150 _100607 n s a t).
Proof. exact (TRANS (@lem3889984 _100607 n s a t) (@lem3889983 _100607 n s a t)). Qed.
Lemma lem3889988 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) (a : _100607) (t : _100607 -> Prop) : (term104 _100607 n s a t) = (term104 _100607 n s a t).
Proof. exact (eq_refl (term104 _100607 n s a t)). Qed.
Lemma lem3889989 {_100607 : Type'} (P : type686 _100607) : (term112 _100607 P) = (term113 _100607 P).
Proof. exact (@lem18394 (_100607 -> Prop) P). Qed.
Lemma lem3889990 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) (a : _100607) : (term153 _100607 n s a) = (term154 _100607 n s a).
Proof. exact (@lem3889989 _100607 (term105 _100607 n s a)). Qed.
Lemma lem3889991 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) (a : _100607) (t : _100607 -> Prop) : (term155 _100607 n s a t) = (term104 _100607 n s a t).
Proof. exact (eq_refl (term155 _100607 n s a t)). Qed.
Lemma lem3889992 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3889993 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) (a : _100607) (t : _100607 -> Prop) : (term156 _100607 n s a t) = (term151 _100607 n s a t).
Proof. exact (MK_COMB (@lem3889992) (@lem3889991 _100607 n s a t)). Qed.
Lemma lem3889994 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) (a : _100607) (t : _100607 -> Prop) : (term156 _100607 n s a t) = (term150 _100607 n s a t).
Proof. exact (TRANS (@lem3889993 _100607 n s a t) (@lem3889985 _100607 n s a t)). Qed.
Lemma lem3889995 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) (a : _100607) : (term157 _100607 n s a) = (term158 _100607 n s a).
Proof. exact (fun_ext (fun t : _100607 -> Prop => @lem3889994 _100607 n s a t)). Qed.
Lemma lem3889996 {_100607 : Type'} : (@all (_100607 -> Prop)) = (@all (_100607 -> Prop)).
Proof. exact (eq_refl (@all (_100607 -> Prop))). Qed.
Lemma lem3889997 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) (a : _100607) : (term154 _100607 n s a) = (term159 _100607 n s a).
Proof. exact (MK_COMB (@lem3889996 _100607) (@lem3889995 _100607 n s a)). Qed.
Lemma lem3889998 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) (a : _100607) : (term153 _100607 n s a) = (term159 _100607 n s a).
Proof. exact (TRANS (@lem3889990 _100607 n s a) (@lem3889997 _100607 n s a)). Qed.
Lemma lem3889999 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) (a : _100607) : (term105 _100607 n s a) = (term105 _100607 n s a).
Proof. exact (fun_ext (fun t : _100607 -> Prop => @lem3889988 _100607 n s a t)). Qed.
Lemma lem3890000 {_100607 : Type'} : (@ex (_100607 -> Prop)) = (@ex (_100607 -> Prop)).
Proof. exact (eq_refl (@ex (_100607 -> Prop))). Qed.
Lemma lem3890001 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) (a : _100607) : (term106 _100607 n s a) = (term106 _100607 n s a).
Proof. exact (MK_COMB (@lem3890000 _100607) (@lem3889999 _100607 n s a)). Qed.
Lemma lem3890002 {_100607 : Type'} (P : _100607 -> Prop) : (term160 _100607 P) = (term161 _100607 P).
Proof. exact (@lem18394 _100607 P). Qed.
Lemma lem3890003 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) : (term162 _100607 n s) = (term163 _100607 n s).
Proof. exact (@lem3890002 _100607 (term107 _100607 n s)). Qed.
Lemma lem3890004 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) (a : _100607) : (term164 _100607 n s a) = (term106 _100607 n s a).
Proof. exact (eq_refl (term164 _100607 n s a)). Qed.
Lemma lem3890005 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3890006 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) (a : _100607) : (term165 _100607 n s a) = (term153 _100607 n s a).
Proof. exact (MK_COMB (@lem3890005) (@lem3890004 _100607 n s a)). Qed.
Lemma lem3890007 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) (a : _100607) : (term165 _100607 n s a) = (term159 _100607 n s a).
Proof. exact (TRANS (@lem3890006 _100607 n s a) (@lem3889998 _100607 n s a)). Qed.
Lemma lem3890008 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) : (term166 _100607 n s) = (term167 _100607 n s).
Proof. exact (fun_ext (fun a : _100607 => @lem3890007 _100607 n s a)). Qed.
Lemma lem3890009 {_100607 : Type'} : (@all _100607) = (@all _100607).
Proof. exact (eq_refl (@all _100607)). Qed.
Lemma lem3890010 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) : (term163 _100607 n s) = (term168 _100607 n s).
Proof. exact (MK_COMB (@lem3890009 _100607) (@lem3890008 _100607 n s)). Qed.
Lemma lem3890011 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) : (term162 _100607 n s) = (term168 _100607 n s).
Proof. exact (TRANS (@lem3890003 _100607 n s) (@lem3890010 _100607 n s)). Qed.
Lemma lem3890012 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) : (term107 _100607 n s) = (term107 _100607 n s).
Proof. exact (fun_ext (fun a : _100607 => @lem3890001 _100607 n s a)). Qed.
Lemma lem3890013 {_100607 : Type'} : (@ex _100607) = (@ex _100607).
Proof. exact (eq_refl (@ex _100607)). Qed.
Lemma lem3890014 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) : (term21 _100607 n s) = (term21 _100607 n s).
Proof. exact (MK_COMB (@lem3890013 _100607) (@lem3890012 _100607 n s)). Qed.
Lemma lem3890015 {_100607 : Type'} (P : type686 _100607) (s : _100607 -> Prop) : (term169 _100607 P s) = (term169 _100607 P s).
Proof. exact (eq_refl (term169 _100607 P s)). Qed.
Lemma lem3890016 {_100607 : Type'} (P : type686 _100607) (s : _100607 -> Prop) : (P s) = (P s).
Proof. exact (eq_refl (P s)). Qed.
Lemma lem3890017 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3890018 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) : (term170 _100607 n s) = (term171 _100607 n s).
Proof. exact (MK_COMB (@lem3890017) (@lem3890011 _100607 n s)). Qed.
Lemma lem3890019 {_100607 : Type'} (n : nat) (P : type686 _100607) (s : _100607 -> Prop) : (term172 _100607 n P s) = (term173 _100607 n P s).
Proof. exact (MK_COMB (@lem3890018 _100607 n s) (@lem3890015 _100607 P s)). Qed.
Lemma lem3890020 {_100607 : Type'} (n : nat) (P : type686 _100607) (s : _100607 -> Prop) : (term174 _100607 n P s) = (term172 _100607 n P s).
Proof. exact (@lem17045 (term21 _100607 n s) (P s)). Qed.
Lemma lem3890021 {_100607 : Type'} (n : nat) (P : type686 _100607) (s : _100607 -> Prop) : (term174 _100607 n P s) = (term173 _100607 n P s).
Proof. exact (TRANS (@lem3890020 _100607 n P s) (@lem3890019 _100607 n P s)). Qed.
Lemma lem3890022 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3890023 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) : (term23 _100607 n s) = (term23 _100607 n s).
Proof. exact (MK_COMB (@lem3890022) (@lem3890014 _100607 n s)). Qed.
Lemma lem3890024 {_100607 : Type'} (n : nat) (P : type686 _100607) (s : _100607 -> Prop) : (term25 _100607 n P s) = (term25 _100607 n P s).
Proof. exact (MK_COMB (@lem3890023 _100607 n s) (@lem3890016 _100607 P s)). Qed.
Lemma lem3890025 {_100607 : Type'} (P : type686 _100607) : (term112 _100607 P) = (term113 _100607 P).
Proof. exact (@lem18394 (_100607 -> Prop) P). Qed.
Lemma lem3890026 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term175 _100607 n P) = (term176 _100607 n P).
Proof. exact (@lem3890025 _100607 (term27 _100607 n P)). Qed.
Lemma lem3890027 {_100607 : Type'} (n : nat) (P : type686 _100607) (s : _100607 -> Prop) : (term177 _100607 n P s) = (term25 _100607 n P s).
Proof. exact (eq_refl (term177 _100607 n P s)). Qed.
Lemma lem3890028 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3890029 {_100607 : Type'} (n : nat) (P : type686 _100607) (s : _100607 -> Prop) : (term178 _100607 n P s) = (term174 _100607 n P s).
Proof. exact (MK_COMB (@lem3890028) (@lem3890027 _100607 n P s)). Qed.
Lemma lem3890030 {_100607 : Type'} (n : nat) (P : type686 _100607) (s : _100607 -> Prop) : (term178 _100607 n P s) = (term173 _100607 n P s).
Proof. exact (TRANS (@lem3890029 _100607 n P s) (@lem3890021 _100607 n P s)). Qed.
Lemma lem3890031 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term179 _100607 n P) = (term180 _100607 n P).
Proof. exact (fun_ext (fun s : _100607 -> Prop => @lem3890030 _100607 n P s)). Qed.
Lemma lem3890032 {_100607 : Type'} : (@all (_100607 -> Prop)) = (@all (_100607 -> Prop)).
Proof. exact (eq_refl (@all (_100607 -> Prop))). Qed.
Lemma lem3890033 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term176 _100607 n P) = (term181 _100607 n P).
Proof. exact (MK_COMB (@lem3890032 _100607) (@lem3890031 _100607 n P)). Qed.
Lemma lem3890034 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term175 _100607 n P) = (term181 _100607 n P).
Proof. exact (TRANS (@lem3890026 _100607 n P) (@lem3890033 _100607 n P)). Qed.
Lemma lem3890035 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term27 _100607 n P) = (term27 _100607 n P).
Proof. exact (fun_ext (fun s : _100607 -> Prop => @lem3890024 _100607 n P s)). Qed.
Lemma lem3890036 {_100607 : Type'} : (@ex (_100607 -> Prop)) = (@ex (_100607 -> Prop)).
Proof. exact (eq_refl (@ex (_100607 -> Prop))). Qed.
Lemma lem3890037 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term29 _100607 n P) = (term29 _100607 n P).
Proof. exact (MK_COMB (@lem3890036 _100607) (@lem3890035 _100607 n P)). Qed.
Lemma lem3890043 {_100607 : Type'} (a : _100607) (s : _100607 -> Prop) : (term140 _100607 a s) = (@IN _100607 a s).
Proof. exact (@lem16933 (@IN _100607 a s)). Qed.
Lemma lem3890044 {_100607 : Type'} (P : type686 _100607) (a : _100607) (s : _100607 -> Prop) : (term182 _100607 P a s) = (term182 _100607 P a s).
Proof. exact (eq_refl (term182 _100607 P a s)). Qed.
Lemma lem3890046 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3890047 {_100607 : Type'} (a : _100607) (s : _100607 -> Prop) : (term142 _100607 a s) = (term143 _100607 a s).
Proof. exact (MK_COMB (@lem3890046) (@lem3890043 _100607 a s)). Qed.
Lemma lem3890048 {_100607 : Type'} (P : type686 _100607) (a : _100607) (s : _100607 -> Prop) : (term183 _100607 P a s) = (term184 _100607 P a s).
Proof. exact (MK_COMB (@lem3890047 _100607 a s) (@lem3890044 _100607 P a s)). Qed.
Lemma lem3890049 {_100607 : Type'} (P : type686 _100607) (a : _100607) (s : _100607 -> Prop) : (term185 _100607 P a s) = (term183 _100607 P a s).
Proof. exact (@lem17045 (term147 _100607 a s) (term186 _100607 P a s)). Qed.
Lemma lem3890050 {_100607 : Type'} (P : type686 _100607) (a : _100607) (s : _100607 -> Prop) : (term185 _100607 P a s) = (term184 _100607 P a s).
Proof. exact (TRANS (@lem3890049 _100607 P a s) (@lem3890048 _100607 P a s)). Qed.
Lemma lem3890055 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) : (term148 _100607 s n) = (term148 _100607 s n).
Proof. exact (eq_refl (term148 _100607 s n)). Qed.
Lemma lem3890056 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) (s : _100607 -> Prop) : (term187 _100607 n P a s) = (term188 _100607 n P a s).
Proof. exact (MK_COMB (@lem3890055 _100607 s n) (@lem3890050 _100607 P a s)). Qed.
Lemma lem3890057 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) (s : _100607 -> Prop) : (term189 _100607 n P a s) = (term187 _100607 n P a s).
Proof. exact (@lem17045 (@HAS_SIZE _100607 s n) (term190 _100607 P a s)). Qed.
Lemma lem3890058 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) (s : _100607 -> Prop) : (term189 _100607 n P a s) = (term188 _100607 n P a s).
Proof. exact (TRANS (@lem3890057 _100607 n P a s) (@lem3890056 _100607 n P a s)). Qed.
Lemma lem3890061 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) (s : _100607 -> Prop) : (term100 _100607 n P a s) = (term100 _100607 n P a s).
Proof. exact (eq_refl (term100 _100607 n P a s)). Qed.
Lemma lem3890062 {_100607 : Type'} (P : type686 _100607) : (term112 _100607 P) = (term113 _100607 P).
Proof. exact (@lem18394 (_100607 -> Prop) P). Qed.
Lemma lem3890063 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) : (term191 _100607 n P a) = (term192 _100607 n P a).
Proof. exact (@lem3890062 _100607 (term101 _100607 n P a)). Qed.
Lemma lem3890064 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) (s : _100607 -> Prop) : (term193 _100607 n P a s) = (term100 _100607 n P a s).
Proof. exact (eq_refl (term193 _100607 n P a s)). Qed.
Lemma lem3890065 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3890066 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) (s : _100607 -> Prop) : (term194 _100607 n P a s) = (term189 _100607 n P a s).
Proof. exact (MK_COMB (@lem3890065) (@lem3890064 _100607 n P a s)). Qed.
Lemma lem3890067 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) (s : _100607 -> Prop) : (term194 _100607 n P a s) = (term188 _100607 n P a s).
Proof. exact (TRANS (@lem3890066 _100607 n P a s) (@lem3890058 _100607 n P a s)). Qed.
Lemma lem3890068 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) : (term195 _100607 n P a) = (term196 _100607 n P a).
Proof. exact (fun_ext (fun s : _100607 -> Prop => @lem3890067 _100607 n P a s)). Qed.
Lemma lem3890069 {_100607 : Type'} : (@all (_100607 -> Prop)) = (@all (_100607 -> Prop)).
Proof. exact (eq_refl (@all (_100607 -> Prop))). Qed.
Lemma lem3890070 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) : (term192 _100607 n P a) = (term197 _100607 n P a).
Proof. exact (MK_COMB (@lem3890069 _100607) (@lem3890068 _100607 n P a)). Qed.
Lemma lem3890071 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) : (term191 _100607 n P a) = (term197 _100607 n P a).
Proof. exact (TRANS (@lem3890063 _100607 n P a) (@lem3890070 _100607 n P a)). Qed.
Lemma lem3890072 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) : (term101 _100607 n P a) = (term101 _100607 n P a).
Proof. exact (fun_ext (fun s : _100607 -> Prop => @lem3890061 _100607 n P a s)). Qed.
Lemma lem3890073 {_100607 : Type'} : (@ex (_100607 -> Prop)) = (@ex (_100607 -> Prop)).
Proof. exact (eq_refl (@ex (_100607 -> Prop))). Qed.
Lemma lem3890074 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) : (term102 _100607 n P a) = (term102 _100607 n P a).
Proof. exact (MK_COMB (@lem3890073 _100607) (@lem3890072 _100607 n P a)). Qed.
Lemma lem3890075 {_100607 : Type'} (P : _100607 -> Prop) : (term160 _100607 P) = (term161 _100607 P).
Proof. exact (@lem18394 _100607 P). Qed.
Lemma lem3890076 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term198 _100607 n P) = (term199 _100607 n P).
Proof. exact (@lem3890075 _100607 (term103 _100607 n P)). Qed.
Lemma lem3890077 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) : (term200 _100607 n P a) = (term102 _100607 n P a).
Proof. exact (eq_refl (term200 _100607 n P a)). Qed.
Lemma lem3890078 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3890079 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) : (term201 _100607 n P a) = (term191 _100607 n P a).
Proof. exact (MK_COMB (@lem3890078) (@lem3890077 _100607 n P a)). Qed.
Lemma lem3890080 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) : (term201 _100607 n P a) = (term197 _100607 n P a).
Proof. exact (TRANS (@lem3890079 _100607 n P a) (@lem3890071 _100607 n P a)). Qed.
Lemma lem3890081 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term202 _100607 n P) = (term203 _100607 n P).
Proof. exact (fun_ext (fun a : _100607 => @lem3890080 _100607 n P a)). Qed.
Lemma lem3890082 {_100607 : Type'} : (@all _100607) = (@all _100607).
Proof. exact (eq_refl (@all _100607)). Qed.
Lemma lem3890083 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term199 _100607 n P) = (term204 _100607 n P).
Proof. exact (MK_COMB (@lem3890082 _100607) (@lem3890081 _100607 n P)). Qed.
Lemma lem3890084 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term198 _100607 n P) = (term204 _100607 n P).
Proof. exact (TRANS (@lem3890076 _100607 n P) (@lem3890083 _100607 n P)). Qed.
Lemma lem3890085 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term103 _100607 n P) = (term103 _100607 n P).
Proof. exact (fun_ext (fun a : _100607 => @lem3890074 _100607 n P a)). Qed.
Lemma lem3890086 {_100607 : Type'} : (@ex _100607) = (@ex _100607).
Proof. exact (eq_refl (@ex _100607)). Qed.
Lemma lem3890087 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term32 _100607 n P) = (term32 _100607 n P).
Proof. exact (MK_COMB (@lem3890086 _100607) (@lem3890085 _100607 n P)). Qed.
Lemma lem3890088 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3890089 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term205 _100607 n P) = (term206 _100607 n P).
Proof. exact (MK_COMB (@lem3890088) (@lem3890034 _100607 n P)). Qed.
Lemma lem3890090 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term207 _100607 n P) = (term208 _100607 n P).
Proof. exact (MK_COMB (@lem3890089 _100607 n P) (@lem3890087 _100607 n P)). Qed.
Lemma lem3890091 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3890092 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term209 _100607 n P) = (term209 _100607 n P).
Proof. exact (MK_COMB (@lem3890091) (@lem3890037 _100607 n P)). Qed.
Lemma lem3890093 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term210 _100607 n P) = (term211 _100607 n P).
Proof. exact (MK_COMB (@lem3890092 _100607 n P) (@lem3890084 _100607 n P)). Qed.
Lemma lem3890094 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3890095 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term212 _100607 n P) = (term213 _100607 n P).
Proof. exact (MK_COMB (@lem3890094) (@lem3890093 _100607 n P)). Qed.
Lemma lem3890096 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term214 _100607 n P) = (term215 _100607 n P).
Proof. exact (MK_COMB (@lem3890095 _100607 n P) (@lem3890090 _100607 n P)). Qed.
Lemma lem3890097 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term216 _100607 n P) = (term214 _100607 n P).
Proof. exact (@lem17646 (term29 _100607 n P) (term32 _100607 n P)). Qed.
Lemma lem3890098 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term216 _100607 n P) = (term215 _100607 n P).
Proof. exact (TRANS (@lem3890097 _100607 n P) (@lem3890096 _100607 n P)). Qed.
Lemma lem3890099 (P : nat -> Prop) : (term217 P) = (term218 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem3890100 {_100607 : Type'} (P : type686 _100607) : (term219 _100607 P) = (term220 _100607 P).
Proof. exact (@lem3890099 (term54 _100607 P)). Qed.
Lemma lem3890101 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term57 _100607 P n) = ((term29 _100607 n P) = (term32 _100607 n P)).
Proof. exact (eq_refl (term57 _100607 P n)). Qed.
Lemma lem3890102 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3890103 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term221 _100607 P n) = (term216 _100607 n P).
Proof. exact (MK_COMB (@lem3890102) (@lem3890101 _100607 n P)). Qed.
Lemma lem3890104 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term221 _100607 P n) = (term215 _100607 n P).
Proof. exact (TRANS (@lem3890103 _100607 n P) (@lem3890098 _100607 n P)). Qed.
Lemma lem3890105 {_100607 : Type'} (P : type686 _100607) : (term222 _100607 P) = (term223 _100607 P).
Proof. exact (fun_ext (fun n : nat => @lem3890104 _100607 n P)). Qed.
Lemma lem3890106 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3890107 {_100607 : Type'} (P : type686 _100607) : (term220 _100607 P) = (term224 _100607 P).
Proof. exact (MK_COMB (@lem3890106) (@lem3890105 _100607 P)). Qed.
Lemma lem3890108 {_100607 : Type'} (P : type686 _100607) : (term219 _100607 P) = (term224 _100607 P).
Proof. exact (TRANS (@lem3890100 _100607 P) (@lem3890107 _100607 P)). Qed.
Lemma lem3890109 {_100607 : Type'} (P : type180 _100607) : (term132 _100607 P) = (term133 _100607 P).
Proof. exact (@lem18392 (type686 _100607) P). Qed.
Lemma lem3890110 {_100607 : Type'} : (term225 _100607) = (term226 _100607).
Proof. exact (@lem3890109 _100607 (term83 _100607)). Qed.
Lemma lem3890111 {_100607 : Type'} (P : type686 _100607) : (term86 _100607 P) = (term69 _100607 P).
Proof. exact (eq_refl (term86 _100607 P)). Qed.
Lemma lem3890112 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3890113 {_100607 : Type'} (P : type686 _100607) : (term227 _100607 P) = (term219 _100607 P).
Proof. exact (MK_COMB (@lem3890112) (@lem3890111 _100607 P)). Qed.
Lemma lem3890114 {_100607 : Type'} (P : type686 _100607) : (term227 _100607 P) = (term224 _100607 P).
Proof. exact (TRANS (@lem3890113 _100607 P) (@lem3890108 _100607 P)). Qed.
Lemma lem3890115 {_100607 : Type'} : (term228 _100607) = (term229 _100607).
Proof. exact (fun_ext (fun P : type686 _100607 => @lem3890114 _100607 P)). Qed.
Lemma lem3890116 {_100607 : Type'} : (@ex ((_100607 -> Prop) -> Prop)) = (@ex ((_100607 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_100607 -> Prop) -> Prop))). Qed.
Lemma lem3890117 {_100607 : Type'} : (term226 _100607) = (term230 _100607).
Proof. exact (MK_COMB (@lem3890116 _100607) (@lem3890115 _100607)). Qed.
Lemma lem3890118 {_100607 : Type'} : (term225 _100607) = (term230 _100607).
Proof. exact (TRANS (@lem3890110 _100607) (@lem3890117 _100607)). Qed.
Lemma lem3890119 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3890120 {_100607 : Type'} : (term231 _100607) = (term232 _100607).
Proof. exact (MK_COMB (@lem3890119) (@lem3889964 _100607)). Qed.
Lemma lem3890121 {_100607 : Type'} : (term233 _100607) = (term234 _100607).
Proof. exact (MK_COMB (@lem3890120 _100607) (@lem3890118 _100607)). Qed.
Lemma lem3890122 {_100607 : Type'} : (term109 _100607) = (term233 _100607).
Proof. exact (@lem17045 (term93 _100607) (term98 _100607)). Qed.
Lemma lem3890123 {_100607 : Type'} : (term109 _100607) = (term234 _100607).
Proof. exact (TRANS (@lem3890122 _100607) (@lem3890121 _100607)). Qed.
Lemma lem3890125 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term235 A P Q) = (term236 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3890126 {_100607 : Type'} (P : type180 _100607) (Q : type180 _100607) : (term237 _100607 P Q) = (term238 _100607 P Q).
Proof. exact (@lem3890125 (type686 _100607) P Q). Qed.
Lemma lem3890127 {_100607 : Type'} : (term239 _100607) = (term240 _100607).
Proof. exact (@lem3890126 _100607 (term241 _100607) (term242 _100607)). Qed.
Lemma lem3890128 {_100607 : Type'} (P : type686 _100607) : (term243 _100607 P) = (term127 _100607 P).
Proof. exact (eq_refl (term243 _100607 P)). Qed.
Lemma lem3890129 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3890130 {_100607 : Type'} (P : type686 _100607) : (term244 _100607 P) = (term128 _100607 P).
Proof. exact (MK_COMB (@lem3890129) (@lem3890128 _100607 P)). Qed.
Lemma lem3890131 {_100607 : Type'} (P : type686 _100607) : (term245 _100607 P) = (term125 _100607 P).
Proof. exact (eq_refl (term245 _100607 P)). Qed.
Lemma lem3890132 {_100607 : Type'} (P : type686 _100607) : (term246 _100607 P) = (term130 _100607 P).
Proof. exact (MK_COMB (@lem3890130 _100607 P) (@lem3890131 _100607 P)). Qed.
Lemma lem3890133 {_100607 : Type'} : (term247 _100607) = (term138 _100607).
Proof. exact (fun_ext (fun P : type686 _100607 => @lem3890132 _100607 P)). Qed.
Lemma lem3890134 {_100607 : Type'} : (@ex ((_100607 -> Prop) -> Prop)) = (@ex ((_100607 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_100607 -> Prop) -> Prop))). Qed.
Lemma lem3890135 {_100607 : Type'} : (term239 _100607) = (term139 _100607).
Proof. exact (MK_COMB (@lem3890134 _100607) (@lem3890133 _100607)). Qed.
Lemma lem3890136 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3890137 {_100607 : Type'} : (term248 _100607) = (term249 _100607).
Proof. exact (MK_COMB (@lem3890136) (@lem3890135 _100607)). Qed.
Lemma lem3890138 {_100607 : Type'} (P : type686 _100607) : (term243 _100607 P) = (term127 _100607 P).
Proof. exact (eq_refl (term243 _100607 P)). Qed.
Lemma lem3890139 {_100607 : Type'} : (term250 _100607) = (term241 _100607).
Proof. exact (fun_ext (fun P : type686 _100607 => @lem3890138 _100607 P)). Qed.
Lemma lem3890140 {_100607 : Type'} : (@ex ((_100607 -> Prop) -> Prop)) = (@ex ((_100607 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_100607 -> Prop) -> Prop))). Qed.
Lemma lem3890141 {_100607 : Type'} : (term251 _100607) = (term252 _100607).
Proof. exact (MK_COMB (@lem3890140 _100607) (@lem3890139 _100607)). Qed.
Lemma lem3890142 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3890143 {_100607 : Type'} : (term253 _100607) = (term254 _100607).
Proof. exact (MK_COMB (@lem3890142) (@lem3890141 _100607)). Qed.
Lemma lem3890144 {_100607 : Type'} (P : type686 _100607) : (term245 _100607 P) = (term125 _100607 P).
Proof. exact (eq_refl (term245 _100607 P)). Qed.
Lemma lem3890145 {_100607 : Type'} : (term255 _100607) = (term242 _100607).
Proof. exact (fun_ext (fun P : type686 _100607 => @lem3890144 _100607 P)). Qed.
Lemma lem3890146 {_100607 : Type'} : (@ex ((_100607 -> Prop) -> Prop)) = (@ex ((_100607 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_100607 -> Prop) -> Prop))). Qed.
Lemma lem3890147 {_100607 : Type'} : (term256 _100607) = (term257 _100607).
Proof. exact (MK_COMB (@lem3890146 _100607) (@lem3890145 _100607)). Qed.
Lemma lem3890148 {_100607 : Type'} : (term240 _100607) = (term258 _100607).
Proof. exact (MK_COMB (@lem3890143 _100607) (@lem3890147 _100607)). Qed.
Lemma lem3890149 {_100607 : Type'} : ((term239 _100607) = (term240 _100607)) = ((term139 _100607) = (term258 _100607)).
Proof. exact (MK_COMB (@lem3890137 _100607) (@lem3890148 _100607)). Qed.
Lemma lem3890150 {_100607 : Type'} : (term139 _100607) = (term258 _100607).
Proof. exact (EQ_MP (@lem3890149 _100607) (@lem3890127 _100607)). Qed.
Lemma lem3890327 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3890328 {_100607 : Type'} : (term232 _100607) = (term259 _100607).
Proof. exact (MK_COMB (@lem3890327) (@lem3890150 _100607)). Qed.
Lemma lem3890334 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term235 A P Q) = (term236 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3890335 (P : nat -> Prop) (Q : nat -> Prop) : (term260 P Q) = (term261 P Q).
Proof. exact (@lem3890334 nat P Q). Qed.
Lemma lem3890336 {_100607 : Type'} (P : type686 _100607) : (term262 _100607 P) = (term263 _100607 P).
Proof. exact (@lem3890335 (term264 _100607 P) (term265 _100607 P)). Qed.
Lemma lem3890337 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term266 _100607 P n) = (term211 _100607 n P).
Proof. exact (eq_refl (term266 _100607 P n)). Qed.
Lemma lem3890338 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3890339 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term267 _100607 P n) = (term213 _100607 n P).
Proof. exact (MK_COMB (@lem3890338) (@lem3890337 _100607 n P)). Qed.
Lemma lem3890340 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term268 _100607 P n) = (term208 _100607 n P).
Proof. exact (eq_refl (term268 _100607 P n)). Qed.
Lemma lem3890341 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term269 _100607 P n) = (term215 _100607 n P).
Proof. exact (MK_COMB (@lem3890339 _100607 n P) (@lem3890340 _100607 n P)). Qed.
Lemma lem3890342 {_100607 : Type'} (P : type686 _100607) : (term270 _100607 P) = (term223 _100607 P).
Proof. exact (fun_ext (fun n : nat => @lem3890341 _100607 n P)). Qed.
Lemma lem3890343 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3890344 {_100607 : Type'} (P : type686 _100607) : (term262 _100607 P) = (term224 _100607 P).
Proof. exact (MK_COMB (@lem3890343) (@lem3890342 _100607 P)). Qed.
Lemma lem3890345 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3890346 {_100607 : Type'} (P : type686 _100607) : (term271 _100607 P) = (term272 _100607 P).
Proof. exact (MK_COMB (@lem3890345) (@lem3890344 _100607 P)). Qed.
Lemma lem3890347 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term266 _100607 P n) = (term211 _100607 n P).
Proof. exact (eq_refl (term266 _100607 P n)). Qed.
Lemma lem3890348 {_100607 : Type'} (P : type686 _100607) : (term273 _100607 P) = (term264 _100607 P).
Proof. exact (fun_ext (fun n : nat => @lem3890347 _100607 n P)). Qed.
Lemma lem3890349 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3890350 {_100607 : Type'} (P : type686 _100607) : (term274 _100607 P) = (term275 _100607 P).
Proof. exact (MK_COMB (@lem3890349) (@lem3890348 _100607 P)). Qed.
Lemma lem3890351 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3890352 {_100607 : Type'} (P : type686 _100607) : (term276 _100607 P) = (term277 _100607 P).
Proof. exact (MK_COMB (@lem3890351) (@lem3890350 _100607 P)). Qed.
Lemma lem3890353 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term268 _100607 P n) = (term208 _100607 n P).
Proof. exact (eq_refl (term268 _100607 P n)). Qed.
Lemma lem3890354 {_100607 : Type'} (P : type686 _100607) : (term278 _100607 P) = (term265 _100607 P).
Proof. exact (fun_ext (fun n : nat => @lem3890353 _100607 n P)). Qed.
Lemma lem3890355 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3890356 {_100607 : Type'} (P : type686 _100607) : (term279 _100607 P) = (term280 _100607 P).
Proof. exact (MK_COMB (@lem3890355) (@lem3890354 _100607 P)). Qed.
Lemma lem3890357 {_100607 : Type'} (P : type686 _100607) : (term263 _100607 P) = (term281 _100607 P).
Proof. exact (MK_COMB (@lem3890352 _100607 P) (@lem3890356 _100607 P)). Qed.
Lemma lem3890358 {_100607 : Type'} (P : type686 _100607) : ((term262 _100607 P) = (term263 _100607 P)) = ((term224 _100607 P) = (term281 _100607 P)).
Proof. exact (MK_COMB (@lem3890346 _100607 P) (@lem3890357 _100607 P)). Qed.
Lemma lem3890359 {_100607 : Type'} (P : type686 _100607) : (term224 _100607 P) = (term281 _100607 P).
Proof. exact (EQ_MP (@lem3890358 _100607 P) (@lem3890336 _100607 P)). Qed.
Lemma lem3890744 {_100607 : Type'} : (term229 _100607) = (term282 _100607).
Proof. exact (fun_ext (fun P : type686 _100607 => @lem3890359 _100607 P)). Qed.
Lemma lem3890745 {_100607 : Type'} : (@ex ((_100607 -> Prop) -> Prop)) = (@ex ((_100607 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_100607 -> Prop) -> Prop))). Qed.
Lemma lem3890746 {_100607 : Type'} : (term230 _100607) = (term283 _100607).
Proof. exact (MK_COMB (@lem3890745 _100607) (@lem3890744 _100607)). Qed.
Lemma lem3890748 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term235 A P Q) = (term236 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem3890749 {_100607 : Type'} (P : type180 _100607) (Q : type180 _100607) : (term237 _100607 P Q) = (term238 _100607 P Q).
Proof. exact (@lem3890748 (type686 _100607) P Q). Qed.
Lemma lem3890750 {_100607 : Type'} : (term284 _100607) = (term285 _100607).
Proof. exact (@lem3890749 _100607 (term286 _100607) (term287 _100607)). Qed.
Lemma lem3890751 {_100607 : Type'} (P : type686 _100607) : (term288 _100607 P) = (term275 _100607 P).
Proof. exact (eq_refl (term288 _100607 P)). Qed.
Lemma lem3890752 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3890753 {_100607 : Type'} (P : type686 _100607) : (term289 _100607 P) = (term277 _100607 P).
Proof. exact (MK_COMB (@lem3890752) (@lem3890751 _100607 P)). Qed.
Lemma lem3890754 {_100607 : Type'} (P : type686 _100607) : (term290 _100607 P) = (term280 _100607 P).
Proof. exact (eq_refl (term290 _100607 P)). Qed.
Lemma lem3890755 {_100607 : Type'} (P : type686 _100607) : (term291 _100607 P) = (term281 _100607 P).
Proof. exact (MK_COMB (@lem3890753 _100607 P) (@lem3890754 _100607 P)). Qed.
Lemma lem3890756 {_100607 : Type'} : (term292 _100607) = (term282 _100607).
Proof. exact (fun_ext (fun P : type686 _100607 => @lem3890755 _100607 P)). Qed.
Lemma lem3890757 {_100607 : Type'} : (@ex ((_100607 -> Prop) -> Prop)) = (@ex ((_100607 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_100607 -> Prop) -> Prop))). Qed.
Lemma lem3890758 {_100607 : Type'} : (term284 _100607) = (term283 _100607).
Proof. exact (MK_COMB (@lem3890757 _100607) (@lem3890756 _100607)). Qed.
Lemma lem3890759 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3890760 {_100607 : Type'} : (term293 _100607) = (term294 _100607).
Proof. exact (MK_COMB (@lem3890759) (@lem3890758 _100607)). Qed.
Lemma lem3890761 {_100607 : Type'} (P : type686 _100607) : (term288 _100607 P) = (term275 _100607 P).
Proof. exact (eq_refl (term288 _100607 P)). Qed.
Lemma lem3890762 {_100607 : Type'} : (term295 _100607) = (term286 _100607).
Proof. exact (fun_ext (fun P : type686 _100607 => @lem3890761 _100607 P)). Qed.
Lemma lem3890763 {_100607 : Type'} : (@ex ((_100607 -> Prop) -> Prop)) = (@ex ((_100607 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_100607 -> Prop) -> Prop))). Qed.
Lemma lem3890764 {_100607 : Type'} : (term296 _100607) = (term297 _100607).
Proof. exact (MK_COMB (@lem3890763 _100607) (@lem3890762 _100607)). Qed.
Lemma lem3890765 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3890766 {_100607 : Type'} : (term298 _100607) = (term299 _100607).
Proof. exact (MK_COMB (@lem3890765) (@lem3890764 _100607)). Qed.
Lemma lem3890767 {_100607 : Type'} (P : type686 _100607) : (term290 _100607 P) = (term280 _100607 P).
Proof. exact (eq_refl (term290 _100607 P)). Qed.
Lemma lem3890768 {_100607 : Type'} : (term300 _100607) = (term287 _100607).
Proof. exact (fun_ext (fun P : type686 _100607 => @lem3890767 _100607 P)). Qed.
Lemma lem3890769 {_100607 : Type'} : (@ex ((_100607 -> Prop) -> Prop)) = (@ex ((_100607 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_100607 -> Prop) -> Prop))). Qed.
Lemma lem3890770 {_100607 : Type'} : (term301 _100607) = (term302 _100607).
Proof. exact (MK_COMB (@lem3890769 _100607) (@lem3890768 _100607)). Qed.
Lemma lem3890771 {_100607 : Type'} : (term285 _100607) = (term303 _100607).
Proof. exact (MK_COMB (@lem3890766 _100607) (@lem3890770 _100607)). Qed.
Lemma lem3890772 {_100607 : Type'} : ((term284 _100607) = (term285 _100607)) = ((term283 _100607) = (term303 _100607)).
Proof. exact (MK_COMB (@lem3890760 _100607) (@lem3890771 _100607)). Qed.
Lemma lem3890773 {_100607 : Type'} : (term283 _100607) = (term303 _100607).
Proof. exact (EQ_MP (@lem3890772 _100607) (@lem3890750 _100607)). Qed.
Lemma lem3891166 {_100607 : Type'} : (term230 _100607) = (term303 _100607).
Proof. exact (TRANS (@lem3890746 _100607) (@lem3890773 _100607)). Qed.
Lemma lem3891167 {_100607 : Type'} : (term234 _100607) = (term304 _100607).
Proof. exact (MK_COMB (@lem3890328 _100607) (@lem3891166 _100607)). Qed.
Lemma lem3891169 {A : Type'} (P : A -> Prop) (Q : Prop) : (term305 A P Q) = (term306 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3891170 {_100607 : Type'} (P : type686 _100607) (Q : Prop) : (term307 _100607 P Q) = (term308 _100607 P Q).
Proof. exact (@lem3891169 (_100607 -> Prop) P Q). Qed.
Lemma lem3891171 {_100607 : Type'} (P : type686 _100607) : (term309 _100607 P) = (term310 _100607 P).
Proof. exact (@lem3891170 _100607 (term13 _100607 P) (term121 _100607 P)). Qed.
Lemma lem3891172 {_100607 : Type'} (P : type686 _100607) (s : _100607 -> Prop) : (term116 _100607 P s) = (term11 _100607 P s).
Proof. exact (eq_refl (term116 _100607 P s)). Qed.
Lemma lem3891173 {_100607 : Type'} (P : type686 _100607) : (term311 _100607 P) = (term13 _100607 P).
Proof. exact (fun_ext (fun s : _100607 -> Prop => @lem3891172 _100607 P s)). Qed.
Lemma lem3891174 {_100607 : Type'} : (@ex (_100607 -> Prop)) = (@ex (_100607 -> Prop)).
Proof. exact (eq_refl (@ex (_100607 -> Prop))). Qed.
Lemma lem3891175 {_100607 : Type'} (P : type686 _100607) : (term312 _100607 P) = (term15 _100607 P).
Proof. exact (MK_COMB (@lem3891174 _100607) (@lem3891173 _100607 P)). Qed.
Lemma lem3891176 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3891177 {_100607 : Type'} (P : type686 _100607) : (term313 _100607 P) = (term126 _100607 P).
Proof. exact (MK_COMB (@lem3891176) (@lem3891175 _100607 P)). Qed.
Lemma lem3891178 {_100607 : Type'} (P : type686 _100607) : (term121 _100607 P) = (term121 _100607 P).
Proof. exact (eq_refl (term121 _100607 P)). Qed.
Lemma lem3891179 {_100607 : Type'} (P : type686 _100607) : (term309 _100607 P) = (term127 _100607 P).
Proof. exact (MK_COMB (@lem3891177 _100607 P) (@lem3891178 _100607 P)). Qed.
Lemma lem3891180 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3891181 {_100607 : Type'} (P : type686 _100607) : (term314 _100607 P) = (term315 _100607 P).
Proof. exact (MK_COMB (@lem3891180) (@lem3891179 _100607 P)). Qed.
Lemma lem3891182 {_100607 : Type'} (P : type686 _100607) (s : _100607 -> Prop) : (term116 _100607 P s) = (term11 _100607 P s).
Proof. exact (eq_refl (term116 _100607 P s)). Qed.
Lemma lem3891183 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3891184 {_100607 : Type'} (P : type686 _100607) (s : _100607 -> Prop) : (term316 _100607 P s) = (term317 _100607 P s).
Proof. exact (MK_COMB (@lem3891183) (@lem3891182 _100607 P s)). Qed.
Lemma lem3891185 {_100607 : Type'} (P : type686 _100607) : (term121 _100607 P) = (term121 _100607 P).
Proof. exact (eq_refl (term121 _100607 P)). Qed.
Lemma lem3891186 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) : (term318 _100607 s P) = (term319 _100607 s P).
Proof. exact (MK_COMB (@lem3891184 _100607 P s) (@lem3891185 _100607 P)). Qed.
Lemma lem3891187 {_100607 : Type'} (P : type686 _100607) : (term320 _100607 P) = (term321 _100607 P).
Proof. exact (fun_ext (fun s : _100607 -> Prop => @lem3891186 _100607 s P)). Qed.
Lemma lem3891188 {_100607 : Type'} : (@ex (_100607 -> Prop)) = (@ex (_100607 -> Prop)).
Proof. exact (eq_refl (@ex (_100607 -> Prop))). Qed.
Lemma lem3891189 {_100607 : Type'} (P : type686 _100607) : (term310 _100607 P) = (term322 _100607 P).
Proof. exact (MK_COMB (@lem3891188 _100607) (@lem3891187 _100607 P)). Qed.
Lemma lem3891190 {_100607 : Type'} (P : type686 _100607) : ((term309 _100607 P) = (term310 _100607 P)) = ((term127 _100607 P) = (term322 _100607 P)).
Proof. exact (MK_COMB (@lem3891181 _100607 P) (@lem3891189 _100607 P)). Qed.
Lemma lem3891191 {_100607 : Type'} (P : type686 _100607) : (term127 _100607 P) = (term322 _100607 P).
Proof. exact (EQ_MP (@lem3891190 _100607 P) (@lem3891171 _100607 P)). Qed.
Lemma lem3891192 {_100607 : Type'} : (term241 _100607) = (term323 _100607).
Proof. exact (fun_ext (fun P : type686 _100607 => @lem3891191 _100607 P)). Qed.
Lemma lem3891193 {_100607 : Type'} : (@ex ((_100607 -> Prop) -> Prop)) = (@ex ((_100607 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_100607 -> Prop) -> Prop))). Qed.
Lemma lem3891194 {_100607 : Type'} : (term252 _100607) = (term324 _100607).
Proof. exact (MK_COMB (@lem3891193 _100607) (@lem3891192 _100607)). Qed.
Lemma lem3891195 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3891196 {_100607 : Type'} : (term254 _100607) = (term325 _100607).
Proof. exact (MK_COMB (@lem3891195) (@lem3891194 _100607)). Qed.
Lemma lem3891197 {_100607 : Type'} : (term257 _100607) = (term257 _100607).
Proof. exact (eq_refl (term257 _100607)). Qed.
Lemma lem3891198 {_100607 : Type'} : (term258 _100607) = (term326 _100607).
Proof. exact (MK_COMB (@lem3891196 _100607) (@lem3891197 _100607)). Qed.
Lemma lem3891200 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term236 A P Q) = (term235 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3891201 {_100607 : Type'} (P : type180 _100607) (Q : type180 _100607) : (term238 _100607 P Q) = (term237 _100607 P Q).
Proof. exact (@lem3891200 (type686 _100607) P Q). Qed.
Lemma lem3891202 {_100607 : Type'} : (term327 _100607) = (term328 _100607).
Proof. exact (@lem3891201 _100607 (term323 _100607) (term242 _100607)). Qed.
Lemma lem3891203 {_100607 : Type'} (P : type686 _100607) : (term329 _100607 P) = (term322 _100607 P).
Proof. exact (eq_refl (term329 _100607 P)). Qed.
Lemma lem3891204 {_100607 : Type'} : (term330 _100607) = (term323 _100607).
Proof. exact (fun_ext (fun P : type686 _100607 => @lem3891203 _100607 P)). Qed.
Lemma lem3891205 {_100607 : Type'} : (@ex ((_100607 -> Prop) -> Prop)) = (@ex ((_100607 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_100607 -> Prop) -> Prop))). Qed.
Lemma lem3891206 {_100607 : Type'} : (term331 _100607) = (term324 _100607).
Proof. exact (MK_COMB (@lem3891205 _100607) (@lem3891204 _100607)). Qed.
Lemma lem3891207 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3891208 {_100607 : Type'} : (term332 _100607) = (term325 _100607).
Proof. exact (MK_COMB (@lem3891207) (@lem3891206 _100607)). Qed.
Lemma lem3891209 {_100607 : Type'} (P : type686 _100607) : (term245 _100607 P) = (term125 _100607 P).
Proof. exact (eq_refl (term245 _100607 P)). Qed.
Lemma lem3891210 {_100607 : Type'} : (term255 _100607) = (term242 _100607).
Proof. exact (fun_ext (fun P : type686 _100607 => @lem3891209 _100607 P)). Qed.
Lemma lem3891211 {_100607 : Type'} : (@ex ((_100607 -> Prop) -> Prop)) = (@ex ((_100607 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_100607 -> Prop) -> Prop))). Qed.
Lemma lem3891212 {_100607 : Type'} : (term256 _100607) = (term257 _100607).
Proof. exact (MK_COMB (@lem3891211 _100607) (@lem3891210 _100607)). Qed.
Lemma lem3891213 {_100607 : Type'} : (term327 _100607) = (term326 _100607).
Proof. exact (MK_COMB (@lem3891208 _100607) (@lem3891212 _100607)). Qed.
Lemma lem3891214 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3891215 {_100607 : Type'} : (term333 _100607) = (term334 _100607).
Proof. exact (MK_COMB (@lem3891214) (@lem3891213 _100607)). Qed.
Lemma lem3891216 {_100607 : Type'} (P : type686 _100607) : (term329 _100607 P) = (term322 _100607 P).
Proof. exact (eq_refl (term329 _100607 P)). Qed.
Lemma lem3891217 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3891218 {_100607 : Type'} (P : type686 _100607) : (term335 _100607 P) = (term336 _100607 P).
Proof. exact (MK_COMB (@lem3891217) (@lem3891216 _100607 P)). Qed.
Lemma lem3891219 {_100607 : Type'} (P : type686 _100607) : (term245 _100607 P) = (term125 _100607 P).
Proof. exact (eq_refl (term245 _100607 P)). Qed.
Lemma lem3891220 {_100607 : Type'} (P : type686 _100607) : (term337 _100607 P) = (term338 _100607 P).
Proof. exact (MK_COMB (@lem3891218 _100607 P) (@lem3891219 _100607 P)). Qed.
Lemma lem3891221 {_100607 : Type'} : (term339 _100607) = (term340 _100607).
Proof. exact (fun_ext (fun P : type686 _100607 => @lem3891220 _100607 P)). Qed.
Lemma lem3891222 {_100607 : Type'} : (@ex ((_100607 -> Prop) -> Prop)) = (@ex ((_100607 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_100607 -> Prop) -> Prop))). Qed.
Lemma lem3891223 {_100607 : Type'} : (term328 _100607) = (term341 _100607).
Proof. exact (MK_COMB (@lem3891222 _100607) (@lem3891221 _100607)). Qed.
Lemma lem3891224 {_100607 : Type'} : ((term327 _100607) = (term328 _100607)) = ((term326 _100607) = (term341 _100607)).
Proof. exact (MK_COMB (@lem3891215 _100607) (@lem3891223 _100607)). Qed.
Lemma lem3891225 {_100607 : Type'} : (term326 _100607) = (term341 _100607).
Proof. exact (EQ_MP (@lem3891224 _100607) (@lem3891202 _100607)). Qed.
Lemma lem3891227 {A : Type'} (P : A -> Prop) (Q : Prop) : (term342 A P Q) = (term343 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3891228 {_100607 : Type'} (P : type686 _100607) (Q : Prop) : (term344 _100607 P Q) = (term345 _100607 P Q).
Proof. exact (@lem3891227 (_100607 -> Prop) P Q). Qed.
Lemma lem3891229 {_100607 : Type'} (P : type686 _100607) : (term346 _100607 P) = (term347 _100607 P).
Proof. exact (@lem3891228 _100607 (term321 _100607 P) (term125 _100607 P)). Qed.
Lemma lem3891230 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) : (term348 _100607 P s) = (term319 _100607 s P).
Proof. exact (eq_refl (term348 _100607 P s)). Qed.
Lemma lem3891231 {_100607 : Type'} (P : type686 _100607) : (term349 _100607 P) = (term321 _100607 P).
Proof. exact (fun_ext (fun s : _100607 -> Prop => @lem3891230 _100607 s P)). Qed.
Lemma lem3891232 {_100607 : Type'} : (@ex (_100607 -> Prop)) = (@ex (_100607 -> Prop)).
Proof. exact (eq_refl (@ex (_100607 -> Prop))). Qed.
Lemma lem3891233 {_100607 : Type'} (P : type686 _100607) : (term350 _100607 P) = (term322 _100607 P).
Proof. exact (MK_COMB (@lem3891232 _100607) (@lem3891231 _100607 P)). Qed.
Lemma lem3891234 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3891235 {_100607 : Type'} (P : type686 _100607) : (term351 _100607 P) = (term336 _100607 P).
Proof. exact (MK_COMB (@lem3891234) (@lem3891233 _100607 P)). Qed.
Lemma lem3891236 {_100607 : Type'} (P : type686 _100607) : (term125 _100607 P) = (term125 _100607 P).
Proof. exact (eq_refl (term125 _100607 P)). Qed.
Lemma lem3891237 {_100607 : Type'} (P : type686 _100607) : (term346 _100607 P) = (term338 _100607 P).
Proof. exact (MK_COMB (@lem3891235 _100607 P) (@lem3891236 _100607 P)). Qed.
Lemma lem3891238 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3891239 {_100607 : Type'} (P : type686 _100607) : (term352 _100607 P) = (term353 _100607 P).
Proof. exact (MK_COMB (@lem3891238) (@lem3891237 _100607 P)). Qed.
Lemma lem3891240 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) : (term348 _100607 P s) = (term319 _100607 s P).
Proof. exact (eq_refl (term348 _100607 P s)). Qed.
Lemma lem3891241 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3891242 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) : (term354 _100607 P s) = (term355 _100607 s P).
Proof. exact (MK_COMB (@lem3891241) (@lem3891240 _100607 s P)). Qed.
Lemma lem3891243 {_100607 : Type'} (P : type686 _100607) : (term125 _100607 P) = (term125 _100607 P).
Proof. exact (eq_refl (term125 _100607 P)). Qed.
Lemma lem3891244 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) : (term356 _100607 s P) = (term357 _100607 s P).
Proof. exact (MK_COMB (@lem3891242 _100607 s P) (@lem3891243 _100607 P)). Qed.
Lemma lem3891245 {_100607 : Type'} (P : type686 _100607) : (term358 _100607 P) = (term359 _100607 P).
Proof. exact (fun_ext (fun s : _100607 -> Prop => @lem3891244 _100607 s P)). Qed.
Lemma lem3891246 {_100607 : Type'} : (@ex (_100607 -> Prop)) = (@ex (_100607 -> Prop)).
Proof. exact (eq_refl (@ex (_100607 -> Prop))). Qed.
Lemma lem3891247 {_100607 : Type'} (P : type686 _100607) : (term347 _100607 P) = (term360 _100607 P).
Proof. exact (MK_COMB (@lem3891246 _100607) (@lem3891245 _100607 P)). Qed.
Lemma lem3891248 {_100607 : Type'} (P : type686 _100607) : ((term346 _100607 P) = (term347 _100607 P)) = ((term338 _100607 P) = (term360 _100607 P)).
Proof. exact (MK_COMB (@lem3891239 _100607 P) (@lem3891247 _100607 P)). Qed.
Lemma lem3891249 {_100607 : Type'} (P : type686 _100607) : (term338 _100607 P) = (term360 _100607 P).
Proof. exact (EQ_MP (@lem3891248 _100607 P) (@lem3891229 _100607 P)). Qed.
Lemma lem3891250 {_100607 : Type'} : (term340 _100607) = (term361 _100607).
Proof. exact (fun_ext (fun P : type686 _100607 => @lem3891249 _100607 P)). Qed.
Lemma lem3891251 {_100607 : Type'} : (@ex ((_100607 -> Prop) -> Prop)) = (@ex ((_100607 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_100607 -> Prop) -> Prop))). Qed.
Lemma lem3891252 {_100607 : Type'} : (term341 _100607) = (term362 _100607).
Proof. exact (MK_COMB (@lem3891251 _100607) (@lem3891250 _100607)). Qed.
Lemma lem3891253 {_100607 : Type'} : (term326 _100607) = (term362 _100607).
Proof. exact (TRANS (@lem3891225 _100607) (@lem3891252 _100607)). Qed.
Lemma lem3891254 {_100607 : Type'} : (term258 _100607) = (term362 _100607).
Proof. exact (TRANS (@lem3891198 _100607) (@lem3891253 _100607)). Qed.
Lemma lem3891255 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3891256 {_100607 : Type'} : (term259 _100607) = (term363 _100607).
Proof. exact (MK_COMB (@lem3891255) (@lem3891254 _100607)). Qed.
Lemma lem3891258 {A : Type'} (P : A -> Prop) (Q : Prop) : (term305 A P Q) = (term306 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3891259 {_100607 : Type'} (P : _100607 -> Prop) (Q : Prop) : (term305 _100607 P Q) = (term306 _100607 P Q).
Proof. exact (@lem3891258 _100607 P Q). Qed.
Lemma lem3891260 {_100607 : Type'} (n : nat) (P : type686 _100607) (s : _100607 -> Prop) : (term364 _100607 n P s) = (term365 _100607 n P s).
Proof. exact (@lem3891259 _100607 (term107 _100607 n s) (P s)). Qed.
Lemma lem3891261 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) (a : _100607) : (term164 _100607 n s a) = (term106 _100607 n s a).
Proof. exact (eq_refl (term164 _100607 n s a)). Qed.
Lemma lem3891262 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) : (term366 _100607 n s) = (term107 _100607 n s).
Proof. exact (fun_ext (fun a : _100607 => @lem3891261 _100607 n s a)). Qed.
Lemma lem3891263 {_100607 : Type'} : (@ex _100607) = (@ex _100607).
Proof. exact (eq_refl (@ex _100607)). Qed.
Lemma lem3891264 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) : (term367 _100607 n s) = (term21 _100607 n s).
Proof. exact (MK_COMB (@lem3891263 _100607) (@lem3891262 _100607 n s)). Qed.
Lemma lem3891265 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3891266 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) : (term368 _100607 n s) = (term23 _100607 n s).
Proof. exact (MK_COMB (@lem3891265) (@lem3891264 _100607 n s)). Qed.
Lemma lem3891267 {_100607 : Type'} (P : type686 _100607) (s : _100607 -> Prop) : (P s) = (P s).
Proof. exact (eq_refl (P s)). Qed.
Lemma lem3891268 {_100607 : Type'} (n : nat) (P : type686 _100607) (s : _100607 -> Prop) : (term364 _100607 n P s) = (term25 _100607 n P s).
Proof. exact (MK_COMB (@lem3891266 _100607 n s) (@lem3891267 _100607 P s)). Qed.
Lemma lem3891269 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3891270 {_100607 : Type'} (n : nat) (P : type686 _100607) (s : _100607 -> Prop) : (term369 _100607 n P s) = (term370 _100607 n P s).
Proof. exact (MK_COMB (@lem3891269) (@lem3891268 _100607 n P s)). Qed.
Lemma lem3891271 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) (a : _100607) : (term164 _100607 n s a) = (term106 _100607 n s a).
Proof. exact (eq_refl (term164 _100607 n s a)). Qed.
Lemma lem3891272 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3891273 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) (a : _100607) : (term371 _100607 n s a) = (term372 _100607 n s a).
Proof. exact (MK_COMB (@lem3891272) (@lem3891271 _100607 n s a)). Qed.
Lemma lem3891274 {_100607 : Type'} (P : type686 _100607) (s : _100607 -> Prop) : (P s) = (P s).
Proof. exact (eq_refl (P s)). Qed.
Lemma lem3891275 {_100607 : Type'} (n : nat) (a : _100607) (P : type686 _100607) (s : _100607 -> Prop) : (term373 _100607 n a P s) = (term374 _100607 n a P s).
Proof. exact (MK_COMB (@lem3891273 _100607 n s a) (@lem3891274 _100607 P s)). Qed.
Lemma lem3891276 {_100607 : Type'} (n : nat) (P : type686 _100607) (s : _100607 -> Prop) : (term375 _100607 n P s) = (term376 _100607 n P s).
Proof. exact (fun_ext (fun a : _100607 => @lem3891275 _100607 n a P s)). Qed.
Lemma lem3891277 {_100607 : Type'} : (@ex _100607) = (@ex _100607).
Proof. exact (eq_refl (@ex _100607)). Qed.
Lemma lem3891278 {_100607 : Type'} (n : nat) (P : type686 _100607) (s : _100607 -> Prop) : (term365 _100607 n P s) = (term377 _100607 n P s).
Proof. exact (MK_COMB (@lem3891277 _100607) (@lem3891276 _100607 n P s)). Qed.
Lemma lem3891279 {_100607 : Type'} (n : nat) (P : type686 _100607) (s : _100607 -> Prop) : ((term364 _100607 n P s) = (term365 _100607 n P s)) = ((term25 _100607 n P s) = (term377 _100607 n P s)).
Proof. exact (MK_COMB (@lem3891270 _100607 n P s) (@lem3891278 _100607 n P s)). Qed.
Lemma lem3891280 {_100607 : Type'} (n : nat) (P : type686 _100607) (s : _100607 -> Prop) : (term25 _100607 n P s) = (term377 _100607 n P s).
Proof. exact (EQ_MP (@lem3891279 _100607 n P s) (@lem3891260 _100607 n P s)). Qed.
Lemma lem3891282 {A : Type'} (P : A -> Prop) (Q : Prop) : (term305 A P Q) = (term306 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3891283 {_100607 : Type'} (P : type686 _100607) (Q : Prop) : (term307 _100607 P Q) = (term308 _100607 P Q).
Proof. exact (@lem3891282 (_100607 -> Prop) P Q). Qed.
Lemma lem3891284 {_100607 : Type'} (n : nat) (a : _100607) (P : type686 _100607) (s : _100607 -> Prop) : (term378 _100607 n a P s) = (term379 _100607 n a P s).
Proof. exact (@lem3891283 _100607 (term105 _100607 n s a) (P s)). Qed.
Lemma lem3891285 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) (a : _100607) (t : _100607 -> Prop) : (term155 _100607 n s a t) = (term104 _100607 n s a t).
Proof. exact (eq_refl (term155 _100607 n s a t)). Qed.
Lemma lem3891286 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) (a : _100607) : (term380 _100607 n s a) = (term105 _100607 n s a).
Proof. exact (fun_ext (fun t : _100607 -> Prop => @lem3891285 _100607 n s a t)). Qed.
Lemma lem3891287 {_100607 : Type'} : (@ex (_100607 -> Prop)) = (@ex (_100607 -> Prop)).
Proof. exact (eq_refl (@ex (_100607 -> Prop))). Qed.
Lemma lem3891288 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) (a : _100607) : (term381 _100607 n s a) = (term106 _100607 n s a).
Proof. exact (MK_COMB (@lem3891287 _100607) (@lem3891286 _100607 n s a)). Qed.
Lemma lem3891289 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3891290 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) (a : _100607) : (term382 _100607 n s a) = (term372 _100607 n s a).
Proof. exact (MK_COMB (@lem3891289) (@lem3891288 _100607 n s a)). Qed.
Lemma lem3891291 {_100607 : Type'} (P : type686 _100607) (s : _100607 -> Prop) : (P s) = (P s).
Proof. exact (eq_refl (P s)). Qed.
Lemma lem3891292 {_100607 : Type'} (n : nat) (a : _100607) (P : type686 _100607) (s : _100607 -> Prop) : (term378 _100607 n a P s) = (term374 _100607 n a P s).
Proof. exact (MK_COMB (@lem3891290 _100607 n s a) (@lem3891291 _100607 P s)). Qed.
Lemma lem3891293 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3891294 {_100607 : Type'} (n : nat) (a : _100607) (P : type686 _100607) (s : _100607 -> Prop) : (term383 _100607 n a P s) = (term384 _100607 n a P s).
Proof. exact (MK_COMB (@lem3891293) (@lem3891292 _100607 n a P s)). Qed.
Lemma lem3891295 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) (a : _100607) (t : _100607 -> Prop) : (term155 _100607 n s a t) = (term104 _100607 n s a t).
Proof. exact (eq_refl (term155 _100607 n s a t)). Qed.
Lemma lem3891296 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3891297 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) (a : _100607) (t : _100607 -> Prop) : (term385 _100607 n s a t) = (term386 _100607 n s a t).
Proof. exact (MK_COMB (@lem3891296) (@lem3891295 _100607 n s a t)). Qed.
Lemma lem3891298 {_100607 : Type'} (P : type686 _100607) (s : _100607 -> Prop) : (P s) = (P s).
Proof. exact (eq_refl (P s)). Qed.
Lemma lem3891299 {_100607 : Type'} (n : nat) (a : _100607) (t : _100607 -> Prop) (P : type686 _100607) (s : _100607 -> Prop) : (term387 _100607 n a t P s) = (term388 _100607 n a t P s).
Proof. exact (MK_COMB (@lem3891297 _100607 n s a t) (@lem3891298 _100607 P s)). Qed.
Lemma lem3891300 {_100607 : Type'} (n : nat) (a : _100607) (P : type686 _100607) (s : _100607 -> Prop) : (term389 _100607 n a P s) = (term390 _100607 n a P s).
Proof. exact (fun_ext (fun t : _100607 -> Prop => @lem3891299 _100607 n a t P s)). Qed.
Lemma lem3891301 {_100607 : Type'} : (@ex (_100607 -> Prop)) = (@ex (_100607 -> Prop)).
Proof. exact (eq_refl (@ex (_100607 -> Prop))). Qed.
Lemma lem3891302 {_100607 : Type'} (n : nat) (a : _100607) (P : type686 _100607) (s : _100607 -> Prop) : (term379 _100607 n a P s) = (term391 _100607 n a P s).
Proof. exact (MK_COMB (@lem3891301 _100607) (@lem3891300 _100607 n a P s)). Qed.
Lemma lem3891303 {_100607 : Type'} (n : nat) (a : _100607) (P : type686 _100607) (s : _100607 -> Prop) : ((term378 _100607 n a P s) = (term379 _100607 n a P s)) = ((term374 _100607 n a P s) = (term391 _100607 n a P s)).
Proof. exact (MK_COMB (@lem3891294 _100607 n a P s) (@lem3891302 _100607 n a P s)). Qed.
Lemma lem3891304 {_100607 : Type'} (n : nat) (a : _100607) (P : type686 _100607) (s : _100607 -> Prop) : (term374 _100607 n a P s) = (term391 _100607 n a P s).
Proof. exact (EQ_MP (@lem3891303 _100607 n a P s) (@lem3891284 _100607 n a P s)). Qed.
Lemma lem3891305 {_100607 : Type'} (n : nat) (P : type686 _100607) (s : _100607 -> Prop) : (term376 _100607 n P s) = (term392 _100607 n P s).
Proof. exact (fun_ext (fun a : _100607 => @lem3891304 _100607 n a P s)). Qed.
Lemma lem3891306 {_100607 : Type'} : (@ex _100607) = (@ex _100607).
Proof. exact (eq_refl (@ex _100607)). Qed.
Lemma lem3891307 {_100607 : Type'} (n : nat) (P : type686 _100607) (s : _100607 -> Prop) : (term377 _100607 n P s) = (term393 _100607 n P s).
Proof. exact (MK_COMB (@lem3891306 _100607) (@lem3891305 _100607 n P s)). Qed.
Lemma lem3891308 {_100607 : Type'} (n : nat) (P : type686 _100607) (s : _100607 -> Prop) : (term25 _100607 n P s) = (term393 _100607 n P s).
Proof. exact (TRANS (@lem3891280 _100607 n P s) (@lem3891307 _100607 n P s)). Qed.
Lemma lem3891309 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term27 _100607 n P) = (term394 _100607 n P).
Proof. exact (fun_ext (fun s : _100607 -> Prop => @lem3891308 _100607 n P s)). Qed.
Lemma lem3891310 {_100607 : Type'} : (@ex (_100607 -> Prop)) = (@ex (_100607 -> Prop)).
Proof. exact (eq_refl (@ex (_100607 -> Prop))). Qed.
Lemma lem3891311 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term29 _100607 n P) = (term395 _100607 n P).
Proof. exact (MK_COMB (@lem3891310 _100607) (@lem3891309 _100607 n P)). Qed.
Lemma lem3891312 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3891313 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term209 _100607 n P) = (term396 _100607 n P).
Proof. exact (MK_COMB (@lem3891312) (@lem3891311 _100607 n P)). Qed.
Lemma lem3891314 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term204 _100607 n P) = (term204 _100607 n P).
Proof. exact (eq_refl (term204 _100607 n P)). Qed.
Lemma lem3891315 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term211 _100607 n P) = (term397 _100607 n P).
Proof. exact (MK_COMB (@lem3891313 _100607 n P) (@lem3891314 _100607 n P)). Qed.
Lemma lem3891317 {A : Type'} (P : A -> Prop) (Q : Prop) : (term305 A P Q) = (term306 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3891318 {_100607 : Type'} (P : type686 _100607) (Q : Prop) : (term307 _100607 P Q) = (term308 _100607 P Q).
Proof. exact (@lem3891317 (_100607 -> Prop) P Q). Qed.
Lemma lem3891319 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term398 _100607 n P) = (term399 _100607 n P).
Proof. exact (@lem3891318 _100607 (term394 _100607 n P) (term204 _100607 n P)). Qed.
Lemma lem3891320 {_100607 : Type'} (n : nat) (P : type686 _100607) (s : _100607 -> Prop) : (term400 _100607 n P s) = (term393 _100607 n P s).
Proof. exact (eq_refl (term400 _100607 n P s)). Qed.
Lemma lem3891321 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term401 _100607 n P) = (term394 _100607 n P).
Proof. exact (fun_ext (fun s : _100607 -> Prop => @lem3891320 _100607 n P s)). Qed.
Lemma lem3891322 {_100607 : Type'} : (@ex (_100607 -> Prop)) = (@ex (_100607 -> Prop)).
Proof. exact (eq_refl (@ex (_100607 -> Prop))). Qed.
Lemma lem3891323 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term402 _100607 n P) = (term395 _100607 n P).
Proof. exact (MK_COMB (@lem3891322 _100607) (@lem3891321 _100607 n P)). Qed.
Lemma lem3891324 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3891325 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term403 _100607 n P) = (term396 _100607 n P).
Proof. exact (MK_COMB (@lem3891324) (@lem3891323 _100607 n P)). Qed.
Lemma lem3891326 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term204 _100607 n P) = (term204 _100607 n P).
Proof. exact (eq_refl (term204 _100607 n P)). Qed.
Lemma lem3891327 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term398 _100607 n P) = (term397 _100607 n P).
Proof. exact (MK_COMB (@lem3891325 _100607 n P) (@lem3891326 _100607 n P)). Qed.
Lemma lem3891328 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3891329 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term404 _100607 n P) = (term405 _100607 n P).
Proof. exact (MK_COMB (@lem3891328) (@lem3891327 _100607 n P)). Qed.
Lemma lem3891330 {_100607 : Type'} (n : nat) (P : type686 _100607) (s : _100607 -> Prop) : (term400 _100607 n P s) = (term393 _100607 n P s).
Proof. exact (eq_refl (term400 _100607 n P s)). Qed.
Lemma lem3891331 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3891332 {_100607 : Type'} (n : nat) (P : type686 _100607) (s : _100607 -> Prop) : (term406 _100607 n P s) = (term407 _100607 n P s).
Proof. exact (MK_COMB (@lem3891331) (@lem3891330 _100607 n P s)). Qed.
Lemma lem3891333 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term204 _100607 n P) = (term204 _100607 n P).
Proof. exact (eq_refl (term204 _100607 n P)). Qed.
Lemma lem3891334 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term408 _100607 s n P) = (term409 _100607 s n P).
Proof. exact (MK_COMB (@lem3891332 _100607 n P s) (@lem3891333 _100607 n P)). Qed.
Lemma lem3891335 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term410 _100607 n P) = (term411 _100607 n P).
Proof. exact (fun_ext (fun s : _100607 -> Prop => @lem3891334 _100607 s n P)). Qed.
Lemma lem3891336 {_100607 : Type'} : (@ex (_100607 -> Prop)) = (@ex (_100607 -> Prop)).
Proof. exact (eq_refl (@ex (_100607 -> Prop))). Qed.
Lemma lem3891337 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term399 _100607 n P) = (term412 _100607 n P).
Proof. exact (MK_COMB (@lem3891336 _100607) (@lem3891335 _100607 n P)). Qed.
Lemma lem3891338 {_100607 : Type'} (n : nat) (P : type686 _100607) : ((term398 _100607 n P) = (term399 _100607 n P)) = ((term397 _100607 n P) = (term412 _100607 n P)).
Proof. exact (MK_COMB (@lem3891329 _100607 n P) (@lem3891337 _100607 n P)). Qed.
Lemma lem3891339 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term397 _100607 n P) = (term412 _100607 n P).
Proof. exact (EQ_MP (@lem3891338 _100607 n P) (@lem3891319 _100607 n P)). Qed.
Lemma lem3891341 {A : Type'} (P : A -> Prop) (Q : Prop) : (term305 A P Q) = (term306 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3891342 {_100607 : Type'} (P : _100607 -> Prop) (Q : Prop) : (term305 _100607 P Q) = (term306 _100607 P Q).
Proof. exact (@lem3891341 _100607 P Q). Qed.
Lemma lem3891343 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term413 _100607 s n P) = (term414 _100607 s n P).
Proof. exact (@lem3891342 _100607 (term392 _100607 n P s) (term204 _100607 n P)). Qed.
Lemma lem3891344 {_100607 : Type'} (n : nat) (a : _100607) (P : type686 _100607) (s : _100607 -> Prop) : (term415 _100607 n P s a) = (term391 _100607 n a P s).
Proof. exact (eq_refl (term415 _100607 n P s a)). Qed.
Lemma lem3891345 {_100607 : Type'} (n : nat) (P : type686 _100607) (s : _100607 -> Prop) : (term416 _100607 n P s) = (term392 _100607 n P s).
Proof. exact (fun_ext (fun a : _100607 => @lem3891344 _100607 n a P s)). Qed.
Lemma lem3891346 {_100607 : Type'} : (@ex _100607) = (@ex _100607).
Proof. exact (eq_refl (@ex _100607)). Qed.
Lemma lem3891347 {_100607 : Type'} (n : nat) (P : type686 _100607) (s : _100607 -> Prop) : (term417 _100607 n P s) = (term393 _100607 n P s).
Proof. exact (MK_COMB (@lem3891346 _100607) (@lem3891345 _100607 n P s)). Qed.
Lemma lem3891348 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3891349 {_100607 : Type'} (n : nat) (P : type686 _100607) (s : _100607 -> Prop) : (term418 _100607 n P s) = (term407 _100607 n P s).
Proof. exact (MK_COMB (@lem3891348) (@lem3891347 _100607 n P s)). Qed.
Lemma lem3891350 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term204 _100607 n P) = (term204 _100607 n P).
Proof. exact (eq_refl (term204 _100607 n P)). Qed.
Lemma lem3891351 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term413 _100607 s n P) = (term409 _100607 s n P).
Proof. exact (MK_COMB (@lem3891349 _100607 n P s) (@lem3891350 _100607 n P)). Qed.
Lemma lem3891352 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3891353 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term419 _100607 s n P) = (term420 _100607 s n P).
Proof. exact (MK_COMB (@lem3891352) (@lem3891351 _100607 s n P)). Qed.
Lemma lem3891354 {_100607 : Type'} (n : nat) (a : _100607) (P : type686 _100607) (s : _100607 -> Prop) : (term415 _100607 n P s a) = (term391 _100607 n a P s).
Proof. exact (eq_refl (term415 _100607 n P s a)). Qed.
Lemma lem3891355 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3891356 {_100607 : Type'} (n : nat) (a : _100607) (P : type686 _100607) (s : _100607 -> Prop) : (term421 _100607 n P s a) = (term422 _100607 n a P s).
Proof. exact (MK_COMB (@lem3891355) (@lem3891354 _100607 n a P s)). Qed.
Lemma lem3891357 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term204 _100607 n P) = (term204 _100607 n P).
Proof. exact (eq_refl (term204 _100607 n P)). Qed.
Lemma lem3891358 {_100607 : Type'} (a : _100607) (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term423 _100607 s a n P) = (term424 _100607 a s n P).
Proof. exact (MK_COMB (@lem3891356 _100607 n a P s) (@lem3891357 _100607 n P)). Qed.
Lemma lem3891359 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term425 _100607 s n P) = (term426 _100607 s n P).
Proof. exact (fun_ext (fun a : _100607 => @lem3891358 _100607 a s n P)). Qed.
Lemma lem3891360 {_100607 : Type'} : (@ex _100607) = (@ex _100607).
Proof. exact (eq_refl (@ex _100607)). Qed.
Lemma lem3891361 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term414 _100607 s n P) = (term427 _100607 s n P).
Proof. exact (MK_COMB (@lem3891360 _100607) (@lem3891359 _100607 s n P)). Qed.
Lemma lem3891362 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : ((term413 _100607 s n P) = (term414 _100607 s n P)) = ((term409 _100607 s n P) = (term427 _100607 s n P)).
Proof. exact (MK_COMB (@lem3891353 _100607 s n P) (@lem3891361 _100607 s n P)). Qed.
Lemma lem3891363 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term409 _100607 s n P) = (term427 _100607 s n P).
Proof. exact (EQ_MP (@lem3891362 _100607 s n P) (@lem3891343 _100607 s n P)). Qed.
Lemma lem3891365 {A : Type'} (P : A -> Prop) (Q : Prop) : (term305 A P Q) = (term306 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3891366 {_100607 : Type'} (P : type686 _100607) (Q : Prop) : (term307 _100607 P Q) = (term308 _100607 P Q).
Proof. exact (@lem3891365 (_100607 -> Prop) P Q). Qed.
Lemma lem3891367 {_100607 : Type'} (a : _100607) (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term428 _100607 a s n P) = (term429 _100607 a s n P).
Proof. exact (@lem3891366 _100607 (term390 _100607 n a P s) (term204 _100607 n P)). Qed.
Lemma lem3891368 {_100607 : Type'} (n : nat) (a : _100607) (t : _100607 -> Prop) (P : type686 _100607) (s : _100607 -> Prop) : (term430 _100607 n a P s t) = (term388 _100607 n a t P s).
Proof. exact (eq_refl (term430 _100607 n a P s t)). Qed.
Lemma lem3891369 {_100607 : Type'} (n : nat) (a : _100607) (P : type686 _100607) (s : _100607 -> Prop) : (term431 _100607 n a P s) = (term390 _100607 n a P s).
Proof. exact (fun_ext (fun t : _100607 -> Prop => @lem3891368 _100607 n a t P s)). Qed.
Lemma lem3891370 {_100607 : Type'} : (@ex (_100607 -> Prop)) = (@ex (_100607 -> Prop)).
Proof. exact (eq_refl (@ex (_100607 -> Prop))). Qed.
Lemma lem3891371 {_100607 : Type'} (n : nat) (a : _100607) (P : type686 _100607) (s : _100607 -> Prop) : (term432 _100607 n a P s) = (term391 _100607 n a P s).
Proof. exact (MK_COMB (@lem3891370 _100607) (@lem3891369 _100607 n a P s)). Qed.
Lemma lem3891372 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3891373 {_100607 : Type'} (n : nat) (a : _100607) (P : type686 _100607) (s : _100607 -> Prop) : (term433 _100607 n a P s) = (term422 _100607 n a P s).
Proof. exact (MK_COMB (@lem3891372) (@lem3891371 _100607 n a P s)). Qed.
Lemma lem3891374 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term204 _100607 n P) = (term204 _100607 n P).
Proof. exact (eq_refl (term204 _100607 n P)). Qed.
Lemma lem3891375 {_100607 : Type'} (a : _100607) (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term428 _100607 a s n P) = (term424 _100607 a s n P).
Proof. exact (MK_COMB (@lem3891373 _100607 n a P s) (@lem3891374 _100607 n P)). Qed.
Lemma lem3891376 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3891377 {_100607 : Type'} (a : _100607) (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term434 _100607 a s n P) = (term435 _100607 a s n P).
Proof. exact (MK_COMB (@lem3891376) (@lem3891375 _100607 a s n P)). Qed.
Lemma lem3891378 {_100607 : Type'} (n : nat) (a : _100607) (t : _100607 -> Prop) (P : type686 _100607) (s : _100607 -> Prop) : (term430 _100607 n a P s t) = (term388 _100607 n a t P s).
Proof. exact (eq_refl (term430 _100607 n a P s t)). Qed.
Lemma lem3891379 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3891380 {_100607 : Type'} (n : nat) (a : _100607) (t : _100607 -> Prop) (P : type686 _100607) (s : _100607 -> Prop) : (term436 _100607 n a P s t) = (term437 _100607 n a t P s).
Proof. exact (MK_COMB (@lem3891379) (@lem3891378 _100607 n a t P s)). Qed.
Lemma lem3891381 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term204 _100607 n P) = (term204 _100607 n P).
Proof. exact (eq_refl (term204 _100607 n P)). Qed.
Lemma lem3891382 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term438 _100607 a s t n P) = (term439 _100607 a t s n P).
Proof. exact (MK_COMB (@lem3891380 _100607 n a t P s) (@lem3891381 _100607 n P)). Qed.
Lemma lem3891383 {_100607 : Type'} (a : _100607) (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term440 _100607 a s n P) = (term441 _100607 a s n P).
Proof. exact (fun_ext (fun t : _100607 -> Prop => @lem3891382 _100607 a t s n P)). Qed.
Lemma lem3891384 {_100607 : Type'} : (@ex (_100607 -> Prop)) = (@ex (_100607 -> Prop)).
Proof. exact (eq_refl (@ex (_100607 -> Prop))). Qed.
Lemma lem3891385 {_100607 : Type'} (a : _100607) (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term429 _100607 a s n P) = (term442 _100607 a s n P).
Proof. exact (MK_COMB (@lem3891384 _100607) (@lem3891383 _100607 a s n P)). Qed.
Lemma lem3891386 {_100607 : Type'} (a : _100607) (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : ((term428 _100607 a s n P) = (term429 _100607 a s n P)) = ((term424 _100607 a s n P) = (term442 _100607 a s n P)).
Proof. exact (MK_COMB (@lem3891377 _100607 a s n P) (@lem3891385 _100607 a s n P)). Qed.
Lemma lem3891387 {_100607 : Type'} (a : _100607) (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term424 _100607 a s n P) = (term442 _100607 a s n P).
Proof. exact (EQ_MP (@lem3891386 _100607 a s n P) (@lem3891367 _100607 a s n P)). Qed.
Lemma lem3891388 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term426 _100607 s n P) = (term443 _100607 s n P).
Proof. exact (fun_ext (fun a : _100607 => @lem3891387 _100607 a s n P)). Qed.
Lemma lem3891389 {_100607 : Type'} : (@ex _100607) = (@ex _100607).
Proof. exact (eq_refl (@ex _100607)). Qed.
Lemma lem3891390 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term427 _100607 s n P) = (term444 _100607 s n P).
Proof. exact (MK_COMB (@lem3891389 _100607) (@lem3891388 _100607 s n P)). Qed.
Lemma lem3891391 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term409 _100607 s n P) = (term444 _100607 s n P).
Proof. exact (TRANS (@lem3891363 _100607 s n P) (@lem3891390 _100607 s n P)). Qed.
Lemma lem3891392 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term411 _100607 n P) = (term445 _100607 n P).
Proof. exact (fun_ext (fun s : _100607 -> Prop => @lem3891391 _100607 s n P)). Qed.
Lemma lem3891393 {_100607 : Type'} : (@ex (_100607 -> Prop)) = (@ex (_100607 -> Prop)).
Proof. exact (eq_refl (@ex (_100607 -> Prop))). Qed.
Lemma lem3891394 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term412 _100607 n P) = (term446 _100607 n P).
Proof. exact (MK_COMB (@lem3891393 _100607) (@lem3891392 _100607 n P)). Qed.
Lemma lem3891395 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term397 _100607 n P) = (term446 _100607 n P).
Proof. exact (TRANS (@lem3891339 _100607 n P) (@lem3891394 _100607 n P)). Qed.
Lemma lem3891396 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term211 _100607 n P) = (term446 _100607 n P).
Proof. exact (TRANS (@lem3891315 _100607 n P) (@lem3891395 _100607 n P)). Qed.
Lemma lem3891397 {_100607 : Type'} (P : type686 _100607) : (term264 _100607 P) = (term447 _100607 P).
Proof. exact (fun_ext (fun n : nat => @lem3891396 _100607 n P)). Qed.
Lemma lem3891398 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3891399 {_100607 : Type'} (P : type686 _100607) : (term275 _100607 P) = (term448 _100607 P).
Proof. exact (MK_COMB (@lem3891398) (@lem3891397 _100607 P)). Qed.
Lemma lem3891400 {_100607 : Type'} : (term286 _100607) = (term449 _100607).
Proof. exact (fun_ext (fun P : type686 _100607 => @lem3891399 _100607 P)). Qed.
Lemma lem3891401 {_100607 : Type'} : (@ex ((_100607 -> Prop) -> Prop)) = (@ex ((_100607 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_100607 -> Prop) -> Prop))). Qed.
Lemma lem3891402 {_100607 : Type'} : (term297 _100607) = (term450 _100607).
Proof. exact (MK_COMB (@lem3891401 _100607) (@lem3891400 _100607)). Qed.
Lemma lem3891403 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3891404 {_100607 : Type'} : (term299 _100607) = (term451 _100607).
Proof. exact (MK_COMB (@lem3891403) (@lem3891402 _100607)). Qed.
Lemma lem3891406 {A : Type'} (P : Prop) (Q : A -> Prop) : (term452 A P Q) = (term453 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3891407 {_100607 : Type'} (P : Prop) (Q : _100607 -> Prop) : (term452 _100607 P Q) = (term453 _100607 P Q).
Proof. exact (@lem3891406 _100607 P Q). Qed.
Lemma lem3891408 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term454 _100607 n P) = (term455 _100607 n P).
Proof. exact (@lem3891407 _100607 (term181 _100607 n P) (term103 _100607 n P)). Qed.
Lemma lem3891409 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) : (term200 _100607 n P a) = (term102 _100607 n P a).
Proof. exact (eq_refl (term200 _100607 n P a)). Qed.
Lemma lem3891410 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term456 _100607 n P) = (term103 _100607 n P).
Proof. exact (fun_ext (fun a : _100607 => @lem3891409 _100607 n P a)). Qed.
Lemma lem3891411 {_100607 : Type'} : (@ex _100607) = (@ex _100607).
Proof. exact (eq_refl (@ex _100607)). Qed.
Lemma lem3891412 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term457 _100607 n P) = (term32 _100607 n P).
Proof. exact (MK_COMB (@lem3891411 _100607) (@lem3891410 _100607 n P)). Qed.
Lemma lem3891413 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term206 _100607 n P) = (term206 _100607 n P).
Proof. exact (eq_refl (term206 _100607 n P)). Qed.
Lemma lem3891414 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term454 _100607 n P) = (term208 _100607 n P).
Proof. exact (MK_COMB (@lem3891413 _100607 n P) (@lem3891412 _100607 n P)). Qed.
Lemma lem3891415 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3891416 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term458 _100607 n P) = (term459 _100607 n P).
Proof. exact (MK_COMB (@lem3891415) (@lem3891414 _100607 n P)). Qed.
Lemma lem3891417 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) : (term200 _100607 n P a) = (term102 _100607 n P a).
Proof. exact (eq_refl (term200 _100607 n P a)). Qed.
Lemma lem3891418 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term206 _100607 n P) = (term206 _100607 n P).
Proof. exact (eq_refl (term206 _100607 n P)). Qed.
Lemma lem3891419 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) : (term460 _100607 n P a) = (term461 _100607 n P a).
Proof. exact (MK_COMB (@lem3891418 _100607 n P) (@lem3891417 _100607 n P a)). Qed.
Lemma lem3891420 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term462 _100607 n P) = (term463 _100607 n P).
Proof. exact (fun_ext (fun a : _100607 => @lem3891419 _100607 n P a)). Qed.
Lemma lem3891421 {_100607 : Type'} : (@ex _100607) = (@ex _100607).
Proof. exact (eq_refl (@ex _100607)). Qed.
Lemma lem3891422 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term455 _100607 n P) = (term464 _100607 n P).
Proof. exact (MK_COMB (@lem3891421 _100607) (@lem3891420 _100607 n P)). Qed.
Lemma lem3891423 {_100607 : Type'} (n : nat) (P : type686 _100607) : ((term454 _100607 n P) = (term455 _100607 n P)) = ((term208 _100607 n P) = (term464 _100607 n P)).
Proof. exact (MK_COMB (@lem3891416 _100607 n P) (@lem3891422 _100607 n P)). Qed.
Lemma lem3891424 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term208 _100607 n P) = (term464 _100607 n P).
Proof. exact (EQ_MP (@lem3891423 _100607 n P) (@lem3891408 _100607 n P)). Qed.
Lemma lem3891426 {A : Type'} (P : Prop) (Q : A -> Prop) : (term452 A P Q) = (term453 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3891427 {_100607 : Type'} (P : Prop) (Q : type686 _100607) : (term465 _100607 P Q) = (term466 _100607 P Q).
Proof. exact (@lem3891426 (_100607 -> Prop) P Q). Qed.
Lemma lem3891428 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) : (term467 _100607 n P a) = (term468 _100607 n P a).
Proof. exact (@lem3891427 _100607 (term181 _100607 n P) (term101 _100607 n P a)). Qed.
Lemma lem3891429 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) (s : _100607 -> Prop) : (term193 _100607 n P a s) = (term100 _100607 n P a s).
Proof. exact (eq_refl (term193 _100607 n P a s)). Qed.
Lemma lem3891430 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) : (term469 _100607 n P a) = (term101 _100607 n P a).
Proof. exact (fun_ext (fun s : _100607 -> Prop => @lem3891429 _100607 n P a s)). Qed.
Lemma lem3891431 {_100607 : Type'} : (@ex (_100607 -> Prop)) = (@ex (_100607 -> Prop)).
Proof. exact (eq_refl (@ex (_100607 -> Prop))). Qed.
Lemma lem3891432 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) : (term470 _100607 n P a) = (term102 _100607 n P a).
Proof. exact (MK_COMB (@lem3891431 _100607) (@lem3891430 _100607 n P a)). Qed.
Lemma lem3891433 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term206 _100607 n P) = (term206 _100607 n P).
Proof. exact (eq_refl (term206 _100607 n P)). Qed.
Lemma lem3891434 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) : (term467 _100607 n P a) = (term461 _100607 n P a).
Proof. exact (MK_COMB (@lem3891433 _100607 n P) (@lem3891432 _100607 n P a)). Qed.
Lemma lem3891435 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3891436 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) : (term471 _100607 n P a) = (term472 _100607 n P a).
Proof. exact (MK_COMB (@lem3891435) (@lem3891434 _100607 n P a)). Qed.
Lemma lem3891437 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) (s : _100607 -> Prop) : (term193 _100607 n P a s) = (term100 _100607 n P a s).
Proof. exact (eq_refl (term193 _100607 n P a s)). Qed.
Lemma lem3891438 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term206 _100607 n P) = (term206 _100607 n P).
Proof. exact (eq_refl (term206 _100607 n P)). Qed.
Lemma lem3891439 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) (s : _100607 -> Prop) : (term473 _100607 n P a s) = (term474 _100607 n P a s).
Proof. exact (MK_COMB (@lem3891438 _100607 n P) (@lem3891437 _100607 n P a s)). Qed.
Lemma lem3891440 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) : (term475 _100607 n P a) = (term476 _100607 n P a).
Proof. exact (fun_ext (fun s : _100607 -> Prop => @lem3891439 _100607 n P a s)). Qed.
Lemma lem3891441 {_100607 : Type'} : (@ex (_100607 -> Prop)) = (@ex (_100607 -> Prop)).
Proof. exact (eq_refl (@ex (_100607 -> Prop))). Qed.
Lemma lem3891442 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) : (term468 _100607 n P a) = (term477 _100607 n P a).
Proof. exact (MK_COMB (@lem3891441 _100607) (@lem3891440 _100607 n P a)). Qed.
Lemma lem3891443 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) : ((term467 _100607 n P a) = (term468 _100607 n P a)) = ((term461 _100607 n P a) = (term477 _100607 n P a)).
Proof. exact (MK_COMB (@lem3891436 _100607 n P a) (@lem3891442 _100607 n P a)). Qed.
Lemma lem3891444 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) : (term461 _100607 n P a) = (term477 _100607 n P a).
Proof. exact (EQ_MP (@lem3891443 _100607 n P a) (@lem3891428 _100607 n P a)). Qed.
Lemma lem3891445 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term463 _100607 n P) = (term478 _100607 n P).
Proof. exact (fun_ext (fun a : _100607 => @lem3891444 _100607 n P a)). Qed.
Lemma lem3891446 {_100607 : Type'} : (@ex _100607) = (@ex _100607).
Proof. exact (eq_refl (@ex _100607)). Qed.
Lemma lem3891447 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term464 _100607 n P) = (term479 _100607 n P).
Proof. exact (MK_COMB (@lem3891446 _100607) (@lem3891445 _100607 n P)). Qed.
Lemma lem3891448 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term208 _100607 n P) = (term479 _100607 n P).
Proof. exact (TRANS (@lem3891424 _100607 n P) (@lem3891447 _100607 n P)). Qed.
Lemma lem3891449 {_100607 : Type'} (P : type686 _100607) : (term265 _100607 P) = (term480 _100607 P).
Proof. exact (fun_ext (fun n : nat => @lem3891448 _100607 n P)). Qed.
Lemma lem3891450 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3891451 {_100607 : Type'} (P : type686 _100607) : (term280 _100607 P) = (term481 _100607 P).
Proof. exact (MK_COMB (@lem3891450) (@lem3891449 _100607 P)). Qed.
Lemma lem3891452 {_100607 : Type'} : (term287 _100607) = (term482 _100607).
Proof. exact (fun_ext (fun P : type686 _100607 => @lem3891451 _100607 P)). Qed.
Lemma lem3891453 {_100607 : Type'} : (@ex ((_100607 -> Prop) -> Prop)) = (@ex ((_100607 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_100607 -> Prop) -> Prop))). Qed.
Lemma lem3891454 {_100607 : Type'} : (term302 _100607) = (term483 _100607).
Proof. exact (MK_COMB (@lem3891453 _100607) (@lem3891452 _100607)). Qed.
Lemma lem3891455 {_100607 : Type'} : (term303 _100607) = (term484 _100607).
Proof. exact (MK_COMB (@lem3891404 _100607) (@lem3891454 _100607)). Qed.
Lemma lem3891457 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term236 A P Q) = (term235 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3891458 {_100607 : Type'} (P : type180 _100607) (Q : type180 _100607) : (term238 _100607 P Q) = (term237 _100607 P Q).
Proof. exact (@lem3891457 (type686 _100607) P Q). Qed.
Lemma lem3891459 {_100607 : Type'} : (term485 _100607) = (term486 _100607).
Proof. exact (@lem3891458 _100607 (term449 _100607) (term482 _100607)). Qed.
Lemma lem3891460 {_100607 : Type'} (P : type686 _100607) : (term487 _100607 P) = (term448 _100607 P).
Proof. exact (eq_refl (term487 _100607 P)). Qed.
Lemma lem3891461 {_100607 : Type'} : (term488 _100607) = (term449 _100607).
Proof. exact (fun_ext (fun P : type686 _100607 => @lem3891460 _100607 P)). Qed.
Lemma lem3891462 {_100607 : Type'} : (@ex ((_100607 -> Prop) -> Prop)) = (@ex ((_100607 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_100607 -> Prop) -> Prop))). Qed.
Lemma lem3891463 {_100607 : Type'} : (term489 _100607) = (term450 _100607).
Proof. exact (MK_COMB (@lem3891462 _100607) (@lem3891461 _100607)). Qed.
Lemma lem3891464 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3891465 {_100607 : Type'} : (term490 _100607) = (term451 _100607).
Proof. exact (MK_COMB (@lem3891464) (@lem3891463 _100607)). Qed.
Lemma lem3891466 {_100607 : Type'} (P : type686 _100607) : (term491 _100607 P) = (term481 _100607 P).
Proof. exact (eq_refl (term491 _100607 P)). Qed.
Lemma lem3891467 {_100607 : Type'} : (term492 _100607) = (term482 _100607).
Proof. exact (fun_ext (fun P : type686 _100607 => @lem3891466 _100607 P)). Qed.
Lemma lem3891468 {_100607 : Type'} : (@ex ((_100607 -> Prop) -> Prop)) = (@ex ((_100607 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_100607 -> Prop) -> Prop))). Qed.
Lemma lem3891469 {_100607 : Type'} : (term493 _100607) = (term483 _100607).
Proof. exact (MK_COMB (@lem3891468 _100607) (@lem3891467 _100607)). Qed.
Lemma lem3891470 {_100607 : Type'} : (term485 _100607) = (term484 _100607).
Proof. exact (MK_COMB (@lem3891465 _100607) (@lem3891469 _100607)). Qed.
Lemma lem3891471 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3891472 {_100607 : Type'} : (term494 _100607) = (term495 _100607).
Proof. exact (MK_COMB (@lem3891471) (@lem3891470 _100607)). Qed.
Lemma lem3891473 {_100607 : Type'} (P : type686 _100607) : (term487 _100607 P) = (term448 _100607 P).
Proof. exact (eq_refl (term487 _100607 P)). Qed.
Lemma lem3891474 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3891475 {_100607 : Type'} (P : type686 _100607) : (term496 _100607 P) = (term497 _100607 P).
Proof. exact (MK_COMB (@lem3891474) (@lem3891473 _100607 P)). Qed.
Lemma lem3891476 {_100607 : Type'} (P : type686 _100607) : (term491 _100607 P) = (term481 _100607 P).
Proof. exact (eq_refl (term491 _100607 P)). Qed.
Lemma lem3891477 {_100607 : Type'} (P : type686 _100607) : (term498 _100607 P) = (term499 _100607 P).
Proof. exact (MK_COMB (@lem3891475 _100607 P) (@lem3891476 _100607 P)). Qed.
Lemma lem3891478 {_100607 : Type'} : (term500 _100607) = (term501 _100607).
Proof. exact (fun_ext (fun P : type686 _100607 => @lem3891477 _100607 P)). Qed.
Lemma lem3891479 {_100607 : Type'} : (@ex ((_100607 -> Prop) -> Prop)) = (@ex ((_100607 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_100607 -> Prop) -> Prop))). Qed.
Lemma lem3891480 {_100607 : Type'} : (term486 _100607) = (term502 _100607).
Proof. exact (MK_COMB (@lem3891479 _100607) (@lem3891478 _100607)). Qed.
Lemma lem3891481 {_100607 : Type'} : ((term485 _100607) = (term486 _100607)) = ((term484 _100607) = (term502 _100607)).
Proof. exact (MK_COMB (@lem3891472 _100607) (@lem3891480 _100607)). Qed.
Lemma lem3891482 {_100607 : Type'} : (term484 _100607) = (term502 _100607).
Proof. exact (EQ_MP (@lem3891481 _100607) (@lem3891459 _100607)). Qed.
Lemma lem3891484 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term236 A P Q) = (term235 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3891485 (P : nat -> Prop) (Q : nat -> Prop) : (term261 P Q) = (term260 P Q).
Proof. exact (@lem3891484 nat P Q). Qed.
Lemma lem3891486 {_100607 : Type'} (P : type686 _100607) : (term503 _100607 P) = (term504 _100607 P).
Proof. exact (@lem3891485 (term447 _100607 P) (term480 _100607 P)). Qed.
Lemma lem3891487 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term505 _100607 P n) = (term446 _100607 n P).
Proof. exact (eq_refl (term505 _100607 P n)). Qed.
Lemma lem3891488 {_100607 : Type'} (P : type686 _100607) : (term506 _100607 P) = (term447 _100607 P).
Proof. exact (fun_ext (fun n : nat => @lem3891487 _100607 n P)). Qed.
Lemma lem3891489 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3891490 {_100607 : Type'} (P : type686 _100607) : (term507 _100607 P) = (term448 _100607 P).
Proof. exact (MK_COMB (@lem3891489) (@lem3891488 _100607 P)). Qed.
Lemma lem3891491 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3891492 {_100607 : Type'} (P : type686 _100607) : (term508 _100607 P) = (term497 _100607 P).
Proof. exact (MK_COMB (@lem3891491) (@lem3891490 _100607 P)). Qed.
Lemma lem3891493 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term509 _100607 P n) = (term479 _100607 n P).
Proof. exact (eq_refl (term509 _100607 P n)). Qed.
Lemma lem3891494 {_100607 : Type'} (P : type686 _100607) : (term510 _100607 P) = (term480 _100607 P).
Proof. exact (fun_ext (fun n : nat => @lem3891493 _100607 n P)). Qed.
Lemma lem3891495 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3891496 {_100607 : Type'} (P : type686 _100607) : (term511 _100607 P) = (term481 _100607 P).
Proof. exact (MK_COMB (@lem3891495) (@lem3891494 _100607 P)). Qed.
Lemma lem3891497 {_100607 : Type'} (P : type686 _100607) : (term503 _100607 P) = (term499 _100607 P).
Proof. exact (MK_COMB (@lem3891492 _100607 P) (@lem3891496 _100607 P)). Qed.
Lemma lem3891498 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3891499 {_100607 : Type'} (P : type686 _100607) : (term512 _100607 P) = (term513 _100607 P).
Proof. exact (MK_COMB (@lem3891498) (@lem3891497 _100607 P)). Qed.
Lemma lem3891500 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term505 _100607 P n) = (term446 _100607 n P).
Proof. exact (eq_refl (term505 _100607 P n)). Qed.
Lemma lem3891501 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3891502 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term514 _100607 P n) = (term515 _100607 n P).
Proof. exact (MK_COMB (@lem3891501) (@lem3891500 _100607 n P)). Qed.
Lemma lem3891503 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term509 _100607 P n) = (term479 _100607 n P).
Proof. exact (eq_refl (term509 _100607 P n)). Qed.
Lemma lem3891504 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term516 _100607 P n) = (term517 _100607 n P).
Proof. exact (MK_COMB (@lem3891502 _100607 n P) (@lem3891503 _100607 n P)). Qed.
Lemma lem3891505 {_100607 : Type'} (P : type686 _100607) : (term518 _100607 P) = (term519 _100607 P).
Proof. exact (fun_ext (fun n : nat => @lem3891504 _100607 n P)). Qed.
Lemma lem3891506 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3891507 {_100607 : Type'} (P : type686 _100607) : (term504 _100607 P) = (term520 _100607 P).
Proof. exact (MK_COMB (@lem3891506) (@lem3891505 _100607 P)). Qed.
Lemma lem3891508 {_100607 : Type'} (P : type686 _100607) : ((term503 _100607 P) = (term504 _100607 P)) = ((term499 _100607 P) = (term520 _100607 P)).
Proof. exact (MK_COMB (@lem3891499 _100607 P) (@lem3891507 _100607 P)). Qed.
Lemma lem3891509 {_100607 : Type'} (P : type686 _100607) : (term499 _100607 P) = (term520 _100607 P).
Proof. exact (EQ_MP (@lem3891508 _100607 P) (@lem3891486 _100607 P)). Qed.
Lemma lem3891513 {A : Type'} (P : A -> Prop) (Q : Prop) : (term342 A P Q) = (term343 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3891514 {_100607 : Type'} (P : type686 _100607) (Q : Prop) : (term344 _100607 P Q) = (term345 _100607 P Q).
Proof. exact (@lem3891513 (_100607 -> Prop) P Q). Qed.
Lemma lem3891515 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term521 _100607 n P) = (term522 _100607 n P).
Proof. exact (@lem3891514 _100607 (term445 _100607 n P) (term479 _100607 n P)). Qed.
Lemma lem3891516 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term523 _100607 n P s) = (term444 _100607 s n P).
Proof. exact (eq_refl (term523 _100607 n P s)). Qed.
Lemma lem3891517 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term524 _100607 n P) = (term445 _100607 n P).
Proof. exact (fun_ext (fun s : _100607 -> Prop => @lem3891516 _100607 s n P)). Qed.
Lemma lem3891518 {_100607 : Type'} : (@ex (_100607 -> Prop)) = (@ex (_100607 -> Prop)).
Proof. exact (eq_refl (@ex (_100607 -> Prop))). Qed.
Lemma lem3891519 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term525 _100607 n P) = (term446 _100607 n P).
Proof. exact (MK_COMB (@lem3891518 _100607) (@lem3891517 _100607 n P)). Qed.
Lemma lem3891520 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3891521 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term526 _100607 n P) = (term515 _100607 n P).
Proof. exact (MK_COMB (@lem3891520) (@lem3891519 _100607 n P)). Qed.
Lemma lem3891522 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term479 _100607 n P) = (term479 _100607 n P).
Proof. exact (eq_refl (term479 _100607 n P)). Qed.
Lemma lem3891523 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term521 _100607 n P) = (term517 _100607 n P).
Proof. exact (MK_COMB (@lem3891521 _100607 n P) (@lem3891522 _100607 n P)). Qed.
Lemma lem3891524 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3891525 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term527 _100607 n P) = (term528 _100607 n P).
Proof. exact (MK_COMB (@lem3891524) (@lem3891523 _100607 n P)). Qed.
Lemma lem3891526 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term523 _100607 n P s) = (term444 _100607 s n P).
Proof. exact (eq_refl (term523 _100607 n P s)). Qed.
Lemma lem3891527 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3891528 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term529 _100607 n P s) = (term530 _100607 s n P).
Proof. exact (MK_COMB (@lem3891527) (@lem3891526 _100607 s n P)). Qed.
Lemma lem3891529 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term479 _100607 n P) = (term479 _100607 n P).
Proof. exact (eq_refl (term479 _100607 n P)). Qed.
Lemma lem3891530 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term531 _100607 s n P) = (term532 _100607 s n P).
Proof. exact (MK_COMB (@lem3891528 _100607 s n P) (@lem3891529 _100607 n P)). Qed.
Lemma lem3891531 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term533 _100607 n P) = (term534 _100607 n P).
Proof. exact (fun_ext (fun s : _100607 -> Prop => @lem3891530 _100607 s n P)). Qed.
Lemma lem3891532 {_100607 : Type'} : (@ex (_100607 -> Prop)) = (@ex (_100607 -> Prop)).
Proof. exact (eq_refl (@ex (_100607 -> Prop))). Qed.
Lemma lem3891533 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term522 _100607 n P) = (term535 _100607 n P).
Proof. exact (MK_COMB (@lem3891532 _100607) (@lem3891531 _100607 n P)). Qed.
Lemma lem3891534 {_100607 : Type'} (n : nat) (P : type686 _100607) : ((term521 _100607 n P) = (term522 _100607 n P)) = ((term517 _100607 n P) = (term535 _100607 n P)).
Proof. exact (MK_COMB (@lem3891525 _100607 n P) (@lem3891533 _100607 n P)). Qed.
Lemma lem3891535 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term517 _100607 n P) = (term535 _100607 n P).
Proof. exact (EQ_MP (@lem3891534 _100607 n P) (@lem3891515 _100607 n P)). Qed.
Lemma lem3891537 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term236 A P Q) = (term235 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3891538 {_100607 : Type'} (P : _100607 -> Prop) (Q : _100607 -> Prop) : (term236 _100607 P Q) = (term235 _100607 P Q).
Proof. exact (@lem3891537 _100607 P Q). Qed.
Lemma lem3891539 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term536 _100607 s n P) = (term537 _100607 s n P).
Proof. exact (@lem3891538 _100607 (term443 _100607 s n P) (term478 _100607 n P)). Qed.
Lemma lem3891540 {_100607 : Type'} (a : _100607) (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term538 _100607 s n P a) = (term442 _100607 a s n P).
Proof. exact (eq_refl (term538 _100607 s n P a)). Qed.
Lemma lem3891541 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term539 _100607 s n P) = (term443 _100607 s n P).
Proof. exact (fun_ext (fun a : _100607 => @lem3891540 _100607 a s n P)). Qed.
Lemma lem3891542 {_100607 : Type'} : (@ex _100607) = (@ex _100607).
Proof. exact (eq_refl (@ex _100607)). Qed.
Lemma lem3891543 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term540 _100607 s n P) = (term444 _100607 s n P).
Proof. exact (MK_COMB (@lem3891542 _100607) (@lem3891541 _100607 s n P)). Qed.
Lemma lem3891544 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3891545 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term541 _100607 s n P) = (term530 _100607 s n P).
Proof. exact (MK_COMB (@lem3891544) (@lem3891543 _100607 s n P)). Qed.
Lemma lem3891546 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) : (term542 _100607 n P a) = (term477 _100607 n P a).
Proof. exact (eq_refl (term542 _100607 n P a)). Qed.
Lemma lem3891547 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term543 _100607 n P) = (term478 _100607 n P).
Proof. exact (fun_ext (fun a : _100607 => @lem3891546 _100607 n P a)). Qed.
Lemma lem3891548 {_100607 : Type'} : (@ex _100607) = (@ex _100607).
Proof. exact (eq_refl (@ex _100607)). Qed.
Lemma lem3891549 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term544 _100607 n P) = (term479 _100607 n P).
Proof. exact (MK_COMB (@lem3891548 _100607) (@lem3891547 _100607 n P)). Qed.
Lemma lem3891550 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term536 _100607 s n P) = (term532 _100607 s n P).
Proof. exact (MK_COMB (@lem3891545 _100607 s n P) (@lem3891549 _100607 n P)). Qed.
Lemma lem3891551 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3891552 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term545 _100607 s n P) = (term546 _100607 s n P).
Proof. exact (MK_COMB (@lem3891551) (@lem3891550 _100607 s n P)). Qed.
Lemma lem3891553 {_100607 : Type'} (a : _100607) (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term538 _100607 s n P a) = (term442 _100607 a s n P).
Proof. exact (eq_refl (term538 _100607 s n P a)). Qed.
Lemma lem3891554 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3891555 {_100607 : Type'} (a : _100607) (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term547 _100607 s n P a) = (term548 _100607 a s n P).
Proof. exact (MK_COMB (@lem3891554) (@lem3891553 _100607 a s n P)). Qed.
Lemma lem3891556 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) : (term542 _100607 n P a) = (term477 _100607 n P a).
Proof. exact (eq_refl (term542 _100607 n P a)). Qed.
Lemma lem3891557 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) : (term549 _100607 s n P a) = (term550 _100607 s n P a).
Proof. exact (MK_COMB (@lem3891555 _100607 a s n P) (@lem3891556 _100607 n P a)). Qed.
Lemma lem3891558 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term551 _100607 s n P) = (term552 _100607 s n P).
Proof. exact (fun_ext (fun a : _100607 => @lem3891557 _100607 s n P a)). Qed.
Lemma lem3891559 {_100607 : Type'} : (@ex _100607) = (@ex _100607).
Proof. exact (eq_refl (@ex _100607)). Qed.
Lemma lem3891560 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term537 _100607 s n P) = (term553 _100607 s n P).
Proof. exact (MK_COMB (@lem3891559 _100607) (@lem3891558 _100607 s n P)). Qed.
Lemma lem3891561 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : ((term536 _100607 s n P) = (term537 _100607 s n P)) = ((term532 _100607 s n P) = (term553 _100607 s n P)).
Proof. exact (MK_COMB (@lem3891552 _100607 s n P) (@lem3891560 _100607 s n P)). Qed.
Lemma lem3891562 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term532 _100607 s n P) = (term553 _100607 s n P).
Proof. exact (EQ_MP (@lem3891561 _100607 s n P) (@lem3891539 _100607 s n P)). Qed.
Lemma lem3891564 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term236 A P Q) = (term235 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3891565 {_100607 : Type'} (P : type686 _100607) (Q : type686 _100607) : (term554 _100607 P Q) = (term555 _100607 P Q).
Proof. exact (@lem3891564 (_100607 -> Prop) P Q). Qed.
Lemma lem3891566 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) : (term556 _100607 s n P a) = (term557 _100607 s n P a).
Proof. exact (@lem3891565 _100607 (term441 _100607 a s n P) (term476 _100607 n P a)). Qed.
Lemma lem3891567 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term558 _100607 a s n P t) = (term439 _100607 a t s n P).
Proof. exact (eq_refl (term558 _100607 a s n P t)). Qed.
Lemma lem3891568 {_100607 : Type'} (a : _100607) (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term559 _100607 a s n P) = (term441 _100607 a s n P).
Proof. exact (fun_ext (fun t : _100607 -> Prop => @lem3891567 _100607 a t s n P)). Qed.
Lemma lem3891569 {_100607 : Type'} : (@ex (_100607 -> Prop)) = (@ex (_100607 -> Prop)).
Proof. exact (eq_refl (@ex (_100607 -> Prop))). Qed.
Lemma lem3891570 {_100607 : Type'} (a : _100607) (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term560 _100607 a s n P) = (term442 _100607 a s n P).
Proof. exact (MK_COMB (@lem3891569 _100607) (@lem3891568 _100607 a s n P)). Qed.
Lemma lem3891571 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3891572 {_100607 : Type'} (a : _100607) (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term561 _100607 a s n P) = (term548 _100607 a s n P).
Proof. exact (MK_COMB (@lem3891571) (@lem3891570 _100607 a s n P)). Qed.
Lemma lem3891573 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) : (term562 _100607 n P a t) = (term474 _100607 n P a t).
Proof. exact (eq_refl (term562 _100607 n P a t)). Qed.
Lemma lem3891574 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) : (term563 _100607 n P a) = (term476 _100607 n P a).
Proof. exact (fun_ext (fun t : _100607 -> Prop => @lem3891573 _100607 n P a t)). Qed.
Lemma lem3891575 {_100607 : Type'} : (@ex (_100607 -> Prop)) = (@ex (_100607 -> Prop)).
Proof. exact (eq_refl (@ex (_100607 -> Prop))). Qed.
Lemma lem3891576 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) : (term564 _100607 n P a) = (term477 _100607 n P a).
Proof. exact (MK_COMB (@lem3891575 _100607) (@lem3891574 _100607 n P a)). Qed.
Lemma lem3891577 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) : (term556 _100607 s n P a) = (term550 _100607 s n P a).
Proof. exact (MK_COMB (@lem3891572 _100607 a s n P) (@lem3891576 _100607 n P a)). Qed.
Lemma lem3891578 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3891579 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) : (term565 _100607 s n P a) = (term566 _100607 s n P a).
Proof. exact (MK_COMB (@lem3891578) (@lem3891577 _100607 s n P a)). Qed.
Lemma lem3891580 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term558 _100607 a s n P t) = (term439 _100607 a t s n P).
Proof. exact (eq_refl (term558 _100607 a s n P t)). Qed.
Lemma lem3891581 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3891582 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term567 _100607 a s n P t) = (term568 _100607 a t s n P).
Proof. exact (MK_COMB (@lem3891581) (@lem3891580 _100607 a t s n P)). Qed.
Lemma lem3891583 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) : (term562 _100607 n P a t) = (term474 _100607 n P a t).
Proof. exact (eq_refl (term562 _100607 n P a t)). Qed.
Lemma lem3891584 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) : (term569 _100607 s n P a t) = (term570 _100607 s n P a t).
Proof. exact (MK_COMB (@lem3891582 _100607 a t s n P) (@lem3891583 _100607 n P a t)). Qed.
Lemma lem3891585 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) : (term571 _100607 s n P a) = (term572 _100607 s n P a).
Proof. exact (fun_ext (fun t : _100607 -> Prop => @lem3891584 _100607 s n P a t)). Qed.
Lemma lem3891586 {_100607 : Type'} : (@ex (_100607 -> Prop)) = (@ex (_100607 -> Prop)).
Proof. exact (eq_refl (@ex (_100607 -> Prop))). Qed.
Lemma lem3891587 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) : (term557 _100607 s n P a) = (term573 _100607 s n P a).
Proof. exact (MK_COMB (@lem3891586 _100607) (@lem3891585 _100607 s n P a)). Qed.
Lemma lem3891588 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) : ((term556 _100607 s n P a) = (term557 _100607 s n P a)) = ((term550 _100607 s n P a) = (term573 _100607 s n P a)).
Proof. exact (MK_COMB (@lem3891579 _100607 s n P a) (@lem3891587 _100607 s n P a)). Qed.
Lemma lem3891589 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) : (term550 _100607 s n P a) = (term573 _100607 s n P a).
Proof. exact (EQ_MP (@lem3891588 _100607 s n P a) (@lem3891566 _100607 s n P a)). Qed.
Lemma lem3891592 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) : (term574 _100607 s n P a) = (term574 _100607 s n P a).
Proof. exact (eq_refl (term574 _100607 s n P a)). Qed.
Lemma lem3891593 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) : (term574 _100607 s n P a) = ((term550 _100607 s n P a) = (term573 _100607 s n P a)).
Proof. exact (eq_refl (term574 _100607 s n P a)). Qed.
Lemma lem3891594 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) : (term575 _100607 s n P a) = (term575 _100607 s n P a).
Proof. exact (eq_refl (term575 _100607 s n P a)). Qed.
Lemma lem3891595 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) : ((term574 _100607 s n P a) = (term574 _100607 s n P a)) = ((term574 _100607 s n P a) = ((term550 _100607 s n P a) = (term573 _100607 s n P a))).
Proof. exact (MK_COMB (@lem3891594 _100607 s n P a) (@lem3891593 _100607 s n P a)). Qed.
Lemma lem3891596 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) : (term574 _100607 s n P a) = ((term550 _100607 s n P a) = (term573 _100607 s n P a)).
Proof. exact (eq_refl (term574 _100607 s n P a)). Qed.
Lemma lem3891597 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3891598 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) : (term575 _100607 s n P a) = (term576 _100607 s n P a).
Proof. exact (MK_COMB (@lem3891597) (@lem3891596 _100607 s n P a)). Qed.
Lemma lem3891599 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) : ((term550 _100607 s n P a) = (term573 _100607 s n P a)) = ((term550 _100607 s n P a) = (term573 _100607 s n P a)).
Proof. exact (eq_refl ((term550 _100607 s n P a) = (term573 _100607 s n P a))). Qed.
Lemma lem3891600 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) : ((term574 _100607 s n P a) = ((term550 _100607 s n P a) = (term573 _100607 s n P a))) = (((term550 _100607 s n P a) = (term573 _100607 s n P a)) = ((term550 _100607 s n P a) = (term573 _100607 s n P a))).
Proof. exact (MK_COMB (@lem3891598 _100607 s n P a) (@lem3891599 _100607 s n P a)). Qed.
Lemma lem3891601 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) : ((term574 _100607 s n P a) = (term574 _100607 s n P a)) = (((term550 _100607 s n P a) = (term573 _100607 s n P a)) = ((term550 _100607 s n P a) = (term573 _100607 s n P a))).
Proof. exact (TRANS (@lem3891595 _100607 s n P a) (@lem3891600 _100607 s n P a)). Qed.
Lemma lem3891602 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) : ((term550 _100607 s n P a) = (term573 _100607 s n P a)) = ((term550 _100607 s n P a) = (term573 _100607 s n P a)).
Proof. exact (EQ_MP (@lem3891601 _100607 s n P a) (@lem3891592 _100607 s n P a)). Qed.
Lemma lem3891603 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) : (term550 _100607 s n P a) = (term573 _100607 s n P a).
Proof. exact (EQ_MP (@lem3891602 _100607 s n P a) (@lem3891589 _100607 s n P a)). Qed.
Lemma lem3891604 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term552 _100607 s n P) = (term577 _100607 s n P).
Proof. exact (fun_ext (fun a : _100607 => @lem3891603 _100607 s n P a)). Qed.
Lemma lem3891605 {_100607 : Type'} : (@ex _100607) = (@ex _100607).
Proof. exact (eq_refl (@ex _100607)). Qed.
Lemma lem3891606 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term553 _100607 s n P) = (term578 _100607 s n P).
Proof. exact (MK_COMB (@lem3891605 _100607) (@lem3891604 _100607 s n P)). Qed.
Lemma lem3891607 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term532 _100607 s n P) = (term578 _100607 s n P).
Proof. exact (TRANS (@lem3891562 _100607 s n P) (@lem3891606 _100607 s n P)). Qed.
Lemma lem3891608 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term534 _100607 n P) = (term579 _100607 n P).
Proof. exact (fun_ext (fun s : _100607 -> Prop => @lem3891607 _100607 s n P)). Qed.
Lemma lem3891609 {_100607 : Type'} : (@ex (_100607 -> Prop)) = (@ex (_100607 -> Prop)).
Proof. exact (eq_refl (@ex (_100607 -> Prop))). Qed.
Lemma lem3891610 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term535 _100607 n P) = (term580 _100607 n P).
Proof. exact (MK_COMB (@lem3891609 _100607) (@lem3891608 _100607 n P)). Qed.
Lemma lem3891611 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term517 _100607 n P) = (term580 _100607 n P).
Proof. exact (TRANS (@lem3891535 _100607 n P) (@lem3891610 _100607 n P)). Qed.
Lemma lem3891612 {_100607 : Type'} (P : type686 _100607) : (term519 _100607 P) = (term581 _100607 P).
Proof. exact (fun_ext (fun n : nat => @lem3891611 _100607 n P)). Qed.
Lemma lem3891613 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3891614 {_100607 : Type'} (P : type686 _100607) : (term520 _100607 P) = (term582 _100607 P).
Proof. exact (MK_COMB (@lem3891613) (@lem3891612 _100607 P)). Qed.
Lemma lem3891615 {_100607 : Type'} (P : type686 _100607) : (term499 _100607 P) = (term582 _100607 P).
Proof. exact (TRANS (@lem3891509 _100607 P) (@lem3891614 _100607 P)). Qed.
Lemma lem3891616 {_100607 : Type'} : (term501 _100607) = (term583 _100607).
Proof. exact (fun_ext (fun P : type686 _100607 => @lem3891615 _100607 P)). Qed.
Lemma lem3891617 {_100607 : Type'} : (@ex ((_100607 -> Prop) -> Prop)) = (@ex ((_100607 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_100607 -> Prop) -> Prop))). Qed.
Lemma lem3891618 {_100607 : Type'} : (term502 _100607) = (term584 _100607).
Proof. exact (MK_COMB (@lem3891617 _100607) (@lem3891616 _100607)). Qed.
Lemma lem3891619 {_100607 : Type'} : (term484 _100607) = (term584 _100607).
Proof. exact (TRANS (@lem3891482 _100607) (@lem3891618 _100607)). Qed.
Lemma lem3891620 {_100607 : Type'} : (term303 _100607) = (term584 _100607).
Proof. exact (TRANS (@lem3891455 _100607) (@lem3891619 _100607)). Qed.
Lemma lem3891621 {_100607 : Type'} : (term304 _100607) = (term585 _100607).
Proof. exact (MK_COMB (@lem3891256 _100607) (@lem3891620 _100607)). Qed.
Lemma lem3891623 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term236 A P Q) = (term235 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3891624 {_100607 : Type'} (P : type180 _100607) (Q : type180 _100607) : (term238 _100607 P Q) = (term237 _100607 P Q).
Proof. exact (@lem3891623 (type686 _100607) P Q). Qed.
Lemma lem3891625 {_100607 : Type'} : (term586 _100607) = (term587 _100607).
Proof. exact (@lem3891624 _100607 (term361 _100607) (term583 _100607)). Qed.
Lemma lem3891626 {_100607 : Type'} (P : type686 _100607) : (term588 _100607 P) = (term360 _100607 P).
Proof. exact (eq_refl (term588 _100607 P)). Qed.
Lemma lem3891627 {_100607 : Type'} : (term589 _100607) = (term361 _100607).
Proof. exact (fun_ext (fun P : type686 _100607 => @lem3891626 _100607 P)). Qed.
Lemma lem3891628 {_100607 : Type'} : (@ex ((_100607 -> Prop) -> Prop)) = (@ex ((_100607 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_100607 -> Prop) -> Prop))). Qed.
Lemma lem3891629 {_100607 : Type'} : (term590 _100607) = (term362 _100607).
Proof. exact (MK_COMB (@lem3891628 _100607) (@lem3891627 _100607)). Qed.
Lemma lem3891630 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3891631 {_100607 : Type'} : (term591 _100607) = (term363 _100607).
Proof. exact (MK_COMB (@lem3891630) (@lem3891629 _100607)). Qed.
Lemma lem3891632 {_100607 : Type'} (P : type686 _100607) : (term592 _100607 P) = (term582 _100607 P).
Proof. exact (eq_refl (term592 _100607 P)). Qed.
Lemma lem3891633 {_100607 : Type'} : (term593 _100607) = (term583 _100607).
Proof. exact (fun_ext (fun P : type686 _100607 => @lem3891632 _100607 P)). Qed.
Lemma lem3891634 {_100607 : Type'} : (@ex ((_100607 -> Prop) -> Prop)) = (@ex ((_100607 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_100607 -> Prop) -> Prop))). Qed.
Lemma lem3891635 {_100607 : Type'} : (term594 _100607) = (term584 _100607).
Proof. exact (MK_COMB (@lem3891634 _100607) (@lem3891633 _100607)). Qed.
Lemma lem3891636 {_100607 : Type'} : (term586 _100607) = (term585 _100607).
Proof. exact (MK_COMB (@lem3891631 _100607) (@lem3891635 _100607)). Qed.
Lemma lem3891637 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3891638 {_100607 : Type'} : (term595 _100607) = (term596 _100607).
Proof. exact (MK_COMB (@lem3891637) (@lem3891636 _100607)). Qed.
Lemma lem3891639 {_100607 : Type'} (P : type686 _100607) : (term588 _100607 P) = (term360 _100607 P).
Proof. exact (eq_refl (term588 _100607 P)). Qed.
Lemma lem3891640 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3891641 {_100607 : Type'} (P : type686 _100607) : (term597 _100607 P) = (term598 _100607 P).
Proof. exact (MK_COMB (@lem3891640) (@lem3891639 _100607 P)). Qed.
Lemma lem3891642 {_100607 : Type'} (P : type686 _100607) : (term592 _100607 P) = (term582 _100607 P).
Proof. exact (eq_refl (term592 _100607 P)). Qed.
Lemma lem3891643 {_100607 : Type'} (P : type686 _100607) : (term599 _100607 P) = (term600 _100607 P).
Proof. exact (MK_COMB (@lem3891641 _100607 P) (@lem3891642 _100607 P)). Qed.
Lemma lem3891644 {_100607 : Type'} : (term601 _100607) = (term602 _100607).
Proof. exact (fun_ext (fun P : type686 _100607 => @lem3891643 _100607 P)). Qed.
Lemma lem3891645 {_100607 : Type'} : (@ex ((_100607 -> Prop) -> Prop)) = (@ex ((_100607 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_100607 -> Prop) -> Prop))). Qed.
Lemma lem3891646 {_100607 : Type'} : (term587 _100607) = (term603 _100607).
Proof. exact (MK_COMB (@lem3891645 _100607) (@lem3891644 _100607)). Qed.
Lemma lem3891647 {_100607 : Type'} : ((term586 _100607) = (term587 _100607)) = ((term585 _100607) = (term603 _100607)).
Proof. exact (MK_COMB (@lem3891638 _100607) (@lem3891646 _100607)). Qed.
Lemma lem3891648 {_100607 : Type'} : (term585 _100607) = (term603 _100607).
Proof. exact (EQ_MP (@lem3891647 _100607) (@lem3891625 _100607)). Qed.
Lemma lem3891652 {A : Type'} (P : A -> Prop) (Q : Prop) : (term342 A P Q) = (term343 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3891653 {_100607 : Type'} (P : type686 _100607) (Q : Prop) : (term344 _100607 P Q) = (term345 _100607 P Q).
Proof. exact (@lem3891652 (_100607 -> Prop) P Q). Qed.
Lemma lem3891654 {_100607 : Type'} (P : type686 _100607) : (term604 _100607 P) = (term605 _100607 P).
Proof. exact (@lem3891653 _100607 (term359 _100607 P) (term582 _100607 P)). Qed.
Lemma lem3891655 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) : (term606 _100607 P s) = (term357 _100607 s P).
Proof. exact (eq_refl (term606 _100607 P s)). Qed.
Lemma lem3891656 {_100607 : Type'} (P : type686 _100607) : (term607 _100607 P) = (term359 _100607 P).
Proof. exact (fun_ext (fun s : _100607 -> Prop => @lem3891655 _100607 s P)). Qed.
Lemma lem3891657 {_100607 : Type'} : (@ex (_100607 -> Prop)) = (@ex (_100607 -> Prop)).
Proof. exact (eq_refl (@ex (_100607 -> Prop))). Qed.
Lemma lem3891658 {_100607 : Type'} (P : type686 _100607) : (term608 _100607 P) = (term360 _100607 P).
Proof. exact (MK_COMB (@lem3891657 _100607) (@lem3891656 _100607 P)). Qed.
Lemma lem3891659 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3891660 {_100607 : Type'} (P : type686 _100607) : (term609 _100607 P) = (term598 _100607 P).
Proof. exact (MK_COMB (@lem3891659) (@lem3891658 _100607 P)). Qed.
Lemma lem3891661 {_100607 : Type'} (P : type686 _100607) : (term582 _100607 P) = (term582 _100607 P).
Proof. exact (eq_refl (term582 _100607 P)). Qed.
Lemma lem3891662 {_100607 : Type'} (P : type686 _100607) : (term604 _100607 P) = (term600 _100607 P).
Proof. exact (MK_COMB (@lem3891660 _100607 P) (@lem3891661 _100607 P)). Qed.
Lemma lem3891663 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3891664 {_100607 : Type'} (P : type686 _100607) : (term610 _100607 P) = (term611 _100607 P).
Proof. exact (MK_COMB (@lem3891663) (@lem3891662 _100607 P)). Qed.
Lemma lem3891665 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) : (term606 _100607 P s) = (term357 _100607 s P).
Proof. exact (eq_refl (term606 _100607 P s)). Qed.
Lemma lem3891666 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3891667 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) : (term612 _100607 P s) = (term613 _100607 s P).
Proof. exact (MK_COMB (@lem3891666) (@lem3891665 _100607 s P)). Qed.
Lemma lem3891668 {_100607 : Type'} (P : type686 _100607) : (term582 _100607 P) = (term582 _100607 P).
Proof. exact (eq_refl (term582 _100607 P)). Qed.
Lemma lem3891669 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) : (term614 _100607 s P) = (term615 _100607 s P).
Proof. exact (MK_COMB (@lem3891667 _100607 s P) (@lem3891668 _100607 P)). Qed.
Lemma lem3891670 {_100607 : Type'} (P : type686 _100607) : (term616 _100607 P) = (term617 _100607 P).
Proof. exact (fun_ext (fun s : _100607 -> Prop => @lem3891669 _100607 s P)). Qed.
Lemma lem3891671 {_100607 : Type'} : (@ex (_100607 -> Prop)) = (@ex (_100607 -> Prop)).
Proof. exact (eq_refl (@ex (_100607 -> Prop))). Qed.
Lemma lem3891672 {_100607 : Type'} (P : type686 _100607) : (term605 _100607 P) = (term618 _100607 P).
Proof. exact (MK_COMB (@lem3891671 _100607) (@lem3891670 _100607 P)). Qed.
Lemma lem3891673 {_100607 : Type'} (P : type686 _100607) : ((term604 _100607 P) = (term605 _100607 P)) = ((term600 _100607 P) = (term618 _100607 P)).
Proof. exact (MK_COMB (@lem3891664 _100607 P) (@lem3891672 _100607 P)). Qed.
Lemma lem3891674 {_100607 : Type'} (P : type686 _100607) : (term600 _100607 P) = (term618 _100607 P).
Proof. exact (EQ_MP (@lem3891673 _100607 P) (@lem3891654 _100607 P)). Qed.
Lemma lem3891676 {A : Type'} (P : Prop) (Q : A -> Prop) : (term619 A P Q) = (term620 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3891677 (P : Prop) (Q : nat -> Prop) : (term621 P Q) = (term622 P Q).
Proof. exact (@lem3891676 nat P Q). Qed.
Lemma lem3891678 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) : (term623 _100607 s P) = (term624 _100607 s P).
Proof. exact (@lem3891677 (term357 _100607 s P) (term581 _100607 P)). Qed.
Lemma lem3891679 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term625 _100607 P n) = (term580 _100607 n P).
Proof. exact (eq_refl (term625 _100607 P n)). Qed.
Lemma lem3891680 {_100607 : Type'} (P : type686 _100607) : (term626 _100607 P) = (term581 _100607 P).
Proof. exact (fun_ext (fun n : nat => @lem3891679 _100607 n P)). Qed.
Lemma lem3891681 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3891682 {_100607 : Type'} (P : type686 _100607) : (term627 _100607 P) = (term582 _100607 P).
Proof. exact (MK_COMB (@lem3891681) (@lem3891680 _100607 P)). Qed.
Lemma lem3891683 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) : (term613 _100607 s P) = (term613 _100607 s P).
Proof. exact (eq_refl (term613 _100607 s P)). Qed.
Lemma lem3891684 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) : (term623 _100607 s P) = (term615 _100607 s P).
Proof. exact (MK_COMB (@lem3891683 _100607 s P) (@lem3891682 _100607 P)). Qed.
Lemma lem3891685 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3891686 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) : (term628 _100607 s P) = (term629 _100607 s P).
Proof. exact (MK_COMB (@lem3891685) (@lem3891684 _100607 s P)). Qed.
Lemma lem3891687 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term625 _100607 P n) = (term580 _100607 n P).
Proof. exact (eq_refl (term625 _100607 P n)). Qed.
Lemma lem3891688 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) : (term613 _100607 s P) = (term613 _100607 s P).
Proof. exact (eq_refl (term613 _100607 s P)). Qed.
Lemma lem3891689 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term630 _100607 s P n) = (term631 _100607 s n P).
Proof. exact (MK_COMB (@lem3891688 _100607 s P) (@lem3891687 _100607 n P)). Qed.
Lemma lem3891690 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) : (term632 _100607 s P) = (term633 _100607 s P).
Proof. exact (fun_ext (fun n : nat => @lem3891689 _100607 s n P)). Qed.
Lemma lem3891691 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3891692 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) : (term624 _100607 s P) = (term634 _100607 s P).
Proof. exact (MK_COMB (@lem3891691) (@lem3891690 _100607 s P)). Qed.
Lemma lem3891693 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) : ((term623 _100607 s P) = (term624 _100607 s P)) = ((term615 _100607 s P) = (term634 _100607 s P)).
Proof. exact (MK_COMB (@lem3891686 _100607 s P) (@lem3891692 _100607 s P)). Qed.
Lemma lem3891694 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) : (term615 _100607 s P) = (term634 _100607 s P).
Proof. exact (EQ_MP (@lem3891693 _100607 s P) (@lem3891678 _100607 s P)). Qed.
Lemma lem3891696 {A : Type'} (P : Prop) (Q : A -> Prop) : (term619 A P Q) = (term620 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3891697 {_100607 : Type'} (P : Prop) (Q : type686 _100607) : (term635 _100607 P Q) = (term636 _100607 P Q).
Proof. exact (@lem3891696 (_100607 -> Prop) P Q). Qed.
Lemma lem3891698 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term637 _100607 s n P) = (term638 _100607 s n P).
Proof. exact (@lem3891697 _100607 (term357 _100607 s P) (term579 _100607 n P)). Qed.
Lemma lem3891699 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term639 _100607 n P s) = (term578 _100607 s n P).
Proof. exact (eq_refl (term639 _100607 n P s)). Qed.
Lemma lem3891700 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term640 _100607 n P) = (term579 _100607 n P).
Proof. exact (fun_ext (fun s : _100607 -> Prop => @lem3891699 _100607 s n P)). Qed.
Lemma lem3891701 {_100607 : Type'} : (@ex (_100607 -> Prop)) = (@ex (_100607 -> Prop)).
Proof. exact (eq_refl (@ex (_100607 -> Prop))). Qed.
Lemma lem3891702 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term641 _100607 n P) = (term580 _100607 n P).
Proof. exact (MK_COMB (@lem3891701 _100607) (@lem3891700 _100607 n P)). Qed.
Lemma lem3891703 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) : (term613 _100607 s P) = (term613 _100607 s P).
Proof. exact (eq_refl (term613 _100607 s P)). Qed.
Lemma lem3891704 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term637 _100607 s n P) = (term631 _100607 s n P).
Proof. exact (MK_COMB (@lem3891703 _100607 s P) (@lem3891702 _100607 n P)). Qed.
Lemma lem3891705 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3891706 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term642 _100607 s n P) = (term643 _100607 s n P).
Proof. exact (MK_COMB (@lem3891705) (@lem3891704 _100607 s n P)). Qed.
Lemma lem3891707 {_100607 : Type'} (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term639 _100607 n P s') = (term578 _100607 s' n P).
Proof. exact (eq_refl (term639 _100607 n P s')). Qed.
Lemma lem3891708 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) : (term613 _100607 s P) = (term613 _100607 s P).
Proof. exact (eq_refl (term613 _100607 s P)). Qed.
Lemma lem3891709 {_100607 : Type'} (s : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term644 _100607 s n P s') = (term645 _100607 s s' n P).
Proof. exact (MK_COMB (@lem3891708 _100607 s P) (@lem3891707 _100607 s' n P)). Qed.
Lemma lem3891710 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term646 _100607 s n P) = (term647 _100607 s n P).
Proof. exact (fun_ext (fun s' : _100607 -> Prop => @lem3891709 _100607 s s' n P)). Qed.
Lemma lem3891711 {_100607 : Type'} : (@ex (_100607 -> Prop)) = (@ex (_100607 -> Prop)).
Proof. exact (eq_refl (@ex (_100607 -> Prop))). Qed.
Lemma lem3891712 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term638 _100607 s n P) = (term648 _100607 s n P).
Proof. exact (MK_COMB (@lem3891711 _100607) (@lem3891710 _100607 s n P)). Qed.
Lemma lem3891713 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : ((term637 _100607 s n P) = (term638 _100607 s n P)) = ((term631 _100607 s n P) = (term648 _100607 s n P)).
Proof. exact (MK_COMB (@lem3891706 _100607 s n P) (@lem3891712 _100607 s n P)). Qed.
Lemma lem3891714 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term631 _100607 s n P) = (term648 _100607 s n P).
Proof. exact (EQ_MP (@lem3891713 _100607 s n P) (@lem3891698 _100607 s n P)). Qed.
Lemma lem3891716 {A : Type'} (P : Prop) (Q : A -> Prop) : (term619 A P Q) = (term620 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3891717 {_100607 : Type'} (P : Prop) (Q : _100607 -> Prop) : (term619 _100607 P Q) = (term620 _100607 P Q).
Proof. exact (@lem3891716 _100607 P Q). Qed.
Lemma lem3891718 {_100607 : Type'} (s : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term649 _100607 s s' n P) = (term650 _100607 s s' n P).
Proof. exact (@lem3891717 _100607 (term357 _100607 s P) (term577 _100607 s' n P)). Qed.
Lemma lem3891719 {_100607 : Type'} (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) : (term651 _100607 s' n P a) = (term573 _100607 s' n P a).
Proof. exact (eq_refl (term651 _100607 s' n P a)). Qed.
Lemma lem3891720 {_100607 : Type'} (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term652 _100607 s' n P) = (term577 _100607 s' n P).
Proof. exact (fun_ext (fun a : _100607 => @lem3891719 _100607 s' n P a)). Qed.
Lemma lem3891721 {_100607 : Type'} : (@ex _100607) = (@ex _100607).
Proof. exact (eq_refl (@ex _100607)). Qed.
Lemma lem3891722 {_100607 : Type'} (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term653 _100607 s' n P) = (term578 _100607 s' n P).
Proof. exact (MK_COMB (@lem3891721 _100607) (@lem3891720 _100607 s' n P)). Qed.
Lemma lem3891723 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) : (term613 _100607 s P) = (term613 _100607 s P).
Proof. exact (eq_refl (term613 _100607 s P)). Qed.
Lemma lem3891724 {_100607 : Type'} (s : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term649 _100607 s s' n P) = (term645 _100607 s s' n P).
Proof. exact (MK_COMB (@lem3891723 _100607 s P) (@lem3891722 _100607 s' n P)). Qed.
Lemma lem3891725 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3891726 {_100607 : Type'} (s : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term654 _100607 s s' n P) = (term655 _100607 s s' n P).
Proof. exact (MK_COMB (@lem3891725) (@lem3891724 _100607 s s' n P)). Qed.
Lemma lem3891727 {_100607 : Type'} (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) : (term651 _100607 s' n P a) = (term573 _100607 s' n P a).
Proof. exact (eq_refl (term651 _100607 s' n P a)). Qed.
Lemma lem3891728 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) : (term613 _100607 s P) = (term613 _100607 s P).
Proof. exact (eq_refl (term613 _100607 s P)). Qed.
Lemma lem3891729 {_100607 : Type'} (s : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) : (term656 _100607 s s' n P a) = (term657 _100607 s s' n P a).
Proof. exact (MK_COMB (@lem3891728 _100607 s P) (@lem3891727 _100607 s' n P a)). Qed.
Lemma lem3891730 {_100607 : Type'} (s : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term658 _100607 s s' n P) = (term659 _100607 s s' n P).
Proof. exact (fun_ext (fun a : _100607 => @lem3891729 _100607 s s' n P a)). Qed.
Lemma lem3891731 {_100607 : Type'} : (@ex _100607) = (@ex _100607).
Proof. exact (eq_refl (@ex _100607)). Qed.
Lemma lem3891732 {_100607 : Type'} (s : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term650 _100607 s s' n P) = (term660 _100607 s s' n P).
Proof. exact (MK_COMB (@lem3891731 _100607) (@lem3891730 _100607 s s' n P)). Qed.
Lemma lem3891733 {_100607 : Type'} (s : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) : ((term649 _100607 s s' n P) = (term650 _100607 s s' n P)) = ((term645 _100607 s s' n P) = (term660 _100607 s s' n P)).
Proof. exact (MK_COMB (@lem3891726 _100607 s s' n P) (@lem3891732 _100607 s s' n P)). Qed.
Lemma lem3891734 {_100607 : Type'} (s : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term645 _100607 s s' n P) = (term660 _100607 s s' n P).
Proof. exact (EQ_MP (@lem3891733 _100607 s s' n P) (@lem3891718 _100607 s s' n P)). Qed.
Lemma lem3891736 {A : Type'} (P : Prop) (Q : A -> Prop) : (term619 A P Q) = (term620 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3891737 {_100607 : Type'} (P : Prop) (Q : type686 _100607) : (term635 _100607 P Q) = (term636 _100607 P Q).
Proof. exact (@lem3891736 (_100607 -> Prop) P Q). Qed.
Lemma lem3891738 {_100607 : Type'} (s : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) : (term661 _100607 s s' n P a) = (term662 _100607 s s' n P a).
Proof. exact (@lem3891737 _100607 (term357 _100607 s P) (term572 _100607 s' n P a)). Qed.
Lemma lem3891739 {_100607 : Type'} (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) : (term663 _100607 s' n P a t) = (term570 _100607 s' n P a t).
Proof. exact (eq_refl (term663 _100607 s' n P a t)). Qed.
Lemma lem3891740 {_100607 : Type'} (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) : (term664 _100607 s' n P a) = (term572 _100607 s' n P a).
Proof. exact (fun_ext (fun t : _100607 -> Prop => @lem3891739 _100607 s' n P a t)). Qed.
Lemma lem3891741 {_100607 : Type'} : (@ex (_100607 -> Prop)) = (@ex (_100607 -> Prop)).
Proof. exact (eq_refl (@ex (_100607 -> Prop))). Qed.
Lemma lem3891742 {_100607 : Type'} (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) : (term665 _100607 s' n P a) = (term573 _100607 s' n P a).
Proof. exact (MK_COMB (@lem3891741 _100607) (@lem3891740 _100607 s' n P a)). Qed.
Lemma lem3891743 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) : (term613 _100607 s P) = (term613 _100607 s P).
Proof. exact (eq_refl (term613 _100607 s P)). Qed.
Lemma lem3891744 {_100607 : Type'} (s : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) : (term661 _100607 s s' n P a) = (term657 _100607 s s' n P a).
Proof. exact (MK_COMB (@lem3891743 _100607 s P) (@lem3891742 _100607 s' n P a)). Qed.
Lemma lem3891745 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3891746 {_100607 : Type'} (s : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) : (term666 _100607 s s' n P a) = (term667 _100607 s s' n P a).
Proof. exact (MK_COMB (@lem3891745) (@lem3891744 _100607 s s' n P a)). Qed.
Lemma lem3891747 {_100607 : Type'} (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) : (term663 _100607 s' n P a t) = (term570 _100607 s' n P a t).
Proof. exact (eq_refl (term663 _100607 s' n P a t)). Qed.
Lemma lem3891748 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) : (term613 _100607 s P) = (term613 _100607 s P).
Proof. exact (eq_refl (term613 _100607 s P)). Qed.
Lemma lem3891749 {_100607 : Type'} (s : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) : (term668 _100607 s s' n P a t) = (term669 _100607 s s' n P a t).
Proof. exact (MK_COMB (@lem3891748 _100607 s P) (@lem3891747 _100607 s' n P a t)). Qed.
Lemma lem3891750 {_100607 : Type'} (s : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) : (term670 _100607 s s' n P a) = (term671 _100607 s s' n P a).
Proof. exact (fun_ext (fun t : _100607 -> Prop => @lem3891749 _100607 s s' n P a t)). Qed.
Lemma lem3891751 {_100607 : Type'} : (@ex (_100607 -> Prop)) = (@ex (_100607 -> Prop)).
Proof. exact (eq_refl (@ex (_100607 -> Prop))). Qed.
Lemma lem3891752 {_100607 : Type'} (s : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) : (term662 _100607 s s' n P a) = (term672 _100607 s s' n P a).
Proof. exact (MK_COMB (@lem3891751 _100607) (@lem3891750 _100607 s s' n P a)). Qed.
Lemma lem3891753 {_100607 : Type'} (s : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) : ((term661 _100607 s s' n P a) = (term662 _100607 s s' n P a)) = ((term657 _100607 s s' n P a) = (term672 _100607 s s' n P a)).
Proof. exact (MK_COMB (@lem3891746 _100607 s s' n P a) (@lem3891752 _100607 s s' n P a)). Qed.
Lemma lem3891754 {_100607 : Type'} (s : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) : (term657 _100607 s s' n P a) = (term672 _100607 s s' n P a).
Proof. exact (EQ_MP (@lem3891753 _100607 s s' n P a) (@lem3891738 _100607 s s' n P a)). Qed.
Lemma lem3891755 {_100607 : Type'} (s : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term659 _100607 s s' n P) = (term673 _100607 s s' n P).
Proof. exact (fun_ext (fun a : _100607 => @lem3891754 _100607 s s' n P a)). Qed.
Lemma lem3891756 {_100607 : Type'} : (@ex _100607) = (@ex _100607).
Proof. exact (eq_refl (@ex _100607)). Qed.
Lemma lem3891757 {_100607 : Type'} (s : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term660 _100607 s s' n P) = (term674 _100607 s s' n P).
Proof. exact (MK_COMB (@lem3891756 _100607) (@lem3891755 _100607 s s' n P)). Qed.
Lemma lem3891758 {_100607 : Type'} (s : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term645 _100607 s s' n P) = (term674 _100607 s s' n P).
Proof. exact (TRANS (@lem3891734 _100607 s s' n P) (@lem3891757 _100607 s s' n P)). Qed.
Lemma lem3891759 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term647 _100607 s n P) = (term675 _100607 s n P).
Proof. exact (fun_ext (fun s' : _100607 -> Prop => @lem3891758 _100607 s s' n P)). Qed.
Lemma lem3891760 {_100607 : Type'} : (@ex (_100607 -> Prop)) = (@ex (_100607 -> Prop)).
Proof. exact (eq_refl (@ex (_100607 -> Prop))). Qed.
Lemma lem3891761 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term648 _100607 s n P) = (term676 _100607 s n P).
Proof. exact (MK_COMB (@lem3891760 _100607) (@lem3891759 _100607 s n P)). Qed.
Lemma lem3891762 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term631 _100607 s n P) = (term676 _100607 s n P).
Proof. exact (TRANS (@lem3891714 _100607 s n P) (@lem3891761 _100607 s n P)). Qed.
Lemma lem3891763 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) : (term633 _100607 s P) = (term677 _100607 s P).
Proof. exact (fun_ext (fun n : nat => @lem3891762 _100607 s n P)). Qed.
Lemma lem3891764 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem3891765 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) : (term634 _100607 s P) = (term678 _100607 s P).
Proof. exact (MK_COMB (@lem3891764) (@lem3891763 _100607 s P)). Qed.
Lemma lem3891766 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) : (term615 _100607 s P) = (term678 _100607 s P).
Proof. exact (TRANS (@lem3891694 _100607 s P) (@lem3891765 _100607 s P)). Qed.
Lemma lem3891767 {_100607 : Type'} (P : type686 _100607) : (term617 _100607 P) = (term679 _100607 P).
Proof. exact (fun_ext (fun s : _100607 -> Prop => @lem3891766 _100607 s P)). Qed.
Lemma lem3891768 {_100607 : Type'} : (@ex (_100607 -> Prop)) = (@ex (_100607 -> Prop)).
Proof. exact (eq_refl (@ex (_100607 -> Prop))). Qed.
Lemma lem3891769 {_100607 : Type'} (P : type686 _100607) : (term618 _100607 P) = (term680 _100607 P).
Proof. exact (MK_COMB (@lem3891768 _100607) (@lem3891767 _100607 P)). Qed.
Lemma lem3891770 {_100607 : Type'} (P : type686 _100607) : (term600 _100607 P) = (term680 _100607 P).
Proof. exact (TRANS (@lem3891674 _100607 P) (@lem3891769 _100607 P)). Qed.
Lemma lem3891771 {_100607 : Type'} : (term602 _100607) = (term681 _100607).
Proof. exact (fun_ext (fun P : type686 _100607 => @lem3891770 _100607 P)). Qed.
Lemma lem3891772 {_100607 : Type'} : (@ex ((_100607 -> Prop) -> Prop)) = (@ex ((_100607 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_100607 -> Prop) -> Prop))). Qed.
Lemma lem3891773 {_100607 : Type'} : (term603 _100607) = (term682 _100607).
Proof. exact (MK_COMB (@lem3891772 _100607) (@lem3891771 _100607)). Qed.
Lemma lem3891774 {_100607 : Type'} : (term585 _100607) = (term682 _100607).
Proof. exact (TRANS (@lem3891648 _100607) (@lem3891773 _100607)). Qed.
Lemma lem3891775 {_100607 : Type'} : (term304 _100607) = (term682 _100607).
Proof. exact (TRANS (@lem3891621 _100607) (@lem3891774 _100607)). Qed.
Lemma lem3891776 {_100607 : Type'} : (term234 _100607) = (term682 _100607).
Proof. exact (TRANS (@lem3891167 _100607) (@lem3891775 _100607)). Qed.
Lemma lem3891777 {_100607 : Type'} : (term109 _100607) = (term682 _100607).
Proof. exact (TRANS (@lem3890123 _100607) (@lem3891776 _100607)). Qed.
Lemma lem3891778 {_100607 : Type'} (h1 : term109 _100607) : term682 _100607.
Proof. exact (EQ_MP (@lem3891777 _100607) (@lem3889916 _100607 h1)). Qed.
Lemma lem3891779 {_100607 : Type'} (P : type686 _100607) (h1 : term680 _100607 P) : term680 _100607 P.
Proof. exact (h1). Qed.
Lemma lem3891780 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) (h1 : term678 _100607 s P) : term678 _100607 s P.
Proof. exact (h1). Qed.
Lemma lem3891781 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) (h1 : term676 _100607 s n P) : term676 _100607 s n P.
Proof. exact (h1). Qed.
Lemma lem3891782 {_100607 : Type'} (s : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (h1 : term674 _100607 s s' n P) : term674 _100607 s s' n P.
Proof. exact (h1). Qed.
Lemma lem3891783 {_100607 : Type'} (s : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) (h1 : term672 _100607 s s' n P a) : term672 _100607 s s' n P a.
Proof. exact (h1). Qed.
Lemma lem3891784 {_100607 : Type'} (s : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) (h1 : term669 _100607 s s' n P a t) : term669 _100607 s s' n P a t.
Proof. exact (h1). Qed.
Lemma lem3891809 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) : (term100 _100607 n P a t) = (term100 _100607 n P a t).
Proof. exact (eq_refl (term100 _100607 n P a t)). Qed.
Lemma lem3891814 {_100607 : Type'} (P : type686 _100607) (s : _100607 -> Prop) : (term169 _100607 P s) = (term169 _100607 P s).
Proof. exact (eq_refl (term169 _100607 P s)). Qed.
Lemma lem3891843 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) (a : _100607) (t : _100607 -> Prop) : (term150 _100607 n s a t) = (term150 _100607 n s a t).
Proof. exact (eq_refl (term150 _100607 n s a t)). Qed.
Lemma lem3891844 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) (a : _100607) : (term158 _100607 n s a) = (term158 _100607 n s a).
Proof. exact (fun_ext (fun t : _100607 -> Prop => @lem3891843 _100607 n s a t)). Qed.
Lemma lem3891845 {_100607 : Type'} : (@all (_100607 -> Prop)) = (@all (_100607 -> Prop)).
Proof. exact (eq_refl (@all (_100607 -> Prop))). Qed.
Lemma lem3891846 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) (a : _100607) : (term159 _100607 n s a) = (term159 _100607 n s a).
Proof. exact (MK_COMB (@lem3891845 _100607) (@lem3891844 _100607 n s a)). Qed.
Lemma lem3891847 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) : (term167 _100607 n s) = (term167 _100607 n s).
Proof. exact (fun_ext (fun a : _100607 => @lem3891846 _100607 n s a)). Qed.
Lemma lem3891848 {_100607 : Type'} : (@all _100607) = (@all _100607).
Proof. exact (eq_refl (@all _100607)). Qed.
Lemma lem3891849 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) : (term168 _100607 n s) = (term168 _100607 n s).
Proof. exact (MK_COMB (@lem3891848 _100607) (@lem3891847 _100607 n s)). Qed.
Lemma lem3891850 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3891851 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) : (term171 _100607 n s) = (term171 _100607 n s).
Proof. exact (MK_COMB (@lem3891850) (@lem3891849 _100607 n s)). Qed.
Lemma lem3891852 {_100607 : Type'} (n : nat) (P : type686 _100607) (s : _100607 -> Prop) : (term173 _100607 n P s) = (term173 _100607 n P s).
Proof. exact (MK_COMB (@lem3891851 _100607 n s) (@lem3891814 _100607 P s)). Qed.
Lemma lem3891853 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term180 _100607 n P) = (term180 _100607 n P).
Proof. exact (fun_ext (fun s : _100607 -> Prop => @lem3891852 _100607 n P s)). Qed.
Lemma lem3891854 {_100607 : Type'} : (@all (_100607 -> Prop)) = (@all (_100607 -> Prop)).
Proof. exact (eq_refl (@all (_100607 -> Prop))). Qed.
Lemma lem3891855 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term181 _100607 n P) = (term181 _100607 n P).
Proof. exact (MK_COMB (@lem3891854 _100607) (@lem3891853 _100607 n P)). Qed.
Lemma lem3891856 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3891857 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term206 _100607 n P) = (term206 _100607 n P).
Proof. exact (MK_COMB (@lem3891856) (@lem3891855 _100607 n P)). Qed.
Lemma lem3891858 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) : (term474 _100607 n P a t) = (term474 _100607 n P a t).
Proof. exact (MK_COMB (@lem3891857 _100607 n P) (@lem3891809 _100607 n P a t)). Qed.
Lemma lem3891885 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) (s : _100607 -> Prop) : (term188 _100607 n P a s) = (term188 _100607 n P a s).
Proof. exact (eq_refl (term188 _100607 n P a s)). Qed.
Lemma lem3891886 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) : (term196 _100607 n P a) = (term196 _100607 n P a).
Proof. exact (fun_ext (fun s : _100607 -> Prop => @lem3891885 _100607 n P a s)). Qed.
Lemma lem3891887 {_100607 : Type'} : (@all (_100607 -> Prop)) = (@all (_100607 -> Prop)).
Proof. exact (eq_refl (@all (_100607 -> Prop))). Qed.
Lemma lem3891888 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) : (term197 _100607 n P a) = (term197 _100607 n P a).
Proof. exact (MK_COMB (@lem3891887 _100607) (@lem3891886 _100607 n P a)). Qed.
Lemma lem3891889 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term203 _100607 n P) = (term203 _100607 n P).
Proof. exact (fun_ext (fun a : _100607 => @lem3891888 _100607 n P a)). Qed.
Lemma lem3891890 {_100607 : Type'} : (@all _100607) = (@all _100607).
Proof. exact (eq_refl (@all _100607)). Qed.
Lemma lem3891891 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term204 _100607 n P) = (term204 _100607 n P).
Proof. exact (MK_COMB (@lem3891890 _100607) (@lem3891889 _100607 n P)). Qed.
Lemma lem3891926 {_100607 : Type'} (n : nat) (a : _100607) (t : _100607 -> Prop) (P : type686 _100607) (s' : _100607 -> Prop) : (term437 _100607 n a t P s') = (term437 _100607 n a t P s').
Proof. exact (eq_refl (term437 _100607 n a t P s')). Qed.
Lemma lem3891927 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term439 _100607 a t s' n P) = (term439 _100607 a t s' n P).
Proof. exact (MK_COMB (@lem3891926 _100607 n a t P s') (@lem3891891 _100607 n P)). Qed.
Lemma lem3891928 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3891929 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) : (term568 _100607 a t s' n P) = (term568 _100607 a t s' n P).
Proof. exact (MK_COMB (@lem3891928) (@lem3891927 _100607 a t s' n P)). Qed.
Lemma lem3891930 {_100607 : Type'} (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) : (term570 _100607 s' n P a t) = (term570 _100607 s' n P a t).
Proof. exact (MK_COMB (@lem3891929 _100607 a t s' n P) (@lem3891858 _100607 n P a t)). Qed.
Lemma lem3891933 {_100607 : Type'} (P : type686 _100607) : (P (@EMPTY _100607)) = (P (@EMPTY _100607)).
Proof. exact (eq_refl (P (@EMPTY _100607))). Qed.
Lemma lem3891948 {_100607 : Type'} (P : type686 _100607) (s : _100607 -> Prop) : (term111 _100607 P s) = (term111 _100607 P s).
Proof. exact (eq_refl (term111 _100607 P s)). Qed.
Lemma lem3891949 {_100607 : Type'} (P : type686 _100607) : (term119 _100607 P) = (term119 _100607 P).
Proof. exact (fun_ext (fun s : _100607 -> Prop => @lem3891948 _100607 P s)). Qed.
Lemma lem3891950 {_100607 : Type'} : (@all (_100607 -> Prop)) = (@all (_100607 -> Prop)).
Proof. exact (eq_refl (@all (_100607 -> Prop))). Qed.
Lemma lem3891951 {_100607 : Type'} (P : type686 _100607) : (term120 _100607 P) = (term120 _100607 P).
Proof. exact (MK_COMB (@lem3891950 _100607) (@lem3891949 _100607 P)). Qed.
Lemma lem3891952 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3891953 {_100607 : Type'} (P : type686 _100607) : (term123 _100607 P) = (term123 _100607 P).
Proof. exact (MK_COMB (@lem3891952) (@lem3891951 _100607 P)). Qed.
Lemma lem3891954 {_100607 : Type'} (P : type686 _100607) : (term125 _100607 P) = (term125 _100607 P).
Proof. exact (MK_COMB (@lem3891953 _100607 P) (@lem3891933 _100607 P)). Qed.
Lemma lem3891975 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) : (term355 _100607 s P) = (term355 _100607 s P).
Proof. exact (eq_refl (term355 _100607 s P)). Qed.
Lemma lem3891976 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) : (term357 _100607 s P) = (term357 _100607 s P).
Proof. exact (MK_COMB (@lem3891975 _100607 s P) (@lem3891954 _100607 P)). Qed.
Lemma lem3891977 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3891978 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) : (term613 _100607 s P) = (term613 _100607 s P).
Proof. exact (MK_COMB (@lem3891977) (@lem3891976 _100607 s P)). Qed.
Lemma lem3891979 {_100607 : Type'} (s : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) : (term669 _100607 s s' n P a t) = (term669 _100607 s s' n P a t).
Proof. exact (MK_COMB (@lem3891978 _100607 s P) (@lem3891930 _100607 s' n P a t)). Qed.
Lemma lem3891980 {_100607 : Type'} (s : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) (h1 : term669 _100607 s s' n P a t) : term669 _100607 s s' n P a t.
Proof. exact (EQ_MP (@lem3891979 _100607 s s' n P a t) (@lem3891784 _100607 s s' n P a t h1)). Qed.
Lemma lem3891981 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) (h1 : term357 _100607 s P) : term357 _100607 s P.
Proof. exact (h1). Qed.
Lemma lem3891982 {_100607 : Type'} (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) (h1 : term570 _100607 s' n P a t) : term570 _100607 s' n P a t.
Proof. exact (h1). Qed.
Lemma lem3891983 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) (h1 : term319 _100607 s P) : term319 _100607 s P.
Proof. exact (h1). Qed.
Lemma lem3891984 {_100607 : Type'} (P : type686 _100607) (h1 : term125 _100607 P) : term125 _100607 P.
Proof. exact (h1). Qed.
Lemma lem3891986 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) (h1 : term319 _100607 s P) : term11 _100607 P s.
Proof. exact (proj1 (@lem3891983 _100607 s P h1)). Qed.
Lemma lem3891990 {_100607 : Type'} (P : type686 _100607) (h1 : term125 _100607 P) : term120 _100607 P.
Proof. exact (proj1 (@lem3891984 _100607 P h1)). Qed.
Lemma lem3891991 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (h1 : term439 _100607 a t s' n P) : term439 _100607 a t s' n P.
Proof. exact (h1). Qed.
Lemma lem3891992 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) (h1 : term474 _100607 n P a t) : term474 _100607 n P a t.
Proof. exact (h1). Qed.
Lemma lem3891993 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (h1 : term439 _100607 a t s' n P) : term204 _100607 n P.
Proof. exact (proj2 (@lem3891991 _100607 a t s' n P h1)). Qed.
Lemma lem3891994 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (h1 : term439 _100607 a t s' n P) : term388 _100607 n a t P s'.
Proof. exact (proj1 (@lem3891991 _100607 a t s' n P h1)). Qed.
Lemma lem3891996 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (h1 : term439 _100607 a t s' n P) : term104 _100607 n s' a t.
Proof. exact (proj1 (@lem3891994 _100607 a t s' n P h1)). Qed.
Lemma lem3891997 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (h1 : term439 _100607 a t s' n P) : term152 _100607 s' a t.
Proof. exact (proj2 (@lem3891996 _100607 a t s' n P h1)). Qed.
Lemma lem3892001 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) (h1 : term474 _100607 n P a t) : term100 _100607 n P a t.
Proof. exact (proj2 (@lem3891992 _100607 n P a t h1)). Qed.
Lemma lem3892002 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) (h1 : term474 _100607 n P a t) : term181 _100607 n P.
Proof. exact (proj1 (@lem3891992 _100607 n P a t h1)). Qed.
Lemma lem3892003 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) (h1 : term474 _100607 n P a t) : term190 _100607 P a t.
Proof. exact (proj2 (@lem3892001 _100607 n P a t h1)). Qed.
Lemma lem3892026 {_100607 : Type'} (P : type686 _100607) (s : _100607 -> Prop) : (term111 _100607 P s) = (term111 _100607 P s).
Proof. exact (eq_refl (term111 _100607 P s)). Qed.
Lemma lem3892027 {_100607 : Type'} (P : type686 _100607) : (term119 _100607 P) = (term119 _100607 P).
Proof. exact (fun_ext (fun s : _100607 -> Prop => @lem3892026 _100607 P s)). Qed.
Lemma lem3892028 {_100607 : Type'} : (@all (_100607 -> Prop)) = (@all (_100607 -> Prop)).
Proof. exact (eq_refl (@all (_100607 -> Prop))). Qed.
Lemma lem3892030 {_100607 : Type'} (P : type686 _100607) : (term120 _100607 P) = (term120 _100607 P).
Proof. exact (MK_COMB (@lem3892028 _100607) (@lem3892027 _100607 P)). Qed.
Lemma lem3892031 {_100607 : Type'} (P : type686 _100607) (h1 : term125 _100607 P) : term120 _100607 P.
Proof. exact (EQ_MP (@lem3892030 _100607 P) (@lem3891990 _100607 P h1)). Qed.
Lemma lem3892049 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) (s : _100607 -> Prop) : (term188 _100607 n P a s) = (term188 _100607 n P a s).
Proof. exact (eq_refl (term188 _100607 n P a s)). Qed.
Lemma lem3892050 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) : (term196 _100607 n P a) = (term196 _100607 n P a).
Proof. exact (fun_ext (fun s : _100607 -> Prop => @lem3892049 _100607 n P a s)). Qed.
Lemma lem3892051 {_100607 : Type'} : (@all (_100607 -> Prop)) = (@all (_100607 -> Prop)).
Proof. exact (eq_refl (@all (_100607 -> Prop))). Qed.
Lemma lem3892052 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) : (term197 _100607 n P a) = (term197 _100607 n P a).
Proof. exact (MK_COMB (@lem3892051 _100607) (@lem3892050 _100607 n P a)). Qed.
Lemma lem3892053 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term203 _100607 n P) = (term203 _100607 n P).
Proof. exact (fun_ext (fun a : _100607 => @lem3892052 _100607 n P a)). Qed.
Lemma lem3892054 {_100607 : Type'} : (@all _100607) = (@all _100607).
Proof. exact (eq_refl (@all _100607)). Qed.
Lemma lem3892056 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term204 _100607 n P) = (term204 _100607 n P).
Proof. exact (MK_COMB (@lem3892054 _100607) (@lem3892053 _100607 n P)). Qed.
Lemma lem3892057 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (h1 : term439 _100607 a t s' n P) : term204 _100607 n P.
Proof. exact (EQ_MP (@lem3892056 _100607 n P) (@lem3891993 _100607 a t s' n P h1)). Qed.
Lemma lem3892075 {A : Type'} (P : A -> Prop) (Q : Prop) : (term683 A P Q) = (term684 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3892076 {_100607 : Type'} (P : _100607 -> Prop) (Q : Prop) : (term683 _100607 P Q) = (term684 _100607 P Q).
Proof. exact (@lem3892075 _100607 P Q). Qed.
Lemma lem3892077 {_100607 : Type'} (n : nat) (P : type686 _100607) (s : _100607 -> Prop) : (term685 _100607 n P s) = (term686 _100607 n P s).
Proof. exact (@lem3892076 _100607 (term167 _100607 n s) (term169 _100607 P s)). Qed.
Lemma lem3892078 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) (a : _100607) : (term687 _100607 n s a) = (term159 _100607 n s a).
Proof. exact (eq_refl (term687 _100607 n s a)). Qed.
Lemma lem3892079 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) : (term688 _100607 n s) = (term167 _100607 n s).
Proof. exact (fun_ext (fun a : _100607 => @lem3892078 _100607 n s a)). Qed.
Lemma lem3892080 {_100607 : Type'} : (@all _100607) = (@all _100607).
Proof. exact (eq_refl (@all _100607)). Qed.
Lemma lem3892081 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) : (term689 _100607 n s) = (term168 _100607 n s).
Proof. exact (MK_COMB (@lem3892080 _100607) (@lem3892079 _100607 n s)). Qed.
Lemma lem3892082 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3892083 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) : (term690 _100607 n s) = (term171 _100607 n s).
Proof. exact (MK_COMB (@lem3892082) (@lem3892081 _100607 n s)). Qed.
Lemma lem3892084 {_100607 : Type'} (P : type686 _100607) (s : _100607 -> Prop) : (term169 _100607 P s) = (term169 _100607 P s).
Proof. exact (eq_refl (term169 _100607 P s)). Qed.
Lemma lem3892085 {_100607 : Type'} (n : nat) (P : type686 _100607) (s : _100607 -> Prop) : (term685 _100607 n P s) = (term173 _100607 n P s).
Proof. exact (MK_COMB (@lem3892083 _100607 n s) (@lem3892084 _100607 P s)). Qed.
Lemma lem3892086 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3892087 {_100607 : Type'} (n : nat) (P : type686 _100607) (s : _100607 -> Prop) : (term691 _100607 n P s) = (term692 _100607 n P s).
Proof. exact (MK_COMB (@lem3892086) (@lem3892085 _100607 n P s)). Qed.
Lemma lem3892088 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) (a : _100607) : (term687 _100607 n s a) = (term159 _100607 n s a).
Proof. exact (eq_refl (term687 _100607 n s a)). Qed.
Lemma lem3892089 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3892090 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) (a : _100607) : (term693 _100607 n s a) = (term694 _100607 n s a).
Proof. exact (MK_COMB (@lem3892089) (@lem3892088 _100607 n s a)). Qed.
Lemma lem3892091 {_100607 : Type'} (P : type686 _100607) (s : _100607 -> Prop) : (term169 _100607 P s) = (term169 _100607 P s).
Proof. exact (eq_refl (term169 _100607 P s)). Qed.
Lemma lem3892092 {_100607 : Type'} (n : nat) (a : _100607) (P : type686 _100607) (s : _100607 -> Prop) : (term695 _100607 n a P s) = (term696 _100607 n a P s).
Proof. exact (MK_COMB (@lem3892090 _100607 n s a) (@lem3892091 _100607 P s)). Qed.
Lemma lem3892093 {_100607 : Type'} (n : nat) (P : type686 _100607) (s : _100607 -> Prop) : (term697 _100607 n P s) = (term698 _100607 n P s).
Proof. exact (fun_ext (fun a : _100607 => @lem3892092 _100607 n a P s)). Qed.
Lemma lem3892094 {_100607 : Type'} : (@all _100607) = (@all _100607).
Proof. exact (eq_refl (@all _100607)). Qed.
Lemma lem3892095 {_100607 : Type'} (n : nat) (P : type686 _100607) (s : _100607 -> Prop) : (term686 _100607 n P s) = (term699 _100607 n P s).
Proof. exact (MK_COMB (@lem3892094 _100607) (@lem3892093 _100607 n P s)). Qed.
Lemma lem3892096 {_100607 : Type'} (n : nat) (P : type686 _100607) (s : _100607 -> Prop) : ((term685 _100607 n P s) = (term686 _100607 n P s)) = ((term173 _100607 n P s) = (term699 _100607 n P s)).
Proof. exact (MK_COMB (@lem3892087 _100607 n P s) (@lem3892095 _100607 n P s)). Qed.
Lemma lem3892097 {_100607 : Type'} (n : nat) (P : type686 _100607) (s : _100607 -> Prop) : (term173 _100607 n P s) = (term699 _100607 n P s).
Proof. exact (EQ_MP (@lem3892096 _100607 n P s) (@lem3892077 _100607 n P s)). Qed.
Lemma lem3892099 {A : Type'} (P : A -> Prop) (Q : Prop) : (term683 A P Q) = (term684 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3892100 {_100607 : Type'} (P : type686 _100607) (Q : Prop) : (term700 _100607 P Q) = (term701 _100607 P Q).
Proof. exact (@lem3892099 (_100607 -> Prop) P Q). Qed.
Lemma lem3892101 {_100607 : Type'} (n : nat) (a : _100607) (P : type686 _100607) (s : _100607 -> Prop) : (term702 _100607 n a P s) = (term703 _100607 n a P s).
Proof. exact (@lem3892100 _100607 (term158 _100607 n s a) (term169 _100607 P s)). Qed.
Lemma lem3892102 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) (a : _100607) (t : _100607 -> Prop) : (term704 _100607 n s a t) = (term150 _100607 n s a t).
Proof. exact (eq_refl (term704 _100607 n s a t)). Qed.
Lemma lem3892103 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) (a : _100607) : (term705 _100607 n s a) = (term158 _100607 n s a).
Proof. exact (fun_ext (fun t : _100607 -> Prop => @lem3892102 _100607 n s a t)). Qed.
Lemma lem3892104 {_100607 : Type'} : (@all (_100607 -> Prop)) = (@all (_100607 -> Prop)).
Proof. exact (eq_refl (@all (_100607 -> Prop))). Qed.
Lemma lem3892105 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) (a : _100607) : (term706 _100607 n s a) = (term159 _100607 n s a).
Proof. exact (MK_COMB (@lem3892104 _100607) (@lem3892103 _100607 n s a)). Qed.
Lemma lem3892106 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3892107 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) (a : _100607) : (term707 _100607 n s a) = (term694 _100607 n s a).
Proof. exact (MK_COMB (@lem3892106) (@lem3892105 _100607 n s a)). Qed.
Lemma lem3892108 {_100607 : Type'} (P : type686 _100607) (s : _100607 -> Prop) : (term169 _100607 P s) = (term169 _100607 P s).
Proof. exact (eq_refl (term169 _100607 P s)). Qed.
Lemma lem3892109 {_100607 : Type'} (n : nat) (a : _100607) (P : type686 _100607) (s : _100607 -> Prop) : (term702 _100607 n a P s) = (term696 _100607 n a P s).
Proof. exact (MK_COMB (@lem3892107 _100607 n s a) (@lem3892108 _100607 P s)). Qed.
Lemma lem3892110 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3892111 {_100607 : Type'} (n : nat) (a : _100607) (P : type686 _100607) (s : _100607 -> Prop) : (term708 _100607 n a P s) = (term709 _100607 n a P s).
Proof. exact (MK_COMB (@lem3892110) (@lem3892109 _100607 n a P s)). Qed.
Lemma lem3892112 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) (a : _100607) (t : _100607 -> Prop) : (term704 _100607 n s a t) = (term150 _100607 n s a t).
Proof. exact (eq_refl (term704 _100607 n s a t)). Qed.
Lemma lem3892113 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3892114 {_100607 : Type'} (n : nat) (s : _100607 -> Prop) (a : _100607) (t : _100607 -> Prop) : (term710 _100607 n s a t) = (term711 _100607 n s a t).
Proof. exact (MK_COMB (@lem3892113) (@lem3892112 _100607 n s a t)). Qed.
Lemma lem3892115 {_100607 : Type'} (P : type686 _100607) (s : _100607 -> Prop) : (term169 _100607 P s) = (term169 _100607 P s).
Proof. exact (eq_refl (term169 _100607 P s)). Qed.
Lemma lem3892116 {_100607 : Type'} (n : nat) (a : _100607) (t : _100607 -> Prop) (P : type686 _100607) (s : _100607 -> Prop) : (term712 _100607 n a t P s) = (term713 _100607 n a t P s).
Proof. exact (MK_COMB (@lem3892114 _100607 n s a t) (@lem3892115 _100607 P s)). Qed.
Lemma lem3892117 {_100607 : Type'} (n : nat) (a : _100607) (P : type686 _100607) (s : _100607 -> Prop) : (term714 _100607 n a P s) = (term715 _100607 n a P s).
Proof. exact (fun_ext (fun t : _100607 -> Prop => @lem3892116 _100607 n a t P s)). Qed.
Lemma lem3892118 {_100607 : Type'} : (@all (_100607 -> Prop)) = (@all (_100607 -> Prop)).
Proof. exact (eq_refl (@all (_100607 -> Prop))). Qed.
Lemma lem3892119 {_100607 : Type'} (n : nat) (a : _100607) (P : type686 _100607) (s : _100607 -> Prop) : (term703 _100607 n a P s) = (term716 _100607 n a P s).
Proof. exact (MK_COMB (@lem3892118 _100607) (@lem3892117 _100607 n a P s)). Qed.
Lemma lem3892120 {_100607 : Type'} (n : nat) (a : _100607) (P : type686 _100607) (s : _100607 -> Prop) : ((term702 _100607 n a P s) = (term703 _100607 n a P s)) = ((term696 _100607 n a P s) = (term716 _100607 n a P s)).
Proof. exact (MK_COMB (@lem3892111 _100607 n a P s) (@lem3892119 _100607 n a P s)). Qed.
Lemma lem3892121 {_100607 : Type'} (n : nat) (a : _100607) (P : type686 _100607) (s : _100607 -> Prop) : (term696 _100607 n a P s) = (term716 _100607 n a P s).
Proof. exact (EQ_MP (@lem3892120 _100607 n a P s) (@lem3892101 _100607 n a P s)). Qed.
Lemma lem3892122 {_100607 : Type'} (n : nat) (P : type686 _100607) (s : _100607 -> Prop) : (term698 _100607 n P s) = (term717 _100607 n P s).
Proof. exact (fun_ext (fun a : _100607 => @lem3892121 _100607 n a P s)). Qed.
Lemma lem3892123 {_100607 : Type'} : (@all _100607) = (@all _100607).
Proof. exact (eq_refl (@all _100607)). Qed.
Lemma lem3892124 {_100607 : Type'} (n : nat) (P : type686 _100607) (s : _100607 -> Prop) : (term699 _100607 n P s) = (term718 _100607 n P s).
Proof. exact (MK_COMB (@lem3892123 _100607) (@lem3892122 _100607 n P s)). Qed.
Lemma lem3892125 {_100607 : Type'} (n : nat) (P : type686 _100607) (s : _100607 -> Prop) : (term173 _100607 n P s) = (term718 _100607 n P s).
Proof. exact (TRANS (@lem3892097 _100607 n P s) (@lem3892124 _100607 n P s)). Qed.
Lemma lem3892126 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term180 _100607 n P) = (term719 _100607 n P).
Proof. exact (fun_ext (fun s : _100607 -> Prop => @lem3892125 _100607 n P s)). Qed.
Lemma lem3892127 {_100607 : Type'} : (@all (_100607 -> Prop)) = (@all (_100607 -> Prop)).
Proof. exact (eq_refl (@all (_100607 -> Prop))). Qed.
Lemma lem3892128 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term181 _100607 n P) = (term720 _100607 n P).
Proof. exact (MK_COMB (@lem3892127 _100607) (@lem3892126 _100607 n P)). Qed.
Lemma lem3892147 {_100607 : Type'} (n : nat) (a : _100607) (t : _100607 -> Prop) (P : type686 _100607) (s : _100607 -> Prop) : (term713 _100607 n a t P s) = (term713 _100607 n a t P s).
Proof. exact (eq_refl (term713 _100607 n a t P s)). Qed.
Lemma lem3892148 {_100607 : Type'} (n : nat) (a : _100607) (P : type686 _100607) (s : _100607 -> Prop) : (term715 _100607 n a P s) = (term715 _100607 n a P s).
Proof. exact (fun_ext (fun t : _100607 -> Prop => @lem3892147 _100607 n a t P s)). Qed.
Lemma lem3892149 {_100607 : Type'} : (@all (_100607 -> Prop)) = (@all (_100607 -> Prop)).
Proof. exact (eq_refl (@all (_100607 -> Prop))). Qed.
Lemma lem3892150 {_100607 : Type'} (n : nat) (a : _100607) (P : type686 _100607) (s : _100607 -> Prop) : (term716 _100607 n a P s) = (term716 _100607 n a P s).
Proof. exact (MK_COMB (@lem3892149 _100607) (@lem3892148 _100607 n a P s)). Qed.
Lemma lem3892151 {_100607 : Type'} (n : nat) (P : type686 _100607) (s : _100607 -> Prop) : (term717 _100607 n P s) = (term717 _100607 n P s).
Proof. exact (fun_ext (fun a : _100607 => @lem3892150 _100607 n a P s)). Qed.
Lemma lem3892152 {_100607 : Type'} : (@all _100607) = (@all _100607).
Proof. exact (eq_refl (@all _100607)). Qed.
Lemma lem3892153 {_100607 : Type'} (n : nat) (P : type686 _100607) (s : _100607 -> Prop) : (term718 _100607 n P s) = (term718 _100607 n P s).
Proof. exact (MK_COMB (@lem3892152 _100607) (@lem3892151 _100607 n P s)). Qed.
Lemma lem3892154 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term719 _100607 n P) = (term719 _100607 n P).
Proof. exact (fun_ext (fun s : _100607 -> Prop => @lem3892153 _100607 n P s)). Qed.
Lemma lem3892155 {_100607 : Type'} : (@all (_100607 -> Prop)) = (@all (_100607 -> Prop)).
Proof. exact (eq_refl (@all (_100607 -> Prop))). Qed.
Lemma lem3892156 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term720 _100607 n P) = (term720 _100607 n P).
Proof. exact (MK_COMB (@lem3892155 _100607) (@lem3892154 _100607 n P)). Qed.
Lemma lem3892157 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term181 _100607 n P) = (term720 _100607 n P).
Proof. exact (TRANS (@lem3892128 _100607 n P) (@lem3892156 _100607 n P)). Qed.
Lemma lem3892158 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) (h1 : term474 _100607 n P a t) : term720 _100607 n P.
Proof. exact (EQ_MP (@lem3892157 _100607 n P) (@lem3892002 _100607 n P a t h1)). Qed.
Lemma lem3892171 {_100607 : Type'} (_45244 : _100607 -> Prop) (P : type686 _100607) (h1 : term125 _100607 P) : term721 _100607 P _45244.
Proof. exact (@lem3892031 _100607 P h1 _45244). Qed.
Lemma lem3892172 {_100607 : Type'} (P : type686 _100607) (_45244 : _100607 -> Prop) : (term721 _100607 P _45244) = (term111 _100607 P _45244).
Proof. exact (eq_refl (term721 _100607 P _45244)). Qed.
Lemma lem3892174 {_100607 : Type'} (_45245 : _100607) (a : _100607) (t : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (h1 : term439 _100607 a t s' n P) : term722 _100607 n P _45245.
Proof. exact (@lem3892057 _100607 a t s' n P h1 _45245). Qed.
Lemma lem3892175 {_100607 : Type'} (n : nat) (P : type686 _100607) (_45245 : _100607) : (term722 _100607 n P _45245) = (term197 _100607 n P _45245).
Proof. exact (eq_refl (term722 _100607 n P _45245)). Qed.
Lemma lem3892176 {_100607 : Type'} (_45245 : _100607) (a : _100607) (t : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (h1 : term439 _100607 a t s' n P) : term197 _100607 n P _45245.
Proof. exact (EQ_MP (@lem3892175 _100607 n P _45245) (@lem3892174 _100607 _45245 a t s' n P h1)). Qed.
Lemma lem3892177 {_100607 : Type'} (_45245 : _100607) (_45246 : _100607 -> Prop) (a : _100607) (t : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (h1 : term439 _100607 a t s' n P) : term723 _100607 n P _45245 _45246.
Proof. exact (@lem3892176 _100607 _45245 a t s' n P h1 _45246). Qed.
Lemma lem3892178 {_100607 : Type'} (n : nat) (P : type686 _100607) (_45245 : _100607) (_45246 : _100607 -> Prop) : (term723 _100607 n P _45245 _45246) = (term188 _100607 n P _45245 _45246).
Proof. exact (eq_refl (term723 _100607 n P _45245 _45246)). Qed.
Lemma lem3892180 {_100607 : Type'} (_45247 : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) (h1 : term474 _100607 n P a t) : term724 _100607 n P _45247.
Proof. exact (@lem3892158 _100607 n P a t h1 _45247). Qed.
Lemma lem3892181 {_100607 : Type'} (n : nat) (P : type686 _100607) (_45247 : _100607 -> Prop) : (term724 _100607 n P _45247) = (term718 _100607 n P _45247).
Proof. exact (eq_refl (term724 _100607 n P _45247)). Qed.
Lemma lem3892182 {_100607 : Type'} (_45247 : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) (h1 : term474 _100607 n P a t) : term718 _100607 n P _45247.
Proof. exact (EQ_MP (@lem3892181 _100607 n P _45247) (@lem3892180 _100607 _45247 n P a t h1)). Qed.
Lemma lem3892183 {_100607 : Type'} (_45247 : _100607 -> Prop) (_45248 : _100607) (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) (h1 : term474 _100607 n P a t) : term725 _100607 n P _45247 _45248.
Proof. exact (@lem3892182 _100607 _45247 n P a t h1 _45248). Qed.
Lemma lem3892184 {_100607 : Type'} (n : nat) (_45248 : _100607) (P : type686 _100607) (_45247 : _100607 -> Prop) : (term725 _100607 n P _45247 _45248) = (term716 _100607 n _45248 P _45247).
Proof. exact (eq_refl (term725 _100607 n P _45247 _45248)). Qed.
Lemma lem3892185 {_100607 : Type'} (_45248 : _100607) (_45247 : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) (h1 : term474 _100607 n P a t) : term716 _100607 n _45248 P _45247.
Proof. exact (EQ_MP (@lem3892184 _100607 n _45248 P _45247) (@lem3892183 _100607 _45247 _45248 n P a t h1)). Qed.
Lemma lem3892186 {_100607 : Type'} (_45248 : _100607) (_45247 : _100607 -> Prop) (_45249 : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) (h1 : term474 _100607 n P a t) : term726 _100607 n _45248 P _45247 _45249.
Proof. exact (@lem3892185 _100607 _45248 _45247 n P a t h1 _45249). Qed.
Lemma lem3892187 {_100607 : Type'} (n : nat) (_45248 : _100607) (_45249 : _100607 -> Prop) (P : type686 _100607) (_45247 : _100607 -> Prop) : (term726 _100607 n _45248 P _45247 _45249) = (term713 _100607 n _45248 _45249 P _45247).
Proof. exact (eq_refl (term726 _100607 n _45248 P _45247 _45249)). Qed.
Lemma lem3892188 {_100607 : Type'} (_45248 : _100607) (_45249 : _100607 -> Prop) (_45247 : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) (h1 : term474 _100607 n P a t) : term713 _100607 n _45248 _45249 P _45247.
Proof. exact (EQ_MP (@lem3892187 _100607 n _45248 _45249 P _45247) (@lem3892186 _100607 _45248 _45247 _45249 n P a t h1)). Qed.
Lemma lem3892192 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) (h1 : term319 _100607 s P) : s = (@EMPTY _100607).
Proof. exact (proj1 (@lem3891986 _100607 s P h1)). Qed.
Lemma lem3892194 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) (h1 : term319 _100607 s P) : P s.
Proof. exact (proj2 (@lem3891986 _100607 s P h1)). Qed.
Lemma lem3892200 {_100607 : Type'} (_45244 : _100607 -> Prop) (P : type686 _100607) (h1 : term125 _100607 P) : term111 _100607 P _45244.
Proof. exact (EQ_MP (@lem3892172 _100607 P _45244) (@lem3892171 _100607 _45244 P h1)). Qed.
Lemma lem3892214 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (h1 : term439 _100607 a t s' n P) : P s'.
Proof. exact (proj2 (@lem3891994 _100607 a t s' n P h1)). Qed.
Lemma lem3892220 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (h1 : term439 _100607 a t s' n P) : s' = (@INSERT _100607 a t).
Proof. exact (proj2 (@lem3891997 _100607 a t s' n P h1)). Qed.
Lemma lem3892224 {_100607 : Type'} (n : nat) (_45248 : _100607) (_45249 : _100607 -> Prop) (P : type686 _100607) (_45247 : _100607 -> Prop) : (term713 _100607 n _45248 _45249 P _45247) = (term727 _100607 n _45248 _45249 P _45247).
Proof. exact (@lem3888998 (term728 _100607 _45249 n) (term145 _100607 _45247 _45248 _45249) (term169 _100607 P _45247)). Qed.
Lemma lem3892231 {_100607 : Type'} (_45248 : _100607) (_45249 : _100607 -> Prop) (P : type686 _100607) (_45247 : _100607 -> Prop) : (term729 _100607 _45248 _45249 P _45247) = (term730 _100607 _45248 _45249 P _45247).
Proof. exact (@lem3888998 (@IN _100607 _45248 _45249) (term141 _100607 _45247 _45248 _45249) (term169 _100607 P _45247)). Qed.
Lemma lem3892232 {_100607 : Type'} (_45249 : _100607 -> Prop) (n : nat) : (term148 _100607 _45249 n) = (term148 _100607 _45249 n).
Proof. exact (eq_refl (term148 _100607 _45249 n)). Qed.
Lemma lem3892235 {_100607 : Type'} (n : nat) (_45248 : _100607) (_45249 : _100607 -> Prop) (P : type686 _100607) (_45247 : _100607 -> Prop) : (term727 _100607 n _45248 _45249 P _45247) = (term731 _100607 n _45248 _45249 P _45247).
Proof. exact (MK_COMB (@lem3892232 _100607 _45249 n) (@lem3892231 _100607 _45248 _45249 P _45247)). Qed.
Lemma lem3892237 {_100607 : Type'} (n : nat) (_45248 : _100607) (_45249 : _100607 -> Prop) (P : type686 _100607) (_45247 : _100607 -> Prop) : (term713 _100607 n _45248 _45249 P _45247) = (term731 _100607 n _45248 _45249 P _45247).
Proof. exact (TRANS (@lem3892224 _100607 n _45248 _45249 P _45247) (@lem3892235 _100607 n _45248 _45249 P _45247)). Qed.
Lemma lem3892238 {_100607 : Type'} (_45248 : _100607) (_45249 : _100607 -> Prop) (_45247 : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) (h1 : term474 _100607 n P a t) : term731 _100607 n _45248 _45249 P _45247.
Proof. exact (EQ_MP (@lem3892237 _100607 n _45248 _45249 P _45247) (@lem3892188 _100607 _45248 _45249 _45247 n P a t h1)). Qed.
Lemma lem3892242 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) (h1 : term474 _100607 n P a t) : term147 _100607 a t.
Proof. exact (proj1 (@lem3892003 _100607 n P a t h1)). Qed.
Lemma lem3892272 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) (h1 : term319 _100607 s P) : term121 _100607 P.
Proof. exact (proj2 (@lem3891983 _100607 s P h1)). Qed.
Lemma lem3892273 {_100607 : Type'} (P : type686 _100607) : (term732 _100607 P) = (term732 _100607 P).
Proof. exact (eq_refl (term732 _100607 P)). Qed.
Lemma lem3892274 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) (h1 : term319 _100607 s P) : (term733 _100607 P s) = (term734 _100607 P).
Proof. exact (MK_COMB (@lem3892273 _100607 P) (@lem3892192 _100607 s P h1)). Qed.
Lemma lem3892275 {_100607 : Type'} (P : type686 _100607) : (term734 _100607 P) = (P (@EMPTY _100607)).
Proof. exact (eq_refl (term734 _100607 P)). Qed.
Lemma lem3892276 {_100607 : Type'} (P : type686 _100607) (s : _100607 -> Prop) : (term735 _100607 P s) = (term735 _100607 P s).
Proof. exact (eq_refl (term735 _100607 P s)). Qed.
Lemma lem3892277 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) : ((term733 _100607 P s) = (term734 _100607 P)) = ((term733 _100607 P s) = (P (@EMPTY _100607))).
Proof. exact (MK_COMB (@lem3892276 _100607 P s) (@lem3892275 _100607 P)). Qed.
Lemma lem3892278 {_100607 : Type'} (P : type686 _100607) (s : _100607 -> Prop) : (term733 _100607 P s) = (P s).
Proof. exact (eq_refl (term733 _100607 P s)). Qed.
Lemma lem3892279 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3892280 {_100607 : Type'} (P : type686 _100607) (s : _100607 -> Prop) : (term735 _100607 P s) = (term736 _100607 P s).
Proof. exact (MK_COMB (@lem3892279) (@lem3892278 _100607 P s)). Qed.
Lemma lem3892281 {_100607 : Type'} (P : type686 _100607) : (P (@EMPTY _100607)) = (P (@EMPTY _100607)).
Proof. exact (eq_refl (P (@EMPTY _100607))). Qed.
Lemma lem3892282 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) : ((term733 _100607 P s) = (P (@EMPTY _100607))) = ((P s) = (P (@EMPTY _100607))).
Proof. exact (MK_COMB (@lem3892280 _100607 P s) (@lem3892281 _100607 P)). Qed.
Lemma lem3892283 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) : ((term733 _100607 P s) = (term734 _100607 P)) = ((P s) = (P (@EMPTY _100607))).
Proof. exact (TRANS (@lem3892277 _100607 s P) (@lem3892282 _100607 s P)). Qed.
Lemma lem3892284 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) (h1 : term319 _100607 s P) : (P s) = (P (@EMPTY _100607)).
Proof. exact (EQ_MP (@lem3892283 _100607 s P) (@lem3892274 _100607 s P h1)). Qed.
Lemma lem3892313 {_100607 : Type'} (_45245 : _100607) (_45246 : _100607 -> Prop) (a : _100607) (t : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (h1 : term439 _100607 a t s' n P) : term188 _100607 n P _45245 _45246.
Proof. exact (EQ_MP (@lem3892178 _100607 n P _45245 _45246) (@lem3892177 _100607 _45245 _45246 a t s' n P h1)). Qed.
Lemma lem3892314 {_100607 : Type'} (P : type686 _100607) : (term732 _100607 P) = (term732 _100607 P).
Proof. exact (eq_refl (term732 _100607 P)). Qed.
Lemma lem3892315 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (h1 : term439 _100607 a t s' n P) : (term733 _100607 P s') = (term737 _100607 P a t).
Proof. exact (MK_COMB (@lem3892314 _100607 P) (@lem3892220 _100607 a t s' n P h1)). Qed.
Lemma lem3892316 {_100607 : Type'} (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) : (term737 _100607 P a t) = (term186 _100607 P a t).
Proof. exact (eq_refl (term737 _100607 P a t)). Qed.
Lemma lem3892317 {_100607 : Type'} (P : type686 _100607) (s' : _100607 -> Prop) : (term735 _100607 P s') = (term735 _100607 P s').
Proof. exact (eq_refl (term735 _100607 P s')). Qed.
Lemma lem3892318 {_100607 : Type'} (s' : _100607 -> Prop) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) : ((term733 _100607 P s') = (term737 _100607 P a t)) = ((term733 _100607 P s') = (term186 _100607 P a t)).
Proof. exact (MK_COMB (@lem3892317 _100607 P s') (@lem3892316 _100607 P a t)). Qed.
Lemma lem3892319 {_100607 : Type'} (P : type686 _100607) (s' : _100607 -> Prop) : (term733 _100607 P s') = (P s').
Proof. exact (eq_refl (term733 _100607 P s')). Qed.
Lemma lem3892320 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3892321 {_100607 : Type'} (P : type686 _100607) (s' : _100607 -> Prop) : (term735 _100607 P s') = (term736 _100607 P s').
Proof. exact (MK_COMB (@lem3892320) (@lem3892319 _100607 P s')). Qed.
Lemma lem3892322 {_100607 : Type'} (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) : (term186 _100607 P a t) = (term186 _100607 P a t).
Proof. exact (eq_refl (term186 _100607 P a t)). Qed.
Lemma lem3892323 {_100607 : Type'} (s' : _100607 -> Prop) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) : ((term733 _100607 P s') = (term186 _100607 P a t)) = ((P s') = (term186 _100607 P a t)).
Proof. exact (MK_COMB (@lem3892321 _100607 P s') (@lem3892322 _100607 P a t)). Qed.
Lemma lem3892324 {_100607 : Type'} (s' : _100607 -> Prop) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) : ((term733 _100607 P s') = (term737 _100607 P a t)) = ((P s') = (term186 _100607 P a t)).
Proof. exact (TRANS (@lem3892318 _100607 s' P a t) (@lem3892323 _100607 s' P a t)). Qed.
Lemma lem3892325 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (h1 : term439 _100607 a t s' n P) : (P s') = (term186 _100607 P a t).
Proof. exact (EQ_MP (@lem3892324 _100607 s' P a t) (@lem3892315 _100607 a t s' n P h1)). Qed.
Lemma lem3892354 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (h1 : term439 _100607 a t s' n P) : term147 _100607 a t.
Proof. exact (proj1 (@lem3891997 _100607 a t s' n P h1)). Qed.
Lemma lem3892356 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) (h1 : term319 _100607 s P) : P (@EMPTY _100607).
Proof. exact (EQ_MP (@lem3892284 _100607 s P h1) (@lem3892194 _100607 s P h1)). Qed.
Lemma lem3892357 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) (h1 : term319 _100607 s P) : term738 _100607 P.
Proof. exact (fun h0 : term121 _100607 P => @lem3892356 _100607 s P h1). Qed.
Lemma lem3892359 (p : Prop) : (term739 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3892360 {_100607 : Type'} (P : type686 _100607) : (term738 _100607 P) = (P (@EMPTY _100607)).
Proof. exact (@lem3892359 (P (@EMPTY _100607))). Qed.
Lemma lem3892361 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) (h1 : term319 _100607 s P) : P (@EMPTY _100607).
Proof. exact (EQ_MP (@lem3892360 _100607 P) (@lem3892357 _100607 s P h1)). Qed.
Lemma lem3892364 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3892366 {_100607 : Type'} (P : type686 _100607) : (term121 _100607 P) = (term740 _100607 P).
Proof. exact (@lem3892364 (P (@EMPTY _100607))). Qed.
Lemma lem3892369 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) (h1 : term319 _100607 s P) : term740 _100607 P.
Proof. exact (EQ_MP (@lem3892366 _100607 P) (@lem3892272 _100607 s P h1)). Qed.
Lemma lem3892372 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) (h1 : term319 _100607 s P) : False.
Proof. exact (@lem3892369 _100607 s P h1 (@lem3892361 _100607 s P h1)). Qed.
Lemma lem3892373 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) (h1 : term319 _100607 s P) : term741.
Proof. exact (fun h0 : ~ False => @lem3892372 _100607 s P h1). Qed.
Lemma lem3892375 (p : Prop) : (term739 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3892376 : term741 = False.
Proof. exact (@lem3892375 False). Qed.
Lemma lem3892393 {_100607 : Type'} (x : _100607 -> Prop) : x = x.
Proof. exact (@lem21386 (_100607 -> Prop) x). Qed.
Lemma lem3892394 {_100607 : Type'} (x : _100607 -> Prop) : x = x.
Proof. exact (@lem3892393 _100607 x). Qed.
Lemma lem3892395 {_100607 : Type'} : (@EMPTY _100607) = (@EMPTY _100607).
Proof. exact (@lem3892394 _100607 (@EMPTY _100607)). Qed.
Lemma lem3892396 {_100607 : Type'} : term742 _100607.
Proof. exact (fun h0 : term743 _100607 => @lem3892395 _100607). Qed.
Lemma lem3892398 (p : Prop) : (term739 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3892399 {_100607 : Type'} : (term742 _100607) = ((@EMPTY _100607) = (@EMPTY _100607)).
Proof. exact (@lem3892398 ((@EMPTY _100607) = (@EMPTY _100607))). Qed.
Lemma lem3892400 {_100607 : Type'} : (@EMPTY _100607) = (@EMPTY _100607).
Proof. exact (EQ_MP (@lem3892399 _100607) (@lem3892396 _100607)). Qed.
Lemma lem3892402 {_100607 : Type'} (P : type686 _100607) (h1 : term125 _100607 P) : P (@EMPTY _100607).
Proof. exact (proj2 (@lem3891984 _100607 P h1)). Qed.
Lemma lem3892403 {_100607 : Type'} (P : type686 _100607) (h1 : term125 _100607 P) : term738 _100607 P.
Proof. exact (fun h0 : term121 _100607 P => @lem3892402 _100607 P h1). Qed.
Lemma lem3892405 (p : Prop) : (term739 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3892406 {_100607 : Type'} (P : type686 _100607) : (term738 _100607 P) = (P (@EMPTY _100607)).
Proof. exact (@lem3892405 (P (@EMPTY _100607))). Qed.
Lemma lem3892407 {_100607 : Type'} (P : type686 _100607) (h1 : term125 _100607 P) : P (@EMPTY _100607).
Proof. exact (EQ_MP (@lem3892406 _100607 P) (@lem3892403 _100607 P h1)). Qed.
Lemma lem3892409 (a : Prop) (b : Prop) : (term744 a b) = (term745 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3892410 {_100607 : Type'} (P : type686 _100607) (_45244 : _100607 -> Prop) : (term111 _100607 P _45244) = (term110 _100607 P _45244).
Proof. exact (@lem3892409 (_45244 = (@EMPTY _100607)) (P _45244)). Qed.
Lemma lem3892412 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3892413 {_100607 : Type'} (P : type686 _100607) (_45244 : _100607 -> Prop) : (term110 _100607 P _45244) = (term746 _100607 P _45244).
Proof. exact (@lem3892412 (term11 _100607 P _45244)). Qed.
Lemma lem3892414 {_100607 : Type'} (P : type686 _100607) (_45244 : _100607 -> Prop) : (term111 _100607 P _45244) = (term746 _100607 P _45244).
Proof. exact (TRANS (@lem3892410 _100607 P _45244) (@lem3892413 _100607 P _45244)). Qed.
Lemma lem3892416 {_100607 : Type'} (P : type686 _100607) (h1 : term125 _100607 P) : term747 _100607 P.
Proof. exact (conj (@lem3892400 _100607) (@lem3892407 _100607 P h1)). Qed.
Lemma lem3892418 {_100607 : Type'} (_45244 : _100607 -> Prop) (P : type686 _100607) (h1 : term125 _100607 P) : term746 _100607 P _45244.
Proof. exact (EQ_MP (@lem3892414 _100607 P _45244) (@lem3892200 _100607 _45244 P h1)). Qed.
Lemma lem3892419 {_100607 : Type'} (_45244 : _100607 -> Prop) (P : type686 _100607) (h1 : term125 _100607 P) : term746 _100607 P _45244.
Proof. exact (@lem3892418 _100607 _45244 P h1). Qed.
Lemma lem3892420 {_100607 : Type'} (P : type686 _100607) (h1 : term125 _100607 P) : term748 _100607 P.
Proof. exact (@lem3892419 _100607 (@EMPTY _100607) P h1). Qed.
Lemma lem3892423 {_100607 : Type'} (P : type686 _100607) (h1 : term125 _100607 P) : False.
Proof. exact (@lem3892420 _100607 P h1 (@lem3892416 _100607 P h1)). Qed.
Lemma lem3892424 {_100607 : Type'} (P : type686 _100607) (h1 : term125 _100607 P) : term741.
Proof. exact (fun h0 : ~ False => @lem3892423 _100607 P h1). Qed.
Lemma lem3892426 (p : Prop) : (term739 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3892427 : term741 = False.
Proof. exact (@lem3892426 False). Qed.
Lemma lem3892428 {_100607 : Type'} (P : type686 _100607) (h1 : term125 _100607 P) : False.
Proof. exact (EQ_MP (@lem3892427) (@lem3892424 _100607 P h1)). Qed.
Lemma lem3892430 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (h1 : term439 _100607 a t s' n P) : @HAS_SIZE _100607 t n.
Proof. exact (proj1 (@lem3891996 _100607 a t s' n P h1)). Qed.
Lemma lem3892431 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (h1 : term439 _100607 a t s' n P) : term749 _100607 t n.
Proof. exact (fun h0 : term728 _100607 t n => @lem3892430 _100607 a t s' n P h1). Qed.
Lemma lem3892433 (p : Prop) : (term739 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3892434 {_100607 : Type'} (t : _100607 -> Prop) (n : nat) : (term749 _100607 t n) = (@HAS_SIZE _100607 t n).
Proof. exact (@lem3892433 (@HAS_SIZE _100607 t n)). Qed.
Lemma lem3892435 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (h1 : term439 _100607 a t s' n P) : @HAS_SIZE _100607 t n.
Proof. exact (EQ_MP (@lem3892434 _100607 t n) (@lem3892431 _100607 a t s' n P h1)). Qed.
Lemma lem3892437 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (h1 : term439 _100607 a t s' n P) : term186 _100607 P a t.
Proof. exact (EQ_MP (@lem3892325 _100607 a t s' n P h1) (@lem3892214 _100607 a t s' n P h1)). Qed.
Lemma lem3892438 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (h1 : term439 _100607 a t s' n P) : term750 _100607 P a t.
Proof. exact (fun h0 : term182 _100607 P a t => @lem3892437 _100607 a t s' n P h1). Qed.
Lemma lem3892440 (p : Prop) : (term739 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3892441 {_100607 : Type'} (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) : (term750 _100607 P a t) = (term186 _100607 P a t).
Proof. exact (@lem3892440 (term186 _100607 P a t)). Qed.
Lemma lem3892442 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (h1 : term439 _100607 a t s' n P) : term186 _100607 P a t.
Proof. exact (EQ_MP (@lem3892441 _100607 P a t) (@lem3892438 _100607 a t s' n P h1)). Qed.
Lemma lem3892448 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3892449 {_100607 : Type'} (n : nat) (P : type686 _100607) (_45245 : _100607) (_45246 : _100607 -> Prop) : (term188 _100607 n P _45245 _45246) = (term751 _100607 n P _45245 _45246).
Proof. exact (@lem3892448 (@IN _100607 _45245 _45246) (term728 _100607 _45246 n) (term182 _100607 P _45245 _45246)). Qed.
Lemma lem3892463 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3892464 {_100607 : Type'} (P : type686 _100607) (_45245 : _100607) (_45246 : _100607 -> Prop) (n : nat) : (term752 _100607 n P _45245 _45246) = (term753 _100607 P _45245 _45246 n).
Proof. exact (@lem3892463 (term182 _100607 P _45245 _45246) (term728 _100607 _45246 n)). Qed.
Lemma lem3892470 {_100607 : Type'} (_45245 : _100607) (_45246 : _100607 -> Prop) : (term143 _100607 _45245 _45246) = (term143 _100607 _45245 _45246).
Proof. exact (eq_refl (term143 _100607 _45245 _45246)). Qed.
Lemma lem3892471 {_100607 : Type'} (P : type686 _100607) (_45245 : _100607) (_45246 : _100607 -> Prop) (n : nat) : (term751 _100607 n P _45245 _45246) = (term754 _100607 P _45245 _45246 n).
Proof. exact (MK_COMB (@lem3892470 _100607 _45245 _45246) (@lem3892464 _100607 P _45245 _45246 n)). Qed.
Lemma lem3892482 {_100607 : Type'} (P : type686 _100607) (_45245 : _100607) (_45246 : _100607 -> Prop) (n : nat) : (term188 _100607 n P _45245 _45246) = (term754 _100607 P _45245 _45246 n).
Proof. exact (TRANS (@lem3892449 _100607 n P _45245 _45246) (@lem3892471 _100607 P _45245 _45246 n)). Qed.
Lemma lem3892483 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3892484 {_100607 : Type'} (P : type686 _100607) (_45245 : _100607) (_45246 : _100607 -> Prop) (n : nat) : (term755 _100607 n P _45245 _45246) = (term756 _100607 P _45245 _45246 n).
Proof. exact (MK_COMB (@lem3892483) (@lem3892482 _100607 P _45245 _45246 n)). Qed.
Lemma lem3892498 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3892499 {_100607 : Type'} (P : type686 _100607) (_45245 : _100607) (_45246 : _100607 -> Prop) (n : nat) : (term752 _100607 n P _45245 _45246) = (term753 _100607 P _45245 _45246 n).
Proof. exact (@lem3892498 (term182 _100607 P _45245 _45246) (term728 _100607 _45246 n)). Qed.
Lemma lem3892505 {_100607 : Type'} (_45245 : _100607) (_45246 : _100607 -> Prop) : (term143 _100607 _45245 _45246) = (term143 _100607 _45245 _45246).
Proof. exact (eq_refl (term143 _100607 _45245 _45246)). Qed.
Lemma lem3892506 {_100607 : Type'} (P : type686 _100607) (_45245 : _100607) (_45246 : _100607 -> Prop) (n : nat) : (term751 _100607 n P _45245 _45246) = (term754 _100607 P _45245 _45246 n).
Proof. exact (MK_COMB (@lem3892505 _100607 _45245 _45246) (@lem3892499 _100607 P _45245 _45246 n)). Qed.
Lemma lem3892517 {_100607 : Type'} (P : type686 _100607) (_45245 : _100607) (_45246 : _100607 -> Prop) (n : nat) : ((term188 _100607 n P _45245 _45246) = (term751 _100607 n P _45245 _45246)) = ((term754 _100607 P _45245 _45246 n) = (term754 _100607 P _45245 _45246 n)).
Proof. exact (MK_COMB (@lem3892484 _100607 P _45245 _45246 n) (@lem3892506 _100607 P _45245 _45246 n)). Qed.
Lemma lem3892519 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3892520 (x : Prop) : (x = x) = True.
Proof. exact (@lem3892519 Prop x). Qed.
Lemma lem3892521 {_100607 : Type'} (P : type686 _100607) (_45245 : _100607) (_45246 : _100607 -> Prop) (n : nat) : ((term754 _100607 P _45245 _45246 n) = (term754 _100607 P _45245 _45246 n)) = True.
Proof. exact (@lem3892520 (term754 _100607 P _45245 _45246 n)). Qed.
Lemma lem3892522 {_100607 : Type'} (n : nat) (P : type686 _100607) (_45245 : _100607) (_45246 : _100607 -> Prop) : ((term188 _100607 n P _45245 _45246) = (term751 _100607 n P _45245 _45246)) = True.
Proof. exact (TRANS (@lem3892517 _100607 P _45245 _45246 n) (@lem3892521 _100607 P _45245 _45246 n)). Qed.
Lemma lem3892523 {_100607 : Type'} (n : nat) (P : type686 _100607) (_45245 : _100607) (_45246 : _100607 -> Prop) : True = ((term188 _100607 n P _45245 _45246) = (term751 _100607 n P _45245 _45246)).
Proof. exact (SYM (@lem3892522 _100607 n P _45245 _45246)). Qed.
Lemma lem3892524 {_100607 : Type'} (n : nat) (P : type686 _100607) (_45245 : _100607) (_45246 : _100607 -> Prop) : (term188 _100607 n P _45245 _45246) = (term751 _100607 n P _45245 _45246).
Proof. exact (EQ_MP (@lem3892523 _100607 n P _45245 _45246) (@lem0)). Qed.
Lemma lem3892525 {_100607 : Type'} (_45245 : _100607) (_45246 : _100607 -> Prop) (a : _100607) (t : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (h1 : term439 _100607 a t s' n P) : term751 _100607 n P _45245 _45246.
Proof. exact (EQ_MP (@lem3892524 _100607 n P _45245 _45246) (@lem3892313 _100607 _45245 _45246 a t s' n P h1)). Qed.
Lemma lem3892527 (b : Prop) (a : Prop) : (a \/ b) = (term757 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3892528 {_100607 : Type'} (n : nat) (P : type686 _100607) (_45245 : _100607) (_45246 : _100607 -> Prop) : (term751 _100607 n P _45245 _45246) = (term758 _100607 n P _45245 _45246).
Proof. exact (@lem3892527 (term752 _100607 n P _45245 _45246) (@IN _100607 _45245 _45246)). Qed.
Lemma lem3892530 (a : Prop) (b : Prop) : (term759 a b) = (term760 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3892531 {_100607 : Type'} (n : nat) (P : type686 _100607) (_45245 : _100607) (_45246 : _100607 -> Prop) : (term761 _100607 n P _45245 _45246) = (term762 _100607 n P _45245 _45246).
Proof. exact (@lem3892530 (term728 _100607 _45246 n) (term182 _100607 P _45245 _45246)). Qed.
Lemma lem3892533 (a : Prop) : (term42 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3892534 {_100607 : Type'} (_45246 : _100607 -> Prop) (n : nat) : (term763 _100607 _45246 n) = (@HAS_SIZE _100607 _45246 n).
Proof. exact (@lem3892533 (@HAS_SIZE _100607 _45246 n)). Qed.
Lemma lem3892535 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3892536 {_100607 : Type'} (_45246 : _100607 -> Prop) (n : nat) : (term764 _100607 _45246 n) = (term765 _100607 _45246 n).
Proof. exact (MK_COMB (@lem3892535) (@lem3892534 _100607 _45246 n)). Qed.
Lemma lem3892538 (a : Prop) : (term42 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3892539 {_100607 : Type'} (P : type686 _100607) (_45245 : _100607) (_45246 : _100607 -> Prop) : (term766 _100607 P _45245 _45246) = (term186 _100607 P _45245 _45246).
Proof. exact (@lem3892538 (term186 _100607 P _45245 _45246)). Qed.
Lemma lem3892540 {_100607 : Type'} (n : nat) (P : type686 _100607) (_45245 : _100607) (_45246 : _100607 -> Prop) : (term762 _100607 n P _45245 _45246) = (term767 _100607 n P _45245 _45246).
Proof. exact (MK_COMB (@lem3892536 _100607 _45246 n) (@lem3892539 _100607 P _45245 _45246)). Qed.
Lemma lem3892541 {_100607 : Type'} (n : nat) (P : type686 _100607) (_45245 : _100607) (_45246 : _100607 -> Prop) : (term761 _100607 n P _45245 _45246) = (term767 _100607 n P _45245 _45246).
Proof. exact (TRANS (@lem3892531 _100607 n P _45245 _45246) (@lem3892540 _100607 n P _45245 _45246)). Qed.
Lemma lem3892542 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3892543 {_100607 : Type'} (n : nat) (P : type686 _100607) (_45245 : _100607) (_45246 : _100607 -> Prop) : (term768 _100607 n P _45245 _45246) = (term769 _100607 n P _45245 _45246).
Proof. exact (MK_COMB (@lem3892542) (@lem3892541 _100607 n P _45245 _45246)). Qed.
Lemma lem3892544 {_100607 : Type'} (_45245 : _100607) (_45246 : _100607 -> Prop) : (@IN _100607 _45245 _45246) = (@IN _100607 _45245 _45246).
Proof. exact (eq_refl (@IN _100607 _45245 _45246)). Qed.
Lemma lem3892545 {_100607 : Type'} (n : nat) (P : type686 _100607) (_45245 : _100607) (_45246 : _100607 -> Prop) : (term758 _100607 n P _45245 _45246) = (term770 _100607 n P _45245 _45246).
Proof. exact (MK_COMB (@lem3892543 _100607 n P _45245 _45246) (@lem3892544 _100607 _45245 _45246)). Qed.
Lemma lem3892546 {_100607 : Type'} (n : nat) (P : type686 _100607) (_45245 : _100607) (_45246 : _100607 -> Prop) : (term751 _100607 n P _45245 _45246) = (term770 _100607 n P _45245 _45246).
Proof. exact (TRANS (@lem3892528 _100607 n P _45245 _45246) (@lem3892545 _100607 n P _45245 _45246)). Qed.
Lemma lem3892548 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (h1 : term439 _100607 a t s' n P) : term767 _100607 n P a t.
Proof. exact (conj (@lem3892435 _100607 a t s' n P h1) (@lem3892442 _100607 a t s' n P h1)). Qed.
Lemma lem3892550 {_100607 : Type'} (_45245 : _100607) (_45246 : _100607 -> Prop) (a : _100607) (t : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (h1 : term439 _100607 a t s' n P) : term770 _100607 n P _45245 _45246.
Proof. exact (EQ_MP (@lem3892546 _100607 n P _45245 _45246) (@lem3892525 _100607 _45245 _45246 a t s' n P h1)). Qed.
Lemma lem3892551 {_100607 : Type'} (_45245 : _100607) (_45246 : _100607 -> Prop) (a : _100607) (t : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (h1 : term439 _100607 a t s' n P) : term770 _100607 n P _45245 _45246.
Proof. exact (@lem3892550 _100607 _45245 _45246 a t s' n P h1). Qed.
Lemma lem3892552 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (h1 : term439 _100607 a t s' n P) : term770 _100607 n P a t.
Proof. exact (@lem3892551 _100607 a t a t s' n P h1). Qed.
Lemma lem3892555 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (h1 : term439 _100607 a t s' n P) : @IN _100607 a t.
Proof. exact (@lem3892552 _100607 a t s' n P h1 (@lem3892548 _100607 a t s' n P h1)). Qed.
Lemma lem3892556 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (h1 : term439 _100607 a t s' n P) : term771 _100607 a t.
Proof. exact (fun h0 : term147 _100607 a t => @lem3892555 _100607 a t s' n P h1). Qed.
Lemma lem3892558 (p : Prop) : (term739 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3892559 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) : (term771 _100607 a t) = (@IN _100607 a t).
Proof. exact (@lem3892558 (@IN _100607 a t)). Qed.
Lemma lem3892560 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (h1 : term439 _100607 a t s' n P) : @IN _100607 a t.
Proof. exact (EQ_MP (@lem3892559 _100607 a t) (@lem3892556 _100607 a t s' n P h1)). Qed.
Lemma lem3892563 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3892565 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) : (term147 _100607 a t) = (term772 _100607 a t).
Proof. exact (@lem3892563 (@IN _100607 a t)). Qed.
Lemma lem3892568 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (h1 : term439 _100607 a t s' n P) : term772 _100607 a t.
Proof. exact (EQ_MP (@lem3892565 _100607 a t) (@lem3892354 _100607 a t s' n P h1)). Qed.
Lemma lem3892571 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (h1 : term439 _100607 a t s' n P) : False.
Proof. exact (@lem3892568 _100607 a t s' n P h1 (@lem3892560 _100607 a t s' n P h1)). Qed.
Lemma lem3892572 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (h1 : term439 _100607 a t s' n P) : term741.
Proof. exact (fun h0 : ~ False => @lem3892571 _100607 a t s' n P h1). Qed.
Lemma lem3892574 (p : Prop) : (term739 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3892575 : term741 = False.
Proof. exact (@lem3892574 False). Qed.
Lemma lem3892649 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) (h1 : term474 _100607 n P a t) : @HAS_SIZE _100607 t n.
Proof. exact (proj1 (@lem3892001 _100607 n P a t h1)). Qed.
Lemma lem3892650 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) (h1 : term474 _100607 n P a t) : term749 _100607 t n.
Proof. exact (fun h0 : term728 _100607 t n => @lem3892649 _100607 n P a t h1). Qed.
Lemma lem3892652 (p : Prop) : (term739 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3892653 {_100607 : Type'} (t : _100607 -> Prop) (n : nat) : (term749 _100607 t n) = (@HAS_SIZE _100607 t n).
Proof. exact (@lem3892652 (@HAS_SIZE _100607 t n)). Qed.
Lemma lem3892654 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) (h1 : term474 _100607 n P a t) : @HAS_SIZE _100607 t n.
Proof. exact (EQ_MP (@lem3892653 _100607 t n) (@lem3892650 _100607 n P a t h1)). Qed.
Lemma lem3892656 {_100607 : Type'} (x : _100607 -> Prop) : x = x.
Proof. exact (@lem21386 (_100607 -> Prop) x). Qed.
Lemma lem3892657 {_100607 : Type'} (x : _100607 -> Prop) : x = x.
Proof. exact (@lem3892656 _100607 x). Qed.
Lemma lem3892658 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) : (@INSERT _100607 a t) = (@INSERT _100607 a t).
Proof. exact (@lem3892657 _100607 (@INSERT _100607 a t)). Qed.
Lemma lem3892659 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) : term773 _100607 a t.
Proof. exact (fun h0 : term774 _100607 a t => @lem3892658 _100607 a t). Qed.
Lemma lem3892661 (p : Prop) : (term739 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3892662 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) : (term773 _100607 a t) = ((@INSERT _100607 a t) = (@INSERT _100607 a t)).
Proof. exact (@lem3892661 ((@INSERT _100607 a t) = (@INSERT _100607 a t))). Qed.
Lemma lem3892663 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) : (@INSERT _100607 a t) = (@INSERT _100607 a t).
Proof. exact (EQ_MP (@lem3892662 _100607 a t) (@lem3892659 _100607 a t)). Qed.
Lemma lem3892665 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) (h1 : term474 _100607 n P a t) : term186 _100607 P a t.
Proof. exact (proj2 (@lem3892003 _100607 n P a t h1)). Qed.
Lemma lem3892666 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) (h1 : term474 _100607 n P a t) : term750 _100607 P a t.
Proof. exact (fun h0 : term182 _100607 P a t => @lem3892665 _100607 n P a t h1). Qed.
Lemma lem3892668 (p : Prop) : (term739 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3892669 {_100607 : Type'} (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) : (term750 _100607 P a t) = (term186 _100607 P a t).
Proof. exact (@lem3892668 (term186 _100607 P a t)). Qed.
Lemma lem3892670 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) (h1 : term474 _100607 n P a t) : term186 _100607 P a t.
Proof. exact (EQ_MP (@lem3892669 _100607 P a t) (@lem3892666 _100607 n P a t h1)). Qed.
Lemma lem3892676 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3892677 {_100607 : Type'} (n : nat) (_45248 : _100607) (_45249 : _100607 -> Prop) (P : type686 _100607) (_45247 : _100607 -> Prop) : (term731 _100607 n _45248 _45249 P _45247) = (term775 _100607 n _45248 _45249 P _45247).
Proof. exact (@lem3892676 (@IN _100607 _45248 _45249) (term728 _100607 _45249 n) (term776 _100607 _45248 _45249 P _45247)). Qed.
Lemma lem3892691 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3892692 {_100607 : Type'} (_45248 : _100607) (_45249 : _100607 -> Prop) (n : nat) (P : type686 _100607) (_45247 : _100607 -> Prop) : (term777 _100607 n _45248 _45249 P _45247) = (term778 _100607 _45248 _45249 n P _45247).
Proof. exact (@lem3892691 (term141 _100607 _45247 _45248 _45249) (term728 _100607 _45249 n) (term169 _100607 P _45247)). Qed.
Lemma lem3892708 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3892709 {_100607 : Type'} (P : type686 _100607) (_45247 : _100607 -> Prop) (_45249 : _100607 -> Prop) (n : nat) : (term779 _100607 _45249 n P _45247) = (term780 _100607 P _45247 _45249 n).
Proof. exact (@lem3892708 (term169 _100607 P _45247) (term728 _100607 _45249 n)). Qed.
Lemma lem3892715 {_100607 : Type'} (_45247 : _100607 -> Prop) (_45248 : _100607) (_45249 : _100607 -> Prop) : (term781 _100607 _45247 _45248 _45249) = (term781 _100607 _45247 _45248 _45249).
Proof. exact (eq_refl (term781 _100607 _45247 _45248 _45249)). Qed.
Lemma lem3892716 {_100607 : Type'} (_45248 : _100607) (P : type686 _100607) (_45247 : _100607 -> Prop) (_45249 : _100607 -> Prop) (n : nat) : (term778 _100607 _45248 _45249 n P _45247) = (term782 _100607 _45248 P _45247 _45249 n).
Proof. exact (MK_COMB (@lem3892715 _100607 _45247 _45248 _45249) (@lem3892709 _100607 P _45247 _45249 n)). Qed.
Lemma lem3892720 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3892721 {_100607 : Type'} (P : type686 _100607) (_45247 : _100607 -> Prop) (_45248 : _100607) (_45249 : _100607 -> Prop) (n : nat) : (term782 _100607 _45248 P _45247 _45249 n) = (term783 _100607 P _45247 _45248 _45249 n).
Proof. exact (@lem3892720 (term169 _100607 P _45247) (term141 _100607 _45247 _45248 _45249) (term728 _100607 _45249 n)). Qed.
Lemma lem3892739 {_100607 : Type'} (P : type686 _100607) (_45247 : _100607 -> Prop) (_45248 : _100607) (_45249 : _100607 -> Prop) (n : nat) : (term778 _100607 _45248 _45249 n P _45247) = (term783 _100607 P _45247 _45248 _45249 n).
Proof. exact (TRANS (@lem3892716 _100607 _45248 P _45247 _45249 n) (@lem3892721 _100607 P _45247 _45248 _45249 n)). Qed.
Lemma lem3892740 {_100607 : Type'} (P : type686 _100607) (_45247 : _100607 -> Prop) (_45248 : _100607) (_45249 : _100607 -> Prop) (n : nat) : (term777 _100607 n _45248 _45249 P _45247) = (term783 _100607 P _45247 _45248 _45249 n).
Proof. exact (TRANS (@lem3892692 _100607 _45248 _45249 n P _45247) (@lem3892739 _100607 P _45247 _45248 _45249 n)). Qed.
Lemma lem3892741 {_100607 : Type'} (_45248 : _100607) (_45249 : _100607 -> Prop) : (term143 _100607 _45248 _45249) = (term143 _100607 _45248 _45249).
Proof. exact (eq_refl (term143 _100607 _45248 _45249)). Qed.
Lemma lem3892742 {_100607 : Type'} (P : type686 _100607) (_45247 : _100607 -> Prop) (_45248 : _100607) (_45249 : _100607 -> Prop) (n : nat) : (term775 _100607 n _45248 _45249 P _45247) = (term784 _100607 P _45247 _45248 _45249 n).
Proof. exact (MK_COMB (@lem3892741 _100607 _45248 _45249) (@lem3892740 _100607 P _45247 _45248 _45249 n)). Qed.
Lemma lem3892753 {_100607 : Type'} (P : type686 _100607) (_45247 : _100607 -> Prop) (_45248 : _100607) (_45249 : _100607 -> Prop) (n : nat) : (term731 _100607 n _45248 _45249 P _45247) = (term784 _100607 P _45247 _45248 _45249 n).
Proof. exact (TRANS (@lem3892677 _100607 n _45248 _45249 P _45247) (@lem3892742 _100607 P _45247 _45248 _45249 n)). Qed.
Lemma lem3892754 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3892755 {_100607 : Type'} (P : type686 _100607) (_45247 : _100607 -> Prop) (_45248 : _100607) (_45249 : _100607 -> Prop) (n : nat) : (term785 _100607 n _45248 _45249 P _45247) = (term786 _100607 P _45247 _45248 _45249 n).
Proof. exact (MK_COMB (@lem3892754) (@lem3892753 _100607 P _45247 _45248 _45249 n)). Qed.
Lemma lem3892769 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3892770 {_100607 : Type'} (_45248 : _100607) (_45249 : _100607 -> Prop) (n : nat) (P : type686 _100607) (_45247 : _100607 -> Prop) : (term777 _100607 n _45248 _45249 P _45247) = (term778 _100607 _45248 _45249 n P _45247).
Proof. exact (@lem3892769 (term141 _100607 _45247 _45248 _45249) (term728 _100607 _45249 n) (term169 _100607 P _45247)). Qed.
Lemma lem3892786 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3892787 {_100607 : Type'} (P : type686 _100607) (_45247 : _100607 -> Prop) (_45249 : _100607 -> Prop) (n : nat) : (term779 _100607 _45249 n P _45247) = (term780 _100607 P _45247 _45249 n).
Proof. exact (@lem3892786 (term169 _100607 P _45247) (term728 _100607 _45249 n)). Qed.
Lemma lem3892793 {_100607 : Type'} (_45247 : _100607 -> Prop) (_45248 : _100607) (_45249 : _100607 -> Prop) : (term781 _100607 _45247 _45248 _45249) = (term781 _100607 _45247 _45248 _45249).
Proof. exact (eq_refl (term781 _100607 _45247 _45248 _45249)). Qed.
Lemma lem3892794 {_100607 : Type'} (_45248 : _100607) (P : type686 _100607) (_45247 : _100607 -> Prop) (_45249 : _100607 -> Prop) (n : nat) : (term778 _100607 _45248 _45249 n P _45247) = (term782 _100607 _45248 P _45247 _45249 n).
Proof. exact (MK_COMB (@lem3892793 _100607 _45247 _45248 _45249) (@lem3892787 _100607 P _45247 _45249 n)). Qed.
Lemma lem3892798 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3892799 {_100607 : Type'} (P : type686 _100607) (_45247 : _100607 -> Prop) (_45248 : _100607) (_45249 : _100607 -> Prop) (n : nat) : (term782 _100607 _45248 P _45247 _45249 n) = (term783 _100607 P _45247 _45248 _45249 n).
Proof. exact (@lem3892798 (term169 _100607 P _45247) (term141 _100607 _45247 _45248 _45249) (term728 _100607 _45249 n)). Qed.
Lemma lem3892817 {_100607 : Type'} (P : type686 _100607) (_45247 : _100607 -> Prop) (_45248 : _100607) (_45249 : _100607 -> Prop) (n : nat) : (term778 _100607 _45248 _45249 n P _45247) = (term783 _100607 P _45247 _45248 _45249 n).
Proof. exact (TRANS (@lem3892794 _100607 _45248 P _45247 _45249 n) (@lem3892799 _100607 P _45247 _45248 _45249 n)). Qed.
Lemma lem3892818 {_100607 : Type'} (P : type686 _100607) (_45247 : _100607 -> Prop) (_45248 : _100607) (_45249 : _100607 -> Prop) (n : nat) : (term777 _100607 n _45248 _45249 P _45247) = (term783 _100607 P _45247 _45248 _45249 n).
Proof. exact (TRANS (@lem3892770 _100607 _45248 _45249 n P _45247) (@lem3892817 _100607 P _45247 _45248 _45249 n)). Qed.
Lemma lem3892819 {_100607 : Type'} (_45248 : _100607) (_45249 : _100607 -> Prop) : (term143 _100607 _45248 _45249) = (term143 _100607 _45248 _45249).
Proof. exact (eq_refl (term143 _100607 _45248 _45249)). Qed.
Lemma lem3892820 {_100607 : Type'} (P : type686 _100607) (_45247 : _100607 -> Prop) (_45248 : _100607) (_45249 : _100607 -> Prop) (n : nat) : (term775 _100607 n _45248 _45249 P _45247) = (term784 _100607 P _45247 _45248 _45249 n).
Proof. exact (MK_COMB (@lem3892819 _100607 _45248 _45249) (@lem3892818 _100607 P _45247 _45248 _45249 n)). Qed.
Lemma lem3892831 {_100607 : Type'} (P : type686 _100607) (_45247 : _100607 -> Prop) (_45248 : _100607) (_45249 : _100607 -> Prop) (n : nat) : ((term731 _100607 n _45248 _45249 P _45247) = (term775 _100607 n _45248 _45249 P _45247)) = ((term784 _100607 P _45247 _45248 _45249 n) = (term784 _100607 P _45247 _45248 _45249 n)).
Proof. exact (MK_COMB (@lem3892755 _100607 P _45247 _45248 _45249 n) (@lem3892820 _100607 P _45247 _45248 _45249 n)). Qed.
Lemma lem3892833 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3892834 (x : Prop) : (x = x) = True.
Proof. exact (@lem3892833 Prop x). Qed.
Lemma lem3892835 {_100607 : Type'} (P : type686 _100607) (_45247 : _100607 -> Prop) (_45248 : _100607) (_45249 : _100607 -> Prop) (n : nat) : ((term784 _100607 P _45247 _45248 _45249 n) = (term784 _100607 P _45247 _45248 _45249 n)) = True.
Proof. exact (@lem3892834 (term784 _100607 P _45247 _45248 _45249 n)). Qed.
Lemma lem3892836 {_100607 : Type'} (n : nat) (_45248 : _100607) (_45249 : _100607 -> Prop) (P : type686 _100607) (_45247 : _100607 -> Prop) : ((term731 _100607 n _45248 _45249 P _45247) = (term775 _100607 n _45248 _45249 P _45247)) = True.
Proof. exact (TRANS (@lem3892831 _100607 P _45247 _45248 _45249 n) (@lem3892835 _100607 P _45247 _45248 _45249 n)). Qed.
Lemma lem3892837 {_100607 : Type'} (n : nat) (_45248 : _100607) (_45249 : _100607 -> Prop) (P : type686 _100607) (_45247 : _100607 -> Prop) : True = ((term731 _100607 n _45248 _45249 P _45247) = (term775 _100607 n _45248 _45249 P _45247)).
Proof. exact (SYM (@lem3892836 _100607 n _45248 _45249 P _45247)). Qed.
Lemma lem3892838 {_100607 : Type'} (n : nat) (_45248 : _100607) (_45249 : _100607 -> Prop) (P : type686 _100607) (_45247 : _100607 -> Prop) : (term731 _100607 n _45248 _45249 P _45247) = (term775 _100607 n _45248 _45249 P _45247).
Proof. exact (EQ_MP (@lem3892837 _100607 n _45248 _45249 P _45247) (@lem0)). Qed.
Lemma lem3892839 {_100607 : Type'} (_45248 : _100607) (_45249 : _100607 -> Prop) (_45247 : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) (h1 : term474 _100607 n P a t) : term775 _100607 n _45248 _45249 P _45247.
Proof. exact (EQ_MP (@lem3892838 _100607 n _45248 _45249 P _45247) (@lem3892238 _100607 _45248 _45249 _45247 n P a t h1)). Qed.
Lemma lem3892841 (b : Prop) (a : Prop) : (a \/ b) = (term757 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3892842 {_100607 : Type'} (n : nat) (P : type686 _100607) (_45247 : _100607 -> Prop) (_45248 : _100607) (_45249 : _100607 -> Prop) : (term775 _100607 n _45248 _45249 P _45247) = (term787 _100607 n P _45247 _45248 _45249).
Proof. exact (@lem3892841 (term777 _100607 n _45248 _45249 P _45247) (@IN _100607 _45248 _45249)). Qed.
Lemma lem3892844 (a : Prop) (b : Prop) : (term759 a b) = (term760 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3892845 {_100607 : Type'} (n : nat) (_45248 : _100607) (_45249 : _100607 -> Prop) (P : type686 _100607) (_45247 : _100607 -> Prop) : (term788 _100607 n _45248 _45249 P _45247) = (term789 _100607 n _45248 _45249 P _45247).
Proof. exact (@lem3892844 (term728 _100607 _45249 n) (term776 _100607 _45248 _45249 P _45247)). Qed.
Lemma lem3892847 (a : Prop) : (term42 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3892848 {_100607 : Type'} (_45249 : _100607 -> Prop) (n : nat) : (term763 _100607 _45249 n) = (@HAS_SIZE _100607 _45249 n).
Proof. exact (@lem3892847 (@HAS_SIZE _100607 _45249 n)). Qed.
Lemma lem3892849 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3892850 {_100607 : Type'} (_45249 : _100607 -> Prop) (n : nat) : (term764 _100607 _45249 n) = (term765 _100607 _45249 n).
Proof. exact (MK_COMB (@lem3892849) (@lem3892848 _100607 _45249 n)). Qed.
Lemma lem3892852 (a : Prop) (b : Prop) : (term759 a b) = (term760 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3892853 {_100607 : Type'} (_45248 : _100607) (_45249 : _100607 -> Prop) (P : type686 _100607) (_45247 : _100607 -> Prop) : (term790 _100607 _45248 _45249 P _45247) = (term791 _100607 _45248 _45249 P _45247).
Proof. exact (@lem3892852 (term141 _100607 _45247 _45248 _45249) (term169 _100607 P _45247)). Qed.
Lemma lem3892855 (a : Prop) : (term42 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3892856 {_100607 : Type'} (_45247 : _100607 -> Prop) (_45248 : _100607) (_45249 : _100607 -> Prop) : (term792 _100607 _45247 _45248 _45249) = (_45247 = (@INSERT _100607 _45248 _45249)).
Proof. exact (@lem3892855 (_45247 = (@INSERT _100607 _45248 _45249))). Qed.
Lemma lem3892857 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3892858 {_100607 : Type'} (_45247 : _100607 -> Prop) (_45248 : _100607) (_45249 : _100607 -> Prop) : (term793 _100607 _45247 _45248 _45249) = (term794 _100607 _45247 _45248 _45249).
Proof. exact (MK_COMB (@lem3892857) (@lem3892856 _100607 _45247 _45248 _45249)). Qed.
Lemma lem3892860 (a : Prop) : (term42 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3892861 {_100607 : Type'} (P : type686 _100607) (_45247 : _100607 -> Prop) : (term795 _100607 P _45247) = (P _45247).
Proof. exact (@lem3892860 (P _45247)). Qed.
Lemma lem3892862 {_100607 : Type'} (_45248 : _100607) (_45249 : _100607 -> Prop) (P : type686 _100607) (_45247 : _100607 -> Prop) : (term791 _100607 _45248 _45249 P _45247) = (term796 _100607 _45248 _45249 P _45247).
Proof. exact (MK_COMB (@lem3892858 _100607 _45247 _45248 _45249) (@lem3892861 _100607 P _45247)). Qed.
Lemma lem3892863 {_100607 : Type'} (_45248 : _100607) (_45249 : _100607 -> Prop) (P : type686 _100607) (_45247 : _100607 -> Prop) : (term790 _100607 _45248 _45249 P _45247) = (term796 _100607 _45248 _45249 P _45247).
Proof. exact (TRANS (@lem3892853 _100607 _45248 _45249 P _45247) (@lem3892862 _100607 _45248 _45249 P _45247)). Qed.
Lemma lem3892864 {_100607 : Type'} (n : nat) (_45248 : _100607) (_45249 : _100607 -> Prop) (P : type686 _100607) (_45247 : _100607 -> Prop) : (term789 _100607 n _45248 _45249 P _45247) = (term797 _100607 n _45248 _45249 P _45247).
Proof. exact (MK_COMB (@lem3892850 _100607 _45249 n) (@lem3892863 _100607 _45248 _45249 P _45247)). Qed.
Lemma lem3892865 {_100607 : Type'} (n : nat) (_45248 : _100607) (_45249 : _100607 -> Prop) (P : type686 _100607) (_45247 : _100607 -> Prop) : (term788 _100607 n _45248 _45249 P _45247) = (term797 _100607 n _45248 _45249 P _45247).
Proof. exact (TRANS (@lem3892845 _100607 n _45248 _45249 P _45247) (@lem3892864 _100607 n _45248 _45249 P _45247)). Qed.
Lemma lem3892866 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3892867 {_100607 : Type'} (n : nat) (_45248 : _100607) (_45249 : _100607 -> Prop) (P : type686 _100607) (_45247 : _100607 -> Prop) : (term798 _100607 n _45248 _45249 P _45247) = (term799 _100607 n _45248 _45249 P _45247).
Proof. exact (MK_COMB (@lem3892866) (@lem3892865 _100607 n _45248 _45249 P _45247)). Qed.
Lemma lem3892868 {_100607 : Type'} (_45248 : _100607) (_45249 : _100607 -> Prop) : (@IN _100607 _45248 _45249) = (@IN _100607 _45248 _45249).
Proof. exact (eq_refl (@IN _100607 _45248 _45249)). Qed.
Lemma lem3892869 {_100607 : Type'} (n : nat) (P : type686 _100607) (_45247 : _100607 -> Prop) (_45248 : _100607) (_45249 : _100607 -> Prop) : (term787 _100607 n P _45247 _45248 _45249) = (term800 _100607 n P _45247 _45248 _45249).
Proof. exact (MK_COMB (@lem3892867 _100607 n _45248 _45249 P _45247) (@lem3892868 _100607 _45248 _45249)). Qed.
Lemma lem3892870 {_100607 : Type'} (n : nat) (P : type686 _100607) (_45247 : _100607 -> Prop) (_45248 : _100607) (_45249 : _100607 -> Prop) : (term775 _100607 n _45248 _45249 P _45247) = (term800 _100607 n P _45247 _45248 _45249).
Proof. exact (TRANS (@lem3892842 _100607 n P _45247 _45248 _45249) (@lem3892869 _100607 n P _45247 _45248 _45249)). Qed.
Lemma lem3892872 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) (h1 : term474 _100607 n P a t) : term801 _100607 P a t.
Proof. exact (conj (@lem3892663 _100607 a t) (@lem3892670 _100607 n P a t h1)). Qed.
Lemma lem3892873 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) (h1 : term474 _100607 n P a t) : term802 _100607 n P a t.
Proof. exact (conj (@lem3892654 _100607 n P a t h1) (@lem3892872 _100607 n P a t h1)). Qed.
Lemma lem3892875 {_100607 : Type'} (_45247 : _100607 -> Prop) (_45248 : _100607) (_45249 : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) (h1 : term474 _100607 n P a t) : term800 _100607 n P _45247 _45248 _45249.
Proof. exact (EQ_MP (@lem3892870 _100607 n P _45247 _45248 _45249) (@lem3892839 _100607 _45248 _45249 _45247 n P a t h1)). Qed.
Lemma lem3892876 {_100607 : Type'} (_45247 : _100607 -> Prop) (_45248 : _100607) (_45249 : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) (h1 : term474 _100607 n P a t) : term800 _100607 n P _45247 _45248 _45249.
Proof. exact (@lem3892875 _100607 _45247 _45248 _45249 n P a t h1). Qed.
Lemma lem3892877 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) (h1 : term474 _100607 n P a t) : term803 _100607 n P a t.
Proof. exact (@lem3892876 _100607 (@INSERT _100607 a t) a t n P a t h1). Qed.
Lemma lem3892880 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) (h1 : term474 _100607 n P a t) : @IN _100607 a t.
Proof. exact (@lem3892877 _100607 n P a t h1 (@lem3892873 _100607 n P a t h1)). Qed.
Lemma lem3892881 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) (h1 : term474 _100607 n P a t) : term771 _100607 a t.
Proof. exact (fun h0 : term147 _100607 a t => @lem3892880 _100607 n P a t h1). Qed.
Lemma lem3892883 (p : Prop) : (term739 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3892884 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) : (term771 _100607 a t) = (@IN _100607 a t).
Proof. exact (@lem3892883 (@IN _100607 a t)). Qed.
Lemma lem3892885 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) (h1 : term474 _100607 n P a t) : @IN _100607 a t.
Proof. exact (EQ_MP (@lem3892884 _100607 a t) (@lem3892881 _100607 n P a t h1)). Qed.
Lemma lem3892888 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3892890 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) : (term147 _100607 a t) = (term772 _100607 a t).
Proof. exact (@lem3892888 (@IN _100607 a t)). Qed.
Lemma lem3892893 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) (h1 : term474 _100607 n P a t) : term772 _100607 a t.
Proof. exact (EQ_MP (@lem3892890 _100607 a t) (@lem3892242 _100607 n P a t h1)). Qed.
Lemma lem3892896 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) (h1 : term474 _100607 n P a t) : False.
Proof. exact (@lem3892893 _100607 n P a t h1 (@lem3892885 _100607 n P a t h1)). Qed.
Lemma lem3892897 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) (h1 : term474 _100607 n P a t) : term741.
Proof. exact (fun h0 : ~ False => @lem3892896 _100607 n P a t h1). Qed.
Lemma lem3892899 (p : Prop) : (term739 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3892900 : term741 = False.
Proof. exact (@lem3892899 False). Qed.
Lemma lem3892901 {_100607 : Type'} (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) (h1 : term474 _100607 n P a t) : False.
Proof. exact (EQ_MP (@lem3892900) (@lem3892897 _100607 n P a t h1)). Qed.
Lemma lem3892902 {_100607 : Type'} (a : _100607) (t : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (h1 : term439 _100607 a t s' n P) : False.
Proof. exact (EQ_MP (@lem3892575) (@lem3892572 _100607 a t s' n P h1)). Qed.
Lemma lem3892903 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) (h1 : term319 _100607 s P) : False.
Proof. exact (EQ_MP (@lem3892376) (@lem3892373 _100607 s P h1)). Qed.
Lemma lem3892904 {_100607 : Type'} (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) (h1 : term570 _100607 s' n P a t) : False.
Proof. exact (or_elim (@lem3891982 _100607 s' n P a t h1) (fun h0 : term439 _100607 a t s' n P => @lem3892902 _100607 a t s' n P h0) (fun h0 : term474 _100607 n P a t => @lem3892901 _100607 n P a t h0)). Qed.
Lemma lem3892905 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) (h1 : term357 _100607 s P) : False.
Proof. exact (or_elim (@lem3891981 _100607 s P h1) (fun h0 : term319 _100607 s P => @lem3892903 _100607 s P h0) (fun h0 : term125 _100607 P => @lem3892428 _100607 P h0)). Qed.
Lemma lem3892906 {_100607 : Type'} (s : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) (h1 : term669 _100607 s s' n P a t) : False.
Proof. exact (or_elim (@lem3891980 _100607 s s' n P a t h1) (fun h0 : term357 _100607 s P => @lem3892905 _100607 s P h0) (fun h0 : term570 _100607 s' n P a t => @lem3892904 _100607 s' n P a t h0)). Qed.
Lemma lem3892907 {_100607 : Type'} (s : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) (h1 : term669 _100607 s s' n P a t) : (term669 _100607 s s' n P a t) = False.
Proof. exact (prop_ext (fun h2 : term669 _100607 s s' n P a t => @lem3892906 _100607 s s' n P a t h1) (fun h2 : False => @lem3891980 _100607 s s' n P a t h1)). Qed.
Lemma lem3892908 {_100607 : Type'} (s : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) (t : _100607 -> Prop) (h1 : term669 _100607 s s' n P a t) : False.
Proof. exact (EQ_MP (@lem3892907 _100607 s s' n P a t h1) (@lem3891980 _100607 s s' n P a t h1)). Qed.
Lemma lem3892909 {_100607 : Type'} (s : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (a : _100607) (h1 : term672 _100607 s s' n P a) : False.
Proof. exact (ex_elim (@lem3891783 _100607 s s' n P a h1) (fun t : _100607 -> Prop => fun h0 : term671 _100607 s s' n P a t => @lem3892908 _100607 s s' n P a t h0)). Qed.
Lemma lem3892910 {_100607 : Type'} (s : _100607 -> Prop) (s' : _100607 -> Prop) (n : nat) (P : type686 _100607) (h1 : term674 _100607 s s' n P) : False.
Proof. exact (ex_elim (@lem3891782 _100607 s s' n P h1) (fun a : _100607 => fun h0 : term673 _100607 s s' n P a => @lem3892909 _100607 s s' n P a h0)). Qed.
Lemma lem3892911 {_100607 : Type'} (s : _100607 -> Prop) (n : nat) (P : type686 _100607) (h1 : term676 _100607 s n P) : False.
Proof. exact (ex_elim (@lem3891781 _100607 s n P h1) (fun s' : _100607 -> Prop => fun h0 : term675 _100607 s n P s' => @lem3892910 _100607 s s' n P h0)). Qed.
Lemma lem3892912 {_100607 : Type'} (s : _100607 -> Prop) (P : type686 _100607) (h1 : term678 _100607 s P) : False.
Proof. exact (ex_elim (@lem3891780 _100607 s P h1) (fun n : nat => fun h0 : term677 _100607 s P n => @lem3892911 _100607 s n P h0)). Qed.
Lemma lem3892913 {_100607 : Type'} (P : type686 _100607) (h1 : term680 _100607 P) : False.
Proof. exact (ex_elim (@lem3891779 _100607 P h1) (fun s : _100607 -> Prop => fun h0 : term679 _100607 P s => @lem3892912 _100607 s P h0)). Qed.
Lemma lem3892914 {_100607 : Type'} (h1 : term109 _100607) : False.
Proof. exact (ex_elim (@lem3891778 _100607 h1) (fun P : type686 _100607 => fun h0 : term681 _100607 P => @lem3892913 _100607 P h0)). Qed.
Lemma lem3892915 {_100607 : Type'} (h1 : term109 _100607) : (term109 _100607) = False.
Proof. exact (prop_ext (fun h2 : term109 _100607 => @lem3892914 _100607 h1) (fun h2 : False => @lem3889916 _100607 h1)). Qed.
Lemma lem3892916 {_100607 : Type'} (h1 : term109 _100607) : False.
Proof. exact (EQ_MP (@lem3892915 _100607 h1) (@lem3889916 _100607 h1)). Qed.
Lemma lem3892917 {_100607 : Type'} : term108 _100607.
Proof. exact (fun h0 : term109 _100607 => @lem3892916 _100607 h0). Qed.
Lemma lem3892918 {_100607 : Type'} : term99 _100607.
Proof. exact (EQ_MP (@lem3889915 _100607) (@lem3892917 _100607)). Qed.
Lemma lem3892919 {_100607 : Type'} : term76 _100607.
Proof. exact (EQ_MP (@lem3889911 _100607) (@lem3892918 _100607)). Qed.
Lemma lem3892920 {_100607 : Type'} (P : type686 _100607) : term804 _100607 P.
Proof. exact (@lem3892919 _100607 P). Qed.
Lemma lem3892921 {_100607 : Type'} (P : type686 _100607) : (term804 _100607 P) = (term45 _100607 P).
Proof. exact (eq_refl (term804 _100607 P)). Qed.
Lemma lem3892922 {_100607 : Type'} (P : type686 _100607) : term45 _100607 P.
Proof. exact (EQ_MP (@lem3892921 _100607 P) (@lem3892920 _100607 P)). Qed.
Lemma lem3892923 {_100607 : Type'} (P : type686 _100607) (n : nat) : term805 _100607 P n.
Proof. exact (@lem3892922 _100607 P n). Qed.
Lemma lem3892924 {_100607 : Type'} (n : nat) (P : type686 _100607) : (term805 _100607 P n) = (term36 _100607 n P).
Proof. exact (eq_refl (term805 _100607 P n)). Qed.
Lemma lem3892925 {_100607 : Type'} (n : nat) (P : type686 _100607) : term36 _100607 n P.
Proof. exact (EQ_MP (@lem3892924 _100607 n P) (@lem3892923 _100607 P n)). Qed.
Lemma lem3892927 {_100607 : Type'} (n : nat) (P : type686 _100607) : term36 _100607 n P.
Proof. exact (@lem3889117 _100607 n P (@lem3892925 _100607 n P)). Qed.
Lemma lem3892928 {_100607 : Type'} (n : nat) (P : type686 _100607) (h1 : term37 _100607 n P) : False.
Proof. exact (@lem3892927 _100607 n P (@lem3889101 _100607 n P h1)). Qed.
Lemma lem3892929 {_100607 : Type'} (n : nat) (P : type686 _100607) (h1 : term37 _100607 n P) : (term37 _100607 n P) = False.
Proof. exact (prop_ext (fun h2 : term37 _100607 n P => @lem3892928 _100607 n P h1) (fun h2 : False => @lem3889101 _100607 n P h1)). Qed.
Lemma lem3892930 {_100607 : Type'} (n : nat) (P : type686 _100607) (h1 : term37 _100607 n P) : False.
Proof. exact (EQ_MP (@lem3892929 _100607 n P h1) (@lem3889101 _100607 n P h1)). Qed.
Lemma lem3892931 {_100607 : Type'} (n : nat) (P : type686 _100607) : term36 _100607 n P.
Proof. exact (fun h0 : term37 _100607 n P => @lem3892930 _100607 n P h0). Qed.
Lemma lem3892932 {_100607 : Type'} (n : nat) (P : type686 _100607) : term34 _100607 n P.
Proof. exact (EQ_MP (@lem3889100 _100607 n P) (@lem3892931 _100607 n P)). Qed.
Lemma lem3892933 {_100607 : Type'} (n : nat) (P : type686 _100607) : term33 _100607 n P.
Proof. exact (EQ_MP (@lem3889096 _100607 n P) (@lem3892932 _100607 n P)). Qed.
