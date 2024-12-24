Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MULT_0_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm80977_spec.
Lemma lem80982 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem80983 : term1.
Proof. exact (@lem80982 term2). Qed.
Lemma lem80984 : term3 = (term4 = (NUMERAL 0)).
Proof. exact (eq_refl term3). Qed.
Lemma lem80985 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem80986 : term5 = term6.
Proof. exact (MK_COMB (@lem80985) (@lem80984)). Qed.
Lemma lem80987 (m : nat) : (term7 m) = ((term8 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem80988 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem80989 (m : nat) : (term9 m) = (term10 m).
Proof. exact (MK_COMB (@lem80988) (@lem80987 m)). Qed.
Lemma lem80990 (m : nat) : (term11 m) = ((term12 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term11 m)). Qed.
Lemma lem80991 (m : nat) : (term13 m) = (term14 m).
Proof. exact (MK_COMB (@lem80989 m) (@lem80990 m)). Qed.
Lemma lem80992 : term15 = term16.
Proof. exact (fun_ext (fun m : nat => @lem80991 m)). Qed.
Lemma lem80993 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem80994 : term17 = term18.
Proof. exact (MK_COMB (@lem80993) (@lem80992)). Qed.
Lemma lem80995 : term19 = term20.
Proof. exact (MK_COMB (@lem80986) (@lem80994)). Qed.
Lemma lem80996 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem80997 : term21 = term22.
Proof. exact (MK_COMB (@lem80996) (@lem80995)). Qed.
Lemma lem80998 (m : nat) : (term7 m) = ((term8 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem80999 : term23 = term2.
Proof. exact (fun_ext (fun m : nat => @lem80998 m)). Qed.
Lemma lem81000 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem81001 : term24 = term25.
Proof. exact (MK_COMB (@lem81000) (@lem80999)). Qed.
Lemma lem81002 : term1 = term26.
Proof. exact (MK_COMB (@lem80997) (@lem81001)). Qed.
Lemma lem81003 : term26.
Proof. exact (EQ_MP (@lem81002) (@lem80983)). Qed.
Lemma lem81036 : term27.
Proof. exact (proj1 (@lem80977)). Qed.
Lemma lem81037 (n : nat) : term28 n.
Proof. exact (@lem81036 n). Qed.
Lemma lem81038 (n : nat) : (term28 n) = ((term29 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term28 n)). Qed.
Lemma lem81043 (n : nat) : (term29 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem81038 n) (@lem81037 n)). Qed.
Lemma lem81044 : term4 = (NUMERAL 0).
Proof. exact (@lem81043 (NUMERAL 0)). Qed.
Lemma lem81045 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem81046 : term30 = term31.
Proof. exact (MK_COMB (@lem81045) (@lem81044)). Qed.
Lemma lem81047 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem81048 : (term4 = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem81046) (@lem81047)). Qed.
Lemma lem81050 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem81051 (x : nat) : (x = x) = True.
Proof. exact (@lem81050 nat x). Qed.
Lemma lem81052 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem81051 (NUMERAL 0)). Qed.
Lemma lem81053 : (term4 = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem81048) (@lem81052)). Qed.
Lemma lem81054 : True = (term4 = (NUMERAL 0)).
Proof. exact (SYM (@lem81053)). Qed.
Lemma lem81055 : term4 = (NUMERAL 0).
Proof. exact (EQ_MP (@lem81054) (@lem0)). Qed.
Lemma lem81056 : term32.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem81072 : term33.
Proof. exact (proj1 (@lem81056)). Qed.
Lemma lem81073 (m : nat) : term34 m.
Proof. exact (@lem81072 m). Qed.
Lemma lem81074 (m : nat) : (term34 m) = ((term35 m) = m).
Proof. exact (eq_refl (term34 m)). Qed.
Lemma lem81080 : term36.
Proof. exact (proj2 (@lem80977)). Qed.
Lemma lem81081 (m : nat) : term37 m.
Proof. exact (@lem81080 m). Qed.
Lemma lem81082 (m : nat) : (term37 m) = (term38 m).
Proof. exact (eq_refl (term37 m)). Qed.
Lemma lem81083 (m : nat) : term38 m.
Proof. exact (EQ_MP (@lem81082 m) (@lem81081 m)). Qed.
Lemma lem81084 (m : nat) (n : nat) : term39 m n.
Proof. exact (@lem81083 m n). Qed.
Lemma lem81085 (m : nat) (n : nat) : (term39 m n) = ((term40 m n) = (term41 m n)).
Proof. exact (eq_refl (term39 m n)). Qed.
Lemma lem81094 (m : nat) (n : nat) : (term40 m n) = (term41 m n).
Proof. exact (EQ_MP (@lem81085 m n) (@lem81084 m n)). Qed.
Lemma lem81095 (m : nat) : (term12 m) = (term42 m).
Proof. exact (@lem81094 m (NUMERAL 0)). Qed.
Lemma lem81097 (m : nat) : (term35 m) = m.
Proof. exact (EQ_MP (@lem81074 m) (@lem81073 m)). Qed.
Lemma lem81098 (m : nat) : (term42 m) = (term8 m).
Proof. exact (@lem81097 (term8 m)). Qed.
Lemma lem81100 (m : nat) (h1 : (term8 m) = (NUMERAL 0)) : (term8 m) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem81101 (m : nat) (h1 : (term8 m) = (NUMERAL 0)) : (term42 m) = (NUMERAL 0).
Proof. exact (TRANS (@lem81098 m) (@lem81100 m h1)). Qed.
Lemma lem81102 (m : nat) (h1 : (term8 m) = (NUMERAL 0)) : (term12 m) = (NUMERAL 0).
Proof. exact (TRANS (@lem81095 m) (@lem81101 m h1)). Qed.
Lemma lem81103 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem81104 (m : nat) (h1 : (term8 m) = (NUMERAL 0)) : (term43 m) = term31.
Proof. exact (MK_COMB (@lem81103) (@lem81102 m h1)). Qed.
Lemma lem81105 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem81106 (m : nat) (h1 : (term8 m) = (NUMERAL 0)) : ((term12 m) = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem81104 m h1) (@lem81105)). Qed.
Lemma lem81108 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem81109 (x : nat) : (x = x) = True.
Proof. exact (@lem81108 nat x). Qed.
Lemma lem81110 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem81109 (NUMERAL 0)). Qed.
Lemma lem81111 (m : nat) (h1 : (term8 m) = (NUMERAL 0)) : ((term12 m) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem81106 m h1) (@lem81110)). Qed.
Lemma lem81112 (m : nat) (h1 : (term8 m) = (NUMERAL 0)) : True = ((term12 m) = (NUMERAL 0)).
Proof. exact (SYM (@lem81111 m h1)). Qed.
Lemma lem81113 (m : nat) (h1 : (term8 m) = (NUMERAL 0)) : (term12 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem81112 m h1) (@lem0)). Qed.
Lemma lem81114 (m : nat) : term14 m.
Proof. exact (fun h0 : (term8 m) = (NUMERAL 0) => @lem81113 m h0). Qed.
Lemma lem81119 : term18.
Proof. exact (fun m : nat => @lem81114 m). Qed.
Lemma lem81120 : term20.
Proof. exact (conj (@lem81055) (@lem81119)). Qed.
Lemma lem81121 : term25.
Proof. exact (@lem81003 (@lem81120)). Qed.
