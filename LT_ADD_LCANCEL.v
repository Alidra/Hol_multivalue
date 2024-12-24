Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LT_ADD_LCANCEL_term_abbrevs.
Require Import ADD_ASSOC_spec.
Require Import EQ_ADD_LCANCEL_spec.
Require Import LT_EXISTS_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem100977 (m : nat) (n : nat) (p : nat) (h1 : (term0 m n p) = (term1 m n p)) : (term0 m n p) = (term1 m n p).
Proof. exact (h1). Qed.
Lemma lem100978 (m : nat) (n : nat) (p : nat) (h1 : (term0 m n p) = (term1 m n p)) : (term1 m n p) = (term0 m n p).
Proof. exact (SYM (@lem100977 m n p h1)). Qed.
Lemma lem100979 (m : nat) (n : nat) (p : nat) (h1 : (term1 m n p) = (term0 m n p)) : (term1 m n p) = (term0 m n p).
Proof. exact (h1). Qed.
Lemma lem100980 (m : nat) (n : nat) (p : nat) (h1 : (term1 m n p) = (term0 m n p)) : (term0 m n p) = (term1 m n p).
Proof. exact (SYM (@lem100979 m n p h1)). Qed.
Lemma lem100981 (m : nat) (n : nat) (p : nat) : ((term0 m n p) = (term1 m n p)) = ((term1 m n p) = (term0 m n p)).
Proof. exact (prop_ext (fun h1 : (term0 m n p) = (term1 m n p) => @lem100978 m n p h1) (fun h1 : (term1 m n p) = (term0 m n p) => @lem100980 m n p h1)). Qed.
Lemma lem100982 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (fun_ext (fun p : nat => @lem100981 m n p)). Qed.
Lemma lem100983 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem100984 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (MK_COMB (@lem100983) (@lem100982 m n)). Qed.
Lemma lem100985 (m : nat) : (term6 m) = (term7 m).
Proof. exact (fun_ext (fun n : nat => @lem100984 m n)). Qed.
Lemma lem100986 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem100987 (m : nat) : (term8 m) = (term9 m).
Proof. exact (MK_COMB (@lem100986) (@lem100985 m)). Qed.
Lemma lem100988 : term10 = term11.
Proof. exact (fun_ext (fun m : nat => @lem100987 m)). Qed.
Lemma lem100989 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem100990 : term12 = term13.
Proof. exact (MK_COMB (@lem100989) (@lem100988)). Qed.
Lemma lem100991 : term13.
Proof. exact (EQ_MP (@lem100990) (@lem77960)). Qed.
Lemma lem100998 (m : nat) : term14 m.
Proof. exact (@lem79639 m). Qed.
Lemma lem100999 (m : nat) : (term14 m) = (term15 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem101000 (m : nat) : term15 m.
Proof. exact (EQ_MP (@lem100999 m) (@lem100998 m)). Qed.
Lemma lem101001 (m : nat) (n : nat) : term16 m n.
Proof. exact (@lem101000 m n). Qed.
Lemma lem101002 (m : nat) (n : nat) : (term16 m n) = (term17 m n).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem101003 (m : nat) (n : nat) : term17 m n.
Proof. exact (EQ_MP (@lem101002 m n) (@lem101001 m n)). Qed.
Lemma lem101004 (m : nat) (n : nat) (p : nat) : term18 m n p.
Proof. exact (@lem101003 m n p). Qed.
Lemma lem101005 (m : nat) (n : nat) (p : nat) : (term18 m n p) = (((Nat.add m n) = (Nat.add m p)) = (n = p)).
Proof. exact (eq_refl (term18 m n p)). Qed.
Lemma lem101007 (m : nat) : term19 m.
Proof. exact (@lem100991 m). Qed.
Lemma lem101008 (m : nat) : (term19 m) = (term9 m).
Proof. exact (eq_refl (term19 m)). Qed.
Lemma lem101009 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem101008 m) (@lem101007 m)). Qed.
Lemma lem101010 (m : nat) (n : nat) : term20 m n.
Proof. exact (@lem101009 m n). Qed.
Lemma lem101011 (m : nat) (n : nat) : (term20 m n) = (term5 m n).
Proof. exact (eq_refl (term20 m n)). Qed.
Lemma lem101012 (m : nat) (n : nat) : term5 m n.
Proof. exact (EQ_MP (@lem101011 m n) (@lem101010 m n)). Qed.
Lemma lem101013 (m : nat) (n : nat) (p : nat) : term21 m n p.
Proof. exact (@lem101012 m n p). Qed.
Lemma lem101014 (m : nat) (n : nat) (p : nat) : (term21 m n p) = ((term1 m n p) = (term0 m n p)).
Proof. exact (eq_refl (term21 m n p)). Qed.
Lemma lem101016 (m : nat) : term22 m.
Proof. exact (@lem100361 m). Qed.
Lemma lem101017 (m : nat) : (term22 m) = (term23 m).
Proof. exact (eq_refl (term22 m)). Qed.
Lemma lem101018 (m : nat) : term23 m.
Proof. exact (EQ_MP (@lem101017 m) (@lem101016 m)). Qed.
Lemma lem101019 (m : nat) (n : nat) : term24 m n.
Proof. exact (@lem101018 m n). Qed.
Lemma lem101020 (n : nat) (m : nat) : (term24 m n) = ((Peano.lt m n) = (term25 n m)).
Proof. exact (eq_refl (term24 m n)). Qed.
Lemma lem101037 (n : nat) (m : nat) : (Peano.lt m n) = (term25 n m).
Proof. exact (EQ_MP (@lem101020 n m) (@lem101019 m n)). Qed.
Lemma lem101038 (p : nat) (m : nat) (n : nat) : (term26 n m p) = (term27 p m n).
Proof. exact (@lem101037 (Nat.add m p) (Nat.add m n)). Qed.
Lemma lem101048 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term0 m n p).
Proof. exact (EQ_MP (@lem101014 m n p) (@lem101013 m n p)). Qed.
Lemma lem101049 (m : nat) (n : nat) (d : nat) : (term28 m n d) = (term29 m n d).
Proof. exact (@lem101048 m n (S d)). Qed.
Lemma lem101050 (m : nat) (p : nat) : (term30 m p) = (term30 m p).
Proof. exact (eq_refl (term30 m p)). Qed.
Lemma lem101051 (p : nat) (m : nat) (n : nat) (d : nat) : ((Nat.add m p) = (term28 m n d)) = ((Nat.add m p) = (term29 m n d)).
Proof. exact (MK_COMB (@lem101050 m p) (@lem101049 m n d)). Qed.
Lemma lem101053 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem101005 m n p) (@lem101004 m n p)). Qed.
Lemma lem101054 (m : nat) (p : nat) (n : nat) (d : nat) : ((Nat.add m p) = (term29 m n d)) = (p = (term31 n d)).
Proof. exact (@lem101053 m p (term31 n d)). Qed.
Lemma lem101057 (m : nat) (p : nat) (n : nat) (d : nat) : ((Nat.add m p) = (term28 m n d)) = (p = (term31 n d)).
Proof. exact (TRANS (@lem101051 p m n d) (@lem101054 m p n d)). Qed.
Lemma lem101058 (m : nat) (p : nat) (n : nat) : (term32 p m n) = (term33 p n).
Proof. exact (fun_ext (fun d : nat => @lem101057 m p n d)). Qed.
Lemma lem101059 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem101060 (m : nat) (p : nat) (n : nat) : (term27 p m n) = (term25 p n).
Proof. exact (MK_COMB (@lem101059) (@lem101058 m p n)). Qed.
Lemma lem101065 (m : nat) (p : nat) (n : nat) : (term26 n m p) = (term25 p n).
Proof. exact (TRANS (@lem101038 p m n) (@lem101060 m p n)). Qed.
Lemma lem101066 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem101067 (m : nat) (p : nat) (n : nat) : (term34 n m p) = (term35 p n).
Proof. exact (MK_COMB (@lem101066) (@lem101065 m p n)). Qed.
Lemma lem101069 (n : nat) (m : nat) : (Peano.lt m n) = (term25 n m).
Proof. exact (EQ_MP (@lem101020 n m) (@lem101019 m n)). Qed.
Lemma lem101070 (p : nat) (n : nat) : (Peano.lt n p) = (term25 p n).
Proof. exact (@lem101069 p n). Qed.
Lemma lem101077 (m : nat) (p : nat) (n : nat) : ((term26 n m p) = (Peano.lt n p)) = ((term25 p n) = (term25 p n)).
Proof. exact (MK_COMB (@lem101067 m p n) (@lem101070 p n)). Qed.
Lemma lem101079 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem101080 (x : Prop) : (x = x) = True.
Proof. exact (@lem101079 Prop x). Qed.
Lemma lem101081 (p : nat) (n : nat) : ((term25 p n) = (term25 p n)) = True.
Proof. exact (@lem101080 (term25 p n)). Qed.
Lemma lem101082 (m : nat) (n : nat) (p : nat) : ((term26 n m p) = (Peano.lt n p)) = True.
Proof. exact (TRANS (@lem101077 m p n) (@lem101081 p n)). Qed.
Lemma lem101083 (m : nat) (n : nat) : (term36 m n) = term37.
Proof. exact (fun_ext (fun p : nat => @lem101082 m n p)). Qed.
Lemma lem101084 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem101085 (m : nat) (n : nat) : (term38 m n) = term39.
Proof. exact (MK_COMB (@lem101084) (@lem101083 m n)). Qed.
Lemma lem101087 {A : Type'} (t : Prop) : (term40 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem101088 (t : Prop) : (term41 t) = t.
Proof. exact (@lem101087 nat t). Qed.
Lemma lem101089 : term39 = True.
Proof. exact (@lem101088 True). Qed.
Lemma lem101090 (m : nat) (n : nat) : (term38 m n) = True.
Proof. exact (TRANS (@lem101085 m n) (@lem101089)). Qed.
Lemma lem101091 (m : nat) : (term42 m) = term37.
Proof. exact (fun_ext (fun n : nat => @lem101090 m n)). Qed.
Lemma lem101092 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem101093 (m : nat) : (term43 m) = term39.
Proof. exact (MK_COMB (@lem101092) (@lem101091 m)). Qed.
Lemma lem101095 {A : Type'} (t : Prop) : (term40 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem101096 (t : Prop) : (term41 t) = t.
Proof. exact (@lem101095 nat t). Qed.
Lemma lem101097 : term39 = True.
Proof. exact (@lem101096 True). Qed.
Lemma lem101098 (m : nat) : (term43 m) = True.
Proof. exact (TRANS (@lem101093 m) (@lem101097)). Qed.
Lemma lem101099 : term44 = term37.
Proof. exact (fun_ext (fun m : nat => @lem101098 m)). Qed.
Lemma lem101100 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem101101 : term45 = term39.
Proof. exact (MK_COMB (@lem101100) (@lem101099)). Qed.
Lemma lem101103 {A : Type'} (t : Prop) : (term40 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem101104 (t : Prop) : (term41 t) = t.
Proof. exact (@lem101103 nat t). Qed.
Lemma lem101105 : term39 = True.
Proof. exact (@lem101104 True). Qed.
Lemma lem101106 : term45 = True.
Proof. exact (TRANS (@lem101101) (@lem101105)). Qed.
Lemma lem101107 : True = term45.
Proof. exact (SYM (@lem101106)). Qed.
Lemma lem101108 : term45.
Proof. exact (EQ_MP (@lem101107) (@lem0)). Qed.
