Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LE_LDIV_EQ_term_abbrevs.
Require Import ADD1_spec.
Require Import LE_RDIV_EQ_spec.
Require Import LE_SUC_LT_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_LE_spec.
Require Import NOT_LT_spec.
Require Import thm0_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm82_spec.
Lemma lem188987 (m : nat) : term0 m.
Proof. exact (@lem80621 m). Qed.
Lemma lem188988 (m : nat) : (term0 m) = ((S m) = (term1 m)).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem188990 (m : nat) : term2 m.
Proof. exact (@lem97961 m). Qed.
Lemma lem188991 (m : nat) : (term2 m) = (term3 m).
Proof. exact (eq_refl (term2 m)). Qed.
Lemma lem188992 (m : nat) : term3 m.
Proof. exact (EQ_MP (@lem188991 m) (@lem188990 m)). Qed.
Lemma lem188993 (m : nat) (n : nat) : term4 m n.
Proof. exact (@lem188992 m n). Qed.
Lemma lem188994 (n : nat) (m : nat) : (term4 m n) = ((term5 m n) = (Peano.lt n m)).
Proof. exact (eq_refl (term4 m n)). Qed.
Lemma lem189004 (m : nat) (n : nat) (h1 : (term6 m n) = (Peano.lt m n)) : (term6 m n) = (Peano.lt m n).
Proof. exact (h1). Qed.
Lemma lem189005 (m : nat) (n : nat) (h1 : (term6 m n) = (Peano.lt m n)) : (Peano.lt m n) = (term6 m n).
Proof. exact (SYM (@lem189004 m n h1)). Qed.
Lemma lem189006 (m : nat) (n : nat) (h1 : (Peano.lt m n) = (term6 m n)) : (Peano.lt m n) = (term6 m n).
Proof. exact (h1). Qed.
Lemma lem189007 (m : nat) (n : nat) (h1 : (Peano.lt m n) = (term6 m n)) : (term6 m n) = (Peano.lt m n).
Proof. exact (SYM (@lem189006 m n h1)). Qed.
Lemma lem189008 (m : nat) (n : nat) : ((term6 m n) = (Peano.lt m n)) = ((Peano.lt m n) = (term6 m n)).
Proof. exact (prop_ext (fun h1 : (term6 m n) = (Peano.lt m n) => @lem189005 m n h1) (fun h1 : (Peano.lt m n) = (term6 m n) => @lem189007 m n h1)). Qed.
Lemma lem189009 (m : nat) : (term7 m) = (term8 m).
Proof. exact (fun_ext (fun n : nat => @lem189008 m n)). Qed.
Lemma lem189010 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem189011 (m : nat) : (term9 m) = (term10 m).
Proof. exact (MK_COMB (@lem189010) (@lem189009 m)). Qed.
Lemma lem189012 : term11 = term12.
Proof. exact (fun_ext (fun m : nat => @lem189011 m)). Qed.
Lemma lem189013 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem189014 : term13 = term14.
Proof. exact (MK_COMB (@lem189013) (@lem189012)). Qed.
Lemma lem189015 : term14.
Proof. exact (EQ_MP (@lem189014) (@lem91144)). Qed.
Lemma lem189016 (m : nat) : term15 m.
Proof. exact (@lem189015 m). Qed.
Lemma lem189017 (m : nat) : (term15 m) = (term10 m).
Proof. exact (eq_refl (term15 m)). Qed.
Lemma lem189018 (m : nat) : term10 m.
Proof. exact (EQ_MP (@lem189017 m) (@lem189016 m)). Qed.
Lemma lem189019 (m : nat) (n : nat) : term16 m n.
Proof. exact (@lem189018 m n). Qed.
Lemma lem189020 (m : nat) (n : nat) : (term16 m n) = ((Peano.lt m n) = (term6 m n)).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem189024 (n : nat) (m : nat) (h1 : (term17 m n) = (Peano.le n m)) : (term17 m n) = (Peano.le n m).
Proof. exact (h1). Qed.
Lemma lem189025 (n : nat) (m : nat) (h1 : (term17 m n) = (Peano.le n m)) : (Peano.le n m) = (term17 m n).
Proof. exact (SYM (@lem189024 n m h1)). Qed.
Lemma lem189026 (m : nat) (n : nat) (h1 : (Peano.le n m) = (term17 m n)) : (Peano.le n m) = (term17 m n).
Proof. exact (h1). Qed.
Lemma lem189027 (m : nat) (n : nat) (h1 : (Peano.le n m) = (term17 m n)) : (term17 m n) = (Peano.le n m).
Proof. exact (SYM (@lem189026 m n h1)). Qed.
Lemma lem189028 (m : nat) (n : nat) : ((term17 m n) = (Peano.le n m)) = ((Peano.le n m) = (term17 m n)).
Proof. exact (prop_ext (fun h1 : (term17 m n) = (Peano.le n m) => @lem189025 n m h1) (fun h1 : (Peano.le n m) = (term17 m n) => @lem189027 m n h1)). Qed.
Lemma lem189029 (m : nat) : (term18 m) = (term19 m).
Proof. exact (fun_ext (fun n : nat => @lem189028 m n)). Qed.
Lemma lem189030 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem189031 (m : nat) : (term20 m) = (term21 m).
Proof. exact (MK_COMB (@lem189030) (@lem189029 m)). Qed.
Lemma lem189032 : term22 = term23.
Proof. exact (fun_ext (fun m : nat => @lem189031 m)). Qed.
Lemma lem189033 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem189034 : term24 = term25.
Proof. exact (MK_COMB (@lem189033) (@lem189032)). Qed.
Lemma lem189035 : term25.
Proof. exact (EQ_MP (@lem189034) (@lem98377)). Qed.
Lemma lem189036 (m : nat) : term26 m.
Proof. exact (@lem189035 m). Qed.
Lemma lem189037 (m : nat) : (term26 m) = (term21 m).
Proof. exact (eq_refl (term26 m)). Qed.
Lemma lem189038 (m : nat) : term21 m.
Proof. exact (EQ_MP (@lem189037 m) (@lem189036 m)). Qed.
Lemma lem189039 (m : nat) (n : nat) : term27 m n.
Proof. exact (@lem189038 m n). Qed.
Lemma lem189040 (m : nat) (n : nat) : (term27 m n) = ((Peano.le n m) = (term17 m n)).
Proof. exact (eq_refl (term27 m n)). Qed.
Lemma lem189042 (a : nat) (h1 : term28 a) : term28 a.
Proof. exact (h1). Qed.
Lemma lem189046 (m : nat) (n : nat) : (Peano.le n m) = (term17 m n).
Proof. exact (EQ_MP (@lem189040 m n) (@lem189039 m n)). Qed.
Lemma lem189047 (n : nat) (b : nat) (a : nat) : (term29 b a n) = (term30 n b a).
Proof. exact (@lem189046 n (Nat.div b a)). Qed.
Lemma lem189048 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem189049 (n : nat) (b : nat) (a : nat) : (term31 b a n) = (term32 n b a).
Proof. exact (MK_COMB (@lem189048) (@lem189047 n b a)). Qed.
Lemma lem189050 (b : nat) (a : nat) (n : nat) : (term33 b a n) = (term33 b a n).
Proof. exact (eq_refl (term33 b a n)). Qed.
Lemma lem189051 (b : nat) (a : nat) (n : nat) : ((term29 b a n) = (term33 b a n)) = ((term30 n b a) = (term33 b a n)).
Proof. exact (MK_COMB (@lem189049 n b a) (@lem189050 b a n)). Qed.
Lemma lem189052 (b : nat) (a : nat) (n : nat) : ((term30 n b a) = (term33 b a n)) = ((term29 b a n) = (term33 b a n)).
Proof. exact (SYM (@lem189051 b a n)). Qed.
Lemma lem189054 (m : nat) (n : nat) : (Peano.lt m n) = (term6 m n).
Proof. exact (EQ_MP (@lem189020 m n) (@lem189019 m n)). Qed.
Lemma lem189055 (n : nat) (b : nat) (a : nat) : (term34 n b a) = (term35 n b a).
Proof. exact (@lem189054 n (Nat.div b a)). Qed.
Lemma lem189056 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem189057 (n : nat) (b : nat) (a : nat) : (term30 n b a) = (term36 n b a).
Proof. exact (MK_COMB (@lem189056) (@lem189055 n b a)). Qed.
Lemma lem189058 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem189059 (n : nat) (b : nat) (a : nat) : (term32 n b a) = (term37 n b a).
Proof. exact (MK_COMB (@lem189058) (@lem189057 n b a)). Qed.
Lemma lem189060 (b : nat) (a : nat) (n : nat) : (term33 b a n) = (term33 b a n).
Proof. exact (eq_refl (term33 b a n)). Qed.
Lemma lem189061 (b : nat) (a : nat) (n : nat) : ((term30 n b a) = (term33 b a n)) = ((term36 n b a) = (term33 b a n)).
Proof. exact (MK_COMB (@lem189059 n b a) (@lem189060 b a n)). Qed.
Lemma lem189062 (b : nat) (a : nat) (n : nat) : ((term36 n b a) = (term33 b a n)) = ((term30 n b a) = (term33 b a n)).
Proof. exact (SYM (@lem189061 b a n)). Qed.
Lemma lem189063 (a : nat) : term38 a.
Proof. exact (@lem188842 a). Qed.
Lemma lem189064 (a : nat) : (term38 a) = (term39 a).
Proof. exact (eq_refl (term38 a)). Qed.
Lemma lem189065 (a : nat) : term39 a.
Proof. exact (EQ_MP (@lem189064 a) (@lem189063 a)). Qed.
Lemma lem189066 (a : nat) (b : nat) : term40 a b.
Proof. exact (@lem189065 a b). Qed.
Lemma lem189067 (a : nat) (b : nat) : (term40 a b) = (term41 a b).
Proof. exact (eq_refl (term40 a b)). Qed.
Lemma lem189068 (a : nat) (b : nat) : term41 a b.
Proof. exact (EQ_MP (@lem189067 a b) (@lem189066 a b)). Qed.
Lemma lem189069 (a : nat) (b : nat) (n : nat) : term42 a b n.
Proof. exact (@lem189068 a b n). Qed.
Lemma lem189070 (a : nat) (n : nat) (b : nat) : (term42 a b n) = (term43 a n b).
Proof. exact (eq_refl (term42 a b n)). Qed.
Lemma lem189071 (a : nat) (n : nat) (b : nat) : term43 a n b.
Proof. exact (EQ_MP (@lem189070 a n b) (@lem189069 a b n)). Qed.
Lemma lem189072 (a : nat) (h1 : term28 a) : term28 a.
Proof. exact (h1). Qed.
Lemma lem189073 (n : nat) (b : nat) (a : nat) (h1 : term28 a) : (term44 n b a) = (term45 a n b).
Proof. exact (@lem189071 a n b (@lem189072 a h1)). Qed.
Lemma lem189079 (a : nat) : term46 a.
Proof. exact (@lem82 (a = (NUMERAL 0))). Qed.
Lemma lem189095 (a : nat) (n : nat) (b : nat) : term43 a n b.
Proof. exact (fun h0 : term28 a => @lem189073 n b a h0). Qed.
Lemma lem189096 (a : nat) (n : nat) (b : nat) : term47 a n b.
Proof. exact (@lem189095 a (S n) b). Qed.
Lemma lem189098 (a : nat) (h1 : term28 a) : (a = (NUMERAL 0)) = False.
Proof. exact (@lem189079 a (@lem189042 a h1)). Qed.
Lemma lem189099 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem189100 (a : nat) (h1 : term28 a) : (term28 a) = (~ False).
Proof. exact (MK_COMB (@lem189099) (@lem189098 a h1)). Qed.
Lemma lem189102 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem189103 (a : nat) (h1 : term28 a) : (term28 a) = True.
Proof. exact (TRANS (@lem189100 a h1) (@lem189102)). Qed.
Lemma lem189104 (a : nat) (h1 : term28 a) : True = (term28 a).
Proof. exact (SYM (@lem189103 a h1)). Qed.
Lemma lem189105 (a : nat) (h1 : term28 a) : term28 a.
Proof. exact (EQ_MP (@lem189104 a h1) (@lem0)). Qed.
Lemma lem189106 (n : nat) (b : nat) (a : nat) (h1 : term28 a) : (term35 n b a) = (term48 a n b).
Proof. exact (@lem189096 a n b (@lem189105 a h1)). Qed.
Lemma lem189107 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem189108 (n : nat) (b : nat) (a : nat) (h1 : term28 a) : (term36 n b a) = (term49 a n b).
Proof. exact (MK_COMB (@lem189107) (@lem189106 n b a h1)). Qed.
Lemma lem189109 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem189110 (n : nat) (b : nat) (a : nat) (h1 : term28 a) : (term37 n b a) = (term50 a n b).
Proof. exact (MK_COMB (@lem189109) (@lem189108 n b a h1)). Qed.
Lemma lem189111 (b : nat) (a : nat) (n : nat) : (term33 b a n) = (term33 b a n).
Proof. exact (eq_refl (term33 b a n)). Qed.
Lemma lem189112 (b : nat) (n : nat) (a : nat) (h1 : term28 a) : ((term36 n b a) = (term33 b a n)) = ((term49 a n b) = (term33 b a n)).
Proof. exact (MK_COMB (@lem189110 n b a h1) (@lem189111 b a n)). Qed.
Lemma lem189115 (b : nat) (n : nat) (a : nat) (h1 : term28 a) : ((term49 a n b) = (term33 b a n)) = ((term36 n b a) = (term33 b a n)).
Proof. exact (SYM (@lem189112 b n a h1)). Qed.
Lemma lem189119 (n : nat) (m : nat) : (term5 m n) = (Peano.lt n m).
Proof. exact (EQ_MP (@lem188994 n m) (@lem188993 m n)). Qed.
Lemma lem189120 (b : nat) (a : nat) (n : nat) : (term49 a n b) = (term51 b a n).
Proof. exact (@lem189119 b (term52 a n)). Qed.
Lemma lem189122 (m : nat) : (S m) = (term1 m).
Proof. exact (EQ_MP (@lem188988 m) (@lem188987 m)). Qed.
Lemma lem189123 (n : nat) : (S n) = (term1 n).
Proof. exact (@lem189122 n). Qed.
Lemma lem189124 (a : nat) : (Nat.mul a) = (Nat.mul a).
Proof. exact (eq_refl (Nat.mul a)). Qed.
Lemma lem189125 (a : nat) (n : nat) : (term52 a n) = (term53 a n).
Proof. exact (MK_COMB (@lem189124 a) (@lem189123 n)). Qed.
Lemma lem189126 (b : nat) : (Peano.lt b) = (Peano.lt b).
Proof. exact (eq_refl (Peano.lt b)). Qed.
Lemma lem189127 (b : nat) (a : nat) (n : nat) : (term51 b a n) = (term33 b a n).
Proof. exact (MK_COMB (@lem189126 b) (@lem189125 a n)). Qed.
Lemma lem189128 (b : nat) (a : nat) (n : nat) : (term49 a n b) = (term33 b a n).
Proof. exact (TRANS (@lem189120 b a n) (@lem189127 b a n)). Qed.
Lemma lem189129 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem189130 (b : nat) (a : nat) (n : nat) : (term50 a n b) = (term54 b a n).
Proof. exact (MK_COMB (@lem189129) (@lem189128 b a n)). Qed.
Lemma lem189131 (b : nat) (a : nat) (n : nat) : (term33 b a n) = (term33 b a n).
Proof. exact (eq_refl (term33 b a n)). Qed.
Lemma lem189132 (b : nat) (a : nat) (n : nat) : ((term49 a n b) = (term33 b a n)) = ((term33 b a n) = (term33 b a n)).
Proof. exact (MK_COMB (@lem189130 b a n) (@lem189131 b a n)). Qed.
Lemma lem189134 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem189135 (x : Prop) : (x = x) = True.
Proof. exact (@lem189134 Prop x). Qed.
Lemma lem189136 (b : nat) (a : nat) (n : nat) : ((term33 b a n) = (term33 b a n)) = True.
Proof. exact (@lem189135 (term33 b a n)). Qed.
Lemma lem189137 (b : nat) (a : nat) (n : nat) : ((term49 a n b) = (term33 b a n)) = True.
Proof. exact (TRANS (@lem189132 b a n) (@lem189136 b a n)). Qed.
Lemma lem189138 (b : nat) (a : nat) (n : nat) : True = ((term49 a n b) = (term33 b a n)).
Proof. exact (SYM (@lem189137 b a n)). Qed.
Lemma lem189139 (b : nat) (a : nat) (n : nat) : (term49 a n b) = (term33 b a n).
Proof. exact (EQ_MP (@lem189138 b a n) (@lem0)). Qed.
Lemma lem189140 (b : nat) (n : nat) (a : nat) (h1 : term28 a) : (term36 n b a) = (term33 b a n).
Proof. exact (EQ_MP (@lem189115 b n a h1) (@lem189139 b a n)). Qed.
Lemma lem189141 (b : nat) (n : nat) (a : nat) (h1 : term28 a) : (term30 n b a) = (term33 b a n).
Proof. exact (EQ_MP (@lem189062 b a n) (@lem189140 b n a h1)). Qed.
Lemma lem189142 (b : nat) (n : nat) (a : nat) (h1 : term28 a) : (term29 b a n) = (term33 b a n).
Proof. exact (EQ_MP (@lem189052 b a n) (@lem189141 b n a h1)). Qed.
Lemma lem189143 (b : nat) (n : nat) (a : nat) (h1 : term28 a) : (term28 a) = ((term29 b a n) = (term33 b a n)).
Proof. exact (prop_ext (fun h2 : term28 a => @lem189142 b n a h1) (fun h2 : (term29 b a n) = (term33 b a n) => @lem189042 a h1)). Qed.
Lemma lem189144 (b : nat) (n : nat) (a : nat) (h1 : term28 a) : (term29 b a n) = (term33 b a n).
Proof. exact (EQ_MP (@lem189143 b n a h1) (@lem189042 a h1)). Qed.
Lemma lem189145 (b : nat) (a : nat) (n : nat) : term55 b a n.
Proof. exact (fun h0 : term28 a => @lem189144 b n a h0). Qed.
Lemma lem189150 (b : nat) (a : nat) : term56 b a.
Proof. exact (fun n : nat => @lem189145 b a n). Qed.
Lemma lem189155 (a : nat) : term57 a.
Proof. exact (fun b : nat => @lem189150 b a). Qed.
Lemma lem189160 : term58.
Proof. exact (fun a : nat => @lem189155 a). Qed.
