Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIST_RADD_term_abbrevs.
Require Import SUB_ADD_RCANCEL_spec.
Require Import dist_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1245076 (m : nat) : term0 m.
Proof. exact (@lem136770 m). Qed.
Lemma lem1245077 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1245078 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1245077 m) (@lem1245076 m)). Qed.
Lemma lem1245079 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1245078 m n). Qed.
Lemma lem1245080 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1245081 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem1245080 m n) (@lem1245079 m n)). Qed.
Lemma lem1245082 (m : nat) (n : nat) (p : nat) : term4 m n p.
Proof. exact (@lem1245081 m n p). Qed.
Lemma lem1245083 (p : nat) (m : nat) (n : nat) : (term4 m n p) = ((term5 m n p) = (Nat.sub m n)).
Proof. exact (eq_refl (term4 m n p)). Qed.
Lemma lem1245085 (n : nat) : term6 n.
Proof. exact (@lem1244710 n). Qed.
Lemma lem1245086 (n : nat) : (term6 n) = (term7 n).
Proof. exact (eq_refl (term6 n)). Qed.
Lemma lem1245087 (n : nat) : term7 n.
Proof. exact (EQ_MP (@lem1245086 n) (@lem1245085 n)). Qed.
Lemma lem1245088 (n : nat) (m : nat) : term8 n m.
Proof. exact (@lem1245087 n m). Qed.
Lemma lem1245089 (n : nat) (m : nat) : (term8 n m) = ((term9 m n) = (term10 n m)).
Proof. exact (eq_refl (term8 n m)). Qed.
Lemma lem1245106 (n : nat) (m : nat) : (term9 m n) = (term10 n m).
Proof. exact (EQ_MP (@lem1245089 n m) (@lem1245088 n m)). Qed.
Lemma lem1245107 (n : nat) (m : nat) (p : nat) : (term11 m n p) = (term12 n m p).
Proof. exact (@lem1245106 (Nat.add n p) (Nat.add m p)). Qed.
Lemma lem1245109 (p : nat) (m : nat) (n : nat) : (term5 m n p) = (Nat.sub m n).
Proof. exact (EQ_MP (@lem1245083 p m n) (@lem1245082 m n p)). Qed.
Lemma lem1245110 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1245111 (p : nat) (m : nat) (n : nat) : (term13 m n p) = (term14 m n).
Proof. exact (MK_COMB (@lem1245110) (@lem1245109 p m n)). Qed.
Lemma lem1245113 (p : nat) (m : nat) (n : nat) : (term5 m n p) = (Nat.sub m n).
Proof. exact (EQ_MP (@lem1245083 p m n) (@lem1245082 m n p)). Qed.
Lemma lem1245114 (p : nat) (n : nat) (m : nat) : (term5 n m p) = (Nat.sub n m).
Proof. exact (@lem1245113 p n m). Qed.
Lemma lem1245115 (p : nat) (n : nat) (m : nat) : (term12 n m p) = (term10 n m).
Proof. exact (MK_COMB (@lem1245111 p m n) (@lem1245114 p n m)). Qed.
Lemma lem1245116 (p : nat) (n : nat) (m : nat) : (term11 m n p) = (term10 n m).
Proof. exact (TRANS (@lem1245107 n m p) (@lem1245115 p n m)). Qed.
Lemma lem1245117 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1245118 (p : nat) (n : nat) (m : nat) : (term15 m n p) = (term16 n m).
Proof. exact (MK_COMB (@lem1245117) (@lem1245116 p n m)). Qed.
Lemma lem1245120 (n : nat) (m : nat) : (term9 m n) = (term10 n m).
Proof. exact (EQ_MP (@lem1245089 n m) (@lem1245088 n m)). Qed.
Lemma lem1245121 (p : nat) (n : nat) (m : nat) : ((term11 m n p) = (term9 m n)) = ((term10 n m) = (term10 n m)).
Proof. exact (MK_COMB (@lem1245118 p n m) (@lem1245120 n m)). Qed.
Lemma lem1245123 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1245124 (x : nat) : (x = x) = True.
Proof. exact (@lem1245123 nat x). Qed.
Lemma lem1245125 (n : nat) (m : nat) : ((term10 n m) = (term10 n m)) = True.
Proof. exact (@lem1245124 (term10 n m)). Qed.
Lemma lem1245126 (p : nat) (m : nat) (n : nat) : ((term11 m n p) = (term9 m n)) = True.
Proof. exact (TRANS (@lem1245121 p n m) (@lem1245125 n m)). Qed.
Lemma lem1245127 (p : nat) (m : nat) : (term17 p m) = term18.
Proof. exact (fun_ext (fun n : nat => @lem1245126 p m n)). Qed.
Lemma lem1245128 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1245129 (p : nat) (m : nat) : (term19 p m) = term20.
Proof. exact (MK_COMB (@lem1245128) (@lem1245127 p m)). Qed.
Lemma lem1245131 {A : Type'} (t : Prop) : (term21 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1245132 (t : Prop) : (term22 t) = t.
Proof. exact (@lem1245131 nat t). Qed.
Lemma lem1245133 : term20 = True.
Proof. exact (@lem1245132 True). Qed.
Lemma lem1245134 (p : nat) (m : nat) : (term19 p m) = True.
Proof. exact (TRANS (@lem1245129 p m) (@lem1245133)). Qed.
Lemma lem1245135 (m : nat) : (term23 m) = term18.
Proof. exact (fun_ext (fun p : nat => @lem1245134 p m)). Qed.
Lemma lem1245136 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1245137 (m : nat) : (term24 m) = term20.
Proof. exact (MK_COMB (@lem1245136) (@lem1245135 m)). Qed.
Lemma lem1245139 {A : Type'} (t : Prop) : (term21 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1245140 (t : Prop) : (term22 t) = t.
Proof. exact (@lem1245139 nat t). Qed.
Lemma lem1245141 : term20 = True.
Proof. exact (@lem1245140 True). Qed.
Lemma lem1245142 (m : nat) : (term24 m) = True.
Proof. exact (TRANS (@lem1245137 m) (@lem1245141)). Qed.
Lemma lem1245143 : term25 = term18.
Proof. exact (fun_ext (fun m : nat => @lem1245142 m)). Qed.
Lemma lem1245144 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1245145 : term26 = term20.
Proof. exact (MK_COMB (@lem1245144) (@lem1245143)). Qed.
Lemma lem1245147 {A : Type'} (t : Prop) : (term21 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1245148 (t : Prop) : (term22 t) = t.
Proof. exact (@lem1245147 nat t). Qed.
Lemma lem1245149 : term20 = True.
Proof. exact (@lem1245148 True). Qed.
Lemma lem1245150 : term26 = True.
Proof. exact (TRANS (@lem1245145) (@lem1245149)). Qed.
Lemma lem1245151 : True = term26.
Proof. exact (SYM (@lem1245150)). Qed.
Lemma lem1245152 : term26.
Proof. exact (EQ_MP (@lem1245151) (@lem0)). Qed.
