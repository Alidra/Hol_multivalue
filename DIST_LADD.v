Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIST_LADD_term_abbrevs.
Require Import SUB_ADD_LCANCEL_spec.
Require Import dist_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1244998 (m : nat) : term0 m.
Proof. exact (@lem136699 m). Qed.
Lemma lem1244999 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1245000 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1244999 m) (@lem1244998 m)). Qed.
Lemma lem1245001 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1245000 m n). Qed.
Lemma lem1245002 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1245003 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem1245002 m n) (@lem1245001 m n)). Qed.
Lemma lem1245004 (m : nat) (n : nat) (p : nat) : term4 m n p.
Proof. exact (@lem1245003 m n p). Qed.
Lemma lem1245005 (m : nat) (n : nat) (p : nat) : (term4 m n p) = ((term5 n m p) = (Nat.sub n p)).
Proof. exact (eq_refl (term4 m n p)). Qed.
Lemma lem1245007 (n : nat) : term6 n.
Proof. exact (@lem1244710 n). Qed.
Lemma lem1245008 (n : nat) : (term6 n) = (term7 n).
Proof. exact (eq_refl (term6 n)). Qed.
Lemma lem1245009 (n : nat) : term7 n.
Proof. exact (EQ_MP (@lem1245008 n) (@lem1245007 n)). Qed.
Lemma lem1245010 (n : nat) (m : nat) : term8 n m.
Proof. exact (@lem1245009 n m). Qed.
Lemma lem1245011 (n : nat) (m : nat) : (term8 n m) = ((term9 m n) = (term10 n m)).
Proof. exact (eq_refl (term8 n m)). Qed.
Lemma lem1245028 (n : nat) (m : nat) : (term9 m n) = (term10 n m).
Proof. exact (EQ_MP (@lem1245011 n m) (@lem1245010 n m)). Qed.
Lemma lem1245029 (p : nat) (m : nat) (n : nat) : (term11 n m p) = (term12 p m n).
Proof. exact (@lem1245028 (Nat.add m p) (Nat.add m n)). Qed.
Lemma lem1245031 (m : nat) (n : nat) (p : nat) : (term5 n m p) = (Nat.sub n p).
Proof. exact (EQ_MP (@lem1245005 m n p) (@lem1245004 m n p)). Qed.
Lemma lem1245032 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1245033 (m : nat) (n : nat) (p : nat) : (term13 n m p) = (term14 n p).
Proof. exact (MK_COMB (@lem1245032) (@lem1245031 m n p)). Qed.
Lemma lem1245035 (m : nat) (n : nat) (p : nat) : (term5 n m p) = (Nat.sub n p).
Proof. exact (EQ_MP (@lem1245005 m n p) (@lem1245004 m n p)). Qed.
Lemma lem1245036 (m : nat) (p : nat) (n : nat) : (term5 p m n) = (Nat.sub p n).
Proof. exact (@lem1245035 m p n). Qed.
Lemma lem1245037 (m : nat) (p : nat) (n : nat) : (term12 p m n) = (term10 p n).
Proof. exact (MK_COMB (@lem1245033 m n p) (@lem1245036 m p n)). Qed.
Lemma lem1245038 (m : nat) (p : nat) (n : nat) : (term11 n m p) = (term10 p n).
Proof. exact (TRANS (@lem1245029 p m n) (@lem1245037 m p n)). Qed.
Lemma lem1245039 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1245040 (m : nat) (p : nat) (n : nat) : (term15 n m p) = (term16 p n).
Proof. exact (MK_COMB (@lem1245039) (@lem1245038 m p n)). Qed.
Lemma lem1245042 (n : nat) (m : nat) : (term9 m n) = (term10 n m).
Proof. exact (EQ_MP (@lem1245011 n m) (@lem1245010 n m)). Qed.
Lemma lem1245043 (p : nat) (n : nat) : (term9 n p) = (term10 p n).
Proof. exact (@lem1245042 p n). Qed.
Lemma lem1245044 (m : nat) (p : nat) (n : nat) : ((term11 n m p) = (term9 n p)) = ((term10 p n) = (term10 p n)).
Proof. exact (MK_COMB (@lem1245040 m p n) (@lem1245043 p n)). Qed.
Lemma lem1245046 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1245047 (x : nat) : (x = x) = True.
Proof. exact (@lem1245046 nat x). Qed.
Lemma lem1245048 (p : nat) (n : nat) : ((term10 p n) = (term10 p n)) = True.
Proof. exact (@lem1245047 (term10 p n)). Qed.
Lemma lem1245049 (m : nat) (n : nat) (p : nat) : ((term11 n m p) = (term9 n p)) = True.
Proof. exact (TRANS (@lem1245044 m p n) (@lem1245048 p n)). Qed.
Lemma lem1245050 (m : nat) (p : nat) : (term17 m p) = term18.
Proof. exact (fun_ext (fun n : nat => @lem1245049 m n p)). Qed.
Lemma lem1245051 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1245052 (m : nat) (p : nat) : (term19 m p) = term20.
Proof. exact (MK_COMB (@lem1245051) (@lem1245050 m p)). Qed.
Lemma lem1245054 {A : Type'} (t : Prop) : (term21 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1245055 (t : Prop) : (term22 t) = t.
Proof. exact (@lem1245054 nat t). Qed.
Lemma lem1245056 : term20 = True.
Proof. exact (@lem1245055 True). Qed.
Lemma lem1245057 (m : nat) (p : nat) : (term19 m p) = True.
Proof. exact (TRANS (@lem1245052 m p) (@lem1245056)). Qed.
Lemma lem1245058 (m : nat) : (term23 m) = term18.
Proof. exact (fun_ext (fun p : nat => @lem1245057 m p)). Qed.
Lemma lem1245059 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1245060 (m : nat) : (term24 m) = term20.
Proof. exact (MK_COMB (@lem1245059) (@lem1245058 m)). Qed.
Lemma lem1245062 {A : Type'} (t : Prop) : (term21 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1245063 (t : Prop) : (term22 t) = t.
Proof. exact (@lem1245062 nat t). Qed.
Lemma lem1245064 : term20 = True.
Proof. exact (@lem1245063 True). Qed.
Lemma lem1245065 (m : nat) : (term24 m) = True.
Proof. exact (TRANS (@lem1245060 m) (@lem1245064)). Qed.
Lemma lem1245066 : term25 = term18.
Proof. exact (fun_ext (fun m : nat => @lem1245065 m)). Qed.
Lemma lem1245067 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1245068 : term26 = term20.
Proof. exact (MK_COMB (@lem1245067) (@lem1245066)). Qed.
Lemma lem1245070 {A : Type'} (t : Prop) : (term21 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1245071 (t : Prop) : (term22 t) = t.
Proof. exact (@lem1245070 nat t). Qed.
Lemma lem1245072 : term20 = True.
Proof. exact (@lem1245071 True). Qed.
Lemma lem1245073 : term26 = True.
Proof. exact (TRANS (@lem1245068) (@lem1245072)). Qed.
Lemma lem1245074 : True = term26.
Proof. exact (SYM (@lem1245073)). Qed.
Lemma lem1245075 : term26.
Proof. exact (EQ_MP (@lem1245074) (@lem0)). Qed.
