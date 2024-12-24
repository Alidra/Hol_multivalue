Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_RMUL_term_abbrevs.
Require Import MULT_SYM_spec.
Require Import NSUM_LMUL_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem6932067 {A : Type'} (f : A -> nat) : term0 A f.
Proof. exact (@lem6932066 A f). Qed.
Lemma lem6932068 {A : Type'} (f : A -> nat) : (term0 A f) = (term1 A f).
Proof. exact (eq_refl (term0 A f)). Qed.
Lemma lem6932069 {A : Type'} (f : A -> nat) : term1 A f.
Proof. exact (EQ_MP (@lem6932068 A f) (@lem6932067 A f)). Qed.
Lemma lem6932070 {A : Type'} (f : A -> nat) (c : nat) : term2 A f c.
Proof. exact (@lem6932069 A f c). Qed.
Lemma lem6932071 {A : Type'} (c : nat) (f : A -> nat) : (term2 A f c) = (term3 A c f).
Proof. exact (eq_refl (term2 A f c)). Qed.
Lemma lem6932072 {A : Type'} (c : nat) (f : A -> nat) : term3 A c f.
Proof. exact (EQ_MP (@lem6932071 A c f) (@lem6932070 A f c)). Qed.
Lemma lem6932073 {A : Type'} (c : nat) (f : A -> nat) (s : A -> Prop) : term4 A c f s.
Proof. exact (@lem6932072 A c f s). Qed.
Lemma lem6932074 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : (term4 A c f s) = ((term5 A s c f) = (term6 A c s f)).
Proof. exact (eq_refl (term4 A c f s)). Qed.
Lemma lem6932076 (m : nat) : term7 m.
Proof. exact (@lem81820 m). Qed.
Lemma lem6932077 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem6932078 (m : nat) : term8 m.
Proof. exact (EQ_MP (@lem6932077 m) (@lem6932076 m)). Qed.
Lemma lem6932079 (m : nat) (n : nat) : term9 m n.
Proof. exact (@lem6932078 m n). Qed.
Lemma lem6932080 (n : nat) (m : nat) : (term9 m n) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl (term9 m n)). Qed.
Lemma lem6932097 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem6932080 n m) (@lem6932079 m n)). Qed.
Lemma lem6932098 {A : Type'} (c : nat) (f : A -> nat) (x : A) : (term10 A f x c) = (term11 A c f x).
Proof. exact (@lem6932097 c (f x)). Qed.
Lemma lem6932099 {A : Type'} (c : nat) (f : A -> nat) : (term12 A f c) = (term13 A c f).
Proof. exact (fun_ext (fun x : A => @lem6932098 A c f x)). Qed.
Lemma lem6932100 {A : Type'} (s : A -> Prop) : (@nsum A s) = (@nsum A s).
Proof. exact (eq_refl (@nsum A s)). Qed.
Lemma lem6932101 {A : Type'} (s : A -> Prop) (c : nat) (f : A -> nat) : (term14 A s f c) = (term5 A s c f).
Proof. exact (MK_COMB (@lem6932100 A s) (@lem6932099 A c f)). Qed.
Lemma lem6932102 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6932103 {A : Type'} (s : A -> Prop) (c : nat) (f : A -> nat) : (term15 A s f c) = (term16 A s c f).
Proof. exact (MK_COMB (@lem6932102) (@lem6932101 A s c f)). Qed.
Lemma lem6932105 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem6932080 n m) (@lem6932079 m n)). Qed.
Lemma lem6932106 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : (term17 A s f c) = (term6 A c s f).
Proof. exact (@lem6932105 c (@nsum A s f)). Qed.
Lemma lem6932107 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : ((term14 A s f c) = (term17 A s f c)) = ((term5 A s c f) = (term6 A c s f)).
Proof. exact (MK_COMB (@lem6932103 A s c f) (@lem6932106 A c s f)). Qed.
Lemma lem6932108 {A : Type'} (c : nat) (f : A -> nat) : (term18 A f c) = (term19 A c f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6932107 A c s f)). Qed.
Lemma lem6932109 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6932110 {A : Type'} (c : nat) (f : A -> nat) : (term20 A f c) = (term3 A c f).
Proof. exact (MK_COMB (@lem6932109 A) (@lem6932108 A c f)). Qed.
Lemma lem6932111 {A : Type'} (f : A -> nat) : (term21 A f) = (term22 A f).
Proof. exact (fun_ext (fun c : nat => @lem6932110 A c f)). Qed.
Lemma lem6932112 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6932113 {A : Type'} (f : A -> nat) : (term23 A f) = (term1 A f).
Proof. exact (MK_COMB (@lem6932112) (@lem6932111 A f)). Qed.
Lemma lem6932114 {A : Type'} : (term24 A) = (term25 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem6932113 A f)). Qed.
Lemma lem6932115 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6932116 {A : Type'} : (term26 A) = (term27 A).
Proof. exact (MK_COMB (@lem6932115 A) (@lem6932114 A)). Qed.
Lemma lem6932117 {A : Type'} : (term27 A) = (term26 A).
Proof. exact (SYM (@lem6932116 A)). Qed.
Lemma lem6932133 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : (term5 A s c f) = (term6 A c s f).
Proof. exact (EQ_MP (@lem6932074 A c s f) (@lem6932073 A c f s)). Qed.
Lemma lem6932134 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : (term5 A s c f) = (term6 A c s f).
Proof. exact (@lem6932133 A c s f). Qed.
Lemma lem6932135 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6932136 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : (term16 A s c f) = (term28 A c s f).
Proof. exact (MK_COMB (@lem6932135) (@lem6932134 A c s f)). Qed.
Lemma lem6932137 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : (term6 A c s f) = (term6 A c s f).
Proof. exact (eq_refl (term6 A c s f)). Qed.
Lemma lem6932138 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : ((term5 A s c f) = (term6 A c s f)) = ((term6 A c s f) = (term6 A c s f)).
Proof. exact (MK_COMB (@lem6932136 A c s f) (@lem6932137 A c s f)). Qed.
Lemma lem6932140 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6932141 (x : nat) : (x = x) = True.
Proof. exact (@lem6932140 nat x). Qed.
Lemma lem6932142 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : ((term6 A c s f) = (term6 A c s f)) = True.
Proof. exact (@lem6932141 (term6 A c s f)). Qed.
Lemma lem6932143 {A : Type'} (c : nat) (s : A -> Prop) (f : A -> nat) : ((term5 A s c f) = (term6 A c s f)) = True.
Proof. exact (TRANS (@lem6932138 A c s f) (@lem6932142 A c s f)). Qed.
Lemma lem6932144 {A : Type'} (c : nat) (f : A -> nat) : (term19 A c f) = (term29 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6932143 A c s f)). Qed.
Lemma lem6932145 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6932146 {A : Type'} (c : nat) (f : A -> nat) : (term3 A c f) = (term30 A).
Proof. exact (MK_COMB (@lem6932145 A) (@lem6932144 A c f)). Qed.
Lemma lem6932148 {A : Type'} (t : Prop) : (term31 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6932149 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (@lem6932148 (A -> Prop) t). Qed.
Lemma lem6932150 {A : Type'} : (term30 A) = True.
Proof. exact (@lem6932149 A True). Qed.
Lemma lem6932151 {A : Type'} (c : nat) (f : A -> nat) : (term3 A c f) = True.
Proof. exact (TRANS (@lem6932146 A c f) (@lem6932150 A)). Qed.
Lemma lem6932152 {A : Type'} (f : A -> nat) : (term22 A f) = term33.
Proof. exact (fun_ext (fun c : nat => @lem6932151 A c f)). Qed.
Lemma lem6932153 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6932154 {A : Type'} (f : A -> nat) : (term1 A f) = term34.
Proof. exact (MK_COMB (@lem6932153) (@lem6932152 A f)). Qed.
Lemma lem6932156 {A : Type'} (t : Prop) : (term31 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6932157 (t : Prop) : (term35 t) = t.
Proof. exact (@lem6932156 nat t). Qed.
Lemma lem6932158 : term34 = True.
Proof. exact (@lem6932157 True). Qed.
Lemma lem6932159 {A : Type'} (f : A -> nat) : (term1 A f) = True.
Proof. exact (TRANS (@lem6932154 A f) (@lem6932158)). Qed.
Lemma lem6932160 {A : Type'} : (term25 A) = (term36 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem6932159 A f)). Qed.
Lemma lem6932161 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6932162 {A : Type'} : (term27 A) = (term37 A).
Proof. exact (MK_COMB (@lem6932161 A) (@lem6932160 A)). Qed.
Lemma lem6932164 {A : Type'} (t : Prop) : (term31 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6932165 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (@lem6932164 (A -> nat) t). Qed.
Lemma lem6932166 {A : Type'} : (term37 A) = True.
Proof. exact (@lem6932165 A True). Qed.
Lemma lem6932167 {A : Type'} : (term27 A) = True.
Proof. exact (TRANS (@lem6932162 A) (@lem6932166 A)). Qed.
Lemma lem6932168 {A : Type'} : True = (term27 A).
Proof. exact (SYM (@lem6932167 A)). Qed.
Lemma lem6932169 {A : Type'} : term27 A.
Proof. exact (EQ_MP (@lem6932168 A) (@lem0)). Qed.
Lemma lem6932170 {A : Type'} : term26 A.
Proof. exact (EQ_MP (@lem6932117 A) (@lem6932169 A)). Qed.
