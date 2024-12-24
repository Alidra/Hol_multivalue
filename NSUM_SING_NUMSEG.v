Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_SING_NUMSEG_term_abbrevs.
Require Import NSUM_SING_spec.
Require Import NUMSEG_SING_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem7047064 (n : nat) : term0 n.
Proof. exact (@lem5374366 n). Qed.
Lemma lem7047065 (n : nat) : (term0 n) = ((dotdot n n) = (@INSERT nat n (@EMPTY nat))).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem7047067 {_127448 : Type'} (f : _127448 -> nat) : term1 _127448 f.
Proof. exact (@lem6960691 _127448 f). Qed.
Lemma lem7047068 {_127448 : Type'} (f : _127448 -> nat) : (term1 _127448 f) = (term2 _127448 f).
Proof. exact (eq_refl (term1 _127448 f)). Qed.
Lemma lem7047069 {_127448 : Type'} (f : _127448 -> nat) : term2 _127448 f.
Proof. exact (EQ_MP (@lem7047068 _127448 f) (@lem7047067 _127448 f)). Qed.
Lemma lem7047070 {_127448 : Type'} (f : _127448 -> nat) (x : _127448) : term3 _127448 f x.
Proof. exact (@lem7047069 _127448 f x). Qed.
Lemma lem7047071 {_127448 : Type'} (f : _127448 -> nat) (x : _127448) : (term3 _127448 f x) = ((term4 _127448 x f) = (f x)).
Proof. exact (eq_refl (term3 _127448 f x)). Qed.
Lemma lem7047084 (n : nat) : (dotdot n n) = (@INSERT nat n (@EMPTY nat)).
Proof. exact (EQ_MP (@lem7047065 n) (@lem7047064 n)). Qed.
Lemma lem7047085 : (@nsum nat) = (@nsum nat).
Proof. exact (eq_refl (@nsum nat)). Qed.
Lemma lem7047086 (n : nat) : (term5 n) = (term6 n).
Proof. exact (MK_COMB (@lem7047085) (@lem7047084 n)). Qed.
Lemma lem7047087 (f : nat -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7047088 (n : nat) (f : nat -> nat) : (term7 n f) = (term8 n f).
Proof. exact (MK_COMB (@lem7047086 n) (@lem7047087 f)). Qed.
Lemma lem7047090 {_127448 : Type'} (f : _127448 -> nat) (x : _127448) : (term4 _127448 x f) = (f x).
Proof. exact (EQ_MP (@lem7047071 _127448 f x) (@lem7047070 _127448 f x)). Qed.
Lemma lem7047091 (f : nat -> nat) (x : nat) : (term8 x f) = (f x).
Proof. exact (@lem7047090 nat f x). Qed.
Lemma lem7047092 (f : nat -> nat) (n : nat) : (term8 n f) = (f n).
Proof. exact (@lem7047091 f n). Qed.
Lemma lem7047093 (f : nat -> nat) (n : nat) : (term7 n f) = (f n).
Proof. exact (TRANS (@lem7047088 n f) (@lem7047092 f n)). Qed.
Lemma lem7047094 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7047095 (f : nat -> nat) (n : nat) : (term9 n f) = (term10 f n).
Proof. exact (MK_COMB (@lem7047094) (@lem7047093 f n)). Qed.
Lemma lem7047096 (f : nat -> nat) (n : nat) : (f n) = (f n).
Proof. exact (eq_refl (f n)). Qed.
Lemma lem7047097 (f : nat -> nat) (n : nat) : ((term7 n f) = (f n)) = ((f n) = (f n)).
Proof. exact (MK_COMB (@lem7047095 f n) (@lem7047096 f n)). Qed.
Lemma lem7047099 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7047100 (x : nat) : (x = x) = True.
Proof. exact (@lem7047099 nat x). Qed.
Lemma lem7047101 (f : nat -> nat) (n : nat) : ((f n) = (f n)) = True.
Proof. exact (@lem7047100 (f n)). Qed.
Lemma lem7047102 (f : nat -> nat) (n : nat) : ((term7 n f) = (f n)) = True.
Proof. exact (TRANS (@lem7047097 f n) (@lem7047101 f n)). Qed.
Lemma lem7047103 (f : nat -> nat) : (term11 f) = term12.
Proof. exact (fun_ext (fun n : nat => @lem7047102 f n)). Qed.
Lemma lem7047104 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7047105 (f : nat -> nat) : (term13 f) = term14.
Proof. exact (MK_COMB (@lem7047104) (@lem7047103 f)). Qed.
Lemma lem7047107 {A : Type'} (t : Prop) : (term15 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7047108 (t : Prop) : (term16 t) = t.
Proof. exact (@lem7047107 nat t). Qed.
Lemma lem7047109 : term14 = True.
Proof. exact (@lem7047108 True). Qed.
Lemma lem7047110 (f : nat -> nat) : (term13 f) = True.
Proof. exact (TRANS (@lem7047105 f) (@lem7047109)). Qed.
Lemma lem7047111 : term17 = term18.
Proof. exact (fun_ext (fun f : nat -> nat => @lem7047110 f)). Qed.
Lemma lem7047112 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7047113 : term19 = term20.
Proof. exact (MK_COMB (@lem7047112) (@lem7047111)). Qed.
Lemma lem7047115 {A : Type'} (t : Prop) : (term15 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7047116 (t : Prop) : (term21 t) = t.
Proof. exact (@lem7047115 (nat -> nat) t). Qed.
Lemma lem7047117 : term20 = True.
Proof. exact (@lem7047116 True). Qed.
Lemma lem7047118 : term19 = True.
Proof. exact (TRANS (@lem7047113) (@lem7047117)). Qed.
Lemma lem7047119 : True = term19.
Proof. exact (SYM (@lem7047118)). Qed.
Lemma lem7047120 : term19.
Proof. exact (EQ_MP (@lem7047119) (@lem0)). Qed.
