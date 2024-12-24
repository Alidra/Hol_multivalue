Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INJP_INJ_term_abbrevs.
Require Import AND_FORALL_THM_spec.
Require Import ETA_AX_spec.
Require Import FUN_EQ_THM_spec.
Require Import INJP_spec.
Require Import thm0_spec.
Require Import thm1055112_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm32_spec.
Require Import thm4211_spec.
Lemma lem1056994 {A : Type'} (f1 : type1597 A) : term0 A f1.
Proof. exact (@lem1056993 A f1). Qed.
Lemma lem1056995 {A : Type'} (f1 : type1597 A) : (term0 A f1) = (term1 A f1).
Proof. exact (eq_refl (term0 A f1)). Qed.
Lemma lem1056996 {A : Type'} (f1 : type1597 A) : term1 A f1.
Proof. exact (EQ_MP (@lem1056995 A f1) (@lem1056994 A f1)). Qed.
Lemma lem1056997 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) : term2 A f1 f2.
Proof. exact (@lem1056996 A f1 f2). Qed.
Lemma lem1056998 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) : (term2 A f1 f2) = ((@INJP A f1 f2) = (term3 A f1 f2)).
Proof. exact (eq_refl (term2 A f1 f2)). Qed.
Lemma lem1057000 {A : Type'} (P : A -> Prop) : term4 A P.
Proof. exact (@lem5146 A P). Qed.
Lemma lem1057001 {A : Type'} (P : A -> Prop) : (term4 A P) = (term5 A P).
Proof. exact (eq_refl (term4 A P)). Qed.
Lemma lem1057002 {A : Type'} (P : A -> Prop) : term5 A P.
Proof. exact (EQ_MP (@lem1057001 A P) (@lem1057000 A P)). Qed.
Lemma lem1057003 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term6 A P Q.
Proof. exact (@lem1057002 A P Q). Qed.
Lemma lem1057004 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term6 A P Q) = ((term7 A P Q) = (term8 A P Q)).
Proof. exact (eq_refl (term6 A P Q)). Qed.
Lemma lem1057006 {A B : Type'} (f : A -> B) : term9 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem1057007 {A B : Type'} (f : A -> B) : (term9 A B f) = (term10 A B f).
Proof. exact (eq_refl (term9 A B f)). Qed.
Lemma lem1057008 {A B : Type'} (f : A -> B) : term10 A B f.
Proof. exact (EQ_MP (@lem1057007 A B f) (@lem1057006 A B f)). Qed.
Lemma lem1057009 {A B : Type'} (f : A -> B) (g : A -> B) : term11 A B f g.
Proof. exact (@lem1057008 A B f g). Qed.
Lemma lem1057010 {A B : Type'} (f : A -> B) (g : A -> B) : (term11 A B f g) = ((f = g) = (term12 A B f g)).
Proof. exact (eq_refl (term11 A B f g)). Qed.
Lemma lem1057012 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (f1' : type1597 A) (f2' : type1597 A) (h1 : (@INJP A f1 f2) = (@INJP A f1' f2')) : (@INJP A f1 f2) = (@INJP A f1' f2').
Proof. exact (h1). Qed.
Lemma lem1057013 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (h1 : term13 A f1 f1' f2 f2') : term13 A f1 f1' f2 f2'.
Proof. exact (h1). Qed.
Lemma lem1057027 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (h1 : term13 A f1 f1' f2 f2') : f1 = f1'.
Proof. exact (proj1 (@lem1057013 A f1 f1' f2 f2' h1)). Qed.
Lemma lem1057028 {A : Type'} : (@INJP A) = (@INJP A).
Proof. exact (eq_refl (@INJP A)). Qed.
Lemma lem1057029 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (h1 : term13 A f1 f1' f2 f2') : (@INJP A f1) = (@INJP A f1').
Proof. exact (MK_COMB (@lem1057028 A) (@lem1057027 A f1 f1' f2 f2' h1)). Qed.
Lemma lem1057031 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (h1 : term13 A f1 f1' f2 f2') : f2 = f2'.
Proof. exact (proj2 (@lem1057013 A f1 f1' f2 f2' h1)). Qed.
Lemma lem1057032 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (h1 : term13 A f1 f1' f2 f2') : (@INJP A f1 f2) = (@INJP A f1' f2').
Proof. exact (MK_COMB (@lem1057029 A f1 f1' f2 f2' h1) (@lem1057031 A f1 f1' f2 f2' h1)). Qed.
Lemma lem1057033 {A : Type'} : (@eq (nat -> A -> Prop)) = (@eq (nat -> A -> Prop)).
Proof. exact (eq_refl (@eq (nat -> A -> Prop))). Qed.
Lemma lem1057034 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (h1 : term13 A f1 f1' f2 f2') : (term14 A f1 f2) = (term14 A f1' f2').
Proof. exact (MK_COMB (@lem1057033 A) (@lem1057032 A f1 f1' f2 f2' h1)). Qed.
Lemma lem1057035 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) : (@INJP A f1' f2') = (@INJP A f1' f2').
Proof. exact (eq_refl (@INJP A f1' f2')). Qed.
Lemma lem1057036 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (h1 : term13 A f1 f1' f2 f2') : ((@INJP A f1 f2) = (@INJP A f1' f2')) = ((@INJP A f1' f2') = (@INJP A f1' f2')).
Proof. exact (MK_COMB (@lem1057034 A f1 f1' f2 f2' h1) (@lem1057035 A f1' f2')). Qed.
Lemma lem1057038 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1057039 {A : Type'} (x : type1597 A) : (x = x) = True.
Proof. exact (@lem1057038 (type1597 A) x). Qed.
Lemma lem1057040 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) : ((@INJP A f1' f2') = (@INJP A f1' f2')) = True.
Proof. exact (@lem1057039 A (@INJP A f1' f2')). Qed.
Lemma lem1057041 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (h1 : term13 A f1 f1' f2 f2') : ((@INJP A f1 f2) = (@INJP A f1' f2')) = True.
Proof. exact (TRANS (@lem1057036 A f1 f1' f2 f2' h1) (@lem1057040 A f1' f2')). Qed.
Lemma lem1057042 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (h1 : term13 A f1 f1' f2 f2') : True = ((@INJP A f1 f2) = (@INJP A f1' f2')).
Proof. exact (SYM (@lem1057041 A f1 f1' f2 f2' h1)). Qed.
Lemma lem1057043 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (h1 : term13 A f1 f1' f2 f2') : (@INJP A f1 f2) = (@INJP A f1' f2').
Proof. exact (EQ_MP (@lem1057042 A f1 f1' f2 f2' h1) (@lem0)). Qed.
Lemma lem1057049 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term12 A B f g).
Proof. exact (EQ_MP (@lem1057010 A B f g) (@lem1057009 A B f g)). Qed.
Lemma lem1057050 {A : Type'} (f : type1597 A) (g : type1597 A) : (f = g) = (term15 A f g).
Proof. exact (@lem1057049 nat (A -> Prop) f g). Qed.
Lemma lem1057051 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) : (f1 = f1') = (term15 A f1 f1').
Proof. exact (@lem1057050 A f1 f1'). Qed.
Lemma lem1057052 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1057053 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) : (term16 A f1 f1') = (term17 A f1 f1').
Proof. exact (MK_COMB (@lem1057052) (@lem1057051 A f1 f1')). Qed.
Lemma lem1057057 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term12 A B f g).
Proof. exact (EQ_MP (@lem1057010 A B f g) (@lem1057009 A B f g)). Qed.
Lemma lem1057058 {A : Type'} (f : type1597 A) (g : type1597 A) : (f = g) = (term15 A f g).
Proof. exact (@lem1057057 nat (A -> Prop) f g). Qed.
Lemma lem1057059 {A : Type'} (f2 : type1597 A) (f2' : type1597 A) : (f2 = f2') = (term15 A f2 f2').
Proof. exact (@lem1057058 A f2 f2'). Qed.
Lemma lem1057060 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) : (term13 A f1 f1' f2 f2') = (term18 A f1 f1' f2 f2').
Proof. exact (MK_COMB (@lem1057053 A f1 f1') (@lem1057059 A f2 f2')). Qed.
Lemma lem1057061 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) : (term18 A f1 f1' f2 f2') = (term13 A f1 f1' f2 f2').
Proof. exact (SYM (@lem1057060 A f1 f1' f2 f2')). Qed.
Lemma lem1057063 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term7 A P Q) = (term8 A P Q).
Proof. exact (EQ_MP (@lem1057004 A P Q) (@lem1057003 A P Q)). Qed.
Lemma lem1057064 (P : nat -> Prop) (Q : nat -> Prop) : (term19 P Q) = (term20 P Q).
Proof. exact (@lem1057063 nat P Q). Qed.
Lemma lem1057065 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) : (term21 A f1 f1' f2 f2') = (term22 A f1 f1' f2 f2').
Proof. exact (@lem1057064 (term23 A f1 f1') (term23 A f2 f2')). Qed.
Lemma lem1057066 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (x : nat) : (term24 A f1 f1' x) = ((f1 x) = (f1' x)).
Proof. exact (eq_refl (term24 A f1 f1' x)). Qed.
Lemma lem1057067 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) : (term25 A f1 f1') = (term23 A f1 f1').
Proof. exact (fun_ext (fun x : nat => @lem1057066 A f1 f1' x)). Qed.
Lemma lem1057068 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1057069 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) : (term26 A f1 f1') = (term15 A f1 f1').
Proof. exact (MK_COMB (@lem1057068) (@lem1057067 A f1 f1')). Qed.
Lemma lem1057070 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1057071 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) : (term27 A f1 f1') = (term17 A f1 f1').
Proof. exact (MK_COMB (@lem1057070) (@lem1057069 A f1 f1')). Qed.
Lemma lem1057072 {A : Type'} (f2 : type1597 A) (f2' : type1597 A) (x : nat) : (term24 A f2 f2' x) = ((f2 x) = (f2' x)).
Proof. exact (eq_refl (term24 A f2 f2' x)). Qed.
Lemma lem1057073 {A : Type'} (f2 : type1597 A) (f2' : type1597 A) : (term25 A f2 f2') = (term23 A f2 f2').
Proof. exact (fun_ext (fun x : nat => @lem1057072 A f2 f2' x)). Qed.
Lemma lem1057074 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1057075 {A : Type'} (f2 : type1597 A) (f2' : type1597 A) : (term26 A f2 f2') = (term15 A f2 f2').
Proof. exact (MK_COMB (@lem1057074) (@lem1057073 A f2 f2')). Qed.
Lemma lem1057076 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) : (term21 A f1 f1' f2 f2') = (term18 A f1 f1' f2 f2').
Proof. exact (MK_COMB (@lem1057071 A f1 f1') (@lem1057075 A f2 f2')). Qed.
Lemma lem1057077 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1057078 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) : (term28 A f1 f1' f2 f2') = (term29 A f1 f1' f2 f2').
Proof. exact (MK_COMB (@lem1057077) (@lem1057076 A f1 f1' f2 f2')). Qed.
Lemma lem1057079 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (x : nat) : (term24 A f1 f1' x) = ((f1 x) = (f1' x)).
Proof. exact (eq_refl (term24 A f1 f1' x)). Qed.
Lemma lem1057080 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1057081 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (x : nat) : (term30 A f1 f1' x) = (term31 A f1 f1' x).
Proof. exact (MK_COMB (@lem1057080) (@lem1057079 A f1 f1' x)). Qed.
Lemma lem1057082 {A : Type'} (f2 : type1597 A) (f2' : type1597 A) (x : nat) : (term24 A f2 f2' x) = ((f2 x) = (f2' x)).
Proof. exact (eq_refl (term24 A f2 f2' x)). Qed.
Lemma lem1057083 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (x : nat) : (term32 A f1 f1' f2 f2' x) = (term33 A f1 f1' f2 f2' x).
Proof. exact (MK_COMB (@lem1057081 A f1 f1' x) (@lem1057082 A f2 f2' x)). Qed.
Lemma lem1057084 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) : (term34 A f1 f1' f2 f2') = (term35 A f1 f1' f2 f2').
Proof. exact (fun_ext (fun x : nat => @lem1057083 A f1 f1' f2 f2' x)). Qed.
Lemma lem1057085 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1057086 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) : (term22 A f1 f1' f2 f2') = (term36 A f1 f1' f2 f2').
Proof. exact (MK_COMB (@lem1057085) (@lem1057084 A f1 f1' f2 f2')). Qed.
Lemma lem1057087 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) : ((term21 A f1 f1' f2 f2') = (term22 A f1 f1' f2 f2')) = ((term18 A f1 f1' f2 f2') = (term36 A f1 f1' f2 f2')).
Proof. exact (MK_COMB (@lem1057078 A f1 f1' f2 f2') (@lem1057086 A f1 f1' f2 f2')). Qed.
Lemma lem1057088 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) : (term18 A f1 f1' f2 f2') = (term36 A f1 f1' f2 f2').
Proof. exact (EQ_MP (@lem1057087 A f1 f1' f2 f2') (@lem1057065 A f1 f1' f2 f2')). Qed.
Lemma lem1057099 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) : (term36 A f1 f1' f2 f2') = (term18 A f1 f1' f2 f2').
Proof. exact (SYM (@lem1057088 A f1 f1' f2 f2')). Qed.
Lemma lem1057103 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) : (@INJP A f1 f2) = (term3 A f1 f2).
Proof. exact (EQ_MP (@lem1056998 A f1 f2) (@lem1056997 A f1 f2)). Qed.
Lemma lem1057104 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) : (@INJP A f1 f2) = (term3 A f1 f2).
Proof. exact (@lem1057103 A f1 f2). Qed.
Lemma lem1057105 {A : Type'} : (@eq (nat -> A -> Prop)) = (@eq (nat -> A -> Prop)).
Proof. exact (eq_refl (@eq (nat -> A -> Prop))). Qed.
Lemma lem1057106 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) : (term14 A f1 f2) = (term37 A f1 f2).
Proof. exact (MK_COMB (@lem1057105 A) (@lem1057104 A f1 f2)). Qed.
Lemma lem1057108 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) : (@INJP A f1 f2) = (term3 A f1 f2).
Proof. exact (EQ_MP (@lem1056998 A f1 f2) (@lem1056997 A f1 f2)). Qed.
Lemma lem1057109 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) : (@INJP A f1 f2) = (term3 A f1 f2).
Proof. exact (@lem1057108 A f1 f2). Qed.
Lemma lem1057110 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) : (@INJP A f1' f2') = (term3 A f1' f2').
Proof. exact (@lem1057109 A f1' f2'). Qed.
Lemma lem1057111 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (f1' : type1597 A) (f2' : type1597 A) : ((@INJP A f1 f2) = (@INJP A f1' f2')) = ((term3 A f1 f2) = (term3 A f1' f2')).
Proof. exact (MK_COMB (@lem1057106 A f1 f2) (@lem1057110 A f1' f2')). Qed.
Lemma lem1057114 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (f1' : type1597 A) (f2' : type1597 A) (h1 : (@INJP A f1 f2) = (@INJP A f1' f2')) : (term3 A f1 f2) = (term3 A f1' f2').
Proof. exact (EQ_MP (@lem1057111 A f1 f2 f1' f2') (@lem1057012 A f1 f2 f1' f2' h1)). Qed.
Lemma lem1057115 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (f1' : type1597 A) (f2' : type1597 A) (h1 : (term3 A f1 f2) = (term3 A f1' f2')) : (term3 A f1 f2) = (term3 A f1' f2').
Proof. exact (h1). Qed.
Lemma lem1057116 (b : Prop) (n : nat) : (NUMSUM b n) = (NUMSUM b n).
Proof. exact (eq_refl (NUMSUM b n)). Qed.
Lemma lem1057117 {A : Type'} (b : Prop) (n : nat) (f1 : type1597 A) (f2 : type1597 A) (f1' : type1597 A) (f2' : type1597 A) (h1 : (term3 A f1 f2) = (term3 A f1' f2')) : (term38 A f1 f2 b n) = (term38 A f1' f2' b n).
Proof. exact (MK_COMB (@lem1057115 A f1 f2 f1' f2' h1) (@lem1057116 b n)). Qed.
Lemma lem1057118 {A : Type'} (n : nat) (f1 : type1597 A) (f2 : type1597 A) (f1' : type1597 A) (f2' : type1597 A) (h1 : (term3 A f1 f2) = (term3 A f1' f2')) : term39 A f1 f2 f1' f2' n.
Proof. exact (fun b : Prop => @lem1057117 A b n f1 f2 f1' f2' h1). Qed.
Lemma lem1057119 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (f1' : type1597 A) (f2' : type1597 A) (n : nat) (h1 : term39 A f1 f2 f1' f2' n) : term39 A f1 f2 f1' f2' n.
Proof. exact (h1). Qed.
Lemma lem1057120 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (f1' : type1597 A) (f2' : type1597 A) (n : nat) (h1 : term39 A f1 f2 f1' f2' n) : term40 A f1 f2 f1' f2' n.
Proof. exact (@lem1057119 A f1 f2 f1' f2' n h1 False). Qed.
Lemma lem1057121 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (f1' : type1597 A) (f2' : type1597 A) (n : nat) : (term40 A f1 f2 f1' f2' n) = ((term41 A f1 f2 n) = (term41 A f1' f2' n)).
Proof. exact (eq_refl (term40 A f1 f2 f1' f2' n)). Qed.
Lemma lem1057122 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (f1' : type1597 A) (f2' : type1597 A) (n : nat) (h1 : term39 A f1 f2 f1' f2' n) : (term41 A f1 f2 n) = (term41 A f1' f2' n).
Proof. exact (EQ_MP (@lem1057121 A f1 f2 f1' f2' n) (@lem1057120 A f1 f2 f1' f2' n h1)). Qed.
Lemma lem1057123 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (f1' : type1597 A) (f2' : type1597 A) (n : nat) (h1 : term39 A f1 f2 f1' f2' n) : term42 A f1 f2 f1' f2' n.
Proof. exact (@lem1057119 A f1 f2 f1' f2' n h1 True). Qed.
Lemma lem1057124 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (f1' : type1597 A) (f2' : type1597 A) (n : nat) : (term42 A f1 f2 f1' f2' n) = ((term43 A f1 f2 n) = (term43 A f1' f2' n)).
Proof. exact (eq_refl (term42 A f1 f2 f1' f2' n)). Qed.
Lemma lem1057125 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (f1' : type1597 A) (f2' : type1597 A) (n : nat) (h1 : term39 A f1 f2 f1' f2' n) : (term43 A f1 f2 n) = (term43 A f1' f2' n).
Proof. exact (EQ_MP (@lem1057124 A f1 f2 f1' f2' n) (@lem1057123 A f1 f2 f1' f2' n h1)). Qed.
Lemma lem1057126 {A B : Type'} (t : A -> B) : term44 A B t.
Proof. exact (@lem9121 A B t). Qed.
Lemma lem1057127 {A B : Type'} (t : A -> B) : (term44 A B t) = ((term45 A B t) = t).
Proof. exact (eq_refl (term44 A B t)). Qed.
Lemma lem1057128 {A B : Type'} (t : A -> B) : (term45 A B t) = t.
Proof. exact (EQ_MP (@lem1057127 A B t) (@lem1057126 A B t)). Qed.
Lemma lem1057129 (x : Prop) : term46 x.
Proof. exact (@lem1055112 x). Qed.
Lemma lem1057130 (x : Prop) : (term46 x) = (term47 x).
Proof. exact (eq_refl (term46 x)). Qed.
Lemma lem1057131 (x : Prop) : term47 x.
Proof. exact (EQ_MP (@lem1057130 x) (@lem1057129 x)). Qed.
Lemma lem1057132 (x : Prop) (y : nat) : term48 x y.
Proof. exact (@lem1057131 x y). Qed.
Lemma lem1057133 (x : Prop) (y : nat) : (term48 x y) = (term49 x y).
Proof. exact (eq_refl (term48 x y)). Qed.
Lemma lem1057134 (x : Prop) (y : nat) : term49 x y.
Proof. exact (EQ_MP (@lem1057133 x y) (@lem1057132 x y)). Qed.
Lemma lem1057142 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term50 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1057143 (p : Prop) (q : Prop) (p' : Prop) : term51 p q p'.
Proof. exact (fun q' : Prop => @lem1057142 p q p' q'). Qed.
Lemma lem1057144 (p : Prop) (q : Prop) : term52 p q.
Proof. exact (fun p' : Prop => @lem1057143 p q p'). Qed.
Lemma lem1057145 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (n : nat) : term53 A f1 f1' f2 f2' n.
Proof. exact (@lem1057144 ((term41 A f1 f2 n) = (term41 A f1' f2' n)) (term54 A f1 f1' f2 f2' n)). Qed.
Lemma lem1057146 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (n : nat) (p' : Prop) : term55 A f1 f1' f2 f2' n p'.
Proof. exact (@lem1057145 A f1 f1' f2 f2' n p'). Qed.
Lemma lem1057147 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (n : nat) (p' : Prop) : (term55 A f1 f1' f2 f2' n p') = (term56 A f1 f1' f2 f2' n p').
Proof. exact (eq_refl (term55 A f1 f1' f2 f2' n p')). Qed.
Lemma lem1057148 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (n : nat) (p' : Prop) : term56 A f1 f1' f2 f2' n p'.
Proof. exact (EQ_MP (@lem1057147 A f1 f1' f2 f2' n p') (@lem1057146 A f1 f1' f2 f2' n p')). Qed.
Lemma lem1057149 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (n : nat) (p' : Prop) (q' : Prop) : term57 A f1 f1' f2 f2' n p' q'.
Proof. exact (@lem1057148 A f1 f1' f2 f2' n p' q'). Qed.
Lemma lem1057150 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (n : nat) (p' : Prop) (q' : Prop) : (term57 A f1 f1' f2 f2' n p' q') = (term58 A f1 f1' f2 f2' n p' q').
Proof. exact (eq_refl (term57 A f1 f1' f2 f2' n p' q')). Qed.
Lemma lem1057151 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (n : nat) (p' : Prop) (q' : Prop) : term58 A f1 f1' f2 f2' n p' q'.
Proof. exact (EQ_MP (@lem1057150 A f1 f1' f2 f2' n p' q') (@lem1057149 A f1 f1' f2 f2' n p' q')). Qed.
Lemma lem1057155 {A B : Type'} (f : A -> B) (y : A) : (term59 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1057156 {A : Type'} (f : type1597 A) (y : nat) : (term60 A f y) = (f y).
Proof. exact (@lem1057155 nat (A -> Prop) f y). Qed.
Lemma lem1057157 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) : (term61 A f1 f2 n) = (term41 A f1 f2 n).
Proof. exact (@lem1057156 A (term3 A f1 f2) (NUMSUM False n)). Qed.
Lemma lem1057158 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) : (term62 A f1 f2 n) = (term63 A f1 f2 n).
Proof. exact (eq_refl (term62 A f1 f2 n)). Qed.
Lemma lem1057159 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) : (term64 A f1 f2) = (term3 A f1 f2).
Proof. exact (fun_ext (fun n : nat => @lem1057158 A f1 f2 n)). Qed.
Lemma lem1057160 (n : nat) : (NUMSUM False n) = (NUMSUM False n).
Proof. exact (eq_refl (NUMSUM False n)). Qed.
Lemma lem1057161 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) : (term61 A f1 f2 n) = (term41 A f1 f2 n).
Proof. exact (MK_COMB (@lem1057159 A f1 f2) (@lem1057160 n)). Qed.
Lemma lem1057162 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem1057163 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) : (term65 A f1 f2 n) = (term66 A f1 f2 n).
Proof. exact (MK_COMB (@lem1057162 A) (@lem1057161 A f1 f2 n)). Qed.
Lemma lem1057164 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) : (term41 A f1 f2 n) = (term67 A f1 f2 n).
Proof. exact (eq_refl (term41 A f1 f2 n)). Qed.
Lemma lem1057165 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) : ((term61 A f1 f2 n) = (term41 A f1 f2 n)) = ((term41 A f1 f2 n) = (term67 A f1 f2 n)).
Proof. exact (MK_COMB (@lem1057163 A f1 f2 n) (@lem1057164 A f1 f2 n)). Qed.
Lemma lem1057166 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) : (term41 A f1 f2 n) = (term67 A f1 f2 n).
Proof. exact (EQ_MP (@lem1057165 A f1 f2 n) (@lem1057157 A f1 f2 n)). Qed.
Lemma lem1057168 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term68 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem1057169 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term69 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem1057168 _2963 g t e g' t' e'). Qed.
Lemma lem1057170 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term70 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem1057169 _2963 g t e g' t'). Qed.
Lemma lem1057171 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term71 _2963 g t e.
Proof. exact (fun g' : Prop => @lem1057170 _2963 g t e g'). Qed.
Lemma lem1057172 (g : Prop) (t : Prop) (e : Prop) : term72 g t e.
Proof. exact (@lem1057171 Prop g t e). Qed.
Lemma lem1057173 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) (a : A) : term73 A f1 f2 n a.
Proof. exact (@lem1057172 (term74 n) (term75 A f1 n a) (term75 A f2 n a)). Qed.
Lemma lem1057174 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) (a : A) (g' : Prop) : term76 A f1 f2 n a g'.
Proof. exact (@lem1057173 A f1 f2 n a g'). Qed.
Lemma lem1057175 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) (a : A) (g' : Prop) : (term76 A f1 f2 n a g') = (term77 A f1 f2 n a g').
Proof. exact (eq_refl (term76 A f1 f2 n a g')). Qed.
Lemma lem1057176 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) (a : A) (g' : Prop) : term77 A f1 f2 n a g'.
Proof. exact (EQ_MP (@lem1057175 A f1 f2 n a g') (@lem1057174 A f1 f2 n a g')). Qed.
Lemma lem1057177 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) (a : A) (g' : Prop) (t' : Prop) : term78 A f1 f2 n a g' t'.
Proof. exact (@lem1057176 A f1 f2 n a g' t'). Qed.
Lemma lem1057178 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) (a : A) (g' : Prop) (t' : Prop) : (term78 A f1 f2 n a g' t') = (term79 A f1 f2 n a g' t').
Proof. exact (eq_refl (term78 A f1 f2 n a g' t')). Qed.
Lemma lem1057179 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) (a : A) (g' : Prop) (t' : Prop) : term79 A f1 f2 n a g' t'.
Proof. exact (EQ_MP (@lem1057178 A f1 f2 n a g' t') (@lem1057177 A f1 f2 n a g' t')). Qed.
Lemma lem1057180 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) (a : A) (g' : Prop) (t' : Prop) (e' : Prop) : term80 A f1 f2 n a g' t' e'.
Proof. exact (@lem1057179 A f1 f2 n a g' t' e'). Qed.
Lemma lem1057181 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) (a : A) (g' : Prop) (t' : Prop) (e' : Prop) : (term80 A f1 f2 n a g' t' e') = (term81 A f1 f2 n a g' t' e').
Proof. exact (eq_refl (term80 A f1 f2 n a g' t' e')). Qed.
Lemma lem1057182 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) (a : A) (g' : Prop) (t' : Prop) (e' : Prop) : term81 A f1 f2 n a g' t' e'.
Proof. exact (EQ_MP (@lem1057181 A f1 f2 n a g' t' e') (@lem1057180 A f1 f2 n a g' t' e')). Qed.
Lemma lem1057184 (y : nat) (x : Prop) : (term82 x y) = x.
Proof. exact (proj1 (@lem1057134 x y)). Qed.
Lemma lem1057185 (n : nat) : (term74 n) = False.
Proof. exact (@lem1057184 n False). Qed.
Lemma lem1057186 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) (a : A) (t' : Prop) (e' : Prop) : term83 A f1 f2 n a t' e'.
Proof. exact (@lem1057182 A f1 f2 n a False t' e'). Qed.
Lemma lem1057187 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) (a : A) (t' : Prop) (e' : Prop) : term84 A f1 f2 n a t' e'.
Proof. exact (@lem1057186 A f1 f2 n a t' e' (@lem1057185 n)). Qed.
Lemma lem1057192 (x : Prop) (y : nat) : (term85 x y) = y.
Proof. exact (proj2 (@lem1057134 x y)). Qed.
Lemma lem1057193 (n : nat) : (term86 n) = n.
Proof. exact (@lem1057192 False n). Qed.
Lemma lem1057194 {A : Type'} (f1 : type1597 A) : f1 = f1.
Proof. exact (eq_refl f1). Qed.
Lemma lem1057195 {A : Type'} (f1 : type1597 A) (n : nat) : (term87 A f1 n) = (f1 n).
Proof. exact (MK_COMB (@lem1057194 A f1) (@lem1057193 n)). Qed.
Lemma lem1057196 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1057197 {A : Type'} (f1 : type1597 A) (n : nat) (a : A) : (term75 A f1 n a) = (f1 n a).
Proof. exact (MK_COMB (@lem1057195 A f1 n) (@lem1057196 A a)). Qed.
Lemma lem1057198 {A : Type'} (f1 : type1597 A) (n : nat) (a : A) : term88 A f1 n a.
Proof. exact (fun h0 : False => @lem1057197 A f1 n a). Qed.
Lemma lem1057199 {A : Type'} (f2 : type1597 A) (f1 : type1597 A) (n : nat) (a : A) (e' : Prop) : term89 A f2 f1 n a e'.
Proof. exact (@lem1057187 A f1 f2 n a (f1 n a) e'). Qed.
Lemma lem1057200 {A : Type'} (f2 : type1597 A) (f1 : type1597 A) (n : nat) (a : A) (e' : Prop) : term90 A f2 f1 n a e'.
Proof. exact (@lem1057199 A f2 f1 n a e' (@lem1057198 A f1 n a)). Qed.
Lemma lem1057207 (x : Prop) (y : nat) : (term85 x y) = y.
Proof. exact (proj2 (@lem1057134 x y)). Qed.
Lemma lem1057208 (n : nat) : (term86 n) = n.
Proof. exact (@lem1057207 False n). Qed.
Lemma lem1057209 {A : Type'} (f2 : type1597 A) : f2 = f2.
Proof. exact (eq_refl f2). Qed.
Lemma lem1057210 {A : Type'} (f2 : type1597 A) (n : nat) : (term87 A f2 n) = (f2 n).
Proof. exact (MK_COMB (@lem1057209 A f2) (@lem1057208 n)). Qed.
Lemma lem1057211 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1057212 {A : Type'} (f2 : type1597 A) (n : nat) (a : A) : (term75 A f2 n a) = (f2 n a).
Proof. exact (MK_COMB (@lem1057210 A f2 n) (@lem1057211 A a)). Qed.
Lemma lem1057213 {A : Type'} (f2 : type1597 A) (n : nat) (a : A) : term91 A f2 n a.
Proof. exact (fun h0 : ~ False => @lem1057212 A f2 n a). Qed.
Lemma lem1057214 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) (a : A) : term92 A f1 f2 n a.
Proof. exact (@lem1057200 A f2 f1 n a (f2 n a)). Qed.
Lemma lem1057215 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) (a : A) : (term93 A f1 f2 n a) = (term94 A f1 f2 n a).
Proof. exact (@lem1057214 A f1 f2 n a (@lem1057213 A f2 n a)). Qed.
Lemma lem1057217 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1057218 (t1 : Prop) (t2 : Prop) : (@COND Prop False t1 t2) = t2.
Proof. exact (@lem1057217 Prop t1 t2). Qed.
Lemma lem1057219 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) (a : A) : (term94 A f1 f2 n a) = (f2 n a).
Proof. exact (@lem1057218 (f1 n a) (f2 n a)). Qed.
Lemma lem1057220 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) (a : A) : (term93 A f1 f2 n a) = (f2 n a).
Proof. exact (TRANS (@lem1057215 A f1 f2 n a) (@lem1057219 A f1 f2 n a)). Qed.
Lemma lem1057221 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) : (term67 A f1 f2 n) = (term95 A f2 n).
Proof. exact (fun_ext (fun a : A => @lem1057220 A f1 f2 n a)). Qed.
Lemma lem1057222 {A : Type'} (t : A -> Prop) : (term96 A t) = t.
Proof. exact (@lem1057128 A Prop t). Qed.
Lemma lem1057223 {A : Type'} (f2 : type1597 A) (n : nat) : (term95 A f2 n) = (f2 n).
Proof. exact (@lem1057222 A (f2 n)). Qed.
Lemma lem1057224 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) : (term67 A f1 f2 n) = (f2 n).
Proof. exact (TRANS (@lem1057221 A f1 f2 n) (@lem1057223 A f2 n)). Qed.
Lemma lem1057225 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) : (term41 A f1 f2 n) = (f2 n).
Proof. exact (TRANS (@lem1057166 A f1 f2 n) (@lem1057224 A f1 f2 n)). Qed.
Lemma lem1057226 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem1057227 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) : (term66 A f1 f2 n) = (term97 A f2 n).
Proof. exact (MK_COMB (@lem1057226 A) (@lem1057225 A f1 f2 n)). Qed.
Lemma lem1057229 {A B : Type'} (f : A -> B) (y : A) : (term59 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1057230 {A : Type'} (f : type1597 A) (y : nat) : (term60 A f y) = (f y).
Proof. exact (@lem1057229 nat (A -> Prop) f y). Qed.
Lemma lem1057231 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) : (term61 A f1' f2' n) = (term41 A f1' f2' n).
Proof. exact (@lem1057230 A (term3 A f1' f2') (NUMSUM False n)). Qed.
Lemma lem1057232 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) : (term62 A f1' f2' n) = (term63 A f1' f2' n).
Proof. exact (eq_refl (term62 A f1' f2' n)). Qed.
Lemma lem1057233 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) : (term64 A f1' f2') = (term3 A f1' f2').
Proof. exact (fun_ext (fun n : nat => @lem1057232 A f1' f2' n)). Qed.
Lemma lem1057234 (n : nat) : (NUMSUM False n) = (NUMSUM False n).
Proof. exact (eq_refl (NUMSUM False n)). Qed.
Lemma lem1057235 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) : (term61 A f1' f2' n) = (term41 A f1' f2' n).
Proof. exact (MK_COMB (@lem1057233 A f1' f2') (@lem1057234 n)). Qed.
Lemma lem1057236 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem1057237 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) : (term65 A f1' f2' n) = (term66 A f1' f2' n).
Proof. exact (MK_COMB (@lem1057236 A) (@lem1057235 A f1' f2' n)). Qed.
Lemma lem1057238 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) : (term41 A f1' f2' n) = (term67 A f1' f2' n).
Proof. exact (eq_refl (term41 A f1' f2' n)). Qed.
Lemma lem1057239 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) : ((term61 A f1' f2' n) = (term41 A f1' f2' n)) = ((term41 A f1' f2' n) = (term67 A f1' f2' n)).
Proof. exact (MK_COMB (@lem1057237 A f1' f2' n) (@lem1057238 A f1' f2' n)). Qed.
Lemma lem1057240 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) : (term41 A f1' f2' n) = (term67 A f1' f2' n).
Proof. exact (EQ_MP (@lem1057239 A f1' f2' n) (@lem1057231 A f1' f2' n)). Qed.
Lemma lem1057242 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term68 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem1057243 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term69 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem1057242 _2963 g t e g' t' e'). Qed.
Lemma lem1057244 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term70 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem1057243 _2963 g t e g' t'). Qed.
Lemma lem1057245 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term71 _2963 g t e.
Proof. exact (fun g' : Prop => @lem1057244 _2963 g t e g'). Qed.
Lemma lem1057246 (g : Prop) (t : Prop) (e : Prop) : term72 g t e.
Proof. exact (@lem1057245 Prop g t e). Qed.
Lemma lem1057247 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) (a : A) : term73 A f1' f2' n a.
Proof. exact (@lem1057246 (term74 n) (term75 A f1' n a) (term75 A f2' n a)). Qed.
Lemma lem1057248 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) (a : A) (g' : Prop) : term76 A f1' f2' n a g'.
Proof. exact (@lem1057247 A f1' f2' n a g'). Qed.
Lemma lem1057249 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) (a : A) (g' : Prop) : (term76 A f1' f2' n a g') = (term77 A f1' f2' n a g').
Proof. exact (eq_refl (term76 A f1' f2' n a g')). Qed.
Lemma lem1057250 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) (a : A) (g' : Prop) : term77 A f1' f2' n a g'.
Proof. exact (EQ_MP (@lem1057249 A f1' f2' n a g') (@lem1057248 A f1' f2' n a g')). Qed.
Lemma lem1057251 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) (a : A) (g' : Prop) (t' : Prop) : term78 A f1' f2' n a g' t'.
Proof. exact (@lem1057250 A f1' f2' n a g' t'). Qed.
Lemma lem1057252 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) (a : A) (g' : Prop) (t' : Prop) : (term78 A f1' f2' n a g' t') = (term79 A f1' f2' n a g' t').
Proof. exact (eq_refl (term78 A f1' f2' n a g' t')). Qed.
Lemma lem1057253 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) (a : A) (g' : Prop) (t' : Prop) : term79 A f1' f2' n a g' t'.
Proof. exact (EQ_MP (@lem1057252 A f1' f2' n a g' t') (@lem1057251 A f1' f2' n a g' t')). Qed.
Lemma lem1057254 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) (a : A) (g' : Prop) (t' : Prop) (e' : Prop) : term80 A f1' f2' n a g' t' e'.
Proof. exact (@lem1057253 A f1' f2' n a g' t' e'). Qed.
Lemma lem1057255 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) (a : A) (g' : Prop) (t' : Prop) (e' : Prop) : (term80 A f1' f2' n a g' t' e') = (term81 A f1' f2' n a g' t' e').
Proof. exact (eq_refl (term80 A f1' f2' n a g' t' e')). Qed.
Lemma lem1057256 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) (a : A) (g' : Prop) (t' : Prop) (e' : Prop) : term81 A f1' f2' n a g' t' e'.
Proof. exact (EQ_MP (@lem1057255 A f1' f2' n a g' t' e') (@lem1057254 A f1' f2' n a g' t' e')). Qed.
Lemma lem1057258 (y : nat) (x : Prop) : (term82 x y) = x.
Proof. exact (proj1 (@lem1057134 x y)). Qed.
Lemma lem1057259 (n : nat) : (term74 n) = False.
Proof. exact (@lem1057258 n False). Qed.
Lemma lem1057260 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) (a : A) (t' : Prop) (e' : Prop) : term83 A f1' f2' n a t' e'.
Proof. exact (@lem1057256 A f1' f2' n a False t' e'). Qed.
Lemma lem1057261 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) (a : A) (t' : Prop) (e' : Prop) : term84 A f1' f2' n a t' e'.
Proof. exact (@lem1057260 A f1' f2' n a t' e' (@lem1057259 n)). Qed.
Lemma lem1057266 (x : Prop) (y : nat) : (term85 x y) = y.
Proof. exact (proj2 (@lem1057134 x y)). Qed.
Lemma lem1057267 (n : nat) : (term86 n) = n.
Proof. exact (@lem1057266 False n). Qed.
Lemma lem1057268 {A : Type'} (f1' : type1597 A) : f1' = f1'.
Proof. exact (eq_refl f1'). Qed.
Lemma lem1057269 {A : Type'} (f1' : type1597 A) (n : nat) : (term87 A f1' n) = (f1' n).
Proof. exact (MK_COMB (@lem1057268 A f1') (@lem1057267 n)). Qed.
Lemma lem1057270 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1057271 {A : Type'} (f1' : type1597 A) (n : nat) (a : A) : (term75 A f1' n a) = (f1' n a).
Proof. exact (MK_COMB (@lem1057269 A f1' n) (@lem1057270 A a)). Qed.
Lemma lem1057272 {A : Type'} (f1' : type1597 A) (n : nat) (a : A) : term88 A f1' n a.
Proof. exact (fun h0 : False => @lem1057271 A f1' n a). Qed.
Lemma lem1057273 {A : Type'} (f2' : type1597 A) (f1' : type1597 A) (n : nat) (a : A) (e' : Prop) : term89 A f2' f1' n a e'.
Proof. exact (@lem1057261 A f1' f2' n a (f1' n a) e'). Qed.
Lemma lem1057274 {A : Type'} (f2' : type1597 A) (f1' : type1597 A) (n : nat) (a : A) (e' : Prop) : term90 A f2' f1' n a e'.
Proof. exact (@lem1057273 A f2' f1' n a e' (@lem1057272 A f1' n a)). Qed.
Lemma lem1057281 (x : Prop) (y : nat) : (term85 x y) = y.
Proof. exact (proj2 (@lem1057134 x y)). Qed.
Lemma lem1057282 (n : nat) : (term86 n) = n.
Proof. exact (@lem1057281 False n). Qed.
Lemma lem1057283 {A : Type'} (f2' : type1597 A) : f2' = f2'.
Proof. exact (eq_refl f2'). Qed.
Lemma lem1057284 {A : Type'} (f2' : type1597 A) (n : nat) : (term87 A f2' n) = (f2' n).
Proof. exact (MK_COMB (@lem1057283 A f2') (@lem1057282 n)). Qed.
Lemma lem1057285 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1057286 {A : Type'} (f2' : type1597 A) (n : nat) (a : A) : (term75 A f2' n a) = (f2' n a).
Proof. exact (MK_COMB (@lem1057284 A f2' n) (@lem1057285 A a)). Qed.
Lemma lem1057287 {A : Type'} (f2' : type1597 A) (n : nat) (a : A) : term91 A f2' n a.
Proof. exact (fun h0 : ~ False => @lem1057286 A f2' n a). Qed.
Lemma lem1057288 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) (a : A) : term92 A f1' f2' n a.
Proof. exact (@lem1057274 A f2' f1' n a (f2' n a)). Qed.
Lemma lem1057289 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) (a : A) : (term93 A f1' f2' n a) = (term94 A f1' f2' n a).
Proof. exact (@lem1057288 A f1' f2' n a (@lem1057287 A f2' n a)). Qed.
Lemma lem1057291 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1057292 (t1 : Prop) (t2 : Prop) : (@COND Prop False t1 t2) = t2.
Proof. exact (@lem1057291 Prop t1 t2). Qed.
Lemma lem1057293 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) (a : A) : (term94 A f1' f2' n a) = (f2' n a).
Proof. exact (@lem1057292 (f1' n a) (f2' n a)). Qed.
Lemma lem1057294 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) (a : A) : (term93 A f1' f2' n a) = (f2' n a).
Proof. exact (TRANS (@lem1057289 A f1' f2' n a) (@lem1057293 A f1' f2' n a)). Qed.
Lemma lem1057295 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) : (term67 A f1' f2' n) = (term95 A f2' n).
Proof. exact (fun_ext (fun a : A => @lem1057294 A f1' f2' n a)). Qed.
Lemma lem1057296 {A : Type'} (t : A -> Prop) : (term96 A t) = t.
Proof. exact (@lem1057128 A Prop t). Qed.
Lemma lem1057297 {A : Type'} (f2' : type1597 A) (n : nat) : (term95 A f2' n) = (f2' n).
Proof. exact (@lem1057296 A (f2' n)). Qed.
Lemma lem1057298 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) : (term67 A f1' f2' n) = (f2' n).
Proof. exact (TRANS (@lem1057295 A f1' f2' n) (@lem1057297 A f2' n)). Qed.
Lemma lem1057299 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) : (term41 A f1' f2' n) = (f2' n).
Proof. exact (TRANS (@lem1057240 A f1' f2' n) (@lem1057298 A f1' f2' n)). Qed.
Lemma lem1057300 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (n : nat) : ((term41 A f1 f2 n) = (term41 A f1' f2' n)) = ((f2 n) = (f2' n)).
Proof. exact (MK_COMB (@lem1057227 A f1 f2 n) (@lem1057299 A f1' f2' n)). Qed.
Lemma lem1057303 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (n : nat) (q' : Prop) : term98 A f1 f1' f2 f2' n q'.
Proof. exact (@lem1057151 A f1 f1' f2 f2' n ((f2 n) = (f2' n)) q'). Qed.
Lemma lem1057304 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (n : nat) (q' : Prop) : term99 A f1 f1' f2 f2' n q'.
Proof. exact (@lem1057303 A f1 f1' f2 f2' n q' (@lem1057300 A f1 f1' f2 f2' n)). Qed.
Lemma lem1057311 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term50 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1057312 (p : Prop) (q : Prop) (p' : Prop) : term51 p q p'.
Proof. exact (fun q' : Prop => @lem1057311 p q p' q'). Qed.
Lemma lem1057313 (p : Prop) (q : Prop) : term52 p q.
Proof. exact (fun p' : Prop => @lem1057312 p q p'). Qed.
Lemma lem1057314 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (n : nat) : term100 A f1 f1' f2 f2' n.
Proof. exact (@lem1057313 ((term43 A f1 f2 n) = (term43 A f1' f2' n)) (term33 A f1 f1' f2 f2' n)). Qed.
Lemma lem1057315 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (n : nat) (p' : Prop) : term101 A f1 f1' f2 f2' n p'.
Proof. exact (@lem1057314 A f1 f1' f2 f2' n p'). Qed.
Lemma lem1057316 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (n : nat) (p' : Prop) : (term101 A f1 f1' f2 f2' n p') = (term102 A f1 f1' f2 f2' n p').
Proof. exact (eq_refl (term101 A f1 f1' f2 f2' n p')). Qed.
Lemma lem1057317 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (n : nat) (p' : Prop) : term102 A f1 f1' f2 f2' n p'.
Proof. exact (EQ_MP (@lem1057316 A f1 f1' f2 f2' n p') (@lem1057315 A f1 f1' f2 f2' n p')). Qed.
Lemma lem1057318 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (n : nat) (p' : Prop) (q' : Prop) : term103 A f1 f1' f2 f2' n p' q'.
Proof. exact (@lem1057317 A f1 f1' f2 f2' n p' q'). Qed.
Lemma lem1057319 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (n : nat) (p' : Prop) (q' : Prop) : (term103 A f1 f1' f2 f2' n p' q') = (term104 A f1 f1' f2 f2' n p' q').
Proof. exact (eq_refl (term103 A f1 f1' f2 f2' n p' q')). Qed.
Lemma lem1057320 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (n : nat) (p' : Prop) (q' : Prop) : term104 A f1 f1' f2 f2' n p' q'.
Proof. exact (EQ_MP (@lem1057319 A f1 f1' f2 f2' n p' q') (@lem1057318 A f1 f1' f2 f2' n p' q')). Qed.
Lemma lem1057324 {A B : Type'} (f : A -> B) (y : A) : (term59 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1057325 {A : Type'} (f : type1597 A) (y : nat) : (term60 A f y) = (f y).
Proof. exact (@lem1057324 nat (A -> Prop) f y). Qed.
Lemma lem1057326 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) : (term105 A f1 f2 n) = (term43 A f1 f2 n).
Proof. exact (@lem1057325 A (term3 A f1 f2) (NUMSUM True n)). Qed.
Lemma lem1057327 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) : (term62 A f1 f2 n) = (term63 A f1 f2 n).
Proof. exact (eq_refl (term62 A f1 f2 n)). Qed.
Lemma lem1057328 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) : (term64 A f1 f2) = (term3 A f1 f2).
Proof. exact (fun_ext (fun n : nat => @lem1057327 A f1 f2 n)). Qed.
Lemma lem1057329 (n : nat) : (NUMSUM True n) = (NUMSUM True n).
Proof. exact (eq_refl (NUMSUM True n)). Qed.
Lemma lem1057330 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) : (term105 A f1 f2 n) = (term43 A f1 f2 n).
Proof. exact (MK_COMB (@lem1057328 A f1 f2) (@lem1057329 n)). Qed.
Lemma lem1057331 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem1057332 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) : (term106 A f1 f2 n) = (term107 A f1 f2 n).
Proof. exact (MK_COMB (@lem1057331 A) (@lem1057330 A f1 f2 n)). Qed.
Lemma lem1057333 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) : (term43 A f1 f2 n) = (term108 A f1 f2 n).
Proof. exact (eq_refl (term43 A f1 f2 n)). Qed.
Lemma lem1057334 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) : ((term105 A f1 f2 n) = (term43 A f1 f2 n)) = ((term43 A f1 f2 n) = (term108 A f1 f2 n)).
Proof. exact (MK_COMB (@lem1057332 A f1 f2 n) (@lem1057333 A f1 f2 n)). Qed.
Lemma lem1057335 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) : (term43 A f1 f2 n) = (term108 A f1 f2 n).
Proof. exact (EQ_MP (@lem1057334 A f1 f2 n) (@lem1057326 A f1 f2 n)). Qed.
Lemma lem1057337 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term68 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem1057338 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term69 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem1057337 _2963 g t e g' t' e'). Qed.
Lemma lem1057339 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term70 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem1057338 _2963 g t e g' t'). Qed.
Lemma lem1057340 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term71 _2963 g t e.
Proof. exact (fun g' : Prop => @lem1057339 _2963 g t e g'). Qed.
Lemma lem1057341 (g : Prop) (t : Prop) (e : Prop) : term72 g t e.
Proof. exact (@lem1057340 Prop g t e). Qed.
Lemma lem1057342 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) (a : A) : term109 A f1 f2 n a.
Proof. exact (@lem1057341 (term110 n) (term111 A f1 n a) (term111 A f2 n a)). Qed.
Lemma lem1057343 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) (a : A) (g' : Prop) : term112 A f1 f2 n a g'.
Proof. exact (@lem1057342 A f1 f2 n a g'). Qed.
Lemma lem1057344 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) (a : A) (g' : Prop) : (term112 A f1 f2 n a g') = (term113 A f1 f2 n a g').
Proof. exact (eq_refl (term112 A f1 f2 n a g')). Qed.
Lemma lem1057345 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) (a : A) (g' : Prop) : term113 A f1 f2 n a g'.
Proof. exact (EQ_MP (@lem1057344 A f1 f2 n a g') (@lem1057343 A f1 f2 n a g')). Qed.
Lemma lem1057346 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) (a : A) (g' : Prop) (t' : Prop) : term114 A f1 f2 n a g' t'.
Proof. exact (@lem1057345 A f1 f2 n a g' t'). Qed.
Lemma lem1057347 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) (a : A) (g' : Prop) (t' : Prop) : (term114 A f1 f2 n a g' t') = (term115 A f1 f2 n a g' t').
Proof. exact (eq_refl (term114 A f1 f2 n a g' t')). Qed.
Lemma lem1057348 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) (a : A) (g' : Prop) (t' : Prop) : term115 A f1 f2 n a g' t'.
Proof. exact (EQ_MP (@lem1057347 A f1 f2 n a g' t') (@lem1057346 A f1 f2 n a g' t')). Qed.
Lemma lem1057349 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) (a : A) (g' : Prop) (t' : Prop) (e' : Prop) : term116 A f1 f2 n a g' t' e'.
Proof. exact (@lem1057348 A f1 f2 n a g' t' e'). Qed.
Lemma lem1057350 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) (a : A) (g' : Prop) (t' : Prop) (e' : Prop) : (term116 A f1 f2 n a g' t' e') = (term117 A f1 f2 n a g' t' e').
Proof. exact (eq_refl (term116 A f1 f2 n a g' t' e')). Qed.
Lemma lem1057351 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) (a : A) (g' : Prop) (t' : Prop) (e' : Prop) : term117 A f1 f2 n a g' t' e'.
Proof. exact (EQ_MP (@lem1057350 A f1 f2 n a g' t' e') (@lem1057349 A f1 f2 n a g' t' e')). Qed.
Lemma lem1057353 (y : nat) (x : Prop) : (term82 x y) = x.
Proof. exact (proj1 (@lem1057134 x y)). Qed.
Lemma lem1057354 (n : nat) : (term110 n) = True.
Proof. exact (@lem1057353 n True). Qed.
Lemma lem1057355 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) (a : A) (t' : Prop) (e' : Prop) : term118 A f1 f2 n a t' e'.
Proof. exact (@lem1057351 A f1 f2 n a True t' e'). Qed.
Lemma lem1057356 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (n : nat) (a : A) (t' : Prop) (e' : Prop) : term119 A f1 f2 n a t' e'.
Proof. exact (@lem1057355 A f1 f2 n a t' e' (@lem1057354 n)). Qed.
Lemma lem1057363 (x : Prop) (y : nat) : (term85 x y) = y.
Proof. exact (proj2 (@lem1057134 x y)). Qed.
Lemma lem1057364 (n : nat) : (term120 n) = n.
Proof. exact (@lem1057363 True n). Qed.
Lemma lem1057365 {A : Type'} (f1 : type1597 A) : f1 = f1.
Proof. exact (eq_refl f1). Qed.
Lemma lem1057366 {A : Type'} (f1 : type1597 A) (n : nat) : (term121 A f1 n) = (f1 n).
Proof. exact (MK_COMB (@lem1057365 A f1) (@lem1057364 n)). Qed.
Lemma lem1057367 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1057368 {A : Type'} (f1 : type1597 A) (n : nat) (a : A) : (term111 A f1 n a) = (f1 n a).
Proof. exact (MK_COMB (@lem1057366 A f1 n) (@lem1057367 A a)). Qed.
Lemma lem1057369 {A : Type'} (f1 : type1597 A) (n : nat) (a : A) : term122 A f1 n a.
Proof. exact (fun h0 : True => @lem1057368 A f1 n a). Qed.
Lemma lem1057370 {A : Type'} (f2 : type1597 A) (f1 : type1597 A) (n : nat) (a : A) (e' : Prop) : term123 A f2 f1 n a e'.
Proof. exact (@lem1057356 A f1 f2 n a (f1 n a) e'). Qed.
Lemma lem1057371 {A : Type'} (f2 : type1597 A) (f1 : type1597 A) (n : nat) (a : A) (e' : Prop) : term124 A f2 f1 n a e'.
Proof. exact (@lem1057370 A f2 f1 n a e' (@lem1057369 A f1 n a)). Qed.
Lemma lem1057376 (x : Prop) (y : nat) : (term85 x y) = y.
Proof. exact (proj2 (@lem1057134 x y)). Qed.
Lemma lem1057377 (n : nat) : (term120 n) = n.
Proof. exact (@lem1057376 True n). Qed.
Lemma lem1057378 {A : Type'} (f2 : type1597 A) : f2 = f2.
Proof. exact (eq_refl f2). Qed.
Lemma lem1057379 {A : Type'} (f2 : type1597 A) (n : nat) : (term121 A f2 n) = (f2 n).
Proof. exact (MK_COMB (@lem1057378 A f2) (@lem1057377 n)). Qed.
Lemma lem1057381 {A : Type'} (f2 : type1597 A) (f2' : type1597 A) (n : nat) (h1 : (f2 n) = (f2' n)) : (f2 n) = (f2' n).
Proof. exact (h1). Qed.
Lemma lem1057382 {A : Type'} (f2 : type1597 A) (f2' : type1597 A) (n : nat) (h1 : (f2 n) = (f2' n)) : (term121 A f2 n) = (f2' n).
Proof. exact (TRANS (@lem1057379 A f2 n) (@lem1057381 A f2 f2' n h1)). Qed.
Lemma lem1057383 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1057384 {A : Type'} (a : A) (f2 : type1597 A) (f2' : type1597 A) (n : nat) (h1 : (f2 n) = (f2' n)) : (term111 A f2 n a) = (f2' n a).
Proof. exact (MK_COMB (@lem1057382 A f2 f2' n h1) (@lem1057383 A a)). Qed.
Lemma lem1057385 {A : Type'} (a : A) (f2 : type1597 A) (f2' : type1597 A) (n : nat) (h1 : (f2 n) = (f2' n)) : term125 A f2 f2' n a.
Proof. exact (fun h0 : ~ True => @lem1057384 A a f2 f2' n h1). Qed.
Lemma lem1057386 {A : Type'} (f2 : type1597 A) (f1 : type1597 A) (f2' : type1597 A) (n : nat) (a : A) : term126 A f2 f1 f2' n a.
Proof. exact (@lem1057371 A f2 f1 n a (f2' n a)). Qed.
Lemma lem1057387 {A : Type'} (f1 : type1597 A) (a : A) (f2 : type1597 A) (f2' : type1597 A) (n : nat) (h1 : (f2 n) = (f2' n)) : (term127 A f1 f2 n a) = (term128 A f1 f2' n a).
Proof. exact (@lem1057386 A f2 f1 f2' n a (@lem1057385 A a f2 f2' n h1)). Qed.
Lemma lem1057389 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1057390 (t2 : Prop) (t1 : Prop) : (@COND Prop True t1 t2) = t1.
Proof. exact (@lem1057389 Prop t2 t1). Qed.
Lemma lem1057391 {A : Type'} (f2' : type1597 A) (f1 : type1597 A) (n : nat) (a : A) : (term128 A f1 f2' n a) = (f1 n a).
Proof. exact (@lem1057390 (f2' n a) (f1 n a)). Qed.
Lemma lem1057392 {A : Type'} (f1 : type1597 A) (a : A) (f2 : type1597 A) (f2' : type1597 A) (n : nat) (h1 : (f2 n) = (f2' n)) : (term127 A f1 f2 n a) = (f1 n a).
Proof. exact (TRANS (@lem1057387 A f1 a f2 f2' n h1) (@lem1057391 A f2' f1 n a)). Qed.
Lemma lem1057393 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (n : nat) (h1 : (f2 n) = (f2' n)) : (term108 A f1 f2 n) = (term95 A f1 n).
Proof. exact (fun_ext (fun a : A => @lem1057392 A f1 a f2 f2' n h1)). Qed.
Lemma lem1057394 {A : Type'} (t : A -> Prop) : (term96 A t) = t.
Proof. exact (@lem1057128 A Prop t). Qed.
Lemma lem1057395 {A : Type'} (f1 : type1597 A) (n : nat) : (term95 A f1 n) = (f1 n).
Proof. exact (@lem1057394 A (f1 n)). Qed.
Lemma lem1057396 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (n : nat) (h1 : (f2 n) = (f2' n)) : (term108 A f1 f2 n) = (f1 n).
Proof. exact (TRANS (@lem1057393 A f1 f2 f2' n h1) (@lem1057395 A f1 n)). Qed.
Lemma lem1057397 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (n : nat) (h1 : (f2 n) = (f2' n)) : (term43 A f1 f2 n) = (f1 n).
Proof. exact (TRANS (@lem1057335 A f1 f2 n) (@lem1057396 A f1 f2 f2' n h1)). Qed.
Lemma lem1057398 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem1057399 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (n : nat) (h1 : (f2 n) = (f2' n)) : (term107 A f1 f2 n) = (term97 A f1 n).
Proof. exact (MK_COMB (@lem1057398 A) (@lem1057397 A f1 f2 f2' n h1)). Qed.
Lemma lem1057401 {A B : Type'} (f : A -> B) (y : A) : (term59 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1057402 {A : Type'} (f : type1597 A) (y : nat) : (term60 A f y) = (f y).
Proof. exact (@lem1057401 nat (A -> Prop) f y). Qed.
Lemma lem1057403 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) : (term105 A f1' f2' n) = (term43 A f1' f2' n).
Proof. exact (@lem1057402 A (term3 A f1' f2') (NUMSUM True n)). Qed.
Lemma lem1057404 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) : (term62 A f1' f2' n) = (term63 A f1' f2' n).
Proof. exact (eq_refl (term62 A f1' f2' n)). Qed.
Lemma lem1057405 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) : (term64 A f1' f2') = (term3 A f1' f2').
Proof. exact (fun_ext (fun n : nat => @lem1057404 A f1' f2' n)). Qed.
Lemma lem1057406 (n : nat) : (NUMSUM True n) = (NUMSUM True n).
Proof. exact (eq_refl (NUMSUM True n)). Qed.
Lemma lem1057407 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) : (term105 A f1' f2' n) = (term43 A f1' f2' n).
Proof. exact (MK_COMB (@lem1057405 A f1' f2') (@lem1057406 n)). Qed.
Lemma lem1057408 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem1057409 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) : (term106 A f1' f2' n) = (term107 A f1' f2' n).
Proof. exact (MK_COMB (@lem1057408 A) (@lem1057407 A f1' f2' n)). Qed.
Lemma lem1057410 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) : (term43 A f1' f2' n) = (term108 A f1' f2' n).
Proof. exact (eq_refl (term43 A f1' f2' n)). Qed.
Lemma lem1057411 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) : ((term105 A f1' f2' n) = (term43 A f1' f2' n)) = ((term43 A f1' f2' n) = (term108 A f1' f2' n)).
Proof. exact (MK_COMB (@lem1057409 A f1' f2' n) (@lem1057410 A f1' f2' n)). Qed.
Lemma lem1057412 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) : (term43 A f1' f2' n) = (term108 A f1' f2' n).
Proof. exact (EQ_MP (@lem1057411 A f1' f2' n) (@lem1057403 A f1' f2' n)). Qed.
Lemma lem1057414 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term68 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem1057415 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term69 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem1057414 _2963 g t e g' t' e'). Qed.
Lemma lem1057416 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term70 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem1057415 _2963 g t e g' t'). Qed.
Lemma lem1057417 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term71 _2963 g t e.
Proof. exact (fun g' : Prop => @lem1057416 _2963 g t e g'). Qed.
Lemma lem1057418 (g : Prop) (t : Prop) (e : Prop) : term72 g t e.
Proof. exact (@lem1057417 Prop g t e). Qed.
Lemma lem1057419 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) (a : A) : term109 A f1' f2' n a.
Proof. exact (@lem1057418 (term110 n) (term111 A f1' n a) (term111 A f2' n a)). Qed.
Lemma lem1057420 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) (a : A) (g' : Prop) : term112 A f1' f2' n a g'.
Proof. exact (@lem1057419 A f1' f2' n a g'). Qed.
Lemma lem1057421 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) (a : A) (g' : Prop) : (term112 A f1' f2' n a g') = (term113 A f1' f2' n a g').
Proof. exact (eq_refl (term112 A f1' f2' n a g')). Qed.
Lemma lem1057422 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) (a : A) (g' : Prop) : term113 A f1' f2' n a g'.
Proof. exact (EQ_MP (@lem1057421 A f1' f2' n a g') (@lem1057420 A f1' f2' n a g')). Qed.
Lemma lem1057423 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) (a : A) (g' : Prop) (t' : Prop) : term114 A f1' f2' n a g' t'.
Proof. exact (@lem1057422 A f1' f2' n a g' t'). Qed.
Lemma lem1057424 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) (a : A) (g' : Prop) (t' : Prop) : (term114 A f1' f2' n a g' t') = (term115 A f1' f2' n a g' t').
Proof. exact (eq_refl (term114 A f1' f2' n a g' t')). Qed.
Lemma lem1057425 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) (a : A) (g' : Prop) (t' : Prop) : term115 A f1' f2' n a g' t'.
Proof. exact (EQ_MP (@lem1057424 A f1' f2' n a g' t') (@lem1057423 A f1' f2' n a g' t')). Qed.
Lemma lem1057426 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) (a : A) (g' : Prop) (t' : Prop) (e' : Prop) : term116 A f1' f2' n a g' t' e'.
Proof. exact (@lem1057425 A f1' f2' n a g' t' e'). Qed.
Lemma lem1057427 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) (a : A) (g' : Prop) (t' : Prop) (e' : Prop) : (term116 A f1' f2' n a g' t' e') = (term117 A f1' f2' n a g' t' e').
Proof. exact (eq_refl (term116 A f1' f2' n a g' t' e')). Qed.
Lemma lem1057428 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) (a : A) (g' : Prop) (t' : Prop) (e' : Prop) : term117 A f1' f2' n a g' t' e'.
Proof. exact (EQ_MP (@lem1057427 A f1' f2' n a g' t' e') (@lem1057426 A f1' f2' n a g' t' e')). Qed.
Lemma lem1057430 (y : nat) (x : Prop) : (term82 x y) = x.
Proof. exact (proj1 (@lem1057134 x y)). Qed.
Lemma lem1057431 (n : nat) : (term110 n) = True.
Proof. exact (@lem1057430 n True). Qed.
Lemma lem1057432 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) (a : A) (t' : Prop) (e' : Prop) : term118 A f1' f2' n a t' e'.
Proof. exact (@lem1057428 A f1' f2' n a True t' e'). Qed.
Lemma lem1057433 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) (a : A) (t' : Prop) (e' : Prop) : term119 A f1' f2' n a t' e'.
Proof. exact (@lem1057432 A f1' f2' n a t' e' (@lem1057431 n)). Qed.
Lemma lem1057440 (x : Prop) (y : nat) : (term85 x y) = y.
Proof. exact (proj2 (@lem1057134 x y)). Qed.
Lemma lem1057441 (n : nat) : (term120 n) = n.
Proof. exact (@lem1057440 True n). Qed.
Lemma lem1057442 {A : Type'} (f1' : type1597 A) : f1' = f1'.
Proof. exact (eq_refl f1'). Qed.
Lemma lem1057443 {A : Type'} (f1' : type1597 A) (n : nat) : (term121 A f1' n) = (f1' n).
Proof. exact (MK_COMB (@lem1057442 A f1') (@lem1057441 n)). Qed.
Lemma lem1057444 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1057445 {A : Type'} (f1' : type1597 A) (n : nat) (a : A) : (term111 A f1' n a) = (f1' n a).
Proof. exact (MK_COMB (@lem1057443 A f1' n) (@lem1057444 A a)). Qed.
Lemma lem1057446 {A : Type'} (f1' : type1597 A) (n : nat) (a : A) : term122 A f1' n a.
Proof. exact (fun h0 : True => @lem1057445 A f1' n a). Qed.
Lemma lem1057447 {A : Type'} (f2' : type1597 A) (f1' : type1597 A) (n : nat) (a : A) (e' : Prop) : term123 A f2' f1' n a e'.
Proof. exact (@lem1057433 A f1' f2' n a (f1' n a) e'). Qed.
Lemma lem1057448 {A : Type'} (f2' : type1597 A) (f1' : type1597 A) (n : nat) (a : A) (e' : Prop) : term124 A f2' f1' n a e'.
Proof. exact (@lem1057447 A f2' f1' n a e' (@lem1057446 A f1' n a)). Qed.
Lemma lem1057453 (x : Prop) (y : nat) : (term85 x y) = y.
Proof. exact (proj2 (@lem1057134 x y)). Qed.
Lemma lem1057454 (n : nat) : (term120 n) = n.
Proof. exact (@lem1057453 True n). Qed.
Lemma lem1057455 {A : Type'} (f2' : type1597 A) : f2' = f2'.
Proof. exact (eq_refl f2'). Qed.
Lemma lem1057456 {A : Type'} (f2' : type1597 A) (n : nat) : (term121 A f2' n) = (f2' n).
Proof. exact (MK_COMB (@lem1057455 A f2') (@lem1057454 n)). Qed.
Lemma lem1057457 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1057458 {A : Type'} (f2' : type1597 A) (n : nat) (a : A) : (term111 A f2' n a) = (f2' n a).
Proof. exact (MK_COMB (@lem1057456 A f2' n) (@lem1057457 A a)). Qed.
Lemma lem1057459 {A : Type'} (f2' : type1597 A) (n : nat) (a : A) : term129 A f2' n a.
Proof. exact (fun h0 : ~ True => @lem1057458 A f2' n a). Qed.
Lemma lem1057460 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) (a : A) : term130 A f1' f2' n a.
Proof. exact (@lem1057448 A f2' f1' n a (f2' n a)). Qed.
Lemma lem1057461 {A : Type'} (f1' : type1597 A) (f2' : type1597 A) (n : nat) (a : A) : (term127 A f1' f2' n a) = (term128 A f1' f2' n a).
Proof. exact (@lem1057460 A f1' f2' n a (@lem1057459 A f2' n a)). Qed.
Lemma lem1057463 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1057464 (t2 : Prop) (t1 : Prop) : (@COND Prop True t1 t2) = t1.
Proof. exact (@lem1057463 Prop t2 t1). Qed.
Lemma lem1057465 {A : Type'} (f2' : type1597 A) (f1' : type1597 A) (n : nat) (a : A) : (term128 A f1' f2' n a) = (f1' n a).
Proof. exact (@lem1057464 (f2' n a) (f1' n a)). Qed.
Lemma lem1057466 {A : Type'} (f2' : type1597 A) (f1' : type1597 A) (n : nat) (a : A) : (term127 A f1' f2' n a) = (f1' n a).
Proof. exact (TRANS (@lem1057461 A f1' f2' n a) (@lem1057465 A f2' f1' n a)). Qed.
Lemma lem1057467 {A : Type'} (f2' : type1597 A) (f1' : type1597 A) (n : nat) : (term108 A f1' f2' n) = (term95 A f1' n).
Proof. exact (fun_ext (fun a : A => @lem1057466 A f2' f1' n a)). Qed.
Lemma lem1057468 {A : Type'} (t : A -> Prop) : (term96 A t) = t.
Proof. exact (@lem1057128 A Prop t). Qed.
Lemma lem1057469 {A : Type'} (f1' : type1597 A) (n : nat) : (term95 A f1' n) = (f1' n).
Proof. exact (@lem1057468 A (f1' n)). Qed.
Lemma lem1057470 {A : Type'} (f2' : type1597 A) (f1' : type1597 A) (n : nat) : (term108 A f1' f2' n) = (f1' n).
Proof. exact (TRANS (@lem1057467 A f2' f1' n) (@lem1057469 A f1' n)). Qed.
Lemma lem1057471 {A : Type'} (f2' : type1597 A) (f1' : type1597 A) (n : nat) : (term43 A f1' f2' n) = (f1' n).
Proof. exact (TRANS (@lem1057412 A f1' f2' n) (@lem1057470 A f2' f1' n)). Qed.
Lemma lem1057472 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (n : nat) (h1 : (f2 n) = (f2' n)) : ((term43 A f1 f2 n) = (term43 A f1' f2' n)) = ((f1 n) = (f1' n)).
Proof. exact (MK_COMB (@lem1057399 A f1 f2 f2' n h1) (@lem1057471 A f2' f1' n)). Qed.
Lemma lem1057475 {A : Type'} (f2 : type1597 A) (f2' : type1597 A) (f1 : type1597 A) (f1' : type1597 A) (n : nat) (q' : Prop) : term131 A f2 f2' f1 f1' n q'.
Proof. exact (@lem1057320 A f1 f1' f2 f2' n ((f1 n) = (f1' n)) q'). Qed.
Lemma lem1057476 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (q' : Prop) (f2 : type1597 A) (f2' : type1597 A) (n : nat) (h1 : (f2 n) = (f2' n)) : term132 A f2 f2' f1 f1' n q'.
Proof. exact (@lem1057475 A f2 f2' f1 f1' n q' (@lem1057472 A f1 f1' f2 f2' n h1)). Qed.
Lemma lem1057483 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (n : nat) (h1 : (f1 n) = (f1' n)) : (f1 n) = (f1' n).
Proof. exact (h1). Qed.
Lemma lem1057484 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem1057485 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (n : nat) (h1 : (f1 n) = (f1' n)) : (term97 A f1 n) = (term97 A f1' n).
Proof. exact (MK_COMB (@lem1057484 A) (@lem1057483 A f1 f1' n h1)). Qed.
Lemma lem1057486 {A : Type'} (f1' : type1597 A) (n : nat) : (f1' n) = (f1' n).
Proof. exact (eq_refl (f1' n)). Qed.
Lemma lem1057487 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (n : nat) (h1 : (f1 n) = (f1' n)) : ((f1 n) = (f1' n)) = ((f1' n) = (f1' n)).
Proof. exact (MK_COMB (@lem1057485 A f1 f1' n h1) (@lem1057486 A f1' n)). Qed.
Lemma lem1057489 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1057490 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem1057489 (A -> Prop) x). Qed.
Lemma lem1057491 {A : Type'} (f1' : type1597 A) (n : nat) : ((f1' n) = (f1' n)) = True.
Proof. exact (@lem1057490 A (f1' n)). Qed.
Lemma lem1057492 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (n : nat) (h1 : (f1 n) = (f1' n)) : ((f1 n) = (f1' n)) = True.
Proof. exact (TRANS (@lem1057487 A f1 f1' n h1) (@lem1057491 A f1' n)). Qed.
Lemma lem1057493 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1057494 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (n : nat) (h1 : (f1 n) = (f1' n)) : (term31 A f1 f1' n) = (and True).
Proof. exact (MK_COMB (@lem1057493) (@lem1057492 A f1 f1' n h1)). Qed.
Lemma lem1057498 {A : Type'} (f2 : type1597 A) (f2' : type1597 A) (n : nat) (h1 : (f2 n) = (f2' n)) : (f2 n) = (f2' n).
Proof. exact (h1). Qed.
Lemma lem1057499 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem1057500 {A : Type'} (f2 : type1597 A) (f2' : type1597 A) (n : nat) (h1 : (f2 n) = (f2' n)) : (term97 A f2 n) = (term97 A f2' n).
Proof. exact (MK_COMB (@lem1057499 A) (@lem1057498 A f2 f2' n h1)). Qed.
Lemma lem1057501 {A : Type'} (f2' : type1597 A) (n : nat) : (f2' n) = (f2' n).
Proof. exact (eq_refl (f2' n)). Qed.
Lemma lem1057502 {A : Type'} (f2 : type1597 A) (f2' : type1597 A) (n : nat) (h1 : (f2 n) = (f2' n)) : ((f2 n) = (f2' n)) = ((f2' n) = (f2' n)).
Proof. exact (MK_COMB (@lem1057500 A f2 f2' n h1) (@lem1057501 A f2' n)). Qed.
Lemma lem1057504 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1057505 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem1057504 (A -> Prop) x). Qed.
Lemma lem1057506 {A : Type'} (f2' : type1597 A) (n : nat) : ((f2' n) = (f2' n)) = True.
Proof. exact (@lem1057505 A (f2' n)). Qed.
Lemma lem1057507 {A : Type'} (f2 : type1597 A) (f2' : type1597 A) (n : nat) (h1 : (f2 n) = (f2' n)) : ((f2 n) = (f2' n)) = True.
Proof. exact (TRANS (@lem1057502 A f2 f2' n h1) (@lem1057506 A f2' n)). Qed.
Lemma lem1057508 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (n : nat) (h1 : (f1 n) = (f1' n)) (h2 : (f2 n) = (f2' n)) : (term33 A f1 f1' f2 f2' n) = (True /\ True).
Proof. exact (MK_COMB (@lem1057494 A f1 f1' n h1) (@lem1057507 A f2 f2' n h2)). Qed.
Lemma lem1057510 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1057511 : (True /\ True) = True.
Proof. exact (@lem1057510 True). Qed.
Lemma lem1057512 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (n : nat) (h1 : (f1 n) = (f1' n)) (h2 : (f2 n) = (f2' n)) : (term33 A f1 f1' f2 f2' n) = True.
Proof. exact (TRANS (@lem1057508 A f1 f1' f2 f2' n h1 h2) (@lem1057511)). Qed.
Lemma lem1057513 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (n : nat) (h1 : (f2 n) = (f2' n)) : term133 A f1 f1' f2 f2' n.
Proof. exact (fun h0 : (f1 n) = (f1' n) => @lem1057512 A f1 f1' f2 f2' n h0 h1). Qed.
Lemma lem1057514 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (n : nat) (h1 : (f2 n) = (f2' n)) : term134 A f2 f2' f1 f1' n.
Proof. exact (@lem1057476 A f1 f1' True f2 f2' n h1). Qed.
Lemma lem1057515 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (n : nat) (h1 : (f2 n) = (f2' n)) : (term54 A f1 f1' f2 f2' n) = (term135 A f1 f1' n).
Proof. exact (@lem1057514 A f1 f1' f2 f2' n h1 (@lem1057513 A f1 f1' f2 f2' n h1)). Qed.
Lemma lem1057519 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1057520 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (n : nat) : (term135 A f1 f1' n) = True.
Proof. exact (@lem1057519 ((f1 n) = (f1' n))). Qed.
Lemma lem1057521 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (n : nat) (h1 : (f2 n) = (f2' n)) : (term54 A f1 f1' f2 f2' n) = True.
Proof. exact (TRANS (@lem1057515 A f1 f1' f2 f2' n h1) (@lem1057520 A f1 f1' n)). Qed.
Lemma lem1057522 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (n : nat) : term136 A f1 f1' f2 f2' n.
Proof. exact (fun h0 : (f2 n) = (f2' n) => @lem1057521 A f1 f1' f2 f2' n h0). Qed.
Lemma lem1057523 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (n : nat) : term137 A f1 f1' f2 f2' n.
Proof. exact (@lem1057304 A f1 f1' f2 f2' n True). Qed.
Lemma lem1057524 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (n : nat) : (term138 A f1 f1' f2 f2' n) = (term135 A f2 f2' n).
Proof. exact (@lem1057523 A f1 f1' f2 f2' n (@lem1057522 A f1 f1' f2 f2' n)). Qed.
Lemma lem1057528 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1057529 {A : Type'} (f2 : type1597 A) (f2' : type1597 A) (n : nat) : (term135 A f2 f2' n) = True.
Proof. exact (@lem1057528 ((f2 n) = (f2' n))). Qed.
Lemma lem1057530 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (n : nat) : (term138 A f1 f1' f2 f2' n) = True.
Proof. exact (TRANS (@lem1057524 A f1 f1' f2 f2' n) (@lem1057529 A f2 f2' n)). Qed.
Lemma lem1057531 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (n : nat) : True = (term138 A f1 f1' f2 f2' n).
Proof. exact (SYM (@lem1057530 A f1 f1' f2 f2' n)). Qed.
Lemma lem1057532 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (n : nat) : term138 A f1 f1' f2 f2' n.
Proof. exact (EQ_MP (@lem1057531 A f1 f1' f2 f2' n) (@lem0)). Qed.
Lemma lem1057533 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (f1' : type1597 A) (f2' : type1597 A) (n : nat) (h1 : term39 A f1 f2 f1' f2' n) : term54 A f1 f1' f2 f2' n.
Proof. exact (@lem1057532 A f1 f1' f2 f2' n (@lem1057122 A f1 f2 f1' f2' n h1)). Qed.
Lemma lem1057534 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (f1' : type1597 A) (f2' : type1597 A) (n : nat) (h1 : term39 A f1 f2 f1' f2' n) : term33 A f1 f1' f2 f2' n.
Proof. exact (@lem1057533 A f1 f2 f1' f2' n h1 (@lem1057125 A f1 f2 f1' f2' n h1)). Qed.
Lemma lem1057535 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (n : nat) : term139 A f1 f1' f2 f2' n.
Proof. exact (fun h0 : term39 A f1 f2 f1' f2' n => @lem1057534 A f1 f2 f1' f2' n h0). Qed.
Lemma lem1057536 {A : Type'} (n : nat) (f1 : type1597 A) (f2 : type1597 A) (f1' : type1597 A) (f2' : type1597 A) (h1 : (term3 A f1 f2) = (term3 A f1' f2')) : term33 A f1 f1' f2 f2' n.
Proof. exact (@lem1057535 A f1 f1' f2 f2' n (@lem1057118 A n f1 f2 f1' f2' h1)). Qed.
Lemma lem1057537 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) (n : nat) : term140 A f1 f1' f2 f2' n.
Proof. exact (fun h0 : (term3 A f1 f2) = (term3 A f1' f2') => @lem1057536 A n f1 f2 f1' f2' h0). Qed.
Lemma lem1057538 {A : Type'} (n : nat) (f1 : type1597 A) (f2 : type1597 A) (f1' : type1597 A) (f2' : type1597 A) (h1 : (@INJP A f1 f2) = (@INJP A f1' f2')) : term33 A f1 f1' f2 f2' n.
Proof. exact (@lem1057537 A f1 f1' f2 f2' n (@lem1057114 A f1 f2 f1' f2' h1)). Qed.
Lemma lem1057543 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (f1' : type1597 A) (f2' : type1597 A) (h1 : (@INJP A f1 f2) = (@INJP A f1' f2')) : term36 A f1 f1' f2 f2'.
Proof. exact (fun n : nat => @lem1057538 A n f1 f2 f1' f2' h1). Qed.
Lemma lem1057544 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (f1' : type1597 A) (f2' : type1597 A) (h1 : (@INJP A f1 f2) = (@INJP A f1' f2')) : term18 A f1 f1' f2 f2'.
Proof. exact (EQ_MP (@lem1057099 A f1 f1' f2 f2') (@lem1057543 A f1 f2 f1' f2' h1)). Qed.
Lemma lem1057546 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (f1' : type1597 A) (f2' : type1597 A) (h1 : (@INJP A f1 f2) = (@INJP A f1' f2')) : term13 A f1 f1' f2 f2'.
Proof. exact (EQ_MP (@lem1057061 A f1 f1' f2 f2') (@lem1057544 A f1 f2 f1' f2' h1)). Qed.
Lemma lem1057547 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (f1' : type1597 A) (f2' : type1597 A) : term141 A f1 f2 f1' f2'.
Proof. exact (fun h0 : term13 A f1 f1' f2 f2' => @lem1057043 A f1 f1' f2 f2' h0). Qed.
Lemma lem1057548 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) : term142 A f1 f1' f2 f2'.
Proof. exact (fun h0 : (@INJP A f1 f2) = (@INJP A f1' f2') => @lem1057546 A f1 f2 f1' f2' h0). Qed.
Lemma lem1057549 {A : Type'} (f1 : type1597 A) (f2 : type1597 A) (f1' : type1597 A) (f2' : type1597 A) : term143 A f1 f2 f1' f2'.
Proof. exact (conj (@lem1057548 A f1 f1' f2 f2') (@lem1057547 A f1 f2 f1' f2')). Qed.
Lemma lem1057550 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) : (term143 A f1 f2 f1' f2') = (((@INJP A f1 f2) = (@INJP A f1' f2')) = (term13 A f1 f1' f2 f2')).
Proof. exact (@lem32 ((@INJP A f1 f2) = (@INJP A f1' f2')) (term13 A f1 f1' f2 f2')). Qed.
Lemma lem1057551 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) : ((@INJP A f1 f2) = (@INJP A f1' f2')) = (term13 A f1 f1' f2 f2').
Proof. exact (EQ_MP (@lem1057550 A f1 f1' f2 f2') (@lem1057549 A f1 f2 f1' f2')). Qed.
Lemma lem1057556 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) : term144 A f1 f1' f2.
Proof. exact (fun f2' : type1597 A => @lem1057551 A f1 f1' f2 f2'). Qed.
Lemma lem1057561 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) : term145 A f1 f1'.
Proof. exact (fun f2 : type1597 A => @lem1057556 A f1 f1' f2). Qed.
Lemma lem1057566 {A : Type'} (f1 : type1597 A) : term146 A f1.
Proof. exact (fun f1' : type1597 A => @lem1057561 A f1 f1'). Qed.
Lemma lem1057571 {A : Type'} : term147 A.
Proof. exact (fun f1 : type1597 A => @lem1057566 A f1). Qed.
