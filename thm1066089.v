Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1066089_term_abbrevs.
Require Import thm1065718_spec.
Require Import thm1066033_spec.
Lemma lem1066034 {A : Type'} : (term0 A) = (term1 A).
Proof. exact (eq_refl (term0 A)). Qed.
Lemma lem1066035 {A : Type'} : term1 A.
Proof. exact (EQ_MP (@lem1066034 A) (@lem1065718 A)). Qed.
Lemma lem1066036 {A : Type'} : term2 A.
Proof. exact (@lem1066035 A term3). Qed.
Lemma lem1066037 {A : Type'} : (term2 A) = (term4 A).
Proof. exact (eq_refl (term2 A)). Qed.
Lemma lem1066038 {A : Type'} : term4 A.
Proof. exact (EQ_MP (@lem1066037 A) (@lem1066036 A)). Qed.
Lemma lem1066039 {A : Type'} (h1 : (@FCONS A) = (term5 A)) : (@FCONS A) = (term5 A).
Proof. exact (h1). Qed.
Lemma lem1066040 {A : Type'} (h1 : (@FCONS A) = (term5 A)) : (term5 A) = (@FCONS A).
Proof. exact (SYM (@lem1066039 A h1)). Qed.
Lemma lem1066041 {A : Type'} (h1 : (term5 A) = (@FCONS A)) : (term5 A) = (@FCONS A).
Proof. exact (h1). Qed.
Lemma lem1066042 {A : Type'} (h1 : (term5 A) = (@FCONS A)) : (@FCONS A) = (term5 A).
Proof. exact (SYM (@lem1066041 A h1)). Qed.
Lemma lem1066043 {A : Type'} : ((@FCONS A) = (term5 A)) = ((term5 A) = (@FCONS A)).
Proof. exact (prop_ext (fun h1 : (@FCONS A) = (term5 A) => @lem1066040 A h1) (fun h1 : (term5 A) = (@FCONS A) => @lem1066042 A h1)). Qed.
Lemma lem1066046 {A : Type'} : (term5 A) = (@FCONS A).
Proof. exact (EQ_MP (@lem1066043 A) (@lem1066033 A)). Qed.
Lemma lem1066047 {A : Type'} : (term5 A) = (@FCONS A).
Proof. exact (@lem1066046 A). Qed.
Lemma lem1066048 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1066049 {A : Type'} (a : A) : (term6 A a) = (@FCONS A a).
Proof. exact (MK_COMB (@lem1066047 A) (@lem1066048 A a)). Qed.
Lemma lem1066050 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1066051 {A : Type'} (a : A) (f : nat -> A) : (term7 A a f) = (@FCONS A a f).
Proof. exact (MK_COMB (@lem1066049 A a) (@lem1066050 A f)). Qed.
Lemma lem1066052 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1066053 {A : Type'} (a : A) (f : nat -> A) : (term8 A a f) = (term9 A a f).
Proof. exact (MK_COMB (@lem1066051 A a f) (@lem1066052)). Qed.
Lemma lem1066054 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1066055 {A : Type'} (a : A) (f : nat -> A) : (term10 A a f) = (term11 A a f).
Proof. exact (MK_COMB (@lem1066054 A) (@lem1066053 A a f)). Qed.
Lemma lem1066056 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1066057 {A : Type'} (f : nat -> A) (a : A) : ((term8 A a f) = a) = ((term9 A a f) = a).
Proof. exact (MK_COMB (@lem1066055 A a f) (@lem1066056 A a)). Qed.
Lemma lem1066058 {A : Type'} (a : A) : (term12 A a) = (term13 A a).
Proof. exact (fun_ext (fun f : nat -> A => @lem1066057 A f a)). Qed.
Lemma lem1066059 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem1066060 {A : Type'} (a : A) : (term14 A a) = (term15 A a).
Proof. exact (MK_COMB (@lem1066059 A) (@lem1066058 A a)). Qed.
Lemma lem1066061 {A : Type'} : (term16 A) = (term17 A).
Proof. exact (fun_ext (fun a : A => @lem1066060 A a)). Qed.
Lemma lem1066062 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1066063 {A : Type'} : (term18 A) = (term19 A).
Proof. exact (MK_COMB (@lem1066062 A) (@lem1066061 A)). Qed.
Lemma lem1066064 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1066065 {A : Type'} : (term20 A) = (term21 A).
Proof. exact (MK_COMB (@lem1066064) (@lem1066063 A)). Qed.
Lemma lem1066067 {A : Type'} : (term5 A) = (@FCONS A).
Proof. exact (EQ_MP (@lem1066043 A) (@lem1066033 A)). Qed.
Lemma lem1066068 {A : Type'} : (term5 A) = (@FCONS A).
Proof. exact (@lem1066067 A). Qed.
Lemma lem1066069 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1066070 {A : Type'} (a : A) : (term6 A a) = (@FCONS A a).
Proof. exact (MK_COMB (@lem1066068 A) (@lem1066069 A a)). Qed.
Lemma lem1066071 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1066072 {A : Type'} (a : A) (f : nat -> A) : (term7 A a f) = (@FCONS A a f).
Proof. exact (MK_COMB (@lem1066070 A a) (@lem1066071 A f)). Qed.
Lemma lem1066073 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem1066074 {A : Type'} (a : A) (f : nat -> A) (n : nat) : (term22 A a f n) = (term23 A a f n).
Proof. exact (MK_COMB (@lem1066072 A a f) (@lem1066073 n)). Qed.
Lemma lem1066075 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1066076 {A : Type'} (a : A) (f : nat -> A) (n : nat) : (term24 A a f n) = (term25 A a f n).
Proof. exact (MK_COMB (@lem1066075 A) (@lem1066074 A a f n)). Qed.
Lemma lem1066077 {A : Type'} (f : nat -> A) (n : nat) : (f n) = (f n).
Proof. exact (eq_refl (f n)). Qed.
Lemma lem1066078 {A : Type'} (a : A) (f : nat -> A) (n : nat) : ((term22 A a f n) = (f n)) = ((term23 A a f n) = (f n)).
Proof. exact (MK_COMB (@lem1066076 A a f n) (@lem1066077 A f n)). Qed.
Lemma lem1066079 {A : Type'} (a : A) (f : nat -> A) : (term26 A a f) = (term27 A a f).
Proof. exact (fun_ext (fun n : nat => @lem1066078 A a f n)). Qed.
Lemma lem1066080 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1066081 {A : Type'} (a : A) (f : nat -> A) : (term28 A a f) = (term29 A a f).
Proof. exact (MK_COMB (@lem1066080) (@lem1066079 A a f)). Qed.
Lemma lem1066082 {A : Type'} (a : A) : (term30 A a) = (term31 A a).
Proof. exact (fun_ext (fun f : nat -> A => @lem1066081 A a f)). Qed.
Lemma lem1066083 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem1066084 {A : Type'} (a : A) : (term32 A a) = (term33 A a).
Proof. exact (MK_COMB (@lem1066083 A) (@lem1066082 A a)). Qed.
Lemma lem1066085 {A : Type'} : (term34 A) = (term35 A).
Proof. exact (fun_ext (fun a : A => @lem1066084 A a)). Qed.
Lemma lem1066086 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1066087 {A : Type'} : (term36 A) = (term37 A).
Proof. exact (MK_COMB (@lem1066086 A) (@lem1066085 A)). Qed.
Lemma lem1066088 {A : Type'} : (term4 A) = (term38 A).
Proof. exact (MK_COMB (@lem1066065 A) (@lem1066087 A)). Qed.
Lemma lem1066089 {A : Type'} : term38 A.
Proof. exact (EQ_MP (@lem1066088 A) (@lem1066038 A)). Qed.
