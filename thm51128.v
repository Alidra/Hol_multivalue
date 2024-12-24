Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm51128_term_abbrevs.
Require Import thm51097_spec.
Require Import thm9396_spec.
Lemma lem51098 {A B : Type'} (_1393 : type1410 A B) : term0 A B _1393.
Proof. exact (@lem51097 A B A _1393). Qed.
Lemma lem51099 {A B : Type'} : term1 A B.
Proof. exact (@lem51098 A B (term2 A B)). Qed.
Lemma lem51100 {A B : Type'} (a0 : A) : (term3 A B a0) = (term4 A B a0).
Proof. exact (eq_refl (term3 A B a0)). Qed.
Lemma lem51101 {B : Type'} (a1 : B) : a1 = a1.
Proof. exact (eq_refl a1). Qed.
Lemma lem51102 {A B : Type'} (a0 : A) (a1 : B) : (term5 A B a0 a1) = (term6 A B a0 a1).
Proof. exact (MK_COMB (@lem51100 A B a0) (@lem51101 B a1)). Qed.
Lemma lem51103 {A B : Type'} (a1 : B) (a0 : A) : (term6 A B a0 a1) = a0.
Proof. exact (eq_refl (term6 A B a0 a1)). Qed.
Lemma lem51104 {A B : Type'} (a1 : B) (a0 : A) : (term5 A B a0 a1) = a0.
Proof. exact (TRANS (@lem51102 A B a0 a1) (@lem51103 A B a1 a0)). Qed.
Lemma lem51105 {A B : Type'} (fn : type1207 A B) (a0 : A) (a1 : B) : (term7 A B fn a0 a1) = (term7 A B fn a0 a1).
Proof. exact (eq_refl (term7 A B fn a0 a1)). Qed.
Lemma lem51106 {A B : Type'} (fn : type1207 A B) (a1 : B) (a0 : A) : ((term8 A B fn a0 a1) = (term5 A B a0 a1)) = ((term8 A B fn a0 a1) = a0).
Proof. exact (MK_COMB (@lem51105 A B fn a0 a1) (@lem51104 A B a1 a0)). Qed.
Lemma lem51107 {A B : Type'} (fn : type1207 A B) (a0 : A) : (term9 A B fn a0) = (term10 A B fn a0).
Proof. exact (fun_ext (fun a1 : B => @lem51106 A B fn a1 a0)). Qed.
Lemma lem51108 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem51109 {A B : Type'} (fn : type1207 A B) (a0 : A) : (term11 A B fn a0) = (term12 A B fn a0).
Proof. exact (MK_COMB (@lem51108 B) (@lem51107 A B fn a0)). Qed.
Lemma lem51110 {A B : Type'} (fn : type1207 A B) : (term13 A B fn) = (term14 A B fn).
Proof. exact (fun_ext (fun a0 : A => @lem51109 A B fn a0)). Qed.
Lemma lem51111 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem51112 {A B : Type'} (fn : type1207 A B) : (term15 A B fn) = (term16 A B fn).
Proof. exact (MK_COMB (@lem51111 A) (@lem51110 A B fn)). Qed.
Lemma lem51113 {A B : Type'} : (term17 A B) = (term18 A B).
Proof. exact (fun_ext (fun fn : type1207 A B => @lem51112 A B fn)). Qed.
Lemma lem51114 {A B : Type'} : (@ex ((prod A B) -> A)) = (@ex ((prod A B) -> A)).
Proof. exact (eq_refl (@ex ((prod A B) -> A))). Qed.
Lemma lem51115 {A B : Type'} : (term1 A B) = (term19 A B).
Proof. exact (MK_COMB (@lem51114 A B) (@lem51113 A B)). Qed.
Lemma lem51116 {A B : Type'} : term19 A B.
Proof. exact (EQ_MP (@lem51115 A B) (@lem51099 A B)). Qed.
Lemma lem51117 {A B : Type'} (P : type316 A B) : term20 A B P.
Proof. exact (@lem9396 (type1207 A B) P). Qed.
Lemma lem51118 {A B : Type'} : term21 A B.
Proof. exact (@lem51117 A B (term18 A B)). Qed.
Lemma lem51119 {A B : Type'} : term22 A B.
Proof. exact (@lem51118 A B (@lem51116 A B)). Qed.
Lemma lem51120 {A B : Type'} : (term22 A B) = (term23 A B).
Proof. exact (eq_refl (term22 A B)). Qed.
Lemma lem51121 {A B : Type'} : term23 A B.
Proof. exact (EQ_MP (@lem51120 A B) (@lem51119 A B)). Qed.
Lemma lem51122 {A B : Type'} (a0 : A) : term24 A B a0.
Proof. exact (@lem51121 A B a0). Qed.
Lemma lem51123 {A B : Type'} (a0 : A) : (term24 A B a0) = (term25 A B a0).
Proof. exact (eq_refl (term24 A B a0)). Qed.
Lemma lem51124 {A B : Type'} (a0 : A) : term25 A B a0.
Proof. exact (EQ_MP (@lem51123 A B a0) (@lem51122 A B a0)). Qed.
Lemma lem51125 {A B : Type'} (a0 : A) (a1 : B) : term26 A B a0 a1.
Proof. exact (@lem51124 A B a0 a1). Qed.
Lemma lem51126 {A B : Type'} (a1 : B) (a0 : A) : (term26 A B a0 a1) = ((term27 A B a0 a1) = a0).
Proof. exact (eq_refl (term26 A B a0 a1)). Qed.
Lemma lem51127 {A B : Type'} (a1 : B) (a0 : A) : (term27 A B a0 a1) = a0.
Proof. exact (EQ_MP (@lem51126 A B a1 a0) (@lem51125 A B a0 a1)). Qed.
Lemma lem51128 {A B : Type'} (a0 : A) (a1 : B) : a0 = (term27 A B a0 a1).
Proof. exact (SYM (@lem51127 A B a1 a0)). Qed.
