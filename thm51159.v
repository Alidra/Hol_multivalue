Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm51159_term_abbrevs.
Require Import thm51097_spec.
Require Import thm9396_spec.
Lemma lem51129 {A B : Type'} (_1393 : type1411 A B) : term0 A B _1393.
Proof. exact (@lem51097 A B B _1393). Qed.
Lemma lem51130 {A B : Type'} : term1 A B.
Proof. exact (@lem51129 A B (term2 A B)). Qed.
Lemma lem51131 {A B : Type'} (a0 : A) : (term3 A B a0) = (term4 B).
Proof. exact (eq_refl (term3 A B a0)). Qed.
Lemma lem51132 {B : Type'} (a1 : B) : a1 = a1.
Proof. exact (eq_refl a1). Qed.
Lemma lem51133 {A B : Type'} (a0 : A) (a1 : B) : (term5 A B a0 a1) = (term6 B a1).
Proof. exact (MK_COMB (@lem51131 A B a0) (@lem51132 B a1)). Qed.
Lemma lem51134 {B : Type'} (a1 : B) : (term6 B a1) = a1.
Proof. exact (eq_refl (term6 B a1)). Qed.
Lemma lem51135 {A B : Type'} (a0 : A) (a1 : B) : (term5 A B a0 a1) = a1.
Proof. exact (TRANS (@lem51133 A B a0 a1) (@lem51134 B a1)). Qed.
Lemma lem51136 {A B : Type'} (fn : type1208 A B) (a0 : A) (a1 : B) : (term7 A B fn a0 a1) = (term7 A B fn a0 a1).
Proof. exact (eq_refl (term7 A B fn a0 a1)). Qed.
Lemma lem51137 {A B : Type'} (fn : type1208 A B) (a0 : A) (a1 : B) : ((term8 A B fn a0 a1) = (term5 A B a0 a1)) = ((term8 A B fn a0 a1) = a1).
Proof. exact (MK_COMB (@lem51136 A B fn a0 a1) (@lem51135 A B a0 a1)). Qed.
Lemma lem51138 {A B : Type'} (fn : type1208 A B) (a0 : A) : (term9 A B fn a0) = (term10 A B fn a0).
Proof. exact (fun_ext (fun a1 : B => @lem51137 A B fn a0 a1)). Qed.
Lemma lem51139 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem51140 {A B : Type'} (fn : type1208 A B) (a0 : A) : (term11 A B fn a0) = (term12 A B fn a0).
Proof. exact (MK_COMB (@lem51139 B) (@lem51138 A B fn a0)). Qed.
Lemma lem51141 {A B : Type'} (fn : type1208 A B) : (term13 A B fn) = (term14 A B fn).
Proof. exact (fun_ext (fun a0 : A => @lem51140 A B fn a0)). Qed.
Lemma lem51142 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem51143 {A B : Type'} (fn : type1208 A B) : (term15 A B fn) = (term16 A B fn).
Proof. exact (MK_COMB (@lem51142 A) (@lem51141 A B fn)). Qed.
Lemma lem51144 {A B : Type'} : (term17 A B) = (term18 A B).
Proof. exact (fun_ext (fun fn : type1208 A B => @lem51143 A B fn)). Qed.
Lemma lem51145 {A B : Type'} : (@ex ((prod A B) -> B)) = (@ex ((prod A B) -> B)).
Proof. exact (eq_refl (@ex ((prod A B) -> B))). Qed.
Lemma lem51146 {A B : Type'} : (term1 A B) = (term19 A B).
Proof. exact (MK_COMB (@lem51145 A B) (@lem51144 A B)). Qed.
Lemma lem51147 {A B : Type'} : term19 A B.
Proof. exact (EQ_MP (@lem51146 A B) (@lem51130 A B)). Qed.
Lemma lem51148 {A B : Type'} (P : type317 A B) : term20 A B P.
Proof. exact (@lem9396 (type1208 A B) P). Qed.
Lemma lem51149 {A B : Type'} : term21 A B.
Proof. exact (@lem51148 A B (term18 A B)). Qed.
Lemma lem51150 {A B : Type'} : term22 A B.
Proof. exact (@lem51149 A B (@lem51147 A B)). Qed.
Lemma lem51151 {A B : Type'} : (term22 A B) = (term23 A B).
Proof. exact (eq_refl (term22 A B)). Qed.
Lemma lem51152 {A B : Type'} : term23 A B.
Proof. exact (EQ_MP (@lem51151 A B) (@lem51150 A B)). Qed.
Lemma lem51153 {A B : Type'} (a0 : A) : term24 A B a0.
Proof. exact (@lem51152 A B a0). Qed.
Lemma lem51154 {A B : Type'} (a0 : A) : (term24 A B a0) = (term25 A B a0).
Proof. exact (eq_refl (term24 A B a0)). Qed.
Lemma lem51155 {A B : Type'} (a0 : A) : term25 A B a0.
Proof. exact (EQ_MP (@lem51154 A B a0) (@lem51153 A B a0)). Qed.
Lemma lem51156 {A B : Type'} (a0 : A) (a1 : B) : term26 A B a0 a1.
Proof. exact (@lem51155 A B a0 a1). Qed.
Lemma lem51157 {A B : Type'} (a0 : A) (a1 : B) : (term26 A B a0 a1) = ((term27 A B a0 a1) = a1).
Proof. exact (eq_refl (term26 A B a0 a1)). Qed.
Lemma lem51158 {A B : Type'} (a0 : A) (a1 : B) : (term27 A B a0 a1) = a1.
Proof. exact (EQ_MP (@lem51157 A B a0 a1) (@lem51156 A B a0 a1)). Qed.
Lemma lem51159 {A B : Type'} (a0 : A) (a1 : B) : a1 = (term27 A B a0 a1).
Proof. exact (SYM (@lem51158 A B a0 a1)). Qed.
