Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1240885_term_abbrevs.
Require Import thm1240242_spec.
Require Import thm1240243_spec.
Require Import thm1240294_spec.
Require Import thm1240298_spec.
Require Import thm1240755_spec.
Lemma lem1240756 (P : Ascii.ascii -> Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term0 _22730')) : term1 _22730' char' P.
Proof. exact (@lem1240243 char' _22730' h1 (term2 char' P)). Qed.
Lemma lem1240757 (_22730' : type1539) (char' : type1335) (P : Ascii.ascii -> Prop) : (term1 _22730' char' P) = (term3 _22730' char' P).
Proof. exact (eq_refl (term1 _22730' char' P)). Qed.
Lemma lem1240758 (P : Ascii.ascii -> Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term0 _22730')) : term3 _22730' char' P.
Proof. exact (EQ_MP (@lem1240757 _22730' char' P) (@lem1240756 P char' _22730' h1)). Qed.
Lemma lem1240760 (char' : type1335) (P : Ascii.ascii -> Prop) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term4 char' P _22730' a0 a1 a2 a3 a4 a5 a6 a7) = (term5 char' P _22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (eq_refl (term4 char' P _22730' a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1240761 (a0 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term0 _22730')) : term6 char' _22730' a0.
Proof. exact (@lem1240242 char' _22730' h1 a0). Qed.
Lemma lem1240762 (char' : type1335) (_22730' : type1539) (a0 : Prop) : (term6 char' _22730' a0) = (term7 char' _22730' a0).
Proof. exact (eq_refl (term6 char' _22730' a0)). Qed.
Lemma lem1240763 (a0 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term0 _22730')) : term7 char' _22730' a0.
Proof. exact (EQ_MP (@lem1240762 char' _22730' a0) (@lem1240761 a0 char' _22730' h1)). Qed.
Lemma lem1240764 (a0 : Prop) (a1 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term0 _22730')) : term8 char' _22730' a0 a1.
Proof. exact (@lem1240763 a0 char' _22730' h1 a1). Qed.
Lemma lem1240765 (char' : type1335) (_22730' : type1539) (a0 : Prop) (a1 : Prop) : (term8 char' _22730' a0 a1) = (term9 char' _22730' a0 a1).
Proof. exact (eq_refl (term8 char' _22730' a0 a1)). Qed.
Lemma lem1240766 (a0 : Prop) (a1 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term0 _22730')) : term9 char' _22730' a0 a1.
Proof. exact (EQ_MP (@lem1240765 char' _22730' a0 a1) (@lem1240764 a0 a1 char' _22730' h1)). Qed.
Lemma lem1240767 (a0 : Prop) (a1 : Prop) (a2 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term0 _22730')) : term10 char' _22730' a0 a1 a2.
Proof. exact (@lem1240766 a0 a1 char' _22730' h1 a2). Qed.
Lemma lem1240768 (char' : type1335) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) : (term10 char' _22730' a0 a1 a2) = (term11 char' _22730' a0 a1 a2).
Proof. exact (eq_refl (term10 char' _22730' a0 a1 a2)). Qed.
Lemma lem1240769 (a0 : Prop) (a1 : Prop) (a2 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term0 _22730')) : term11 char' _22730' a0 a1 a2.
Proof. exact (EQ_MP (@lem1240768 char' _22730' a0 a1 a2) (@lem1240767 a0 a1 a2 char' _22730' h1)). Qed.
Lemma lem1240770 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term0 _22730')) : term12 char' _22730' a0 a1 a2 a3.
Proof. exact (@lem1240769 a0 a1 a2 char' _22730' h1 a3). Qed.
Lemma lem1240771 (char' : type1335) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) : (term12 char' _22730' a0 a1 a2 a3) = (term13 char' _22730' a0 a1 a2 a3).
Proof. exact (eq_refl (term12 char' _22730' a0 a1 a2 a3)). Qed.
Lemma lem1240772 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term0 _22730')) : term13 char' _22730' a0 a1 a2 a3.
Proof. exact (EQ_MP (@lem1240771 char' _22730' a0 a1 a2 a3) (@lem1240770 a0 a1 a2 a3 char' _22730' h1)). Qed.
Lemma lem1240773 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term0 _22730')) : term14 char' _22730' a0 a1 a2 a3 a4.
Proof. exact (@lem1240772 a0 a1 a2 a3 char' _22730' h1 a4). Qed.
Lemma lem1240774 (char' : type1335) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) : (term14 char' _22730' a0 a1 a2 a3 a4) = (term15 char' _22730' a0 a1 a2 a3 a4).
Proof. exact (eq_refl (term14 char' _22730' a0 a1 a2 a3 a4)). Qed.
Lemma lem1240775 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term0 _22730')) : term15 char' _22730' a0 a1 a2 a3 a4.
Proof. exact (EQ_MP (@lem1240774 char' _22730' a0 a1 a2 a3 a4) (@lem1240773 a0 a1 a2 a3 a4 char' _22730' h1)). Qed.
Lemma lem1240776 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term0 _22730')) : term16 char' _22730' a0 a1 a2 a3 a4 a5.
Proof. exact (@lem1240775 a0 a1 a2 a3 a4 char' _22730' h1 a5). Qed.
Lemma lem1240777 (char' : type1335) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) : (term16 char' _22730' a0 a1 a2 a3 a4 a5) = (term17 char' _22730' a0 a1 a2 a3 a4 a5).
Proof. exact (eq_refl (term16 char' _22730' a0 a1 a2 a3 a4 a5)). Qed.
Lemma lem1240778 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term0 _22730')) : term17 char' _22730' a0 a1 a2 a3 a4 a5.
Proof. exact (EQ_MP (@lem1240777 char' _22730' a0 a1 a2 a3 a4 a5) (@lem1240776 a0 a1 a2 a3 a4 a5 char' _22730' h1)). Qed.
Lemma lem1240779 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term0 _22730')) : term18 char' _22730' a0 a1 a2 a3 a4 a5 a6.
Proof. exact (@lem1240778 a0 a1 a2 a3 a4 a5 char' _22730' h1 a6). Qed.
Lemma lem1240780 (char' : type1335) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) : (term18 char' _22730' a0 a1 a2 a3 a4 a5 a6) = (term19 char' _22730' a0 a1 a2 a3 a4 a5 a6).
Proof. exact (eq_refl (term18 char' _22730' a0 a1 a2 a3 a4 a5 a6)). Qed.
Lemma lem1240781 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term0 _22730')) : term19 char' _22730' a0 a1 a2 a3 a4 a5 a6.
Proof. exact (EQ_MP (@lem1240780 char' _22730' a0 a1 a2 a3 a4 a5 a6) (@lem1240779 a0 a1 a2 a3 a4 a5 a6 char' _22730' h1)). Qed.
Lemma lem1240782 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term0 _22730')) : term20 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7.
Proof. exact (@lem1240781 a0 a1 a2 a3 a4 a5 a6 char' _22730' h1 a7). Qed.
Lemma lem1240783 (char' : type1335) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term20 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7) = (term21 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (eq_refl (term20 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1240786 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term0 _22730')) : term21 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7.
Proof. exact (EQ_MP (@lem1240783 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7) (@lem1240782 a0 a1 a2 a3 a4 a5 a6 a7 char' _22730' h1)). Qed.
Lemma lem1240788 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1539) (h1 : _22730' = term22) : (term23 _22730' a0 a1 a2 a3 a4 a5 a6 a7) = (_22730 a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (SYM (@lem1240755 a0 a1 a2 a3 a4 a5 a6 a7 _22730' h1)). Qed.
Lemma lem1240789 (P : Ascii.ascii -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1240790 (P : Ascii.ascii -> Prop) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1539) (h1 : _22730' = term22) : (term24 P _22730' a0 a1 a2 a3 a4 a5 a6 a7) = (term25 P a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (MK_COMB (@lem1240789 P) (@lem1240788 a0 a1 a2 a3 a4 a5 a6 a7 _22730' h1)). Qed.
Lemma lem1240791 (char' : type1335) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term26 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7) = (term26 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (eq_refl (term26 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1240792 (char' : type1335) (P : Ascii.ascii -> Prop) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1539) (h1 : _22730' = term22) : (term5 char' P _22730' a0 a1 a2 a3 a4 a5 a6 a7) = (term27 char' _22730' P a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (MK_COMB (@lem1240791 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7) (@lem1240790 P a0 a1 a2 a3 a4 a5 a6 a7 _22730' h1)). Qed.
Lemma lem1240793 (char' : type1335) (P : Ascii.ascii -> Prop) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term28 char' P _22730' a0 a1 a2 a3 a4 a5 a6 a7) = (term28 char' P _22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (eq_refl (term28 char' P _22730' a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1240794 (char' : type1335) (P : Ascii.ascii -> Prop) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1539) (h1 : _22730' = term22) : ((term4 char' P _22730' a0 a1 a2 a3 a4 a5 a6 a7) = (term5 char' P _22730' a0 a1 a2 a3 a4 a5 a6 a7)) = ((term4 char' P _22730' a0 a1 a2 a3 a4 a5 a6 a7) = (term27 char' _22730' P a0 a1 a2 a3 a4 a5 a6 a7)).
Proof. exact (MK_COMB (@lem1240793 char' P _22730' a0 a1 a2 a3 a4 a5 a6 a7) (@lem1240792 char' P a0 a1 a2 a3 a4 a5 a6 a7 _22730' h1)). Qed.
Lemma lem1240795 (char' : type1335) (P : Ascii.ascii -> Prop) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1539) (h1 : _22730' = term22) : (term4 char' P _22730' a0 a1 a2 a3 a4 a5 a6 a7) = (term27 char' _22730' P a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (EQ_MP (@lem1240794 char' P a0 a1 a2 a3 a4 a5 a6 a7 _22730' h1) (@lem1240760 char' P _22730' a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1240796 (P : Ascii.ascii -> Prop) (h1 : term29 P) : term29 P.
Proof. exact (h1). Qed.
Lemma lem1240797 (a0 : Prop) (P : Ascii.ascii -> Prop) (h1 : term29 P) : term30 P a0.
Proof. exact (@lem1240796 P h1 a0). Qed.
Lemma lem1240798 (P : Ascii.ascii -> Prop) (a0 : Prop) : (term30 P a0) = (term31 P a0).
Proof. exact (eq_refl (term30 P a0)). Qed.
Lemma lem1240799 (a0 : Prop) (P : Ascii.ascii -> Prop) (h1 : term29 P) : term31 P a0.
Proof. exact (EQ_MP (@lem1240798 P a0) (@lem1240797 a0 P h1)). Qed.
Lemma lem1240800 (a0 : Prop) (a1 : Prop) (P : Ascii.ascii -> Prop) (h1 : term29 P) : term32 P a0 a1.
Proof. exact (@lem1240799 a0 P h1 a1). Qed.
Lemma lem1240801 (P : Ascii.ascii -> Prop) (a0 : Prop) (a1 : Prop) : (term32 P a0 a1) = (term33 P a0 a1).
Proof. exact (eq_refl (term32 P a0 a1)). Qed.
Lemma lem1240802 (a0 : Prop) (a1 : Prop) (P : Ascii.ascii -> Prop) (h1 : term29 P) : term33 P a0 a1.
Proof. exact (EQ_MP (@lem1240801 P a0 a1) (@lem1240800 a0 a1 P h1)). Qed.
Lemma lem1240803 (a0 : Prop) (a1 : Prop) (a2 : Prop) (P : Ascii.ascii -> Prop) (h1 : term29 P) : term34 P a0 a1 a2.
Proof. exact (@lem1240802 a0 a1 P h1 a2). Qed.
Lemma lem1240804 (P : Ascii.ascii -> Prop) (a0 : Prop) (a1 : Prop) (a2 : Prop) : (term34 P a0 a1 a2) = (term35 P a0 a1 a2).
Proof. exact (eq_refl (term34 P a0 a1 a2)). Qed.
Lemma lem1240805 (a0 : Prop) (a1 : Prop) (a2 : Prop) (P : Ascii.ascii -> Prop) (h1 : term29 P) : term35 P a0 a1 a2.
Proof. exact (EQ_MP (@lem1240804 P a0 a1 a2) (@lem1240803 a0 a1 a2 P h1)). Qed.
Lemma lem1240806 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (P : Ascii.ascii -> Prop) (h1 : term29 P) : term36 P a0 a1 a2 a3.
Proof. exact (@lem1240805 a0 a1 a2 P h1 a3). Qed.
Lemma lem1240807 (P : Ascii.ascii -> Prop) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) : (term36 P a0 a1 a2 a3) = (term37 P a0 a1 a2 a3).
Proof. exact (eq_refl (term36 P a0 a1 a2 a3)). Qed.
Lemma lem1240808 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (P : Ascii.ascii -> Prop) (h1 : term29 P) : term37 P a0 a1 a2 a3.
Proof. exact (EQ_MP (@lem1240807 P a0 a1 a2 a3) (@lem1240806 a0 a1 a2 a3 P h1)). Qed.
Lemma lem1240809 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (P : Ascii.ascii -> Prop) (h1 : term29 P) : term38 P a0 a1 a2 a3 a4.
Proof. exact (@lem1240808 a0 a1 a2 a3 P h1 a4). Qed.
Lemma lem1240810 (P : Ascii.ascii -> Prop) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) : (term38 P a0 a1 a2 a3 a4) = (term39 P a0 a1 a2 a3 a4).
Proof. exact (eq_refl (term38 P a0 a1 a2 a3 a4)). Qed.
Lemma lem1240811 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (P : Ascii.ascii -> Prop) (h1 : term29 P) : term39 P a0 a1 a2 a3 a4.
Proof. exact (EQ_MP (@lem1240810 P a0 a1 a2 a3 a4) (@lem1240809 a0 a1 a2 a3 a4 P h1)). Qed.
Lemma lem1240812 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (P : Ascii.ascii -> Prop) (h1 : term29 P) : term40 P a0 a1 a2 a3 a4 a5.
Proof. exact (@lem1240811 a0 a1 a2 a3 a4 P h1 a5). Qed.
Lemma lem1240813 (P : Ascii.ascii -> Prop) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) : (term40 P a0 a1 a2 a3 a4 a5) = (term41 P a0 a1 a2 a3 a4 a5).
Proof. exact (eq_refl (term40 P a0 a1 a2 a3 a4 a5)). Qed.
Lemma lem1240814 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (P : Ascii.ascii -> Prop) (h1 : term29 P) : term41 P a0 a1 a2 a3 a4 a5.
Proof. exact (EQ_MP (@lem1240813 P a0 a1 a2 a3 a4 a5) (@lem1240812 a0 a1 a2 a3 a4 a5 P h1)). Qed.
Lemma lem1240815 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (P : Ascii.ascii -> Prop) (h1 : term29 P) : term42 P a0 a1 a2 a3 a4 a5 a6.
Proof. exact (@lem1240814 a0 a1 a2 a3 a4 a5 P h1 a6). Qed.
Lemma lem1240816 (P : Ascii.ascii -> Prop) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) : (term42 P a0 a1 a2 a3 a4 a5 a6) = (term43 P a0 a1 a2 a3 a4 a5 a6).
Proof. exact (eq_refl (term42 P a0 a1 a2 a3 a4 a5 a6)). Qed.
Lemma lem1240817 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (P : Ascii.ascii -> Prop) (h1 : term29 P) : term43 P a0 a1 a2 a3 a4 a5 a6.
Proof. exact (EQ_MP (@lem1240816 P a0 a1 a2 a3 a4 a5 a6) (@lem1240815 a0 a1 a2 a3 a4 a5 a6 P h1)). Qed.
Lemma lem1240818 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (P : Ascii.ascii -> Prop) (h1 : term29 P) : term44 P a0 a1 a2 a3 a4 a5 a6 a7.
Proof. exact (@lem1240817 a0 a1 a2 a3 a4 a5 a6 P h1 a7). Qed.
Lemma lem1240819 (P : Ascii.ascii -> Prop) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term44 P a0 a1 a2 a3 a4 a5 a6 a7) = (term25 P a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (eq_refl (term44 P a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1240820 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (P : Ascii.ascii -> Prop) (h1 : term29 P) : term25 P a0 a1 a2 a3 a4 a5 a6 a7.
Proof. exact (EQ_MP (@lem1240819 P a0 a1 a2 a3 a4 a5 a6 a7) (@lem1240818 a0 a1 a2 a3 a4 a5 a6 a7 P h1)). Qed.
Lemma lem1240821 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (P : Ascii.ascii -> Prop) (char' : type1335) (_22730' : type1539) (h1 : term29 P) (h2 : char' = (term0 _22730')) : term27 char' _22730' P a0 a1 a2 a3 a4 a5 a6 a7.
Proof. exact (conj (@lem1240786 a0 a1 a2 a3 a4 a5 a6 a7 char' _22730' h2) (@lem1240820 a0 a1 a2 a3 a4 a5 a6 a7 P h1)). Qed.
Lemma lem1240822 (char' : type1335) (P : Ascii.ascii -> Prop) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1539) (h1 : _22730' = term22) : (term27 char' _22730' P a0 a1 a2 a3 a4 a5 a6 a7) = (term4 char' P _22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (SYM (@lem1240795 char' P a0 a1 a2 a3 a4 a5 a6 a7 _22730' h1)). Qed.
Lemma lem1240823 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (P : Ascii.ascii -> Prop) (char' : type1335) (_22730' : type1539) (h1 : term29 P) (h2 : _22730' = term22) (h3 : char' = (term0 _22730')) : term4 char' P _22730' a0 a1 a2 a3 a4 a5 a6 a7.
Proof. exact (EQ_MP (@lem1240822 char' P a0 a1 a2 a3 a4 a5 a6 a7 _22730' h2) (@lem1240821 a0 a1 a2 a3 a4 a5 a6 a7 P char' _22730' h1 h3)). Qed.
Lemma lem1240824 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (P : Ascii.ascii -> Prop) (char' : type1335) (_22730' : type1539) (h1 : term29 P) (h2 : _22730' = term22) (h3 : char' = (term0 _22730')) : term45 char' P _22730' a0 a1 a2 a3 a4 a5 a6.
Proof. exact (fun a7 : Prop => @lem1240823 a0 a1 a2 a3 a4 a5 a6 a7 P char' _22730' h1 h2 h3). Qed.
Lemma lem1240825 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (P : Ascii.ascii -> Prop) (char' : type1335) (_22730' : type1539) (h1 : term29 P) (h2 : _22730' = term22) (h3 : char' = (term0 _22730')) : term46 char' P _22730' a0 a1 a2 a3 a4 a5.
Proof. exact (fun a6 : Prop => @lem1240824 a0 a1 a2 a3 a4 a5 a6 P char' _22730' h1 h2 h3). Qed.
Lemma lem1240826 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (P : Ascii.ascii -> Prop) (char' : type1335) (_22730' : type1539) (h1 : term29 P) (h2 : _22730' = term22) (h3 : char' = (term0 _22730')) : term47 char' P _22730' a0 a1 a2 a3 a4.
Proof. exact (fun a5 : Prop => @lem1240825 a0 a1 a2 a3 a4 a5 P char' _22730' h1 h2 h3). Qed.
Lemma lem1240827 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (P : Ascii.ascii -> Prop) (char' : type1335) (_22730' : type1539) (h1 : term29 P) (h2 : _22730' = term22) (h3 : char' = (term0 _22730')) : term48 char' P _22730' a0 a1 a2 a3.
Proof. exact (fun a4 : Prop => @lem1240826 a0 a1 a2 a3 a4 P char' _22730' h1 h2 h3). Qed.
Lemma lem1240828 (a0 : Prop) (a1 : Prop) (a2 : Prop) (P : Ascii.ascii -> Prop) (char' : type1335) (_22730' : type1539) (h1 : term29 P) (h2 : _22730' = term22) (h3 : char' = (term0 _22730')) : term49 char' P _22730' a0 a1 a2.
Proof. exact (fun a3 : Prop => @lem1240827 a0 a1 a2 a3 P char' _22730' h1 h2 h3). Qed.
Lemma lem1240829 (a0 : Prop) (a1 : Prop) (P : Ascii.ascii -> Prop) (char' : type1335) (_22730' : type1539) (h1 : term29 P) (h2 : _22730' = term22) (h3 : char' = (term0 _22730')) : term50 char' P _22730' a0 a1.
Proof. exact (fun a2 : Prop => @lem1240828 a0 a1 a2 P char' _22730' h1 h2 h3). Qed.
Lemma lem1240830 (a0 : Prop) (P : Ascii.ascii -> Prop) (char' : type1335) (_22730' : type1539) (h1 : term29 P) (h2 : _22730' = term22) (h3 : char' = (term0 _22730')) : term51 char' P _22730' a0.
Proof. exact (fun a1 : Prop => @lem1240829 a0 a1 P char' _22730' h1 h2 h3). Qed.
Lemma lem1240831 (P : Ascii.ascii -> Prop) (char' : type1335) (_22730' : type1539) (h1 : term29 P) (h2 : _22730' = term22) (h3 : char' = (term0 _22730')) : term52 char' P _22730'.
Proof. exact (fun a0 : Prop => @lem1240830 a0 P char' _22730' h1 h2 h3). Qed.
Lemma lem1240832 (P : Ascii.ascii -> Prop) (char' : type1335) (_22730' : type1539) (h1 : _22730' = term22) (h2 : char' = (term0 _22730')) : term53 char' P _22730'.
Proof. exact (fun h0 : term29 P => @lem1240831 P char' _22730' h0 h1 h2). Qed.
Lemma lem1240833 (P : Ascii.ascii -> Prop) (h1 : term29 P) : term29 P.
Proof. exact (h1). Qed.
Lemma lem1240834 (P : Ascii.ascii -> Prop) (char' : type1335) (_22730' : type1539) (h1 : term29 P) (h2 : _22730' = term22) (h3 : char' = (term0 _22730')) : term52 char' P _22730'.
Proof. exact (@lem1240832 P char' _22730' h2 h3 (@lem1240833 P h1)). Qed.
Lemma lem1240835 (P : Ascii.ascii -> Prop) (char' : type1335) (_22730' : type1539) (h1 : term29 P) (h2 : _22730' = term22) (h3 : char' = (term0 _22730')) : term54 char' P.
Proof. exact (@lem1240758 P char' _22730' h3 (@lem1240834 P char' _22730' h1 h2 h3)). Qed.
Lemma lem1240836 (x : Ascii.ascii) (P : Ascii.ascii -> Prop) (char' : type1335) (_22730' : type1539) (h1 : term29 P) (h2 : _22730' = term22) (h3 : char' = (term0 _22730')) : term55 char' P x.
Proof. exact (@lem1240835 P char' _22730' h1 h2 h3 (_dest_char x)). Qed.
Lemma lem1240837 (char' : type1335) (P : Ascii.ascii -> Prop) (x : Ascii.ascii) : (term55 char' P x) = (term56 char' P x).
Proof. exact (eq_refl (term55 char' P x)). Qed.
Lemma lem1240838 (x : Ascii.ascii) (P : Ascii.ascii -> Prop) (char' : type1335) (_22730' : type1539) (h1 : term29 P) (h2 : _22730' = term22) (h3 : char' = (term0 _22730')) : term56 char' P x.
Proof. exact (EQ_MP (@lem1240837 char' P x) (@lem1240836 x P char' _22730' h1 h2 h3)). Qed.
Lemma lem1240840 (r : type1678) (char' : type1335) (_22730' : type1539) (h1 : _22730' = term22) (h2 : char' = (term0 _22730')) : (char' r) = ((term57 r) = r).
Proof. exact (TRANS (@lem1240298 r char' _22730' h1 h2) (@lem1240294 r)). Qed.
Lemma lem1240841 (x : Ascii.ascii) (char' : type1335) (_22730' : type1539) (h1 : _22730' = term22) (h2 : char' = (term0 _22730')) : (term58 char' x) = ((term59 x) = (_dest_char x)).
Proof. exact (@lem1240840 (_dest_char x) char' _22730' h1 h2). Qed.
Lemma lem1240842 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1240843 (x : Ascii.ascii) (char' : type1335) (_22730' : type1539) (h1 : _22730' = term22) (h2 : char' = (term0 _22730')) : (term60 char' x) = (term61 x).
Proof. exact (MK_COMB (@lem1240842) (@lem1240841 x char' _22730' h1 h2)). Qed.
Lemma lem1240844 (char' : type1335) (P : Ascii.ascii -> Prop) (x : Ascii.ascii) : (term62 char' P x) = (term62 char' P x).
Proof. exact (eq_refl (term62 char' P x)). Qed.
Lemma lem1240845 (P : Ascii.ascii -> Prop) (x : Ascii.ascii) (char' : type1335) (_22730' : type1539) (h1 : _22730' = term22) (h2 : char' = (term0 _22730')) : (term56 char' P x) = (term63 char' P x).
Proof. exact (MK_COMB (@lem1240843 x char' _22730' h1 h2) (@lem1240844 char' P x)). Qed.
Lemma lem1240846 (x : Ascii.ascii) (P : Ascii.ascii -> Prop) (char' : type1335) (_22730' : type1539) (h1 : term29 P) (h2 : _22730' = term22) (h3 : char' = (term0 _22730')) : term63 char' P x.
Proof. exact (EQ_MP (@lem1240845 P x char' _22730' h2 h3) (@lem1240838 x P char' _22730' h1 h2 h3)). Qed.
Lemma lem1240848 (a : Ascii.ascii) : (term64 a) = a.
Proof. exact (@axiom_17 a). Qed.
Lemma lem1240849 (x : Ascii.ascii) : (term64 x) = x.
Proof. exact (@lem1240848 x). Qed.
Lemma lem1240850 : _dest_char = _dest_char.
Proof. exact (eq_refl _dest_char). Qed.
Lemma lem1240851 (x : Ascii.ascii) : (term59 x) = (_dest_char x).
Proof. exact (MK_COMB (@lem1240850) (@lem1240849 x)). Qed.
Lemma lem1240852 : (@eq (recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))))) = (@eq (recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))))).
Proof. exact (eq_refl (@eq (recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))))). Qed.
Lemma lem1240853 (x : Ascii.ascii) : (term65 x) = (term66 x).
Proof. exact (MK_COMB (@lem1240852) (@lem1240851 x)). Qed.
Lemma lem1240854 (x : Ascii.ascii) : (_dest_char x) = (_dest_char x).
Proof. exact (eq_refl (_dest_char x)). Qed.
Lemma lem1240855 (x : Ascii.ascii) : ((term59 x) = (_dest_char x)) = ((_dest_char x) = (_dest_char x)).
Proof. exact (MK_COMB (@lem1240853 x) (@lem1240854 x)). Qed.
Lemma lem1240856 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1240857 (x : Ascii.ascii) : (term61 x) = (term67 x).
Proof. exact (MK_COMB (@lem1240856) (@lem1240855 x)). Qed.
Lemma lem1240858 (char' : type1335) (P : Ascii.ascii -> Prop) (x : Ascii.ascii) : (term62 char' P x) = (term62 char' P x).
Proof. exact (eq_refl (term62 char' P x)). Qed.
Lemma lem1240859 (char' : type1335) (P : Ascii.ascii -> Prop) (x : Ascii.ascii) : (term63 char' P x) = (term68 char' P x).
Proof. exact (MK_COMB (@lem1240857 x) (@lem1240858 char' P x)). Qed.
Lemma lem1240860 (x : Ascii.ascii) (P : Ascii.ascii -> Prop) (char' : type1335) (_22730' : type1539) (h1 : term29 P) (h2 : _22730' = term22) (h3 : char' = (term0 _22730')) : term68 char' P x.
Proof. exact (EQ_MP (@lem1240859 char' P x) (@lem1240846 x P char' _22730' h1 h2 h3)). Qed.
Lemma lem1240861 (x : Ascii.ascii) : (_dest_char x) = (_dest_char x).
Proof. exact (eq_refl (_dest_char x)). Qed.
Lemma lem1240862 (x : Ascii.ascii) (P : Ascii.ascii -> Prop) (char' : type1335) (_22730' : type1539) (h1 : term29 P) (h2 : _22730' = term22) (h3 : char' = (term0 _22730')) : term62 char' P x.
Proof. exact (@lem1240860 x P char' _22730' h1 h2 h3 (@lem1240861 x)). Qed.
Lemma lem1240863 (char' : type1335) (P : Ascii.ascii -> Prop) (x : Ascii.ascii) : (term62 char' P x) = (term69 char' P x).
Proof. exact (eq_refl (term62 char' P x)). Qed.
Lemma lem1240864 (x : Ascii.ascii) (P : Ascii.ascii -> Prop) (char' : type1335) (_22730' : type1539) (h1 : term29 P) (h2 : _22730' = term22) (h3 : char' = (term0 _22730')) : term69 char' P x.
Proof. exact (EQ_MP (@lem1240863 char' P x) (@lem1240862 x P char' _22730' h1 h2 h3)). Qed.
Lemma lem1240865 (x : Ascii.ascii) (P : Ascii.ascii -> Prop) (char' : type1335) (_22730' : type1539) (h1 : term29 P) (h2 : _22730' = term22) (h3 : char' = (term0 _22730')) : term70 P x.
Proof. exact (proj2 (@lem1240864 x P char' _22730' h1 h2 h3)). Qed.
Lemma lem1240867 (a : Ascii.ascii) : (term64 a) = a.
Proof. exact (@axiom_17 a). Qed.
Lemma lem1240868 (x : Ascii.ascii) : (term64 x) = x.
Proof. exact (@lem1240867 x). Qed.
Lemma lem1240869 (P : Ascii.ascii -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1240870 (P : Ascii.ascii -> Prop) (x : Ascii.ascii) : (term70 P x) = (P x).
Proof. exact (MK_COMB (@lem1240869 P) (@lem1240868 x)). Qed.
Lemma lem1240871 (x : Ascii.ascii) (P : Ascii.ascii -> Prop) (char' : type1335) (_22730' : type1539) (h1 : term29 P) (h2 : _22730' = term22) (h3 : char' = (term0 _22730')) : P x.
Proof. exact (EQ_MP (@lem1240870 P x) (@lem1240865 x P char' _22730' h1 h2 h3)). Qed.
Lemma lem1240872 (P : Ascii.ascii -> Prop) (char' : type1335) (_22730' : type1539) (h1 : term29 P) (h2 : _22730' = term22) (h3 : char' = (term0 _22730')) : term71 P.
Proof. exact (fun x : Ascii.ascii => @lem1240871 x P char' _22730' h1 h2 h3). Qed.
Lemma lem1240873 (P : Ascii.ascii -> Prop) (char' : type1335) (_22730' : type1539) (h1 : _22730' = term22) (h2 : char' = (term0 _22730')) : term72 P.
Proof. exact (fun h0 : term29 P => @lem1240872 P char' _22730' h0 h1 h2). Qed.
Lemma lem1240874 (char' : type1335) (_22730' : type1539) (h1 : _22730' = term22) (h2 : char' = (term0 _22730')) : term73.
Proof. exact (fun P : Ascii.ascii -> Prop => @lem1240873 P char' _22730' h1 h2). Qed.
Lemma lem1240875 (char' : type1335) (_22730' : type1539) (h1 : _22730' = term22) : term74 char' _22730'.
Proof. exact (fun h0 : char' = (term0 _22730') => @lem1240874 char' _22730' h1 h0). Qed.
Lemma lem1240876 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1240877 (char' : type1335) (_22730' : type1539) : term75 char' _22730'.
Proof. exact (fun h0 : _22730' = term22 => @lem1240875 char' _22730' h0). Qed.
Lemma lem1240878 (char' : type1335) : term76 char'.
Proof. exact (@lem1240877 char' term22). Qed.
Lemma lem1240879 (char' : type1335) : term77 char'.
Proof. exact (@lem1240878 char' (@lem1240876)). Qed.
Lemma lem1240880 (char' : type1335) (h1 : char' = term78) : char' = term78.
Proof. exact (h1). Qed.
Lemma lem1240881 (char' : type1335) (h1 : char' = term78) : term73.
Proof. exact (@lem1240879 char' (@lem1240880 char' h1)). Qed.
Lemma lem1240882 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem1240883 (char' : type1335) : term77 char'.
Proof. exact (fun h0 : char' = term78 => @lem1240881 char' h0). Qed.
Lemma lem1240884 : term79.
Proof. exact (@lem1240883 term78). Qed.
Lemma lem1240885 : term73.
Proof. exact (@lem1240884 (@lem1240882)). Qed.
