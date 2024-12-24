Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1241957_term_abbrevs.
Require Import CONSTR_REC_spec.
Require Import FST_spec.
Require Import SND_spec.
Require Import thm1066568_spec.
Require Import thm1066569_spec.
Require Import thm1240242_spec.
Require Import thm1240294_spec.
Require Import thm1240298_spec.
Require Import thm1240755_spec.
Require Import thm9102_spec.
Lemma lem1240886 {Z : Type'} (fn : Ascii.ascii -> Z) (fn' : type1334 Z) (h1 : fn = (term0 Z fn')) : fn = (term0 Z fn').
Proof. exact (h1). Qed.
Lemma lem1240887 {Z : Type'} (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1539) (fn : Ascii.ascii -> Z) (fn' : type1334 Z) (h1 : _22730' = term1) (h2 : fn = (term0 Z fn')) : (term2 Z fn a0 a1 a2 a3 a4 a5 a6 a7) = (term3 Z fn' _22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (MK_COMB (@lem1240886 Z fn fn' h2) (@lem1240755 a0 a1 a2 a3 a4 a5 a6 a7 _22730' h1)). Qed.
Lemma lem1240888 {Z : Type'} (fn : type1334 Z) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term3 Z fn _22730' a0 a1 a2 a3 a4 a5 a6 a7) = (term4 Z fn _22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (eq_refl (term3 Z fn _22730' a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1240889 {Z : Type'} (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1539) (fn : Ascii.ascii -> Z) (fn' : type1334 Z) (h1 : _22730' = term1) (h2 : fn = (term0 Z fn')) : (term2 Z fn a0 a1 a2 a3 a4 a5 a6 a7) = (term4 Z fn' _22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (TRANS (@lem1240887 Z a0 a1 a2 a3 a4 a5 a6 a7 _22730' fn fn' h1 h2) (@lem1240888 Z fn' _22730' a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1240897 (a0 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term5 _22730')) : term6 char' _22730' a0.
Proof. exact (@lem1240242 char' _22730' h1 a0). Qed.
Lemma lem1240898 (char' : type1335) (_22730' : type1539) (a0 : Prop) : (term6 char' _22730' a0) = (term7 char' _22730' a0).
Proof. exact (eq_refl (term6 char' _22730' a0)). Qed.
Lemma lem1240899 (a0 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term5 _22730')) : term7 char' _22730' a0.
Proof. exact (EQ_MP (@lem1240898 char' _22730' a0) (@lem1240897 a0 char' _22730' h1)). Qed.
Lemma lem1240900 (a0 : Prop) (a1 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term5 _22730')) : term8 char' _22730' a0 a1.
Proof. exact (@lem1240899 a0 char' _22730' h1 a1). Qed.
Lemma lem1240901 (char' : type1335) (_22730' : type1539) (a0 : Prop) (a1 : Prop) : (term8 char' _22730' a0 a1) = (term9 char' _22730' a0 a1).
Proof. exact (eq_refl (term8 char' _22730' a0 a1)). Qed.
Lemma lem1240902 (a0 : Prop) (a1 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term5 _22730')) : term9 char' _22730' a0 a1.
Proof. exact (EQ_MP (@lem1240901 char' _22730' a0 a1) (@lem1240900 a0 a1 char' _22730' h1)). Qed.
Lemma lem1240903 (a0 : Prop) (a1 : Prop) (a2 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term5 _22730')) : term10 char' _22730' a0 a1 a2.
Proof. exact (@lem1240902 a0 a1 char' _22730' h1 a2). Qed.
Lemma lem1240904 (char' : type1335) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) : (term10 char' _22730' a0 a1 a2) = (term11 char' _22730' a0 a1 a2).
Proof. exact (eq_refl (term10 char' _22730' a0 a1 a2)). Qed.
Lemma lem1240905 (a0 : Prop) (a1 : Prop) (a2 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term5 _22730')) : term11 char' _22730' a0 a1 a2.
Proof. exact (EQ_MP (@lem1240904 char' _22730' a0 a1 a2) (@lem1240903 a0 a1 a2 char' _22730' h1)). Qed.
Lemma lem1240906 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term5 _22730')) : term12 char' _22730' a0 a1 a2 a3.
Proof. exact (@lem1240905 a0 a1 a2 char' _22730' h1 a3). Qed.
Lemma lem1240907 (char' : type1335) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) : (term12 char' _22730' a0 a1 a2 a3) = (term13 char' _22730' a0 a1 a2 a3).
Proof. exact (eq_refl (term12 char' _22730' a0 a1 a2 a3)). Qed.
Lemma lem1240908 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term5 _22730')) : term13 char' _22730' a0 a1 a2 a3.
Proof. exact (EQ_MP (@lem1240907 char' _22730' a0 a1 a2 a3) (@lem1240906 a0 a1 a2 a3 char' _22730' h1)). Qed.
Lemma lem1240909 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term5 _22730')) : term14 char' _22730' a0 a1 a2 a3 a4.
Proof. exact (@lem1240908 a0 a1 a2 a3 char' _22730' h1 a4). Qed.
Lemma lem1240910 (char' : type1335) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) : (term14 char' _22730' a0 a1 a2 a3 a4) = (term15 char' _22730' a0 a1 a2 a3 a4).
Proof. exact (eq_refl (term14 char' _22730' a0 a1 a2 a3 a4)). Qed.
Lemma lem1240911 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term5 _22730')) : term15 char' _22730' a0 a1 a2 a3 a4.
Proof. exact (EQ_MP (@lem1240910 char' _22730' a0 a1 a2 a3 a4) (@lem1240909 a0 a1 a2 a3 a4 char' _22730' h1)). Qed.
Lemma lem1240912 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term5 _22730')) : term16 char' _22730' a0 a1 a2 a3 a4 a5.
Proof. exact (@lem1240911 a0 a1 a2 a3 a4 char' _22730' h1 a5). Qed.
Lemma lem1240913 (char' : type1335) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) : (term16 char' _22730' a0 a1 a2 a3 a4 a5) = (term17 char' _22730' a0 a1 a2 a3 a4 a5).
Proof. exact (eq_refl (term16 char' _22730' a0 a1 a2 a3 a4 a5)). Qed.
Lemma lem1240914 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term5 _22730')) : term17 char' _22730' a0 a1 a2 a3 a4 a5.
Proof. exact (EQ_MP (@lem1240913 char' _22730' a0 a1 a2 a3 a4 a5) (@lem1240912 a0 a1 a2 a3 a4 a5 char' _22730' h1)). Qed.
Lemma lem1240915 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term5 _22730')) : term18 char' _22730' a0 a1 a2 a3 a4 a5 a6.
Proof. exact (@lem1240914 a0 a1 a2 a3 a4 a5 char' _22730' h1 a6). Qed.
Lemma lem1240916 (char' : type1335) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) : (term18 char' _22730' a0 a1 a2 a3 a4 a5 a6) = (term19 char' _22730' a0 a1 a2 a3 a4 a5 a6).
Proof. exact (eq_refl (term18 char' _22730' a0 a1 a2 a3 a4 a5 a6)). Qed.
Lemma lem1240917 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term5 _22730')) : term19 char' _22730' a0 a1 a2 a3 a4 a5 a6.
Proof. exact (EQ_MP (@lem1240916 char' _22730' a0 a1 a2 a3 a4 a5 a6) (@lem1240915 a0 a1 a2 a3 a4 a5 a6 char' _22730' h1)). Qed.
Lemma lem1240918 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term5 _22730')) : term20 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7.
Proof. exact (@lem1240917 a0 a1 a2 a3 a4 a5 a6 char' _22730' h1 a7). Qed.
Lemma lem1240919 (char' : type1335) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term20 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7) = (term21 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (eq_refl (term20 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1240922 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term5 _22730')) : term21 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7.
Proof. exact (EQ_MP (@lem1240919 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7) (@lem1240918 a0 a1 a2 a3 a4 a5 a6 a7 char' _22730' h1)). Qed.
Lemma lem1240924 (r : type1678) (char' : type1335) (_22730' : type1539) (h1 : _22730' = term1) (h2 : char' = (term5 _22730')) : (char' r) = ((term22 r) = r).
Proof. exact (TRANS (@lem1240298 r char' _22730' h1 h2) (@lem1240294 r)). Qed.
Lemma lem1240925 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (char' : type1335) (_22730' : type1539) (h1 : _22730' = term1) (h2 : char' = (term5 _22730')) : (term21 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7) = ((term23 _22730' a0 a1 a2 a3 a4 a5 a6 a7) = (_22730' a0 a1 a2 a3 a4 a5 a6 a7)).
Proof. exact (@lem1240924 (_22730' a0 a1 a2 a3 a4 a5 a6 a7) char' _22730' h1 h2). Qed.
Lemma lem1240926 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (char' : type1335) (_22730' : type1539) (h1 : _22730' = term1) (h2 : char' = (term5 _22730')) : (term23 _22730' a0 a1 a2 a3 a4 a5 a6 a7) = (_22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (EQ_MP (@lem1240925 a0 a1 a2 a3 a4 a5 a6 a7 char' _22730' h1 h2) (@lem1240922 a0 a1 a2 a3 a4 a5 a6 a7 char' _22730' h2)). Qed.
Lemma lem1240927 {Z : Type'} (fn : type1334 Z) : fn = fn.
Proof. exact (eq_refl fn). Qed.
Lemma lem1240928 {Z : Type'} (fn : type1334 Z) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (char' : type1335) (_22730' : type1539) (h1 : _22730' = term1) (h2 : char' = (term5 _22730')) : (term4 Z fn _22730' a0 a1 a2 a3 a4 a5 a6 a7) = (term24 Z fn _22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (MK_COMB (@lem1240927 Z fn) (@lem1240926 a0 a1 a2 a3 a4 a5 a6 a7 char' _22730' h1 h2)). Qed.
Lemma lem1240929 {Z : Type'} (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (fn : Ascii.ascii -> Z) (fn' : type1334 Z) (char' : type1335) (_22730' : type1539) (h1 : _22730' = term1) (h2 : fn = (term0 Z fn')) (h3 : char' = (term5 _22730')) : (term2 Z fn a0 a1 a2 a3 a4 a5 a6 a7) = (term24 Z fn' _22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (TRANS (@lem1240889 Z a0 a1 a2 a3 a4 a5 a6 a7 _22730' fn fn' h1 h2) (@lem1240928 Z fn' a0 a1 a2 a3 a4 a5 a6 a7 char' _22730' h1 h3)). Qed.
Lemma lem1240930 (_22730' : type1539) (h1 : _22730' = term1) : _22730' = term1.
Proof. exact (h1). Qed.
Lemma lem1240931 (a0 : Prop) : a0 = a0.
Proof. exact (eq_refl a0). Qed.
Lemma lem1240932 (a0 : Prop) (_22730' : type1539) (h1 : _22730' = term1) : (_22730' a0) = (term25 a0).
Proof. exact (MK_COMB (@lem1240930 _22730' h1) (@lem1240931 a0)). Qed.
Lemma lem1240933 (a0 : Prop) : (term25 a0) = (term26 a0).
Proof. exact (eq_refl (term25 a0)). Qed.
Lemma lem1240934 (_22730' : type1539) (a0 : Prop) : (term27 _22730' a0) = (term27 _22730' a0).
Proof. exact (eq_refl (term27 _22730' a0)). Qed.
Lemma lem1240935 (_22730' : type1539) (a0 : Prop) : ((_22730' a0) = (term25 a0)) = ((_22730' a0) = (term26 a0)).
Proof. exact (MK_COMB (@lem1240934 _22730' a0) (@lem1240933 a0)). Qed.
Lemma lem1240936 (a0 : Prop) (_22730' : type1539) (h1 : _22730' = term1) : (_22730' a0) = (term26 a0).
Proof. exact (EQ_MP (@lem1240935 _22730' a0) (@lem1240932 a0 _22730' h1)). Qed.
Lemma lem1240937 (a1 : Prop) : a1 = a1.
Proof. exact (eq_refl a1). Qed.
Lemma lem1240938 (a0 : Prop) (a1 : Prop) (_22730' : type1539) (h1 : _22730' = term1) : (_22730' a0 a1) = (term28 a0 a1).
Proof. exact (MK_COMB (@lem1240936 a0 _22730' h1) (@lem1240937 a1)). Qed.
Lemma lem1240939 (a0 : Prop) (a1 : Prop) : (term28 a0 a1) = (term29 a0 a1).
Proof. exact (eq_refl (term28 a0 a1)). Qed.
Lemma lem1240940 (_22730' : type1539) (a0 : Prop) (a1 : Prop) : (term30 _22730' a0 a1) = (term30 _22730' a0 a1).
Proof. exact (eq_refl (term30 _22730' a0 a1)). Qed.
Lemma lem1240941 (_22730' : type1539) (a0 : Prop) (a1 : Prop) : ((_22730' a0 a1) = (term28 a0 a1)) = ((_22730' a0 a1) = (term29 a0 a1)).
Proof. exact (MK_COMB (@lem1240940 _22730' a0 a1) (@lem1240939 a0 a1)). Qed.
Lemma lem1240942 (a0 : Prop) (a1 : Prop) (_22730' : type1539) (h1 : _22730' = term1) : (_22730' a0 a1) = (term29 a0 a1).
Proof. exact (EQ_MP (@lem1240941 _22730' a0 a1) (@lem1240938 a0 a1 _22730' h1)). Qed.
Lemma lem1240943 (a2 : Prop) : a2 = a2.
Proof. exact (eq_refl a2). Qed.
Lemma lem1240944 (a0 : Prop) (a1 : Prop) (a2 : Prop) (_22730' : type1539) (h1 : _22730' = term1) : (_22730' a0 a1 a2) = (term31 a0 a1 a2).
Proof. exact (MK_COMB (@lem1240942 a0 a1 _22730' h1) (@lem1240943 a2)). Qed.
Lemma lem1240945 (a0 : Prop) (a1 : Prop) (a2 : Prop) : (term31 a0 a1 a2) = (term32 a0 a1 a2).
Proof. exact (eq_refl (term31 a0 a1 a2)). Qed.
Lemma lem1240946 (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) : (term33 _22730' a0 a1 a2) = (term33 _22730' a0 a1 a2).
Proof. exact (eq_refl (term33 _22730' a0 a1 a2)). Qed.
Lemma lem1240947 (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) : ((_22730' a0 a1 a2) = (term31 a0 a1 a2)) = ((_22730' a0 a1 a2) = (term32 a0 a1 a2)).
Proof. exact (MK_COMB (@lem1240946 _22730' a0 a1 a2) (@lem1240945 a0 a1 a2)). Qed.
Lemma lem1240948 (a0 : Prop) (a1 : Prop) (a2 : Prop) (_22730' : type1539) (h1 : _22730' = term1) : (_22730' a0 a1 a2) = (term32 a0 a1 a2).
Proof. exact (EQ_MP (@lem1240947 _22730' a0 a1 a2) (@lem1240944 a0 a1 a2 _22730' h1)). Qed.
Lemma lem1240949 (a3 : Prop) : a3 = a3.
Proof. exact (eq_refl a3). Qed.
Lemma lem1240950 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (_22730' : type1539) (h1 : _22730' = term1) : (_22730' a0 a1 a2 a3) = (term34 a0 a1 a2 a3).
Proof. exact (MK_COMB (@lem1240948 a0 a1 a2 _22730' h1) (@lem1240949 a3)). Qed.
Lemma lem1240951 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) : (term34 a0 a1 a2 a3) = (term35 a0 a1 a2 a3).
Proof. exact (eq_refl (term34 a0 a1 a2 a3)). Qed.
Lemma lem1240952 (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) : (term36 _22730' a0 a1 a2 a3) = (term36 _22730' a0 a1 a2 a3).
Proof. exact (eq_refl (term36 _22730' a0 a1 a2 a3)). Qed.
Lemma lem1240953 (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) : ((_22730' a0 a1 a2 a3) = (term34 a0 a1 a2 a3)) = ((_22730' a0 a1 a2 a3) = (term35 a0 a1 a2 a3)).
Proof. exact (MK_COMB (@lem1240952 _22730' a0 a1 a2 a3) (@lem1240951 a0 a1 a2 a3)). Qed.
Lemma lem1240954 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (_22730' : type1539) (h1 : _22730' = term1) : (_22730' a0 a1 a2 a3) = (term35 a0 a1 a2 a3).
Proof. exact (EQ_MP (@lem1240953 _22730' a0 a1 a2 a3) (@lem1240950 a0 a1 a2 a3 _22730' h1)). Qed.
Lemma lem1240955 (a4 : Prop) : a4 = a4.
Proof. exact (eq_refl a4). Qed.
Lemma lem1240956 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (_22730' : type1539) (h1 : _22730' = term1) : (_22730' a0 a1 a2 a3 a4) = (term37 a0 a1 a2 a3 a4).
Proof. exact (MK_COMB (@lem1240954 a0 a1 a2 a3 _22730' h1) (@lem1240955 a4)). Qed.
Lemma lem1240957 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) : (term37 a0 a1 a2 a3 a4) = (term38 a0 a1 a2 a3 a4).
Proof. exact (eq_refl (term37 a0 a1 a2 a3 a4)). Qed.
Lemma lem1240958 (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) : (term39 _22730' a0 a1 a2 a3 a4) = (term39 _22730' a0 a1 a2 a3 a4).
Proof. exact (eq_refl (term39 _22730' a0 a1 a2 a3 a4)). Qed.
Lemma lem1240959 (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) : ((_22730' a0 a1 a2 a3 a4) = (term37 a0 a1 a2 a3 a4)) = ((_22730' a0 a1 a2 a3 a4) = (term38 a0 a1 a2 a3 a4)).
Proof. exact (MK_COMB (@lem1240958 _22730' a0 a1 a2 a3 a4) (@lem1240957 a0 a1 a2 a3 a4)). Qed.
Lemma lem1240960 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (_22730' : type1539) (h1 : _22730' = term1) : (_22730' a0 a1 a2 a3 a4) = (term38 a0 a1 a2 a3 a4).
Proof. exact (EQ_MP (@lem1240959 _22730' a0 a1 a2 a3 a4) (@lem1240956 a0 a1 a2 a3 a4 _22730' h1)). Qed.
Lemma lem1240961 (a5 : Prop) : a5 = a5.
Proof. exact (eq_refl a5). Qed.
Lemma lem1240962 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (_22730' : type1539) (h1 : _22730' = term1) : (_22730' a0 a1 a2 a3 a4 a5) = (term40 a0 a1 a2 a3 a4 a5).
Proof. exact (MK_COMB (@lem1240960 a0 a1 a2 a3 a4 _22730' h1) (@lem1240961 a5)). Qed.
Lemma lem1240963 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) : (term40 a0 a1 a2 a3 a4 a5) = (term41 a0 a1 a2 a3 a4 a5).
Proof. exact (eq_refl (term40 a0 a1 a2 a3 a4 a5)). Qed.
Lemma lem1240964 (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) : (term42 _22730' a0 a1 a2 a3 a4 a5) = (term42 _22730' a0 a1 a2 a3 a4 a5).
Proof. exact (eq_refl (term42 _22730' a0 a1 a2 a3 a4 a5)). Qed.
Lemma lem1240965 (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) : ((_22730' a0 a1 a2 a3 a4 a5) = (term40 a0 a1 a2 a3 a4 a5)) = ((_22730' a0 a1 a2 a3 a4 a5) = (term41 a0 a1 a2 a3 a4 a5)).
Proof. exact (MK_COMB (@lem1240964 _22730' a0 a1 a2 a3 a4 a5) (@lem1240963 a0 a1 a2 a3 a4 a5)). Qed.
Lemma lem1240966 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (_22730' : type1539) (h1 : _22730' = term1) : (_22730' a0 a1 a2 a3 a4 a5) = (term41 a0 a1 a2 a3 a4 a5).
Proof. exact (EQ_MP (@lem1240965 _22730' a0 a1 a2 a3 a4 a5) (@lem1240962 a0 a1 a2 a3 a4 a5 _22730' h1)). Qed.
Lemma lem1240967 (a6 : Prop) : a6 = a6.
Proof. exact (eq_refl a6). Qed.
Lemma lem1240968 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (_22730' : type1539) (h1 : _22730' = term1) : (_22730' a0 a1 a2 a3 a4 a5 a6) = (term43 a0 a1 a2 a3 a4 a5 a6).
Proof. exact (MK_COMB (@lem1240966 a0 a1 a2 a3 a4 a5 _22730' h1) (@lem1240967 a6)). Qed.
Lemma lem1240969 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) : (term43 a0 a1 a2 a3 a4 a5 a6) = (term44 a0 a1 a2 a3 a4 a5 a6).
Proof. exact (eq_refl (term43 a0 a1 a2 a3 a4 a5 a6)). Qed.
Lemma lem1240970 (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) : (term45 _22730' a0 a1 a2 a3 a4 a5 a6) = (term45 _22730' a0 a1 a2 a3 a4 a5 a6).
Proof. exact (eq_refl (term45 _22730' a0 a1 a2 a3 a4 a5 a6)). Qed.
Lemma lem1240971 (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) : ((_22730' a0 a1 a2 a3 a4 a5 a6) = (term43 a0 a1 a2 a3 a4 a5 a6)) = ((_22730' a0 a1 a2 a3 a4 a5 a6) = (term44 a0 a1 a2 a3 a4 a5 a6)).
Proof. exact (MK_COMB (@lem1240970 _22730' a0 a1 a2 a3 a4 a5 a6) (@lem1240969 a0 a1 a2 a3 a4 a5 a6)). Qed.
Lemma lem1240972 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (_22730' : type1539) (h1 : _22730' = term1) : (_22730' a0 a1 a2 a3 a4 a5 a6) = (term44 a0 a1 a2 a3 a4 a5 a6).
Proof. exact (EQ_MP (@lem1240971 _22730' a0 a1 a2 a3 a4 a5 a6) (@lem1240968 a0 a1 a2 a3 a4 a5 a6 _22730' h1)). Qed.
Lemma lem1240973 (a7 : Prop) : a7 = a7.
Proof. exact (eq_refl a7). Qed.
Lemma lem1240974 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1539) (h1 : _22730' = term1) : (_22730' a0 a1 a2 a3 a4 a5 a6 a7) = (term46 a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (MK_COMB (@lem1240972 a0 a1 a2 a3 a4 a5 a6 _22730' h1) (@lem1240973 a7)). Qed.
Lemma lem1240975 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term46 a0 a1 a2 a3 a4 a5 a6 a7) = (term47 a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (eq_refl (term46 a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1240976 (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term48 _22730' a0 a1 a2 a3 a4 a5 a6 a7) = (term48 _22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (eq_refl (term48 _22730' a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1240977 (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : ((_22730' a0 a1 a2 a3 a4 a5 a6 a7) = (term46 a0 a1 a2 a3 a4 a5 a6 a7)) = ((_22730' a0 a1 a2 a3 a4 a5 a6 a7) = (term47 a0 a1 a2 a3 a4 a5 a6 a7)).
Proof. exact (MK_COMB (@lem1240976 _22730' a0 a1 a2 a3 a4 a5 a6 a7) (@lem1240975 a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1240978 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1539) (h1 : _22730' = term1) : (_22730' a0 a1 a2 a3 a4 a5 a6 a7) = (term47 a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (EQ_MP (@lem1240977 _22730' a0 a1 a2 a3 a4 a5 a6 a7) (@lem1240974 a0 a1 a2 a3 a4 a5 a6 a7 _22730' h1)). Qed.
Lemma lem1240979 {Z : Type'} (fn : type1334 Z) : fn = fn.
Proof. exact (eq_refl fn). Qed.
Lemma lem1240980 {Z : Type'} (fn : type1334 Z) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1539) (h1 : _22730' = term1) : (term24 Z fn _22730' a0 a1 a2 a3 a4 a5 a6 a7) = (term49 Z fn a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (MK_COMB (@lem1240979 Z fn) (@lem1240978 a0 a1 a2 a3 a4 a5 a6 a7 _22730' h1)). Qed.
Lemma lem1240981 {Z : Type'} (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (fn : Ascii.ascii -> Z) (fn' : type1334 Z) (char' : type1335) (_22730' : type1539) (h1 : _22730' = term1) (h2 : fn = (term0 Z fn')) (h3 : char' = (term5 _22730')) : (term2 Z fn a0 a1 a2 a3 a4 a5 a6 a7) = (term49 Z fn' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (TRANS (@lem1240929 Z a0 a1 a2 a3 a4 a5 a6 a7 fn fn' char' _22730' h1 h2 h3) (@lem1240980 Z fn' a0 a1 a2 a3 a4 a5 a6 a7 _22730' h1)). Qed.
Lemma lem1240982 {Z : Type'} (char' : type1335) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1539) (fn : Ascii.ascii -> Z) (fn' : type1334 Z) (h1 : _22730' = term1) (h2 : fn = (term0 Z fn')) : term50 Z char' _22730' fn fn' a0 a1 a2 a3 a4 a5 a6 a7.
Proof. exact (fun h0 : char' = (term5 _22730') => @lem1240981 Z a0 a1 a2 a3 a4 a5 a6 a7 fn fn' char' _22730' h1 h2 h0). Qed.
Lemma lem1240983 : term1 = term1.
Proof. exact (eq_refl term1). Qed.
Lemma lem1240984 {Z : Type'} (char' : type1335) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (fn : Ascii.ascii -> Z) (fn' : type1334 Z) (h1 : fn = (term0 Z fn')) : term51 Z char' _22730' fn fn' a0 a1 a2 a3 a4 a5 a6 a7.
Proof. exact (fun h0 : _22730' = term1 => @lem1240982 Z char' a0 a1 a2 a3 a4 a5 a6 a7 _22730' fn fn' h0 h1). Qed.
Lemma lem1240985 {Z : Type'} (char' : type1335) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (fn : Ascii.ascii -> Z) (fn' : type1334 Z) (h1 : fn = (term0 Z fn')) : term52 Z char' fn fn' a0 a1 a2 a3 a4 a5 a6 a7.
Proof. exact (@lem1240984 Z char' term1 a0 a1 a2 a3 a4 a5 a6 a7 fn fn' h1). Qed.
Lemma lem1240986 {Z : Type'} (char' : type1335) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (fn : Ascii.ascii -> Z) (fn' : type1334 Z) (h1 : fn = (term0 Z fn')) : term53 Z char' fn fn' a0 a1 a2 a3 a4 a5 a6 a7.
Proof. exact (@lem1240985 Z char' a0 a1 a2 a3 a4 a5 a6 a7 fn fn' h1 (@lem1240983)). Qed.
Lemma lem1240987 (char' : type1335) (h1 : char' = term54) : char' = term54.
Proof. exact (h1). Qed.
Lemma lem1240988 {Z : Type'} (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (fn : Ascii.ascii -> Z) (fn' : type1334 Z) (char' : type1335) (h1 : fn = (term0 Z fn')) (h2 : char' = term54) : (term2 Z fn a0 a1 a2 a3 a4 a5 a6 a7) = (term49 Z fn' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (@lem1240986 Z char' a0 a1 a2 a3 a4 a5 a6 a7 fn fn' h1 (@lem1240987 char' h2)). Qed.
Lemma lem1240989 : term54 = term54.
Proof. exact (eq_refl term54). Qed.
Lemma lem1240990 {Z : Type'} (char' : type1335) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (fn : Ascii.ascii -> Z) (fn' : type1334 Z) (h1 : fn = (term0 Z fn')) : term53 Z char' fn fn' a0 a1 a2 a3 a4 a5 a6 a7.
Proof. exact (fun h0 : char' = term54 => @lem1240988 Z a0 a1 a2 a3 a4 a5 a6 a7 fn fn' char' h1 h0). Qed.
Lemma lem1240991 {Z : Type'} (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (fn : Ascii.ascii -> Z) (fn' : type1334 Z) (h1 : fn = (term0 Z fn')) : term55 Z fn fn' a0 a1 a2 a3 a4 a5 a6 a7.
Proof. exact (@lem1240990 Z term54 a0 a1 a2 a3 a4 a5 a6 a7 fn fn' h1). Qed.
Lemma lem1240992 {Z : Type'} (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (fn : Ascii.ascii -> Z) (fn' : type1334 Z) (h1 : fn = (term0 Z fn')) : (term2 Z fn a0 a1 a2 a3 a4 a5 a6 a7) = (term49 Z fn' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (@lem1240991 Z a0 a1 a2 a3 a4 a5 a6 a7 fn fn' h1 (@lem1240989)). Qed.
Lemma lem1241616 {Z : Type'} : term56 Z.
Proof. exact (@lem1065430 type1661 Z). Qed.
Lemma lem1241617 {Z : Type'} (_22730' : type1540 Z) : term57 Z _22730'.
Proof. exact (@lem1241616 Z (term58 Z _22730')). Qed.
Lemma lem1241618 {Z : Type'} (_22730' : type1540 Z) : (term57 Z _22730') = (term59 Z _22730').
Proof. exact (eq_refl (term57 Z _22730')). Qed.
Lemma lem1241619 {Z : Type'} (_22730' : type1540 Z) : term59 Z _22730'.
Proof. exact (EQ_MP (@lem1241618 Z _22730') (@lem1241617 Z _22730')). Qed.
Lemma lem1241620 {Z : Type'} (_22730' : type1540 Z) (fn : type1334 Z) (h1 : term60 Z _22730' fn) : term60 Z _22730' fn.
Proof. exact (h1). Qed.
Lemma lem1241621 {Z : Type'} (c : nat) (_22730' : type1540 Z) (fn : type1334 Z) (h1 : term60 Z _22730' fn) : term61 Z _22730' fn c.
Proof. exact (@lem1241620 Z _22730' fn h1 c). Qed.
Lemma lem1241622 {Z : Type'} (_22730' : type1540 Z) (c : nat) (fn : type1334 Z) : (term61 Z _22730' fn c) = (term62 Z _22730' c fn).
Proof. exact (eq_refl (term61 Z _22730' fn c)). Qed.
Lemma lem1241623 {Z : Type'} (c : nat) (_22730' : type1540 Z) (fn : type1334 Z) (h1 : term60 Z _22730' fn) : term62 Z _22730' c fn.
Proof. exact (EQ_MP (@lem1241622 Z _22730' c fn) (@lem1241621 Z c _22730' fn h1)). Qed.
Lemma lem1241624 {Z : Type'} (c : nat) (i : type1661) (_22730' : type1540 Z) (fn : type1334 Z) (h1 : term60 Z _22730' fn) : term63 Z _22730' c fn i.
Proof. exact (@lem1241623 Z c _22730' fn h1 i). Qed.
Lemma lem1241625 {Z : Type'} (_22730' : type1540 Z) (c : nat) (i : type1661) (fn : type1334 Z) : (term63 Z _22730' c fn i) = (term64 Z _22730' c i fn).
Proof. exact (eq_refl (term63 Z _22730' c fn i)). Qed.
Lemma lem1241626 {Z : Type'} (c : nat) (i : type1661) (_22730' : type1540 Z) (fn : type1334 Z) (h1 : term60 Z _22730' fn) : term64 Z _22730' c i fn.
Proof. exact (EQ_MP (@lem1241625 Z _22730' c i fn) (@lem1241624 Z c i _22730' fn h1)). Qed.
Lemma lem1241627 {Z : Type'} (c : nat) (i : type1661) (r : type1613) (_22730' : type1540 Z) (fn : type1334 Z) (h1 : term60 Z _22730' fn) : term65 Z _22730' c i fn r.
Proof. exact (@lem1241626 Z c i _22730' fn h1 r). Qed.
Lemma lem1241628 {Z : Type'} (_22730' : type1540 Z) (c : nat) (i : type1661) (fn : type1334 Z) (r : type1613) : (term65 Z _22730' c i fn r) = ((term66 Z fn c i r) = (term67 Z _22730' c i fn r)).
Proof. exact (eq_refl (term65 Z _22730' c i fn r)). Qed.
Lemma lem1241661 {A B : Type'} (x : A) : term68 A B x.
Proof. exact (@lem48019 A B x). Qed.
Lemma lem1241662 {A B : Type'} (x : A) : (term68 A B x) = (term69 A B x).
Proof. exact (eq_refl (term68 A B x)). Qed.
Lemma lem1241663 {A B : Type'} (x : A) : term69 A B x.
Proof. exact (EQ_MP (@lem1241662 A B x) (@lem1241661 A B x)). Qed.
Lemma lem1241664 {A B : Type'} (x : A) (y : B) : term70 A B x y.
Proof. exact (@lem1241663 A B x y). Qed.
Lemma lem1241665 {A B : Type'} (x : A) (y : B) : (term70 A B x y) = ((term71 A B x y) = y).
Proof. exact (eq_refl (term70 A B x y)). Qed.
Lemma lem1241667 {A B : Type'} (x : A) : term72 A B x.
Proof. exact (@lem47827 A B x). Qed.
Lemma lem1241668 {A B : Type'} (x : A) : (term72 A B x) = (term73 A B x).
Proof. exact (eq_refl (term72 A B x)). Qed.
Lemma lem1241669 {A B : Type'} (x : A) : term73 A B x.
Proof. exact (EQ_MP (@lem1241668 A B x) (@lem1241667 A B x)). Qed.
Lemma lem1241670 {A B : Type'} (x : A) (y : B) : term74 A B x y.
Proof. exact (@lem1241669 A B x y). Qed.
Lemma lem1241671 {A B : Type'} (y : B) (x : A) : (term74 A B x y) = ((term75 A B x y) = x).
Proof. exact (eq_refl (term74 A B x y)). Qed.
Lemma lem1241674 {Z : Type'} (c : nat) (i : type1661) (r : type1613) (_22730' : type1540 Z) (fn : type1334 Z) (h1 : term60 Z _22730' fn) : (term66 Z fn c i r) = (term67 Z _22730' c i fn r).
Proof. exact (EQ_MP (@lem1241628 Z _22730' c i fn r) (@lem1241627 Z c i r _22730' fn h1)). Qed.
Lemma lem1241675 {Z : Type'} (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1540 Z) (fn : type1334 Z) (h1 : term60 Z _22730' fn) : (term49 Z fn a0 a1 a2 a3 a4 a5 a6 a7) = (term76 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7 fn).
Proof. exact (@lem1241674 Z (NUMERAL 0) (term77 a0 a1 a2 a3 a4 a5 a6 a7) term78 _22730' fn h1). Qed.
Lemma lem1241676 {Z : Type'} (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1540 Z) (fn : Ascii.ascii -> Z) (fn' : type1334 Z) (h1 : term60 Z _22730' fn') (h2 : fn = (term0 Z fn')) : (term2 Z fn a0 a1 a2 a3 a4 a5 a6 a7) = (term76 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7 fn').
Proof. exact (TRANS (@lem1240992 Z a0 a1 a2 a3 a4 a5 a6 a7 fn fn' h2) (@lem1241675 Z a0 a1 a2 a3 a4 a5 a6 a7 _22730' fn' h1)). Qed.
Lemma lem1241678 {A : Type'} (f : nat -> A) (a : A) : (term79 A a f) = a.
Proof. exact (EQ_MP (@lem1066569 A f a) (@lem1066568 A a f)). Qed.
Lemma lem1241679 {Z : Type'} (f : type1589 Z) (a : type1231 Z) : (term80 Z a f) = a.
Proof. exact (@lem1241678 (type1231 Z) f a). Qed.
Lemma lem1241682 {Z : Type'} (_22730' : type1540 Z) : (term81 Z _22730') = (term82 Z _22730').
Proof. exact (@lem1241679 Z (@FNIL ((prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))) -> (nat -> recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))) -> (nat -> Z) -> Z)) (term82 Z _22730')). Qed.
Lemma lem1241683 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term77 a0 a1 a2 a3 a4 a5 a6 a7) = (term77 a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (eq_refl (term77 a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241684 {Z : Type'} (_22730' : type1540 Z) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term83 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7) = (term84 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (MK_COMB (@lem1241682 Z _22730') (@lem1241683 a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241685 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem1241686 {Z : Type'} (_22730' : type1540 Z) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term85 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7) = (term86 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (MK_COMB (@lem1241684 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7) (@lem1241685)). Qed.
Lemma lem1241687 {Z : Type'} (fn : type1334 Z) : (term87 Z fn) = (term87 Z fn).
Proof. exact (eq_refl (term87 Z fn)). Qed.
Lemma lem1241688 {Z : Type'} (_22730' : type1540 Z) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (fn : type1334 Z) : (term76 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7 fn) = (term88 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7 fn).
Proof. exact (MK_COMB (@lem1241686 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7) (@lem1241687 Z fn)). Qed.
Lemma lem1241689 {Z : Type'} (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1540 Z) (fn : Ascii.ascii -> Z) (fn' : type1334 Z) (h1 : term60 Z _22730' fn') (h2 : fn = (term0 Z fn')) : (term2 Z fn a0 a1 a2 a3 a4 a5 a6 a7) = (term88 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7 fn').
Proof. exact (TRANS (@lem1241676 Z a0 a1 a2 a3 a4 a5 a6 a7 _22730' fn fn' h1 h2) (@lem1241688 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7 fn')). Qed.
Lemma lem1241690 {Z : Type'} (_22730' : type1540 Z) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term84 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7) = (term89 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (eq_refl (term84 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241691 : term78 = term78.
Proof. exact (eq_refl term78). Qed.
Lemma lem1241692 {Z : Type'} (_22730' : type1540 Z) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term86 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7) = (term90 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (MK_COMB (@lem1241690 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7) (@lem1241691)). Qed.
Lemma lem1241693 {Z : Type'} (fn : type1334 Z) : (term87 Z fn) = (term87 Z fn).
Proof. exact (eq_refl (term87 Z fn)). Qed.
Lemma lem1241694 {Z : Type'} (_22730' : type1540 Z) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (fn : type1334 Z) : (term88 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7 fn) = (term91 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7 fn).
Proof. exact (MK_COMB (@lem1241692 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7) (@lem1241693 Z fn)). Qed.
Lemma lem1241695 {Z : Type'} (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1540 Z) (fn : Ascii.ascii -> Z) (fn' : type1334 Z) (h1 : term60 Z _22730' fn') (h2 : fn = (term0 Z fn')) : (term2 Z fn a0 a1 a2 a3 a4 a5 a6 a7) = (term91 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7 fn').
Proof. exact (TRANS (@lem1241689 Z a0 a1 a2 a3 a4 a5 a6 a7 _22730' fn fn' h1 h2) (@lem1241694 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7 fn')). Qed.
Lemma lem1241696 {Z : Type'} (_22730' : type1540 Z) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term90 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7) = (term92 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (eq_refl (term90 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241697 {Z : Type'} (fn : type1334 Z) : (term87 Z fn) = (term87 Z fn).
Proof. exact (eq_refl (term87 Z fn)). Qed.
Lemma lem1241698 {Z : Type'} (_22730' : type1540 Z) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (fn : type1334 Z) : (term91 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7 fn) = (term93 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7 fn).
Proof. exact (MK_COMB (@lem1241696 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7) (@lem1241697 Z fn)). Qed.
Lemma lem1241699 {Z : Type'} (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1540 Z) (fn : Ascii.ascii -> Z) (fn' : type1334 Z) (h1 : term60 Z _22730' fn') (h2 : fn = (term0 Z fn')) : (term2 Z fn a0 a1 a2 a3 a4 a5 a6 a7) = (term93 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7 fn').
Proof. exact (TRANS (@lem1241695 Z a0 a1 a2 a3 a4 a5 a6 a7 _22730' fn fn' h1 h2) (@lem1241698 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7 fn')). Qed.
Lemma lem1241700 {Z : Type'} (fn : type1334 Z) (_22730' : type1540 Z) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term93 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7 fn) = (term94 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (eq_refl (term93 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7 fn)). Qed.
Lemma lem1241701 {Z : Type'} (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1540 Z) (fn : Ascii.ascii -> Z) (fn' : type1334 Z) (h1 : term60 Z _22730' fn') (h2 : fn = (term0 Z fn')) : (term2 Z fn a0 a1 a2 a3 a4 a5 a6 a7) = (term94 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (TRANS (@lem1241699 Z a0 a1 a2 a3 a4 a5 a6 a7 _22730' fn fn' h1 h2) (@lem1241700 Z fn' _22730' a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241703 {A B : Type'} (y : B) (x : A) : (term75 A B x y) = x.
Proof. exact (EQ_MP (@lem1241671 A B y x) (@lem1241670 A B x y)). Qed.
Lemma lem1241704 (y : type1662) (x : Prop) : (term95 x y) = x.
Proof. exact (@lem1241703 Prop type1662 y x). Qed.
Lemma lem1241705 (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (a0 : Prop) : (term96 a0 a1 a2 a3 a4 a5 a6 a7) = a0.
Proof. exact (@lem1241704 (term97 a1 a2 a3 a4 a5 a6 a7) a0). Qed.
Lemma lem1241706 {Z : Type'} (_22730' : type1540 Z) : _22730' = _22730'.
Proof. exact (eq_refl _22730'). Qed.
Lemma lem1241707 {Z : Type'} (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1540 Z) (a0 : Prop) : (term98 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7) = (_22730' a0).
Proof. exact (MK_COMB (@lem1241706 Z _22730') (@lem1241705 a1 a2 a3 a4 a5 a6 a7 a0)). Qed.
Lemma lem1241709 {A B : Type'} (x : A) (y : B) : (term71 A B x y) = y.
Proof. exact (EQ_MP (@lem1241665 A B x y) (@lem1241664 A B x y)). Qed.
Lemma lem1241710 (x : Prop) (y : type1662) : (term99 x y) = y.
Proof. exact (@lem1241709 Prop type1662 x y). Qed.
Lemma lem1241711 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term100 a0 a1 a2 a3 a4 a5 a6 a7) = (term97 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (@lem1241710 a0 (term97 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241712 : (@fst Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))) = (@fst Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))).
Proof. exact (eq_refl (@fst Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))). Qed.
Lemma lem1241713 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term101 a0 a1 a2 a3 a4 a5 a6 a7) = (term102 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (MK_COMB (@lem1241712) (@lem1241711 a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241715 {A B : Type'} (y : B) (x : A) : (term75 A B x y) = x.
Proof. exact (EQ_MP (@lem1241671 A B y x) (@lem1241670 A B x y)). Qed.
Lemma lem1241716 (y : type1663) (x : Prop) : (term103 x y) = x.
Proof. exact (@lem1241715 Prop type1663 y x). Qed.
Lemma lem1241717 (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (a1 : Prop) : (term102 a1 a2 a3 a4 a5 a6 a7) = a1.
Proof. exact (@lem1241716 (term104 a2 a3 a4 a5 a6 a7) a1). Qed.
Lemma lem1241718 (a0 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (a1 : Prop) : (term101 a0 a1 a2 a3 a4 a5 a6 a7) = a1.
Proof. exact (TRANS (@lem1241713 a0 a1 a2 a3 a4 a5 a6 a7) (@lem1241717 a2 a3 a4 a5 a6 a7 a1)). Qed.
Lemma lem1241719 {Z : Type'} (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1540 Z) (a0 : Prop) (a1 : Prop) : (term105 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7) = (_22730' a0 a1).
Proof. exact (MK_COMB (@lem1241707 Z a1 a2 a3 a4 a5 a6 a7 _22730' a0) (@lem1241718 a0 a2 a3 a4 a5 a6 a7 a1)). Qed.
Lemma lem1241721 {A B : Type'} (x : A) (y : B) : (term71 A B x y) = y.
Proof. exact (EQ_MP (@lem1241665 A B x y) (@lem1241664 A B x y)). Qed.
Lemma lem1241722 (x : Prop) (y : type1662) : (term99 x y) = y.
Proof. exact (@lem1241721 Prop type1662 x y). Qed.
Lemma lem1241723 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term100 a0 a1 a2 a3 a4 a5 a6 a7) = (term97 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (@lem1241722 a0 (term97 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241724 : (@snd Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))) = (@snd Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))).
Proof. exact (eq_refl (@snd Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))). Qed.
Lemma lem1241725 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term106 a0 a1 a2 a3 a4 a5 a6 a7) = (term107 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (MK_COMB (@lem1241724) (@lem1241723 a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241727 {A B : Type'} (x : A) (y : B) : (term71 A B x y) = y.
Proof. exact (EQ_MP (@lem1241665 A B x y) (@lem1241664 A B x y)). Qed.
Lemma lem1241728 (x : Prop) (y : type1663) : (term108 x y) = y.
Proof. exact (@lem1241727 Prop type1663 x y). Qed.
Lemma lem1241729 (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term107 a1 a2 a3 a4 a5 a6 a7) = (term104 a2 a3 a4 a5 a6 a7).
Proof. exact (@lem1241728 a1 (term104 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241730 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term106 a0 a1 a2 a3 a4 a5 a6 a7) = (term104 a2 a3 a4 a5 a6 a7).
Proof. exact (TRANS (@lem1241725 a0 a1 a2 a3 a4 a5 a6 a7) (@lem1241729 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241731 : (@fst Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))) = (@fst Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))).
Proof. exact (eq_refl (@fst Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))). Qed.
Lemma lem1241732 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term109 a0 a1 a2 a3 a4 a5 a6 a7) = (term110 a2 a3 a4 a5 a6 a7).
Proof. exact (MK_COMB (@lem1241731) (@lem1241730 a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241734 {A B : Type'} (y : B) (x : A) : (term75 A B x y) = x.
Proof. exact (EQ_MP (@lem1241671 A B y x) (@lem1241670 A B x y)). Qed.
Lemma lem1241735 (y : type1664) (x : Prop) : (term111 x y) = x.
Proof. exact (@lem1241734 Prop type1664 y x). Qed.
Lemma lem1241736 (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (a2 : Prop) : (term110 a2 a3 a4 a5 a6 a7) = a2.
Proof. exact (@lem1241735 (term112 a3 a4 a5 a6 a7) a2). Qed.
Lemma lem1241737 (a0 : Prop) (a1 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (a2 : Prop) : (term109 a0 a1 a2 a3 a4 a5 a6 a7) = a2.
Proof. exact (TRANS (@lem1241732 a0 a1 a2 a3 a4 a5 a6 a7) (@lem1241736 a3 a4 a5 a6 a7 a2)). Qed.
Lemma lem1241738 {Z : Type'} (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1540 Z) (a0 : Prop) (a1 : Prop) (a2 : Prop) : (term113 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7) = (_22730' a0 a1 a2).
Proof. exact (MK_COMB (@lem1241719 Z a2 a3 a4 a5 a6 a7 _22730' a0 a1) (@lem1241737 a0 a1 a3 a4 a5 a6 a7 a2)). Qed.
Lemma lem1241740 {A B : Type'} (x : A) (y : B) : (term71 A B x y) = y.
Proof. exact (EQ_MP (@lem1241665 A B x y) (@lem1241664 A B x y)). Qed.
Lemma lem1241741 (x : Prop) (y : type1662) : (term99 x y) = y.
Proof. exact (@lem1241740 Prop type1662 x y). Qed.
Lemma lem1241742 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term100 a0 a1 a2 a3 a4 a5 a6 a7) = (term97 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (@lem1241741 a0 (term97 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241743 : (@snd Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))) = (@snd Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))).
Proof. exact (eq_refl (@snd Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))). Qed.
Lemma lem1241744 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term106 a0 a1 a2 a3 a4 a5 a6 a7) = (term107 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (MK_COMB (@lem1241743) (@lem1241742 a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241746 {A B : Type'} (x : A) (y : B) : (term71 A B x y) = y.
Proof. exact (EQ_MP (@lem1241665 A B x y) (@lem1241664 A B x y)). Qed.
Lemma lem1241747 (x : Prop) (y : type1663) : (term108 x y) = y.
Proof. exact (@lem1241746 Prop type1663 x y). Qed.
Lemma lem1241748 (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term107 a1 a2 a3 a4 a5 a6 a7) = (term104 a2 a3 a4 a5 a6 a7).
Proof. exact (@lem1241747 a1 (term104 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241749 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term106 a0 a1 a2 a3 a4 a5 a6 a7) = (term104 a2 a3 a4 a5 a6 a7).
Proof. exact (TRANS (@lem1241744 a0 a1 a2 a3 a4 a5 a6 a7) (@lem1241748 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241750 : (@snd Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))) = (@snd Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))).
Proof. exact (eq_refl (@snd Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))). Qed.
Lemma lem1241751 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term114 a0 a1 a2 a3 a4 a5 a6 a7) = (term115 a2 a3 a4 a5 a6 a7).
Proof. exact (MK_COMB (@lem1241750) (@lem1241749 a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241753 {A B : Type'} (x : A) (y : B) : (term71 A B x y) = y.
Proof. exact (EQ_MP (@lem1241665 A B x y) (@lem1241664 A B x y)). Qed.
Lemma lem1241754 (x : Prop) (y : type1664) : (term116 x y) = y.
Proof. exact (@lem1241753 Prop type1664 x y). Qed.
Lemma lem1241755 (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term115 a2 a3 a4 a5 a6 a7) = (term112 a3 a4 a5 a6 a7).
Proof. exact (@lem1241754 a2 (term112 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241756 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term114 a0 a1 a2 a3 a4 a5 a6 a7) = (term112 a3 a4 a5 a6 a7).
Proof. exact (TRANS (@lem1241751 a0 a1 a2 a3 a4 a5 a6 a7) (@lem1241755 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241757 : (@fst Prop (prod Prop (prod Prop (prod Prop Prop)))) = (@fst Prop (prod Prop (prod Prop (prod Prop Prop)))).
Proof. exact (eq_refl (@fst Prop (prod Prop (prod Prop (prod Prop Prop))))). Qed.
Lemma lem1241758 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term117 a0 a1 a2 a3 a4 a5 a6 a7) = (term118 a3 a4 a5 a6 a7).
Proof. exact (MK_COMB (@lem1241757) (@lem1241756 a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241760 {A B : Type'} (y : B) (x : A) : (term75 A B x y) = x.
Proof. exact (EQ_MP (@lem1241671 A B y x) (@lem1241670 A B x y)). Qed.
Lemma lem1241761 (y : type1665) (x : Prop) : (term119 x y) = x.
Proof. exact (@lem1241760 Prop type1665 y x). Qed.
Lemma lem1241762 (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (a3 : Prop) : (term118 a3 a4 a5 a6 a7) = a3.
Proof. exact (@lem1241761 (term120 a4 a5 a6 a7) a3). Qed.
Lemma lem1241763 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (a3 : Prop) : (term117 a0 a1 a2 a3 a4 a5 a6 a7) = a3.
Proof. exact (TRANS (@lem1241758 a0 a1 a2 a3 a4 a5 a6 a7) (@lem1241762 a4 a5 a6 a7 a3)). Qed.
Lemma lem1241764 {Z : Type'} (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1540 Z) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) : (term121 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7) = (_22730' a0 a1 a2 a3).
Proof. exact (MK_COMB (@lem1241738 Z a3 a4 a5 a6 a7 _22730' a0 a1 a2) (@lem1241763 a0 a1 a2 a4 a5 a6 a7 a3)). Qed.
Lemma lem1241766 {A B : Type'} (x : A) (y : B) : (term71 A B x y) = y.
Proof. exact (EQ_MP (@lem1241665 A B x y) (@lem1241664 A B x y)). Qed.
Lemma lem1241767 (x : Prop) (y : type1662) : (term99 x y) = y.
Proof. exact (@lem1241766 Prop type1662 x y). Qed.
Lemma lem1241768 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term100 a0 a1 a2 a3 a4 a5 a6 a7) = (term97 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (@lem1241767 a0 (term97 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241769 : (@snd Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))) = (@snd Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))).
Proof. exact (eq_refl (@snd Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))). Qed.
Lemma lem1241770 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term106 a0 a1 a2 a3 a4 a5 a6 a7) = (term107 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (MK_COMB (@lem1241769) (@lem1241768 a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241772 {A B : Type'} (x : A) (y : B) : (term71 A B x y) = y.
Proof. exact (EQ_MP (@lem1241665 A B x y) (@lem1241664 A B x y)). Qed.
Lemma lem1241773 (x : Prop) (y : type1663) : (term108 x y) = y.
Proof. exact (@lem1241772 Prop type1663 x y). Qed.
Lemma lem1241774 (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term107 a1 a2 a3 a4 a5 a6 a7) = (term104 a2 a3 a4 a5 a6 a7).
Proof. exact (@lem1241773 a1 (term104 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241775 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term106 a0 a1 a2 a3 a4 a5 a6 a7) = (term104 a2 a3 a4 a5 a6 a7).
Proof. exact (TRANS (@lem1241770 a0 a1 a2 a3 a4 a5 a6 a7) (@lem1241774 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241776 : (@snd Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))) = (@snd Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))).
Proof. exact (eq_refl (@snd Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))). Qed.
Lemma lem1241777 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term114 a0 a1 a2 a3 a4 a5 a6 a7) = (term115 a2 a3 a4 a5 a6 a7).
Proof. exact (MK_COMB (@lem1241776) (@lem1241775 a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241779 {A B : Type'} (x : A) (y : B) : (term71 A B x y) = y.
Proof. exact (EQ_MP (@lem1241665 A B x y) (@lem1241664 A B x y)). Qed.
Lemma lem1241780 (x : Prop) (y : type1664) : (term116 x y) = y.
Proof. exact (@lem1241779 Prop type1664 x y). Qed.
Lemma lem1241781 (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term115 a2 a3 a4 a5 a6 a7) = (term112 a3 a4 a5 a6 a7).
Proof. exact (@lem1241780 a2 (term112 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241782 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term114 a0 a1 a2 a3 a4 a5 a6 a7) = (term112 a3 a4 a5 a6 a7).
Proof. exact (TRANS (@lem1241777 a0 a1 a2 a3 a4 a5 a6 a7) (@lem1241781 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241783 : (@snd Prop (prod Prop (prod Prop (prod Prop Prop)))) = (@snd Prop (prod Prop (prod Prop (prod Prop Prop)))).
Proof. exact (eq_refl (@snd Prop (prod Prop (prod Prop (prod Prop Prop))))). Qed.
Lemma lem1241784 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term122 a0 a1 a2 a3 a4 a5 a6 a7) = (term123 a3 a4 a5 a6 a7).
Proof. exact (MK_COMB (@lem1241783) (@lem1241782 a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241786 {A B : Type'} (x : A) (y : B) : (term71 A B x y) = y.
Proof. exact (EQ_MP (@lem1241665 A B x y) (@lem1241664 A B x y)). Qed.
Lemma lem1241787 (x : Prop) (y : type1665) : (term124 x y) = y.
Proof. exact (@lem1241786 Prop type1665 x y). Qed.
Lemma lem1241788 (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term123 a3 a4 a5 a6 a7) = (term120 a4 a5 a6 a7).
Proof. exact (@lem1241787 a3 (term120 a4 a5 a6 a7)). Qed.
Lemma lem1241789 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term122 a0 a1 a2 a3 a4 a5 a6 a7) = (term120 a4 a5 a6 a7).
Proof. exact (TRANS (@lem1241784 a0 a1 a2 a3 a4 a5 a6 a7) (@lem1241788 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241790 : (@fst Prop (prod Prop (prod Prop Prop))) = (@fst Prop (prod Prop (prod Prop Prop))).
Proof. exact (eq_refl (@fst Prop (prod Prop (prod Prop Prop)))). Qed.
Lemma lem1241791 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term125 a0 a1 a2 a3 a4 a5 a6 a7) = (term126 a4 a5 a6 a7).
Proof. exact (MK_COMB (@lem1241790) (@lem1241789 a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241793 {A B : Type'} (y : B) (x : A) : (term75 A B x y) = x.
Proof. exact (EQ_MP (@lem1241671 A B y x) (@lem1241670 A B x y)). Qed.
Lemma lem1241794 (y : type1666) (x : Prop) : (term127 x y) = x.
Proof. exact (@lem1241793 Prop type1666 y x). Qed.
Lemma lem1241795 (a5 : Prop) (a6 : Prop) (a7 : Prop) (a4 : Prop) : (term126 a4 a5 a6 a7) = a4.
Proof. exact (@lem1241794 (term128 a5 a6 a7) a4). Qed.
Lemma lem1241796 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (a4 : Prop) : (term125 a0 a1 a2 a3 a4 a5 a6 a7) = a4.
Proof. exact (TRANS (@lem1241791 a0 a1 a2 a3 a4 a5 a6 a7) (@lem1241795 a5 a6 a7 a4)). Qed.
Lemma lem1241797 {Z : Type'} (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1540 Z) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) : (term129 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7) = (_22730' a0 a1 a2 a3 a4).
Proof. exact (MK_COMB (@lem1241764 Z a4 a5 a6 a7 _22730' a0 a1 a2 a3) (@lem1241796 a0 a1 a2 a3 a5 a6 a7 a4)). Qed.
Lemma lem1241799 {A B : Type'} (x : A) (y : B) : (term71 A B x y) = y.
Proof. exact (EQ_MP (@lem1241665 A B x y) (@lem1241664 A B x y)). Qed.
Lemma lem1241800 (x : Prop) (y : type1662) : (term99 x y) = y.
Proof. exact (@lem1241799 Prop type1662 x y). Qed.
Lemma lem1241801 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term100 a0 a1 a2 a3 a4 a5 a6 a7) = (term97 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (@lem1241800 a0 (term97 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241802 : (@snd Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))) = (@snd Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))).
Proof. exact (eq_refl (@snd Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))). Qed.
Lemma lem1241803 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term106 a0 a1 a2 a3 a4 a5 a6 a7) = (term107 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (MK_COMB (@lem1241802) (@lem1241801 a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241805 {A B : Type'} (x : A) (y : B) : (term71 A B x y) = y.
Proof. exact (EQ_MP (@lem1241665 A B x y) (@lem1241664 A B x y)). Qed.
Lemma lem1241806 (x : Prop) (y : type1663) : (term108 x y) = y.
Proof. exact (@lem1241805 Prop type1663 x y). Qed.
Lemma lem1241807 (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term107 a1 a2 a3 a4 a5 a6 a7) = (term104 a2 a3 a4 a5 a6 a7).
Proof. exact (@lem1241806 a1 (term104 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241808 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term106 a0 a1 a2 a3 a4 a5 a6 a7) = (term104 a2 a3 a4 a5 a6 a7).
Proof. exact (TRANS (@lem1241803 a0 a1 a2 a3 a4 a5 a6 a7) (@lem1241807 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241809 : (@snd Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))) = (@snd Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))).
Proof. exact (eq_refl (@snd Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))). Qed.
Lemma lem1241810 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term114 a0 a1 a2 a3 a4 a5 a6 a7) = (term115 a2 a3 a4 a5 a6 a7).
Proof. exact (MK_COMB (@lem1241809) (@lem1241808 a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241812 {A B : Type'} (x : A) (y : B) : (term71 A B x y) = y.
Proof. exact (EQ_MP (@lem1241665 A B x y) (@lem1241664 A B x y)). Qed.
Lemma lem1241813 (x : Prop) (y : type1664) : (term116 x y) = y.
Proof. exact (@lem1241812 Prop type1664 x y). Qed.
Lemma lem1241814 (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term115 a2 a3 a4 a5 a6 a7) = (term112 a3 a4 a5 a6 a7).
Proof. exact (@lem1241813 a2 (term112 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241815 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term114 a0 a1 a2 a3 a4 a5 a6 a7) = (term112 a3 a4 a5 a6 a7).
Proof. exact (TRANS (@lem1241810 a0 a1 a2 a3 a4 a5 a6 a7) (@lem1241814 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241816 : (@snd Prop (prod Prop (prod Prop (prod Prop Prop)))) = (@snd Prop (prod Prop (prod Prop (prod Prop Prop)))).
Proof. exact (eq_refl (@snd Prop (prod Prop (prod Prop (prod Prop Prop))))). Qed.
Lemma lem1241817 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term122 a0 a1 a2 a3 a4 a5 a6 a7) = (term123 a3 a4 a5 a6 a7).
Proof. exact (MK_COMB (@lem1241816) (@lem1241815 a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241819 {A B : Type'} (x : A) (y : B) : (term71 A B x y) = y.
Proof. exact (EQ_MP (@lem1241665 A B x y) (@lem1241664 A B x y)). Qed.
Lemma lem1241820 (x : Prop) (y : type1665) : (term124 x y) = y.
Proof. exact (@lem1241819 Prop type1665 x y). Qed.
Lemma lem1241821 (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term123 a3 a4 a5 a6 a7) = (term120 a4 a5 a6 a7).
Proof. exact (@lem1241820 a3 (term120 a4 a5 a6 a7)). Qed.
Lemma lem1241822 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term122 a0 a1 a2 a3 a4 a5 a6 a7) = (term120 a4 a5 a6 a7).
Proof. exact (TRANS (@lem1241817 a0 a1 a2 a3 a4 a5 a6 a7) (@lem1241821 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241823 : (@snd Prop (prod Prop (prod Prop Prop))) = (@snd Prop (prod Prop (prod Prop Prop))).
Proof. exact (eq_refl (@snd Prop (prod Prop (prod Prop Prop)))). Qed.
Lemma lem1241824 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term130 a0 a1 a2 a3 a4 a5 a6 a7) = (term131 a4 a5 a6 a7).
Proof. exact (MK_COMB (@lem1241823) (@lem1241822 a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241826 {A B : Type'} (x : A) (y : B) : (term71 A B x y) = y.
Proof. exact (EQ_MP (@lem1241665 A B x y) (@lem1241664 A B x y)). Qed.
Lemma lem1241827 (x : Prop) (y : type1666) : (term132 x y) = y.
Proof. exact (@lem1241826 Prop type1666 x y). Qed.
Lemma lem1241828 (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term131 a4 a5 a6 a7) = (term128 a5 a6 a7).
Proof. exact (@lem1241827 a4 (term128 a5 a6 a7)). Qed.
Lemma lem1241829 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term130 a0 a1 a2 a3 a4 a5 a6 a7) = (term128 a5 a6 a7).
Proof. exact (TRANS (@lem1241824 a0 a1 a2 a3 a4 a5 a6 a7) (@lem1241828 a4 a5 a6 a7)). Qed.
Lemma lem1241830 : (@fst Prop (prod Prop Prop)) = (@fst Prop (prod Prop Prop)).
Proof. exact (eq_refl (@fst Prop (prod Prop Prop))). Qed.
Lemma lem1241831 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term133 a0 a1 a2 a3 a4 a5 a6 a7) = (term134 a5 a6 a7).
Proof. exact (MK_COMB (@lem1241830) (@lem1241829 a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241833 {A B : Type'} (y : B) (x : A) : (term75 A B x y) = x.
Proof. exact (EQ_MP (@lem1241671 A B y x) (@lem1241670 A B x y)). Qed.
Lemma lem1241834 (y : prod Prop Prop) (x : Prop) : (term135 x y) = x.
Proof. exact (@lem1241833 Prop (prod Prop Prop) y x). Qed.
Lemma lem1241835 (a6 : Prop) (a7 : Prop) (a5 : Prop) : (term134 a5 a6 a7) = a5.
Proof. exact (@lem1241834 (@pair Prop Prop a6 a7) a5). Qed.
Lemma lem1241836 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a6 : Prop) (a7 : Prop) (a5 : Prop) : (term133 a0 a1 a2 a3 a4 a5 a6 a7) = a5.
Proof. exact (TRANS (@lem1241831 a0 a1 a2 a3 a4 a5 a6 a7) (@lem1241835 a6 a7 a5)). Qed.
Lemma lem1241837 {Z : Type'} (a6 : Prop) (a7 : Prop) (_22730' : type1540 Z) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) : (term136 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7) = (_22730' a0 a1 a2 a3 a4 a5).
Proof. exact (MK_COMB (@lem1241797 Z a5 a6 a7 _22730' a0 a1 a2 a3 a4) (@lem1241836 a0 a1 a2 a3 a4 a6 a7 a5)). Qed.
Lemma lem1241839 {A B : Type'} (x : A) (y : B) : (term71 A B x y) = y.
Proof. exact (EQ_MP (@lem1241665 A B x y) (@lem1241664 A B x y)). Qed.
Lemma lem1241840 (x : Prop) (y : type1662) : (term99 x y) = y.
Proof. exact (@lem1241839 Prop type1662 x y). Qed.
Lemma lem1241841 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term100 a0 a1 a2 a3 a4 a5 a6 a7) = (term97 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (@lem1241840 a0 (term97 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241842 : (@snd Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))) = (@snd Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))).
Proof. exact (eq_refl (@snd Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))). Qed.
Lemma lem1241843 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term106 a0 a1 a2 a3 a4 a5 a6 a7) = (term107 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (MK_COMB (@lem1241842) (@lem1241841 a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241845 {A B : Type'} (x : A) (y : B) : (term71 A B x y) = y.
Proof. exact (EQ_MP (@lem1241665 A B x y) (@lem1241664 A B x y)). Qed.
Lemma lem1241846 (x : Prop) (y : type1663) : (term108 x y) = y.
Proof. exact (@lem1241845 Prop type1663 x y). Qed.
Lemma lem1241847 (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term107 a1 a2 a3 a4 a5 a6 a7) = (term104 a2 a3 a4 a5 a6 a7).
Proof. exact (@lem1241846 a1 (term104 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241848 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term106 a0 a1 a2 a3 a4 a5 a6 a7) = (term104 a2 a3 a4 a5 a6 a7).
Proof. exact (TRANS (@lem1241843 a0 a1 a2 a3 a4 a5 a6 a7) (@lem1241847 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241849 : (@snd Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))) = (@snd Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))).
Proof. exact (eq_refl (@snd Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))). Qed.
Lemma lem1241850 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term114 a0 a1 a2 a3 a4 a5 a6 a7) = (term115 a2 a3 a4 a5 a6 a7).
Proof. exact (MK_COMB (@lem1241849) (@lem1241848 a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241852 {A B : Type'} (x : A) (y : B) : (term71 A B x y) = y.
Proof. exact (EQ_MP (@lem1241665 A B x y) (@lem1241664 A B x y)). Qed.
Lemma lem1241853 (x : Prop) (y : type1664) : (term116 x y) = y.
Proof. exact (@lem1241852 Prop type1664 x y). Qed.
Lemma lem1241854 (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term115 a2 a3 a4 a5 a6 a7) = (term112 a3 a4 a5 a6 a7).
Proof. exact (@lem1241853 a2 (term112 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241855 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term114 a0 a1 a2 a3 a4 a5 a6 a7) = (term112 a3 a4 a5 a6 a7).
Proof. exact (TRANS (@lem1241850 a0 a1 a2 a3 a4 a5 a6 a7) (@lem1241854 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241856 : (@snd Prop (prod Prop (prod Prop (prod Prop Prop)))) = (@snd Prop (prod Prop (prod Prop (prod Prop Prop)))).
Proof. exact (eq_refl (@snd Prop (prod Prop (prod Prop (prod Prop Prop))))). Qed.
Lemma lem1241857 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term122 a0 a1 a2 a3 a4 a5 a6 a7) = (term123 a3 a4 a5 a6 a7).
Proof. exact (MK_COMB (@lem1241856) (@lem1241855 a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241859 {A B : Type'} (x : A) (y : B) : (term71 A B x y) = y.
Proof. exact (EQ_MP (@lem1241665 A B x y) (@lem1241664 A B x y)). Qed.
Lemma lem1241860 (x : Prop) (y : type1665) : (term124 x y) = y.
Proof. exact (@lem1241859 Prop type1665 x y). Qed.
Lemma lem1241861 (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term123 a3 a4 a5 a6 a7) = (term120 a4 a5 a6 a7).
Proof. exact (@lem1241860 a3 (term120 a4 a5 a6 a7)). Qed.
Lemma lem1241862 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term122 a0 a1 a2 a3 a4 a5 a6 a7) = (term120 a4 a5 a6 a7).
Proof. exact (TRANS (@lem1241857 a0 a1 a2 a3 a4 a5 a6 a7) (@lem1241861 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241863 : (@snd Prop (prod Prop (prod Prop Prop))) = (@snd Prop (prod Prop (prod Prop Prop))).
Proof. exact (eq_refl (@snd Prop (prod Prop (prod Prop Prop)))). Qed.
Lemma lem1241864 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term130 a0 a1 a2 a3 a4 a5 a6 a7) = (term131 a4 a5 a6 a7).
Proof. exact (MK_COMB (@lem1241863) (@lem1241862 a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241866 {A B : Type'} (x : A) (y : B) : (term71 A B x y) = y.
Proof. exact (EQ_MP (@lem1241665 A B x y) (@lem1241664 A B x y)). Qed.
Lemma lem1241867 (x : Prop) (y : type1666) : (term132 x y) = y.
Proof. exact (@lem1241866 Prop type1666 x y). Qed.
Lemma lem1241868 (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term131 a4 a5 a6 a7) = (term128 a5 a6 a7).
Proof. exact (@lem1241867 a4 (term128 a5 a6 a7)). Qed.
Lemma lem1241869 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term130 a0 a1 a2 a3 a4 a5 a6 a7) = (term128 a5 a6 a7).
Proof. exact (TRANS (@lem1241864 a0 a1 a2 a3 a4 a5 a6 a7) (@lem1241868 a4 a5 a6 a7)). Qed.
Lemma lem1241870 : (@snd Prop (prod Prop Prop)) = (@snd Prop (prod Prop Prop)).
Proof. exact (eq_refl (@snd Prop (prod Prop Prop))). Qed.
Lemma lem1241871 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term137 a0 a1 a2 a3 a4 a5 a6 a7) = (term138 a5 a6 a7).
Proof. exact (MK_COMB (@lem1241870) (@lem1241869 a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241873 {A B : Type'} (x : A) (y : B) : (term71 A B x y) = y.
Proof. exact (EQ_MP (@lem1241665 A B x y) (@lem1241664 A B x y)). Qed.
Lemma lem1241874 (x : Prop) (y : prod Prop Prop) : (term139 x y) = y.
Proof. exact (@lem1241873 Prop (prod Prop Prop) x y). Qed.
Lemma lem1241875 (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term138 a5 a6 a7) = (@pair Prop Prop a6 a7).
Proof. exact (@lem1241874 a5 (@pair Prop Prop a6 a7)). Qed.
Lemma lem1241876 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term137 a0 a1 a2 a3 a4 a5 a6 a7) = (@pair Prop Prop a6 a7).
Proof. exact (TRANS (@lem1241871 a0 a1 a2 a3 a4 a5 a6 a7) (@lem1241875 a5 a6 a7)). Qed.
Lemma lem1241877 : (@fst Prop Prop) = (@fst Prop Prop).
Proof. exact (eq_refl (@fst Prop Prop)). Qed.
Lemma lem1241878 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term140 a0 a1 a2 a3 a4 a5 a6 a7) = (term141 a6 a7).
Proof. exact (MK_COMB (@lem1241877) (@lem1241876 a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241880 {A B : Type'} (y : B) (x : A) : (term75 A B x y) = x.
Proof. exact (EQ_MP (@lem1241671 A B y x) (@lem1241670 A B x y)). Qed.
Lemma lem1241881 (y : Prop) (x : Prop) : (term141 x y) = x.
Proof. exact (@lem1241880 Prop Prop y x). Qed.
Lemma lem1241882 (a7 : Prop) (a6 : Prop) : (term141 a6 a7) = a6.
Proof. exact (@lem1241881 a7 a6). Qed.
Lemma lem1241883 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a7 : Prop) (a6 : Prop) : (term140 a0 a1 a2 a3 a4 a5 a6 a7) = a6.
Proof. exact (TRANS (@lem1241878 a0 a1 a2 a3 a4 a5 a6 a7) (@lem1241882 a7 a6)). Qed.
Lemma lem1241884 {Z : Type'} (a7 : Prop) (_22730' : type1540 Z) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) : (term142 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7) = (_22730' a0 a1 a2 a3 a4 a5 a6).
Proof. exact (MK_COMB (@lem1241837 Z a6 a7 _22730' a0 a1 a2 a3 a4 a5) (@lem1241883 a0 a1 a2 a3 a4 a5 a7 a6)). Qed.
Lemma lem1241886 {A B : Type'} (x : A) (y : B) : (term71 A B x y) = y.
Proof. exact (EQ_MP (@lem1241665 A B x y) (@lem1241664 A B x y)). Qed.
Lemma lem1241887 (x : Prop) (y : type1662) : (term99 x y) = y.
Proof. exact (@lem1241886 Prop type1662 x y). Qed.
Lemma lem1241888 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term100 a0 a1 a2 a3 a4 a5 a6 a7) = (term97 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (@lem1241887 a0 (term97 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241889 : (@snd Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))) = (@snd Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))).
Proof. exact (eq_refl (@snd Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))). Qed.
Lemma lem1241890 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term106 a0 a1 a2 a3 a4 a5 a6 a7) = (term107 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (MK_COMB (@lem1241889) (@lem1241888 a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241892 {A B : Type'} (x : A) (y : B) : (term71 A B x y) = y.
Proof. exact (EQ_MP (@lem1241665 A B x y) (@lem1241664 A B x y)). Qed.
Lemma lem1241893 (x : Prop) (y : type1663) : (term108 x y) = y.
Proof. exact (@lem1241892 Prop type1663 x y). Qed.
Lemma lem1241894 (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term107 a1 a2 a3 a4 a5 a6 a7) = (term104 a2 a3 a4 a5 a6 a7).
Proof. exact (@lem1241893 a1 (term104 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241895 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term106 a0 a1 a2 a3 a4 a5 a6 a7) = (term104 a2 a3 a4 a5 a6 a7).
Proof. exact (TRANS (@lem1241890 a0 a1 a2 a3 a4 a5 a6 a7) (@lem1241894 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241896 : (@snd Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))) = (@snd Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))).
Proof. exact (eq_refl (@snd Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))). Qed.
Lemma lem1241897 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term114 a0 a1 a2 a3 a4 a5 a6 a7) = (term115 a2 a3 a4 a5 a6 a7).
Proof. exact (MK_COMB (@lem1241896) (@lem1241895 a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241899 {A B : Type'} (x : A) (y : B) : (term71 A B x y) = y.
Proof. exact (EQ_MP (@lem1241665 A B x y) (@lem1241664 A B x y)). Qed.
Lemma lem1241900 (x : Prop) (y : type1664) : (term116 x y) = y.
Proof. exact (@lem1241899 Prop type1664 x y). Qed.
Lemma lem1241901 (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term115 a2 a3 a4 a5 a6 a7) = (term112 a3 a4 a5 a6 a7).
Proof. exact (@lem1241900 a2 (term112 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241902 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term114 a0 a1 a2 a3 a4 a5 a6 a7) = (term112 a3 a4 a5 a6 a7).
Proof. exact (TRANS (@lem1241897 a0 a1 a2 a3 a4 a5 a6 a7) (@lem1241901 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241903 : (@snd Prop (prod Prop (prod Prop (prod Prop Prop)))) = (@snd Prop (prod Prop (prod Prop (prod Prop Prop)))).
Proof. exact (eq_refl (@snd Prop (prod Prop (prod Prop (prod Prop Prop))))). Qed.
Lemma lem1241904 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term122 a0 a1 a2 a3 a4 a5 a6 a7) = (term123 a3 a4 a5 a6 a7).
Proof. exact (MK_COMB (@lem1241903) (@lem1241902 a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241906 {A B : Type'} (x : A) (y : B) : (term71 A B x y) = y.
Proof. exact (EQ_MP (@lem1241665 A B x y) (@lem1241664 A B x y)). Qed.
Lemma lem1241907 (x : Prop) (y : type1665) : (term124 x y) = y.
Proof. exact (@lem1241906 Prop type1665 x y). Qed.
Lemma lem1241908 (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term123 a3 a4 a5 a6 a7) = (term120 a4 a5 a6 a7).
Proof. exact (@lem1241907 a3 (term120 a4 a5 a6 a7)). Qed.
Lemma lem1241909 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term122 a0 a1 a2 a3 a4 a5 a6 a7) = (term120 a4 a5 a6 a7).
Proof. exact (TRANS (@lem1241904 a0 a1 a2 a3 a4 a5 a6 a7) (@lem1241908 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241910 : (@snd Prop (prod Prop (prod Prop Prop))) = (@snd Prop (prod Prop (prod Prop Prop))).
Proof. exact (eq_refl (@snd Prop (prod Prop (prod Prop Prop)))). Qed.
Lemma lem1241911 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term130 a0 a1 a2 a3 a4 a5 a6 a7) = (term131 a4 a5 a6 a7).
Proof. exact (MK_COMB (@lem1241910) (@lem1241909 a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241913 {A B : Type'} (x : A) (y : B) : (term71 A B x y) = y.
Proof. exact (EQ_MP (@lem1241665 A B x y) (@lem1241664 A B x y)). Qed.
Lemma lem1241914 (x : Prop) (y : type1666) : (term132 x y) = y.
Proof. exact (@lem1241913 Prop type1666 x y). Qed.
Lemma lem1241915 (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term131 a4 a5 a6 a7) = (term128 a5 a6 a7).
Proof. exact (@lem1241914 a4 (term128 a5 a6 a7)). Qed.
Lemma lem1241916 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term130 a0 a1 a2 a3 a4 a5 a6 a7) = (term128 a5 a6 a7).
Proof. exact (TRANS (@lem1241911 a0 a1 a2 a3 a4 a5 a6 a7) (@lem1241915 a4 a5 a6 a7)). Qed.
Lemma lem1241917 : (@snd Prop (prod Prop Prop)) = (@snd Prop (prod Prop Prop)).
Proof. exact (eq_refl (@snd Prop (prod Prop Prop))). Qed.
Lemma lem1241918 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term137 a0 a1 a2 a3 a4 a5 a6 a7) = (term138 a5 a6 a7).
Proof. exact (MK_COMB (@lem1241917) (@lem1241916 a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241920 {A B : Type'} (x : A) (y : B) : (term71 A B x y) = y.
Proof. exact (EQ_MP (@lem1241665 A B x y) (@lem1241664 A B x y)). Qed.
Lemma lem1241921 (x : Prop) (y : prod Prop Prop) : (term139 x y) = y.
Proof. exact (@lem1241920 Prop (prod Prop Prop) x y). Qed.
Lemma lem1241922 (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term138 a5 a6 a7) = (@pair Prop Prop a6 a7).
Proof. exact (@lem1241921 a5 (@pair Prop Prop a6 a7)). Qed.
Lemma lem1241923 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term137 a0 a1 a2 a3 a4 a5 a6 a7) = (@pair Prop Prop a6 a7).
Proof. exact (TRANS (@lem1241918 a0 a1 a2 a3 a4 a5 a6 a7) (@lem1241922 a5 a6 a7)). Qed.
Lemma lem1241924 : (@snd Prop Prop) = (@snd Prop Prop).
Proof. exact (eq_refl (@snd Prop Prop)). Qed.
Lemma lem1241925 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term143 a0 a1 a2 a3 a4 a5 a6 a7) = (term144 a6 a7).
Proof. exact (MK_COMB (@lem1241924) (@lem1241923 a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241927 {A B : Type'} (x : A) (y : B) : (term71 A B x y) = y.
Proof. exact (EQ_MP (@lem1241665 A B x y) (@lem1241664 A B x y)). Qed.
Lemma lem1241928 (x : Prop) (y : Prop) : (term144 x y) = y.
Proof. exact (@lem1241927 Prop Prop x y). Qed.
Lemma lem1241929 (a6 : Prop) (a7 : Prop) : (term144 a6 a7) = a7.
Proof. exact (@lem1241928 a6 a7). Qed.
Lemma lem1241930 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term143 a0 a1 a2 a3 a4 a5 a6 a7) = a7.
Proof. exact (TRANS (@lem1241925 a0 a1 a2 a3 a4 a5 a6 a7) (@lem1241929 a6 a7)). Qed.
Lemma lem1241931 {Z : Type'} (_22730' : type1540 Z) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term94 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7) = (_22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (MK_COMB (@lem1241884 Z a7 _22730' a0 a1 a2 a3 a4 a5 a6) (@lem1241930 a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241932 {Z : Type'} (fn : Ascii.ascii -> Z) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term145 Z fn a0 a1 a2 a3 a4 a5 a6 a7) = (term145 Z fn a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (eq_refl (term145 Z fn a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241933 {Z : Type'} (fn : Ascii.ascii -> Z) (_22730' : type1540 Z) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : ((term2 Z fn a0 a1 a2 a3 a4 a5 a6 a7) = (term94 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7)) = ((term2 Z fn a0 a1 a2 a3 a4 a5 a6 a7) = (_22730' a0 a1 a2 a3 a4 a5 a6 a7)).
Proof. exact (MK_COMB (@lem1241932 Z fn a0 a1 a2 a3 a4 a5 a6 a7) (@lem1241931 Z _22730' a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1241934 {Z : Type'} (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1540 Z) (fn : Ascii.ascii -> Z) (fn' : type1334 Z) (h1 : term60 Z _22730' fn') (h2 : fn = (term0 Z fn')) : (term2 Z fn a0 a1 a2 a3 a4 a5 a6 a7) = (_22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (EQ_MP (@lem1241933 Z fn _22730' a0 a1 a2 a3 a4 a5 a6 a7) (@lem1241701 Z a0 a1 a2 a3 a4 a5 a6 a7 _22730' fn fn' h1 h2)). Qed.
Lemma lem1241935 {Z : Type'} (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (_22730' : type1540 Z) (fn : Ascii.ascii -> Z) (fn' : type1334 Z) (h1 : term60 Z _22730' fn') (h2 : fn = (term0 Z fn')) : term146 Z fn _22730' a0 a1 a2 a3 a4 a5 a6.
Proof. exact (fun a7 : Prop => @lem1241934 Z a0 a1 a2 a3 a4 a5 a6 a7 _22730' fn fn' h1 h2). Qed.
Lemma lem1241936 {Z : Type'} (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (_22730' : type1540 Z) (fn : Ascii.ascii -> Z) (fn' : type1334 Z) (h1 : term60 Z _22730' fn') (h2 : fn = (term0 Z fn')) : term147 Z fn _22730' a0 a1 a2 a3 a4 a5.
Proof. exact (fun a6 : Prop => @lem1241935 Z a0 a1 a2 a3 a4 a5 a6 _22730' fn fn' h1 h2). Qed.
Lemma lem1241937 {Z : Type'} (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (_22730' : type1540 Z) (fn : Ascii.ascii -> Z) (fn' : type1334 Z) (h1 : term60 Z _22730' fn') (h2 : fn = (term0 Z fn')) : term148 Z fn _22730' a0 a1 a2 a3 a4.
Proof. exact (fun a5 : Prop => @lem1241936 Z a0 a1 a2 a3 a4 a5 _22730' fn fn' h1 h2). Qed.
Lemma lem1241938 {Z : Type'} (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (_22730' : type1540 Z) (fn : Ascii.ascii -> Z) (fn' : type1334 Z) (h1 : term60 Z _22730' fn') (h2 : fn = (term0 Z fn')) : term149 Z fn _22730' a0 a1 a2 a3.
Proof. exact (fun a4 : Prop => @lem1241937 Z a0 a1 a2 a3 a4 _22730' fn fn' h1 h2). Qed.
Lemma lem1241939 {Z : Type'} (a0 : Prop) (a1 : Prop) (a2 : Prop) (_22730' : type1540 Z) (fn : Ascii.ascii -> Z) (fn' : type1334 Z) (h1 : term60 Z _22730' fn') (h2 : fn = (term0 Z fn')) : term150 Z fn _22730' a0 a1 a2.
Proof. exact (fun a3 : Prop => @lem1241938 Z a0 a1 a2 a3 _22730' fn fn' h1 h2). Qed.
Lemma lem1241940 {Z : Type'} (a0 : Prop) (a1 : Prop) (_22730' : type1540 Z) (fn : Ascii.ascii -> Z) (fn' : type1334 Z) (h1 : term60 Z _22730' fn') (h2 : fn = (term0 Z fn')) : term151 Z fn _22730' a0 a1.
Proof. exact (fun a2 : Prop => @lem1241939 Z a0 a1 a2 _22730' fn fn' h1 h2). Qed.
Lemma lem1241941 {Z : Type'} (a0 : Prop) (_22730' : type1540 Z) (fn : Ascii.ascii -> Z) (fn' : type1334 Z) (h1 : term60 Z _22730' fn') (h2 : fn = (term0 Z fn')) : term152 Z fn _22730' a0.
Proof. exact (fun a1 : Prop => @lem1241940 Z a0 a1 _22730' fn fn' h1 h2). Qed.
Lemma lem1241942 {Z : Type'} (_22730' : type1540 Z) (fn : Ascii.ascii -> Z) (fn' : type1334 Z) (h1 : term60 Z _22730' fn') (h2 : fn = (term0 Z fn')) : term153 Z fn _22730'.
Proof. exact (fun a0 : Prop => @lem1241941 Z a0 _22730' fn fn' h1 h2). Qed.
Lemma lem1241943 {Z : Type'} (fn : Ascii.ascii -> Z) (_22730' : type1540 Z) : (term154 Z _22730' fn) = (term153 Z fn _22730').
Proof. exact (eq_refl (term154 Z _22730' fn)). Qed.
Lemma lem1241944 {Z : Type'} : term155 Z.
Proof. exact (@lem9102 (Ascii.ascii -> Z)). Qed.
Lemma lem1241945 {Z : Type'} (_22730' : type1540 Z) : term156 Z _22730'.
Proof. exact (@lem1241944 Z (term157 Z _22730')). Qed.
Lemma lem1241946 {Z : Type'} (_22730' : type1540 Z) : (term156 Z _22730') = (term158 Z _22730').
Proof. exact (eq_refl (term156 Z _22730')). Qed.
Lemma lem1241947 {Z : Type'} (_22730' : type1540 Z) : term158 Z _22730'.
Proof. exact (EQ_MP (@lem1241946 Z _22730') (@lem1241945 Z _22730')). Qed.
Lemma lem1241948 {Z : Type'} (_22730' : type1540 Z) (fn : type1334 Z) : term159 Z _22730' fn.
Proof. exact (@lem1241947 Z _22730' (term0 Z fn)). Qed.
Lemma lem1241949 {Z : Type'} (fn : type1334 Z) (_22730' : type1540 Z) : (term159 Z _22730' fn) = (term160 Z fn _22730').
Proof. exact (eq_refl (term159 Z _22730' fn)). Qed.
Lemma lem1241950 {Z : Type'} (fn : type1334 Z) (_22730' : type1540 Z) : term160 Z fn _22730'.
Proof. exact (EQ_MP (@lem1241949 Z fn _22730') (@lem1241948 Z _22730' fn)). Qed.
Lemma lem1241951 {Z : Type'} (_22730' : type1540 Z) (fn : Ascii.ascii -> Z) : (term153 Z fn _22730') = (term154 Z _22730' fn).
Proof. exact (SYM (@lem1241943 Z fn _22730')). Qed.
Lemma lem1241952 {Z : Type'} (_22730' : type1540 Z) (fn : Ascii.ascii -> Z) (fn' : type1334 Z) (h1 : term60 Z _22730' fn') (h2 : fn = (term0 Z fn')) : term154 Z _22730' fn.
Proof. exact (EQ_MP (@lem1241951 Z _22730' fn) (@lem1241942 Z _22730' fn fn' h1 h2)). Qed.
Lemma lem1241953 {Z : Type'} (fn : Ascii.ascii -> Z) (_22730' : type1540 Z) (fn' : type1334 Z) (h1 : term60 Z _22730' fn') : term161 Z fn' _22730' fn.
Proof. exact (fun h0 : fn = (term0 Z fn') => @lem1241952 Z _22730' fn fn' h1 h0). Qed.
Lemma lem1241954 {Z : Type'} (_22730' : type1540 Z) (fn : type1334 Z) (h1 : term60 Z _22730' fn) : term162 Z fn _22730'.
Proof. exact (fun fn' : Ascii.ascii -> Z => @lem1241953 Z fn' _22730' fn h1). Qed.
Lemma lem1241955 {Z : Type'} (_22730' : type1540 Z) (fn : type1334 Z) (h1 : term60 Z _22730' fn) : term163 Z _22730'.
Proof. exact (@lem1241950 Z fn _22730' (@lem1241954 Z _22730' fn h1)). Qed.
Lemma lem1241956 {Z : Type'} (_22730' : type1540 Z) : term163 Z _22730'.
Proof. exact (ex_elim (@lem1241619 Z _22730') (fun fn : type1334 Z => fun h0 : term164 Z _22730' fn => @lem1241955 Z _22730' fn h0)). Qed.
Lemma lem1241957 {Z : Type'} : term165 Z.
Proof. exact (fun _22730' : type1540 Z => @lem1241956 Z _22730'). Qed.
