Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1066987_term_abbrevs.
Require Import thm1066944_spec.
Require Import thm1066972_spec.
Lemma lem1066973 {A B : Type'} (INL' : type1431 A B) (a : A) : (INL' a) = (INL' a).
Proof. exact (eq_refl (INL' a)). Qed.
Lemma lem1066974 {A B : Type'} (a : A) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : INL' = (term0 A B)) (h2 : INR' = (term1 A B)) (h3 : sum' = (term2 A B INL' INR')) : (term3 A B sum' INL' a) = (term4 A B INL' a).
Proof. exact (MK_COMB (@lem1066972 A B sum' INL' INR' h1 h2 h3) (@lem1066973 A B INL' a)). Qed.
Lemma lem1066975 {A B : Type'} (a : A) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : INL' = (term0 A B)) (h2 : INR' = (term1 A B)) (h3 : sum' = (term2 A B INL' INR')) : term4 A B INL' a.
Proof. exact (EQ_MP (@lem1066974 A B a sum' INL' INR' h1 h2 h3) (@lem1066944 A B a sum' INL' INR' h3)). Qed.
Lemma lem1066976 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) : (term2 A B INL' INR') = (term2 A B INL' INR').
Proof. exact (eq_refl (term2 A B INL' INR')). Qed.
Lemma lem1066977 {A B : Type'} (sum' : type1333 A B) (a : A) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : INL' = (term0 A B)) (h2 : INR' = (term1 A B)) : term5 A B sum' INR' INL' a.
Proof. exact (fun h0 : sum' = (term2 A B INL' INR') => @lem1066975 A B a sum' INL' INR' h1 h2 h0). Qed.
Lemma lem1066978 {A B : Type'} (a : A) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : INL' = (term0 A B)) (h2 : INR' = (term1 A B)) : term6 A B INR' INL' a.
Proof. exact (@lem1066977 A B (term2 A B INL' INR') a INL' INR' h1 h2). Qed.
Lemma lem1066979 {A B : Type'} (a : A) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : INL' = (term0 A B)) (h2 : INR' = (term1 A B)) : term4 A B INL' a.
Proof. exact (@lem1066978 A B a INL' INR' h1 h2 (@lem1066976 A B INL' INR')). Qed.
Lemma lem1066980 {A B : Type'} : (term1 A B) = (term1 A B).
Proof. exact (eq_refl (term1 A B)). Qed.
Lemma lem1066981 {A B : Type'} (INR' : type1479 A B) (a : A) (INL' : type1431 A B) (h1 : INL' = (term0 A B)) : term7 A B INR' INL' a.
Proof. exact (fun h0 : INR' = (term1 A B) => @lem1066979 A B a INL' INR' h1 h0). Qed.
Lemma lem1066982 {A B : Type'} (a : A) (INL' : type1431 A B) (h1 : INL' = (term0 A B)) : term8 A B INL' a.
Proof. exact (@lem1066981 A B (term1 A B) a INL' h1). Qed.
Lemma lem1066983 {A B : Type'} (a : A) (INL' : type1431 A B) (h1 : INL' = (term0 A B)) : term4 A B INL' a.
Proof. exact (@lem1066982 A B a INL' h1 (@lem1066980 A B)). Qed.
Lemma lem1066984 {A B : Type'} : (term0 A B) = (term0 A B).
Proof. exact (eq_refl (term0 A B)). Qed.
Lemma lem1066985 {A B : Type'} (INL' : type1431 A B) (a : A) : term9 A B INL' a.
Proof. exact (fun h0 : INL' = (term0 A B) => @lem1066983 A B a INL' h0). Qed.
Lemma lem1066986 {A B : Type'} (a : A) : term10 A B a.
Proof. exact (@lem1066985 A B (term0 A B) a). Qed.
Lemma lem1066987 {A B : Type'} (a : A) : term11 A B a.
Proof. exact (@lem1066986 A B a (@lem1066984 A B)). Qed.
