Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1066972_term_abbrevs.
Require Import thm1066571_spec.
Require Import thm1066572_spec.
Lemma lem1066948 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum' = (term0 A B INL' INR')) : sum' = (term0 A B INL' INR').
Proof. exact (h1). Qed.
Lemma lem1066949 {A B : Type'} : (term1 A B) = (term1 A B).
Proof. exact (eq_refl (term1 A B)). Qed.
Lemma lem1066950 {A B : Type'} (INL' : type1431 A B) (h1 : INL' = (term2 A B)) : (term3 A B INL') = (term4 A B).
Proof. exact (MK_COMB (@lem1066949 A B) (@lem1066571 A B INL' h1)). Qed.
Lemma lem1066951 {A B : Type'} : (term4 A B) = (term5 A B).
Proof. exact (eq_refl (term4 A B)). Qed.
Lemma lem1066952 {A B : Type'} (INL' : type1431 A B) : (term6 A B INL') = (term6 A B INL').
Proof. exact (eq_refl (term6 A B INL')). Qed.
Lemma lem1066953 {A B : Type'} (INL' : type1431 A B) : ((term3 A B INL') = (term4 A B)) = ((term3 A B INL') = (term5 A B)).
Proof. exact (MK_COMB (@lem1066952 A B INL') (@lem1066951 A B)). Qed.
Lemma lem1066954 {A B : Type'} (INL' : type1431 A B) : (term3 A B INL') = (term7 A B INL').
Proof. exact (eq_refl (term3 A B INL')). Qed.
Lemma lem1066955 {A B : Type'} : (@eq ((B -> recspace (prod A B)) -> (recspace (prod A B)) -> Prop)) = (@eq ((B -> recspace (prod A B)) -> (recspace (prod A B)) -> Prop)).
Proof. exact (eq_refl (@eq ((B -> recspace (prod A B)) -> (recspace (prod A B)) -> Prop))). Qed.
Lemma lem1066956 {A B : Type'} (INL' : type1431 A B) : (term6 A B INL') = (term8 A B INL').
Proof. exact (MK_COMB (@lem1066955 A B) (@lem1066954 A B INL')). Qed.
Lemma lem1066957 {A B : Type'} : (term5 A B) = (term5 A B).
Proof. exact (eq_refl (term5 A B)). Qed.
Lemma lem1066958 {A B : Type'} (INL' : type1431 A B) : ((term3 A B INL') = (term5 A B)) = ((term7 A B INL') = (term5 A B)).
Proof. exact (MK_COMB (@lem1066956 A B INL') (@lem1066957 A B)). Qed.
Lemma lem1066959 {A B : Type'} (INL' : type1431 A B) : ((term3 A B INL') = (term4 A B)) = ((term7 A B INL') = (term5 A B)).
Proof. exact (TRANS (@lem1066953 A B INL') (@lem1066958 A B INL')). Qed.
Lemma lem1066960 {A B : Type'} (INL' : type1431 A B) (h1 : INL' = (term2 A B)) : (term7 A B INL') = (term5 A B).
Proof. exact (EQ_MP (@lem1066959 A B INL') (@lem1066950 A B INL' h1)). Qed.
Lemma lem1066961 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (h1 : INL' = (term2 A B)) (h2 : INR' = (term9 A B)) : (term10 A B INL' INR') = (term11 A B).
Proof. exact (MK_COMB (@lem1066960 A B INL' h1) (@lem1066572 A B INR' h2)). Qed.
Lemma lem1066962 {A B : Type'} : (term11 A B) = (term12 A B).
Proof. exact (eq_refl (term11 A B)). Qed.
Lemma lem1066963 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) : (term13 A B INL' INR') = (term13 A B INL' INR').
Proof. exact (eq_refl (term13 A B INL' INR')). Qed.
Lemma lem1066964 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) : ((term10 A B INL' INR') = (term11 A B)) = ((term10 A B INL' INR') = (term12 A B)).
Proof. exact (MK_COMB (@lem1066963 A B INL' INR') (@lem1066962 A B)). Qed.
Lemma lem1066965 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) : (term10 A B INL' INR') = (term0 A B INL' INR').
Proof. exact (eq_refl (term10 A B INL' INR')). Qed.
Lemma lem1066966 {A B : Type'} : (@eq ((recspace (prod A B)) -> Prop)) = (@eq ((recspace (prod A B)) -> Prop)).
Proof. exact (eq_refl (@eq ((recspace (prod A B)) -> Prop))). Qed.
Lemma lem1066967 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) : (term13 A B INL' INR') = (term14 A B INL' INR').
Proof. exact (MK_COMB (@lem1066966 A B) (@lem1066965 A B INL' INR')). Qed.
Lemma lem1066968 {A B : Type'} : (term12 A B) = (term12 A B).
Proof. exact (eq_refl (term12 A B)). Qed.
Lemma lem1066969 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) : ((term10 A B INL' INR') = (term12 A B)) = ((term0 A B INL' INR') = (term12 A B)).
Proof. exact (MK_COMB (@lem1066967 A B INL' INR') (@lem1066968 A B)). Qed.
Lemma lem1066970 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) : ((term10 A B INL' INR') = (term11 A B)) = ((term0 A B INL' INR') = (term12 A B)).
Proof. exact (TRANS (@lem1066964 A B INL' INR') (@lem1066969 A B INL' INR')). Qed.
Lemma lem1066971 {A B : Type'} (INL' : type1431 A B) (INR' : type1479 A B) (h1 : INL' = (term2 A B)) (h2 : INR' = (term9 A B)) : (term0 A B INL' INR') = (term12 A B).
Proof. exact (EQ_MP (@lem1066970 A B INL' INR') (@lem1066961 A B INL' INR' h1 h2)). Qed.
Lemma lem1066972 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : INL' = (term2 A B)) (h2 : INR' = (term9 A B)) (h3 : sum' = (term0 A B INL' INR')) : sum' = (term12 A B).
Proof. exact (TRANS (@lem1066948 A B sum' INL' INR' h3) (@lem1066971 A B INL' INR' h1 h2)). Qed.
