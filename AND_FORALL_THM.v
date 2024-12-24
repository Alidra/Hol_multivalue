Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import AND_FORALL_THM_term_abbrevs.
Require Import thm32_spec.
Lemma lem5046 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem5048 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term1 A P.
Proof. exact (proj1 (@lem5046 A P Q h1)). Qed.
Lemma lem5058 {A : Type'} (_117 : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term2 A P _117.
Proof. exact (@lem5048 A P Q h1 _117). Qed.
Lemma lem5059 {A : Type'} (P : A -> Prop) (_117 : A) : (term2 A P _117) = (P _117).
Proof. exact (eq_refl (term2 A P _117)). Qed.
Lemma lem5060 {A : Type'} (_117 : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : P _117.
Proof. exact (EQ_MP (@lem5059 A P _117) (@lem5058 A _117 P Q h1)). Qed.
Lemma lem5061 {A : Type'} (x : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : P x.
Proof. exact (@lem5060 A x P Q h1). Qed.
Lemma lem5068 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (@lem5046 A P Q h1). Qed.
Lemma lem5069 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term1 A Q.
Proof. exact (proj2 (@lem5068 A P Q h1)). Qed.
Lemma lem5071 {A : Type'} (_118 : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term2 A Q _118.
Proof. exact (@lem5069 A P Q h1 _118). Qed.
Lemma lem5072 {A : Type'} (Q : A -> Prop) (_118 : A) : (term2 A Q _118) = (Q _118).
Proof. exact (eq_refl (term2 A Q _118)). Qed.
Lemma lem5073 {A : Type'} (_118 : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : Q _118.
Proof. exact (EQ_MP (@lem5072 A Q _118) (@lem5071 A _118 P Q h1)). Qed.
Lemma lem5074 {A : Type'} (x : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : Q x.
Proof. exact (@lem5073 A x P Q h1). Qed.
Lemma lem5081 {A : Type'} (x : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : P x.
Proof. exact (@lem5061 A x P Q h1). Qed.
Lemma lem5082 {A : Type'} (x : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term3 A P Q x.
Proof. exact (conj (@lem5081 A x P Q h1) (@lem5074 A x P Q h1)). Qed.
Lemma lem5087 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term4 A P Q.
Proof. exact (fun x : A => @lem5082 A x P Q h1). Qed.
Lemma lem5088 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term5 A P Q.
Proof. exact (fun h0 : term0 A P Q => @lem5087 A P Q h0). Qed.
Lemma lem5089 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term4 A P Q) : term4 A P Q.
Proof. exact (h1). Qed.
Lemma lem5090 {A : Type'} (_119 : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term4 A P Q) : term6 A P Q _119.
Proof. exact (@lem5089 A P Q h1 _119). Qed.
Lemma lem5091 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (_119 : A) : (term6 A P Q _119) = (term3 A P Q _119).
Proof. exact (eq_refl (term6 A P Q _119)). Qed.
Lemma lem5092 {A : Type'} (_119 : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term4 A P Q) : term3 A P Q _119.
Proof. exact (EQ_MP (@lem5091 A P Q _119) (@lem5090 A _119 P Q h1)). Qed.
Lemma lem5094 {A : Type'} (_119 : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term4 A P Q) : P _119.
Proof. exact (proj1 (@lem5092 A _119 P Q h1)). Qed.
Lemma lem5095 {A : Type'} (x : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term4 A P Q) : P x.
Proof. exact (@lem5094 A x P Q h1). Qed.
Lemma lem5101 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term4 A P Q) : term4 A P Q.
Proof. exact (@lem5089 A P Q h1). Qed.
Lemma lem5102 {A : Type'} (x : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term4 A P Q) : (term4 A P Q) = (P x).
Proof. exact (prop_ext (fun h2 : term4 A P Q => @lem5095 A x P Q h1) (fun h2 : P x => @lem5101 A P Q h1)). Qed.
Lemma lem5103 {A : Type'} (x : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term4 A P Q) : P x.
Proof. exact (EQ_MP (@lem5102 A x P Q h1) (@lem5101 A P Q h1)). Qed.
Lemma lem5108 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term4 A P Q) : term1 A P.
Proof. exact (fun x : A => @lem5103 A x P Q h1). Qed.
Lemma lem5109 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term4 A P Q) : term4 A P Q.
Proof. exact (@lem5089 A P Q h1). Qed.
Lemma lem5110 {A : Type'} (_120 : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term4 A P Q) : term6 A P Q _120.
Proof. exact (@lem5109 A P Q h1 _120). Qed.
Lemma lem5111 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (_120 : A) : (term6 A P Q _120) = (term3 A P Q _120).
Proof. exact (eq_refl (term6 A P Q _120)). Qed.
Lemma lem5112 {A : Type'} (_120 : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term4 A P Q) : term3 A P Q _120.
Proof. exact (EQ_MP (@lem5111 A P Q _120) (@lem5110 A _120 P Q h1)). Qed.
Lemma lem5113 {A : Type'} (_120 : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term4 A P Q) : Q _120.
Proof. exact (proj2 (@lem5112 A _120 P Q h1)). Qed.
Lemma lem5115 {A : Type'} (x : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term4 A P Q) : Q x.
Proof. exact (@lem5113 A x P Q h1). Qed.
Lemma lem5121 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term4 A P Q) : term4 A P Q.
Proof. exact (@lem5109 A P Q h1). Qed.
Lemma lem5122 {A : Type'} (x : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term4 A P Q) : (term4 A P Q) = (Q x).
Proof. exact (prop_ext (fun h2 : term4 A P Q => @lem5115 A x P Q h1) (fun h2 : Q x => @lem5121 A P Q h1)). Qed.
Lemma lem5123 {A : Type'} (x : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term4 A P Q) : Q x.
Proof. exact (EQ_MP (@lem5122 A x P Q h1) (@lem5121 A P Q h1)). Qed.
Lemma lem5128 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term4 A P Q) : term1 A Q.
Proof. exact (fun x : A => @lem5123 A x P Q h1). Qed.
Lemma lem5129 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term4 A P Q) : term1 A P.
Proof. exact (@lem5108 A P Q h1). Qed.
Lemma lem5130 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term4 A P Q) : term0 A P Q.
Proof. exact (conj (@lem5129 A P Q h1) (@lem5128 A P Q h1)). Qed.
Lemma lem5131 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term7 A P Q.
Proof. exact (fun h0 : term4 A P Q => @lem5130 A P Q h0). Qed.
Lemma lem5132 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term5 A P Q.
Proof. exact (@lem5088 A P Q). Qed.
Lemma lem5133 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term8 A P Q.
Proof. exact (conj (@lem5132 A P Q) (@lem5131 A P Q)). Qed.
Lemma lem5134 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term8 A P Q) = ((term0 A P Q) = (term4 A P Q)).
Proof. exact (@lem32 (term0 A P Q) (term4 A P Q)). Qed.
Lemma lem5135 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term0 A P Q) = (term4 A P Q).
Proof. exact (EQ_MP (@lem5134 A P Q) (@lem5133 A P Q)). Qed.
Lemma lem5140 {A : Type'} (P : A -> Prop) : term9 A P.
Proof. exact (fun Q : A -> Prop => @lem5135 A P Q). Qed.
Lemma lem5145 {A : Type'} : term10 A.
Proof. exact (fun P : A -> Prop => @lem5140 A P). Qed.
Lemma lem5146 {A : Type'} : term10 A.
Proof. exact (@lem5145 A). Qed.
