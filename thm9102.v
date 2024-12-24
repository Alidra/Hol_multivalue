Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm9102_term_abbrevs.
Require Import thm1809_spec.
Require Import thm1810_spec.
Lemma lem8960 {A : Type'} : (@ex A) = (term0 A).
Proof. exact (@ex_def A). Qed.
Lemma lem8973 {A : Type'} (P : A -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem8974 {A : Type'} (P : A -> Prop) : (ex P) = (term1 A P).
Proof. exact (MK_COMB (@lem8960 A) (@lem8973 A P)). Qed.
Lemma lem8976 {A B : Type'} (f : A -> B) (y : A) : (term2 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8977 {A : Type'} (f : type686 A) (y : A -> Prop) : (term3 A f y) = (f y).
Proof. exact (@lem8976 (A -> Prop) Prop f y). Qed.
Lemma lem8978 {A : Type'} (P : A -> Prop) : (term4 A P) = (term1 A P).
Proof. exact (@lem8977 A (term0 A) P). Qed.
Lemma lem8979 {A : Type'} (P : A -> Prop) : (term1 A P) = (term5 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem8980 {A : Type'} : (term6 A) = (term0 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem8979 A P)). Qed.
Lemma lem8981 {A : Type'} (P : A -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem8982 {A : Type'} (P : A -> Prop) : (term4 A P) = (term1 A P).
Proof. exact (MK_COMB (@lem8980 A) (@lem8981 A P)). Qed.
Lemma lem8983 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8984 {A : Type'} (P : A -> Prop) : (term7 A P) = (term8 A P).
Proof. exact (MK_COMB (@lem8983) (@lem8982 A P)). Qed.
Lemma lem8985 {A : Type'} (P : A -> Prop) : (term1 A P) = (term5 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem8986 {A : Type'} (P : A -> Prop) : ((term4 A P) = (term1 A P)) = ((term1 A P) = (term5 A P)).
Proof. exact (MK_COMB (@lem8984 A P) (@lem8985 A P)). Qed.
Lemma lem8987 {A : Type'} (P : A -> Prop) : (term1 A P) = (term5 A P).
Proof. exact (EQ_MP (@lem8986 A P) (@lem8978 A P)). Qed.
Lemma lem9000 {A : Type'} (P : A -> Prop) : (ex P) = (term5 A P).
Proof. exact (TRANS (@lem8974 A P) (@lem8987 A P)). Qed.
Lemma lem9001 {A : Type'} (t : A) (P : A -> Prop) : (term9 A t P) = (term9 A t P).
Proof. exact (eq_refl (term9 A t P)). Qed.
Lemma lem9002 {A : Type'} (t : A) (P : A -> Prop) : (term10 A t P) = (term11 A t P).
Proof. exact (MK_COMB (@lem9001 A t P) (@lem9000 A P)). Qed.
Lemma lem9005 {A : Type'} (P : A -> Prop) : (term12 A P) = (term13 A P).
Proof. exact (fun_ext (fun t : A => @lem9002 A t P)). Qed.
Lemma lem9006 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem9007 {A : Type'} (P : A -> Prop) : (term14 A P) = (term15 A P).
Proof. exact (MK_COMB (@lem9006 A) (@lem9005 A P)). Qed.
Lemma lem9012 {A : Type'} : (term16 A) = (term17 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem9007 A P)). Qed.
Lemma lem9013 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem9014 {A : Type'} : (term18 A) = (term19 A).
Proof. exact (MK_COMB (@lem9013 A) (@lem9012 A)). Qed.
Lemma lem9019 {A : Type'} : (term19 A) = (term18 A).
Proof. exact (SYM (@lem9014 A)). Qed.
Lemma lem9022 {A : Type'} (t : A) (P : A -> Prop) (h1 : term20 A t P) : term20 A t P.
Proof. exact (h1). Qed.
Lemma lem9023 {A : Type'} (P : A -> Prop) (q : Prop) (h1 : term21 A P q) : term21 A P q.
Proof. exact (h1). Qed.
Lemma lem9024 {A : Type'} (P : A -> Prop) (q : Prop) (h1 : term21 A P q) : term21 A P q.
Proof. exact (h1). Qed.
Lemma lem9025 {A : Type'} (x : A) (P : A -> Prop) (q : Prop) (h1 : term21 A P q) : term22 A P q x.
Proof. exact (@lem9024 A P q h1 x). Qed.
Lemma lem9026 {A : Type'} (P : A -> Prop) (x : A) (q : Prop) : (term22 A P q x) = (term23 A P x q).
Proof. exact (eq_refl (term22 A P q x)). Qed.
Lemma lem9027 {A : Type'} (x : A) (P : A -> Prop) (q : Prop) (h1 : term21 A P q) : term23 A P x q.
Proof. exact (EQ_MP (@lem9026 A P x q) (@lem9025 A x P q h1)). Qed.
Lemma lem9028 {A : Type'} (P : A -> Prop) (x : A) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem9029 {A : Type'} (q : Prop) (P : A -> Prop) (x : A) (h1 : term21 A P q) (h2 : P x) : q.
Proof. exact (@lem9027 A x P q h1 (@lem9028 A P x h2)). Qed.
Lemma lem9030 {A : Type'} (q : Prop) (P : A -> Prop) (x : A) (h1 : P x) : term24 A P q.
Proof. exact (fun h0 : term21 A P q => @lem9029 A q P x h0 h1). Qed.
Lemma lem9031 {A : Type'} (P : A -> Prop) (h1 : term25 A P) : term25 A P.
Proof. exact (h1). Qed.
Lemma lem9032 {A : Type'} (q : Prop) (P : A -> Prop) (h1 : term25 A P) : term24 A P q.
Proof. exact (ex_elim (@lem9031 A P h1) (fun x : A => fun h0 : term26 A P x => @lem9030 A q P x h0)). Qed.
Lemma lem9033 {A : Type'} (P : A -> Prop) (q : Prop) (h1 : term21 A P q) : term21 A P q.
Proof. exact (h1). Qed.
Lemma lem9034 {A : Type'} (q : Prop) (P : A -> Prop) (h1 : term21 A P q) (h2 : term25 A P) : q.
Proof. exact (@lem9032 A q P h2 (@lem9033 A P q h1)). Qed.
Lemma lem9035 {A : Type'} (P : A -> Prop) (q : Prop) (h1 : term21 A P q) : term27 A P q.
Proof. exact (fun h0 : term25 A P => @lem9034 A q P h1 h0). Qed.
Lemma lem9036 {A : Type'} (P : A -> Prop) (q : Prop) : term28 A P q.
Proof. exact (fun h0 : term21 A P q => @lem9035 A P q h0). Qed.
Lemma lem9039 {A : Type'} (P : A -> Prop) (q : Prop) (h1 : term21 A P q) : term27 A P q.
Proof. exact (@lem9036 A P q (@lem9023 A P q h1)). Qed.
Lemma lem9056 {A : Type'} (t : A) (P : A -> Prop) (h1 : term20 A t P) : term20 A t P.
Proof. exact (h1). Qed.
Lemma lem9057 {A : Type'} (x : A) (t : A) (P : A -> Prop) (h1 : term20 A t P) : term29 A t P x.
Proof. exact (@lem9056 A t P h1 x). Qed.
Lemma lem9058 {A : Type'} (t : A) (P : A -> Prop) (x : A) : (term29 A t P x) = (term30 A t P x).
Proof. exact (eq_refl (term29 A t P x)). Qed.
Lemma lem9059 {A : Type'} (x : A) (t : A) (P : A -> Prop) (h1 : term20 A t P) : term30 A t P x.
Proof. exact (EQ_MP (@lem9058 A t P x) (@lem9057 A x t P h1)). Qed.
Lemma lem9060 {A : Type'} (x : A) (t : A) (h1 : x = t) : x = t.
Proof. exact (h1). Qed.
Lemma lem9061 {A : Type'} (P : A -> Prop) (x : A) (t : A) (h1 : term20 A t P) (h2 : x = t) : P x.
Proof. exact (@lem9059 A x t P h1 (@lem9060 A x t h2)). Qed.
Lemma lem9062 {A : Type'} (P : A -> Prop) (x : A) (t : A) (h1 : x = t) : term31 A t P x.
Proof. exact (fun h0 : term20 A t P => @lem9061 A P x t h0 h1). Qed.
Lemma lem9063 {A : Type'} (t : A) (P : A -> Prop) (h1 : term20 A t P) : term20 A t P.
Proof. exact (h1). Qed.
Lemma lem9064 {A : Type'} (P : A -> Prop) (x : A) (t : A) (h1 : term20 A t P) (h2 : x = t) : P x.
Proof. exact (@lem9062 A P x t h2 (@lem9063 A t P h1)). Qed.
Lemma lem9065 {A : Type'} (x : A) (t : A) (P : A -> Prop) (h1 : term20 A t P) : term30 A t P x.
Proof. exact (fun h0 : x = t => @lem9064 A P x t h1 h0). Qed.
Lemma lem9066 {A : Type'} (t : A) (P : A -> Prop) (h1 : term20 A t P) : term20 A t P.
Proof. exact (fun x : A => @lem9065 A x t P h1). Qed.
Lemma lem9067 {A : Type'} (t : A) (P : A -> Prop) : term32 A t P.
Proof. exact (fun h0 : term20 A t P => @lem9066 A t P h0). Qed.
Lemma lem9068 {A : Type'} (t : A) (P : A -> Prop) (h1 : term20 A t P) : term20 A t P.
Proof. exact (@lem9067 A t P (@lem9022 A t P h1)). Qed.
Lemma lem9069 {A : Type'} (x : A) (t : A) (P : A -> Prop) (h1 : term20 A t P) : term29 A t P x.
Proof. exact (@lem9068 A t P h1 x). Qed.
Lemma lem9070 {A : Type'} (t : A) (P : A -> Prop) (x : A) : (term29 A t P x) = (term30 A t P x).
Proof. exact (eq_refl (term29 A t P x)). Qed.
Lemma lem9073 {A : Type'} (x : A) (t : A) (P : A -> Prop) (h1 : term20 A t P) : term30 A t P x.
Proof. exact (EQ_MP (@lem9070 A t P x) (@lem9069 A x t P h1)). Qed.
Lemma lem9074 {A : Type'} (x : A) (t : A) (P : A -> Prop) (h1 : term20 A t P) : term30 A t P x.
Proof. exact (@lem9073 A x t P h1). Qed.
Lemma lem9075 {A : Type'} (t : A) (P : A -> Prop) (h1 : term20 A t P) : term33 A P t.
Proof. exact (@lem9074 A t t P h1). Qed.
Lemma lem9076 {A : Type'} (t : A) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem9077 {A : Type'} (t : A) (P : A -> Prop) (h1 : term20 A t P) : P t.
Proof. exact (@lem9075 A t P h1 (@lem9076 A t)). Qed.
Lemma lem9078 {A : Type'} (t : A) (P : A -> Prop) (h1 : term20 A t P) : term25 A P.
Proof. exact (ex_intro (term26 A P) t (@lem9077 A t P h1)). Qed.
Lemma lem9079 {A : Type'} (q : Prop) (t : A) (P : A -> Prop) (h1 : term21 A P q) (h2 : term20 A t P) : q.
Proof. exact (@lem9039 A P q h1 (@lem9078 A t P h2)). Qed.
Lemma lem9080 {A : Type'} (q : Prop) (t : A) (P : A -> Prop) (h1 : term21 A P q) (h2 : term20 A t P) : (term21 A P q) = q.
Proof. exact (prop_ext (fun h3 : term21 A P q => @lem9079 A q t P h1 h2) (fun h3 : q => @lem9023 A P q h1)). Qed.
Lemma lem9081 {A : Type'} (q : Prop) (t : A) (P : A -> Prop) (h1 : term21 A P q) (h2 : term20 A t P) : q.
Proof. exact (EQ_MP (@lem9080 A q t P h1 h2) (@lem9023 A P q h1)). Qed.
Lemma lem9082 {A : Type'} (q : Prop) (t : A) (P : A -> Prop) (h1 : term20 A t P) : term24 A P q.
Proof. exact (fun h0 : term21 A P q => @lem9081 A q t P h0 h1). Qed.
Lemma lem9087 {A : Type'} (t : A) (P : A -> Prop) (h1 : term20 A t P) : term5 A P.
Proof. exact (fun q : Prop => @lem9082 A q t P h1). Qed.
Lemma lem9088 {A : Type'} (t : A) (P : A -> Prop) (h1 : term20 A t P) : (term20 A t P) = (term5 A P).
Proof. exact (prop_ext (fun h2 : term20 A t P => @lem9087 A t P h1) (fun h2 : term5 A P => @lem9022 A t P h1)). Qed.
Lemma lem9089 {A : Type'} (t : A) (P : A -> Prop) (h1 : term20 A t P) : term5 A P.
Proof. exact (EQ_MP (@lem9088 A t P h1) (@lem9022 A t P h1)). Qed.
Lemma lem9090 {A : Type'} (t : A) (P : A -> Prop) : term11 A t P.
Proof. exact (fun h0 : term20 A t P => @lem9089 A t P h0). Qed.
Lemma lem9095 {A : Type'} (P : A -> Prop) : term15 A P.
Proof. exact (fun t : A => @lem9090 A t P). Qed.
Lemma lem9101 {A : Type'} : term19 A.
Proof. exact (fun P : A -> Prop => @lem9095 A P). Qed.
Lemma lem9102 {A : Type'} : term18 A.
Proof. exact (EQ_MP (@lem9019 A) (@lem9101 A)). Qed.
