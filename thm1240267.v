Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1240267_term_abbrevs.
Require Import thm1240242_spec.
Lemma lem1240244 (a0 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term0 _22730')) : term1 char' _22730' a0.
Proof. exact (@lem1240242 char' _22730' h1 a0). Qed.
Lemma lem1240245 (char' : type1335) (_22730' : type1539) (a0 : Prop) : (term1 char' _22730' a0) = (term2 char' _22730' a0).
Proof. exact (eq_refl (term1 char' _22730' a0)). Qed.
Lemma lem1240246 (a0 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term0 _22730')) : term2 char' _22730' a0.
Proof. exact (EQ_MP (@lem1240245 char' _22730' a0) (@lem1240244 a0 char' _22730' h1)). Qed.
Lemma lem1240247 (a0 : Prop) (a1 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term0 _22730')) : term3 char' _22730' a0 a1.
Proof. exact (@lem1240246 a0 char' _22730' h1 a1). Qed.
Lemma lem1240248 (char' : type1335) (_22730' : type1539) (a0 : Prop) (a1 : Prop) : (term3 char' _22730' a0 a1) = (term4 char' _22730' a0 a1).
Proof. exact (eq_refl (term3 char' _22730' a0 a1)). Qed.
Lemma lem1240249 (a0 : Prop) (a1 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term0 _22730')) : term4 char' _22730' a0 a1.
Proof. exact (EQ_MP (@lem1240248 char' _22730' a0 a1) (@lem1240247 a0 a1 char' _22730' h1)). Qed.
Lemma lem1240250 (a0 : Prop) (a1 : Prop) (a2 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term0 _22730')) : term5 char' _22730' a0 a1 a2.
Proof. exact (@lem1240249 a0 a1 char' _22730' h1 a2). Qed.
Lemma lem1240251 (char' : type1335) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) : (term5 char' _22730' a0 a1 a2) = (term6 char' _22730' a0 a1 a2).
Proof. exact (eq_refl (term5 char' _22730' a0 a1 a2)). Qed.
Lemma lem1240252 (a0 : Prop) (a1 : Prop) (a2 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term0 _22730')) : term6 char' _22730' a0 a1 a2.
Proof. exact (EQ_MP (@lem1240251 char' _22730' a0 a1 a2) (@lem1240250 a0 a1 a2 char' _22730' h1)). Qed.
Lemma lem1240253 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term0 _22730')) : term7 char' _22730' a0 a1 a2 a3.
Proof. exact (@lem1240252 a0 a1 a2 char' _22730' h1 a3). Qed.
Lemma lem1240254 (char' : type1335) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) : (term7 char' _22730' a0 a1 a2 a3) = (term8 char' _22730' a0 a1 a2 a3).
Proof. exact (eq_refl (term7 char' _22730' a0 a1 a2 a3)). Qed.
Lemma lem1240255 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term0 _22730')) : term8 char' _22730' a0 a1 a2 a3.
Proof. exact (EQ_MP (@lem1240254 char' _22730' a0 a1 a2 a3) (@lem1240253 a0 a1 a2 a3 char' _22730' h1)). Qed.
Lemma lem1240256 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term0 _22730')) : term9 char' _22730' a0 a1 a2 a3 a4.
Proof. exact (@lem1240255 a0 a1 a2 a3 char' _22730' h1 a4). Qed.
Lemma lem1240257 (char' : type1335) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) : (term9 char' _22730' a0 a1 a2 a3 a4) = (term10 char' _22730' a0 a1 a2 a3 a4).
Proof. exact (eq_refl (term9 char' _22730' a0 a1 a2 a3 a4)). Qed.
Lemma lem1240258 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term0 _22730')) : term10 char' _22730' a0 a1 a2 a3 a4.
Proof. exact (EQ_MP (@lem1240257 char' _22730' a0 a1 a2 a3 a4) (@lem1240256 a0 a1 a2 a3 a4 char' _22730' h1)). Qed.
Lemma lem1240259 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term0 _22730')) : term11 char' _22730' a0 a1 a2 a3 a4 a5.
Proof. exact (@lem1240258 a0 a1 a2 a3 a4 char' _22730' h1 a5). Qed.
Lemma lem1240260 (char' : type1335) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) : (term11 char' _22730' a0 a1 a2 a3 a4 a5) = (term12 char' _22730' a0 a1 a2 a3 a4 a5).
Proof. exact (eq_refl (term11 char' _22730' a0 a1 a2 a3 a4 a5)). Qed.
Lemma lem1240261 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term0 _22730')) : term12 char' _22730' a0 a1 a2 a3 a4 a5.
Proof. exact (EQ_MP (@lem1240260 char' _22730' a0 a1 a2 a3 a4 a5) (@lem1240259 a0 a1 a2 a3 a4 a5 char' _22730' h1)). Qed.
Lemma lem1240262 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term0 _22730')) : term13 char' _22730' a0 a1 a2 a3 a4 a5 a6.
Proof. exact (@lem1240261 a0 a1 a2 a3 a4 a5 char' _22730' h1 a6). Qed.
Lemma lem1240263 (char' : type1335) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) : (term13 char' _22730' a0 a1 a2 a3 a4 a5 a6) = (term14 char' _22730' a0 a1 a2 a3 a4 a5 a6).
Proof. exact (eq_refl (term13 char' _22730' a0 a1 a2 a3 a4 a5 a6)). Qed.
Lemma lem1240264 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term0 _22730')) : term14 char' _22730' a0 a1 a2 a3 a4 a5 a6.
Proof. exact (EQ_MP (@lem1240263 char' _22730' a0 a1 a2 a3 a4 a5 a6) (@lem1240262 a0 a1 a2 a3 a4 a5 a6 char' _22730' h1)). Qed.
Lemma lem1240265 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term0 _22730')) : term15 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7.
Proof. exact (@lem1240264 a0 a1 a2 a3 a4 a5 a6 char' _22730' h1 a7). Qed.
Lemma lem1240266 (char' : type1335) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term15 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7) = (term16 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (eq_refl (term15 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1240267 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (char' : type1335) (_22730' : type1539) (h1 : char' = (term0 _22730')) : term16 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7.
Proof. exact (EQ_MP (@lem1240266 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7) (@lem1240265 a0 a1 a2 a3 a4 a5 a6 a7 char' _22730' h1)). Qed.
